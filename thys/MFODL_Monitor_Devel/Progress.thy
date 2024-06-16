(*<*)
theory Progress
  imports Safety
begin
(*>*)


section \<open> Verdict delay \<close>


subsection \<open> Pred and rel mapping \<close>

definition "pred_mapping Q = pred_fun (\<lambda>_. True) (pred_option Q)"
definition "rel_mapping Q = rel_fun (=) (rel_option Q)"

lemma pred_mapping_alt: "pred_mapping Q P = (\<forall>p \<in> dom P. Q (the (P p)))"
  unfolding pred_mapping_def pred_fun_def option.pred_set dom_def
  by (force split: option.splits)

lemma rel_mapping_alt: "rel_mapping Q P P' = (dom P = dom P' \<and> (\<forall>p \<in> dom P. Q (the (P p)) (the (P' p))))"
  unfolding rel_mapping_def rel_fun_def rel_option_iff dom_def
  by (force split: option.splits)

lemma rel_mapping_reflp: "reflp Q \<Longrightarrow> rel_mapping Q P P"
  by (auto simp: rel_mapping_alt reflp_def)

lemma rel_mapping_map_upd[simp]: "Q x y \<Longrightarrow> rel_mapping Q P P' \<Longrightarrow> rel_mapping Q (P(p \<mapsto> x)) (P'(p \<mapsto> y))"
  by (auto simp: rel_mapping_alt)

lemma rel_mapping_order_refl: "rel_mapping (\<le>) (x::'a \<rightharpoonup> 'b::order) x"
  by (intro rel_mapping_reflp reflpI order_refl)

lemma rel_mapping_le_map_upd[simp]: "(x::'a::order) \<le> y \<Longrightarrow> rel_mapping (\<le>) (P(p \<mapsto> x)) (P(p \<mapsto> y))"
  by (simp add: rel_mapping_order_refl)

lemma pred_mapping_map_upd[simp]: "Q x \<Longrightarrow> pred_mapping Q P \<Longrightarrow> pred_mapping Q (P(p \<mapsto> x))"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_fun_upd[simp]: "(case x of Some x \<Rightarrow> Q x | _ \<Rightarrow> True) \<Longrightarrow> pred_mapping Q P \<Longrightarrow> pred_mapping Q (P(p := x))"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_empty[simp]: "pred_mapping Q Map.empty"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_mono: "pred_mapping Q P \<Longrightarrow> Q \<le> R \<Longrightarrow> pred_mapping R P"
  by (auto simp: pred_mapping_alt)

lemma pred_mapping_mono_strong: "pred_mapping Q P \<Longrightarrow>
  (\<And>p. p \<in> dom P \<Longrightarrow> Q (the (P p)) \<Longrightarrow> R (the (P p))) \<Longrightarrow> pred_mapping R P"
  by (auto simp: pred_mapping_alt)

lemma rel_mapping_trans: "P OO Q \<le> R \<Longrightarrow>
  rel_mapping P P1 P2 \<Longrightarrow> rel_mapping Q P2 P3 \<Longrightarrow> rel_mapping R P1 P3"
  by (force simp: rel_mapping_alt dom_def set_eq_iff)

abbreviation range_mapping :: "nat \<Rightarrow> nat \<Rightarrow> ('b \<Rightarrow> nat option) \<Rightarrow> bool" where
  "range_mapping i j P \<equiv> pred_mapping (\<lambda>x. i \<le> x \<and> x \<le> j) P"

lemma range_mapping_relax:
  "range_mapping i j P \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<ge> j \<Longrightarrow> range_mapping i' j' P"
  by (auto simp: pred_mapping_alt dom_def set_eq_iff split: option.splits)

lemma pred_mapping_le:
  "pred_mapping ((\<le>) i) P1 \<Longrightarrow> rel_mapping (\<le>) P1 P2 
  \<Longrightarrow> pred_mapping ((\<le>) (i :: nat)) P2"
  by (force simp: rel_mapping_alt pred_mapping_alt dom_def set_eq_iff)

lemma pred_mapping_le':
  "pred_mapping ((\<le>) j) P1 \<Longrightarrow> i \<le> j \<Longrightarrow> rel_mapping (\<le>) P1 P2 
  \<Longrightarrow> pred_mapping ((\<le>) (i :: nat)) P2"
  by (force simp: rel_mapping_alt pred_mapping_alt dom_def set_eq_iff)


subsection \<open> Progress function \<close>

context fixes \<sigma> :: "'a trace" begin

function (sequential) progress :: "(Formula.name \<times> nat \<rightharpoonup> nat) \<Rightarrow> 't Formula.formula \<Rightarrow> nat \<Rightarrow> nat" where
  "progress P (Formula.Pred e ts) j = (case P (e, length ts) of None \<Rightarrow> j | Some k \<Rightarrow> k)"
| "progress P (Formula.Let p \<phi> \<psi>) j = progress (P((p, Formula.nfv \<phi>) \<mapsto> progress P \<phi> j)) \<psi> j"
| "progress P (Formula.LetPast p \<phi> \<psi>) j =
    (let pn = (p, Formula.nfv \<phi>) in
    progress (P(pn \<mapsto> \<Sqinter>{i. i \<le> j \<and> i = progress (P(pn \<mapsto> i)) \<phi> j})) \<psi> j)"
| "progress P (Formula.Eq t1 t2) j = j"
| "progress P (Formula.Less t1 t2) j = j"
| "progress P (Formula.LessEq t1 t2) j = j"
| "progress P (Formula.Neg \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Or \<phi> \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.And \<phi> \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.Ands l) j = (if l = [] then j else Min (set (map (\<lambda>\<phi>. progress P \<phi> j) l)))"
| "progress P (Formula.Exists t \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Agg y \<omega> b f \<phi>) j = progress P \<phi> j"
| "progress P (Formula.Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress P \<phi> j)) j)"
| "progress P (Formula.Next I \<phi>) j = progress P \<phi> j - 1"
| "progress P (Formula.Since \<phi> I \<psi>) j = min (progress P \<phi> j)
    (if memL I 0 then progress P \<psi> j else Suc (progress P \<psi> j))"
| "progress P (Formula.Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress P \<phi> j) (progress P \<psi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
| "progress P (Formula.Trigger \<phi> I \<psi>) j = min (progress P \<phi> j) (progress P \<psi> j)"
| "progress P (Formula.Release \<phi> I \<psi>) j = (
    \<comment> \<open>for an actual implementation use Inf {i. \<forall>k. k < j \<and> k \<le> min (progress P \<phi> j) (progress P \<psi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)},
    for the rewrite rules the following is necessary as the rewrite rule of always leads to a
    funny term\<close>
    \<comment> \<open>the not bounded condition here just allows the rewrite formula to be applied in the else case\<close>
    if mem I 0 \<or> \<not> bounded I then
      Inf ({i. \<forall>k. k < j \<and> k \<le> min (progress P \<psi> j) (progress P \<phi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<union>
          {i. \<forall>k. k < j \<and> k \<le> progress P \<psi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)})
    else
      (progress P (release_safe_bounded \<phi> I \<psi>) j)
    )"
| "progress P (Formula.MatchP I r) j = min_regex_default (progress P) r j"
| "progress P (Formula.MatchF I r) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min_regex_default (progress P) r j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
| "progress P (Formula.TP t) j = j"
| "progress P (Formula.TS t) j = j"
  by pat_completeness auto
termination
  using size'_and_release size'_Release size'_Or size'_release_aux
  by (relation "measure (\<lambda>(_, \<phi>, _). size' \<phi>)")
  (auto simp add: Nat.less_Suc_eq_le eventually_def Formula.TT_def Formula.FF_def 
    dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size')

(* sanity check for trigger progress *)

lemma progress_FF [simp]: "progress P Formula.FF j = j"
  unfolding Formula.FF_def
  by auto

lemma progress_TT [simp]: "progress P Formula.TT j = j"
  unfolding Formula.TT_def
  by auto

lemma progress_first [simp]: "progress P Formula.first j = j"
  unfolding Formula.first_def
  by auto

lemma progress_Until_le: "progress P (Formula.Until \<phi> I \<psi>) j \<le> min (progress P \<phi> j) (progress P \<psi> j)"
  by (auto simp: trans_le_add1 intro!: cInf_lower)

lemma progress_once [simp]: "progress P (once I \<phi>) j
  = (if memL I 0 then min j (progress P \<phi> j) else min j (Suc (progress P \<phi> j)))"
  unfolding once_def
  by auto

lemma progress_eventually: "progress P (eventually I \<phi>) j
  = Inf {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  unfolding eventually_def
  by (auto intro: arg_cong[where f = Inf])

lemma progress_always_safe_0 [simp]: "progress P (always_safe_0 I \<phi>) j =
  Inf {i. \<forall>k. k < j \<and> k \<le> progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
proof -
  have set_eq: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> Suc (local.progress P \<phi> j) \<and> k \<le> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)} =
        {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  have subset: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<subseteq>
  {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    using memR_flip_int_double_upper
    by auto
  have "(local.progress P \<phi> j + 1) \<in> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    by auto
  then have non_empty: "{i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<noteq> {}"
    by blast

  have "min (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)})
     (\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<and> k \<le> j - Suc 0 \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}) =
    \<Sqinter> {i. \<forall>k. k < j \<and> k \<le> local.progress P \<phi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    using Inf_leq[OF non_empty subset]
    by auto
  
  then show ?thesis
    using set_eq
    unfolding always_safe_0_def
    by auto
qed

lemma progress_eventually_nempty: 
  "{i. \<forall>k. k < j \<and> k \<le> n \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} \<noteq> {}"
  by (auto intro!: exI[of _ n])

lemma progress_eventually_or[simp]: "progress P (eventually I (Formula.Or \<phi> \<psi>)) j =
  min (progress P (eventually I \<phi>) j) (progress P (eventually I \<psi>) j)"
  unfolding progress_eventually min_Inf[OF progress_eventually_nempty progress_eventually_nempty]
  by (cases "progress P \<phi> j \<le> progress P \<psi> j") (auto intro: arg_cong[where ?f=Inf])

lemma progress_eventually_double_upper: 
  "(progress P (eventually I (eventually (int_remove_lower_bound I) \<phi>)) j) =
  (case j of 0 \<Rightarrow> 0
   | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)}) - \<tau> \<sigma> i)})"
proof -
  have "(progress P (eventually I (eventually (int_remove_lower_bound I) \<phi>)) j) =
    (case j of 0 \<Rightarrow> 0
     | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (min x (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)})) - \<tau> \<sigma> i)})"
  unfolding progress_eventually Inf_memR_conv
  by transfer' (auto split: nat.splits)
  moreover have "\<dots> = (case j of 0 \<Rightarrow> 0
     | Suc x \<Rightarrow> \<Sqinter> {i. memR I (\<tau> \<sigma> (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x (progress P \<phi> j)) - \<tau> \<sigma> i)}) - \<tau> \<sigma> i)})"
    by (auto simp: min_x_Inf split: nat.splits)
  finally show ?thesis .
qed

lemma progress_release_rewrite_0:
  assumes "mem I 0"
  shows "progress P (release_safe_0 \<phi> I \<psi>) j = progress P (formula.Release \<phi> I \<psi>) j"
proof -
  define A where "A = {i. \<forall>k. k < j \<and> k \<le> min (progress P \<psi> j) (progress P \<phi> j) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  define B where "B = {i. \<forall>k. k < j \<and> k \<le> progress P \<psi> j \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"

  have "progress P (release_safe_0 \<phi> I \<psi>) j = min (progress P (formula.Until \<psi> I (formula.And \<psi> \<phi>)) j) (progress P (always_safe_0 I \<psi>) j)"
    unfolding release_safe_0_def
    by auto
  moreover have "progress P (formula.Until \<psi> I (formula.And \<psi> \<phi>)) j = Inf A"
    unfolding A_def
    by auto
  moreover have "progress P (always_safe_0 I \<psi>) j = Inf B"
    unfolding B_def
    by auto
  ultimately have progress_eq: "progress P (release_safe_0 \<phi> I \<psi>) j = min (Inf A) (Inf B)"
    by auto

  have
    "(min (local.progress P \<psi> j) (local.progress P \<phi> j)) \<in> A"
    "progress P \<psi> j \<in> B"
    unfolding A_def B_def
    by auto
  then have non_empty: 
    "A \<noteq> {}"
    "B \<noteq> {}"
    by auto

  then show ?thesis
    using progress_eq min_Inf[OF non_empty] assms
    unfolding A_def B_def
    by auto
qed

lemma progress_release_safe_bounded_evtl: 
  "min (progress P (Formula.eventually I Formula.TT) j) (progress P (release_safe_bounded \<phi> I \<psi>) j)
  = progress P (release_safe_bounded \<phi> I \<psi>) j"
  unfolding release_safe_bounded_def
  by (auto simp: progress_eventually)

lemma progress_eventually_monos:
  assumes "progress P \<phi> j \<le> progress P' \<psi> j'" and "j \<le> j'"
  shows "(progress P (Formula.eventually I \<phi>) j) \<le> (progress P' (Formula.eventually I \<psi>) j')"
    and "(progress P (Formula.eventually (int_remove_lower_bound I) \<phi>) j) 
        \<le> (progress P' (Formula.eventually (int_remove_lower_bound I) \<psi>) j')"
    and "(progress P (Formula.eventually (flip_int_less_lower I) \<phi>) j) 
        \<le> (progress P' (Formula.eventually (flip_int_less_lower I) \<psi>) j')"
  using assms 
  by (auto simp: progress_eventually intro!: Inf_leq
          elim!: allE[of "\<lambda>x. \<exists>k<j'. k \<le> _ \<and> \<not> memR _ (\<tau> \<sigma> k - \<tau> \<sigma> x)" j'])

lemma progress_and_release_rewrite_bounded:
  assumes "\<not> mem I 0" "bounded I"
  shows "Progress.progress \<sigma> P (and_release_safe_bounded \<phi> \<phi>' I \<psi>') j 
  = progress P (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) j"
proof -
  have "progress P (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) j 
  = min (progress P \<phi> j) 
      (min (progress P (Formula.eventually I Formula.TT) j) 
          (progress P (release_safe_bounded \<phi>' I \<psi>') j))"
    using assms
    by (auto simp only: progress_release_safe_bounded_evtl[of P I j \<phi>' \<psi>'] 
        progress.simps split: if_splits)
  then show ?thesis
    using assms
    unfolding and_release_safe_bounded_def
    by (auto simp: progress_eventually)
qed

definition "progress_regex P = min_regex_default (progress P)"
definition "letpast_progress P p \<phi> j = \<Sqinter>{i. i \<le> j \<and> i = progress (P(p \<mapsto> i)) \<phi> j}"

declare progress.simps[simp del]
lemmas progress_simps[simp] 
  = progress.simps[folded progress_regex_def[THEN fun_cong, THEN fun_cong] letpast_progress_def]

end

lemma progress_fixpoint_ex':
  assumes "(\<And>P. pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> Progress.progress \<sigma> P \<phi> j \<le> j)"
  and "(\<And>P P'. pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P' \<Longrightarrow> rel_mapping (\<le>) P P' 
    \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j)"
  shows "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> \<exists>i \<le> j. i = Progress.progress \<sigma> (P(p \<mapsto> i)) \<phi> j"
  by (rule bounded_fixpoint_ex)
    (auto simp: reflp_def intro!: mono_onI assms rel_mapping_map_upd rel_mapping_reflp)

lemma progress_fixpoint_ex_above:
  assumes "(\<And>j P. pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P \<phi> j \<le> j)"
  and "(\<And>j j' P P'. j \<le> j' \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j') P' \<Longrightarrow> rel_mapping (\<le>) P P' \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j')"
  and "j \<le> j'" "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'" "rel_mapping (\<le>) P P'"
    "i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j" "i \<le> j"
shows "\<exists>x \<le> j'. x = progress \<sigma> (P'(p \<mapsto> x)) \<phi> j' \<and> i \<le> x"
proof -
  have "\<exists>x \<in> {i .. j'}. x = progress \<sigma> (P'(p \<mapsto> x)) \<phi> j'"
  proof (rule bounded_fixpoint_ex_above)
    show "mono_on {i..j'} (\<lambda>x. progress \<sigma> (P'(p \<mapsto> x)) \<phi> j')"
      by (auto intro!: mono_onI assms(2,4,5) pred_mapping_map_upd rel_mapping_map_upd rel_mapping_reflp reflpI)
    show "\<forall>x\<in>{i..j'}. progress \<sigma> (P'(p \<mapsto> x)) \<phi> j' \<in> {i..j'}"
      unfolding Ball_def atLeastAtMost_iff
    proof safe
      fix x assume *: "i \<le> x" "x \<le> j'"
      then show "i \<le> progress \<sigma> (P'(p \<mapsto> x)) \<phi> j'"
        by (subst assms(7)) (auto intro!: assms(2-6,8) pred_mapping_map_upd rel_mapping_map_upd)
      from * show "progress \<sigma> (P'(p \<mapsto> x)) \<phi> j' \<le> j'"
        by (auto intro!: assms(1,5) pred_mapping_map_upd)
    qed
    show "i \<le> j'" using assms(3,8) by simp
  qed
  then show ?thesis
    by auto
qed

lemma progress_le_gen: "\<And>j P. pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress \<sigma> P \<phi> j \<le> j" 
  and progress_mono_gen: "\<And>j j' P P'. j \<le> j' \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P 
    \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j') P' \<Longrightarrow> rel_mapping (\<le>) P P' 
    \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j'"
proof (induction \<phi>)
  case (Pred e ts) case 1
  then show ?case
    by (force simp: pred_mapping_alt dom_def split: option.splits)
next
  case (Pred e ts) case 2
  then show ?case
    by (force simp: rel_mapping_alt dom_def split: option.splits)
next
  case (Ands l) case 1
  with Ands show ?case
    by (auto simp: image_iff 
        intro!: Min.coboundedI[where a="progress \<sigma> P (hd l) j", THEN order_trans])
next
  case (Ands l) case 2
  with Ands show ?case
    by (auto simp: image_iff 
        intro!: Min.coboundedI[THEN order_trans])
next
  case (Since \<phi> I \<psi>)
  {
    case 1
    from Since.IH(1)[OF 1] show ?case by simp
  next
    case 2
    then have
      "progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> j'"
      "progress \<sigma> P \<psi> j \<le> progress \<sigma> P' \<psi> j'"
      using Since.IH(2,4) by auto
    then show ?case by auto
  }
next
  case (Until \<phi> I \<psi>) case 1
  then show ?case
    by (auto intro!: cInf_lower)
next
  case (Until \<phi> I \<psi>) case 2
  with Until(2,4)[of j j' P P'] show ?case
    by (auto 0 3 dest: memR_nonzeroD less_\<tau>D spec[of _ j'] 
        intro!: cInf_superset_mono)
next
  case (Release \<phi> I \<psi>) case 1
  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    then show ?thesis 
      using Release 
      by (auto intro!: cInf_lower)
  next
    case False
    have fact1: "progress \<sigma> P (Formula.eventually I Formula.TT) j \<le> j"
      by (simp add: progress_eventually) (rule cInf_lower; clarsimp)
    have fact2: "(progress \<sigma> P (Formula.eventually I \<psi>') j) \<le> progress \<sigma> P \<psi>' j" 
      for \<psi>' :: "'b Formula.formula"
      by (simp add: progress_eventually) (rule cInf_lower; clarsimp)
    hence "(progress \<sigma> P (always_safe_bounded I \<psi>) j) \<le> progress \<sigma> P \<psi> j"
      by (clarsimp simp: always_safe_bounded_def)
        (meson min_le_iff_disj)
    thus ?thesis
      using Release(1,3)[OF 1] 1 False fact1 fact2 min.coboundedI1
      by (auto simp add: release_safe_bounded_def)
  qed
next
  case (Release \<phi> I \<psi>) case 2
  show ?case 
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    thus ?thesis
      using Release(2,4)[of _ _ P P'] Release(1,3)
      apply (auto 0 3 dest: memR_nonzeroD less_\<tau>D spec[of _ j'] intro!: cInf_superset_mono)
      subgoal for x k l
        apply (subgoal_tac "l < j'")
        using "2.prems" le_trans apply presburger
        using "2.prems"(1) by linarith
      subgoal for x k l
        apply (subgoal_tac "k < j'")
        using "2.prems" le_trans apply meson 
        using "2.prems"(1) by linarith
      by (meson bounded_memR)+
  next
    case False
    have fact1: "progress \<sigma> P (Formula.eventually I Formula.TT) j 
      \<le> progress \<sigma> P' (Formula.eventually I Formula.TT) j'"
      and fact2: "progress \<sigma> P (Formula.eventually (flip_int_less_lower I) \<phi>) j
      \<le> progress \<sigma> P' (Formula.eventually (flip_int_less_lower I) \<phi>) j'"
      using 2(1) False Release(2,4)[OF 2]
      by (auto simp: progress_eventually intro!: Inf_leq exI[of _ j'] 
          elim!: allE[of "\<lambda>x. \<exists>k<j'. k \<le> _ \<and> \<not> memR _ (\<tau> \<sigma> k - \<tau> \<sigma> x)" j'])
    have fact3: "(progress \<sigma> P (Formula.eventually I \<psi>') j) 
        \<le> (progress \<sigma> P' (Formula.eventually I \<psi>') j')" 
      and fact4: "(progress \<sigma> P (Formula.eventually (int_remove_lower_bound I) \<psi>') j) 
        \<le> (progress \<sigma> P' (Formula.eventually (int_remove_lower_bound I) \<psi>') j')"
      and fact5: "(progress \<sigma> P (Formula.eventually (flip_int_less_lower I) \<psi>') j) 
        \<le> (progress \<sigma> P' (Formula.eventually (flip_int_less_lower I) \<psi>') j')"
      if "progress \<sigma> P \<psi>' j \<le> progress \<sigma> P' \<psi>' j'"
      for \<psi>' :: "'b Formula.formula"
      using progress_eventually_monos[OF that 2(1)] 
      by blast+
    hence "(progress \<sigma> P (always_safe_bounded I \<psi>) j) 
        \<le> (progress \<sigma> P' (always_safe_bounded I \<psi>) j')" 
      using Release(2,4)[OF 2] 2(1) 
      by (clarsimp simp: always_safe_bounded_def min_le_iff_disj)
    thus ?thesis 
      using Release(2,4)[OF 2] False
      apply (clarsimp simp: release_safe_bounded_def)
      apply (intro conjI impI allI iffI)
      using fact1 min.coboundedI1 apply blast
      apply linarith 
      using fact2 apply (meson min_le_iff_disj)  
      apply (subst min_le_iff_disj, intro disjI2)+ 
      apply (rule fact5)
      apply (clarsimp simp: Min_le_iff intro!: diff_le_mono )
      apply (rule Inf_leq; clarsimp)
      apply (metis \<tau>_mono diff_is_0_eq' memR_zero)
      by (meson "2.prems"(1) le_trans order_less_le_trans)
  qed
next
  case (MatchF I r) case 1
  then show ?case
    by (auto intro!: cInf_lower)
next
  case (MatchF I r) case 2
  with MatchF(2)[of _ j j' P P'] show ?case
    by (auto 0 3 simp: Min_le_iff progress_regex_def dest: memR_nonzeroD less_\<tau>D spec[of _ j']
      elim!: order_trans less_le_trans intro!: cInf_superset_mono)
next
  case (LetPast p \<phi>1 \<phi>2) case 1
  obtain i where fp: "i = progress \<sigma> (P((p, Formula.nfv \<phi>1) \<mapsto> i)) \<phi>1 j" "i \<le> j"
    using progress_fixpoint_ex'[OF LetPast(1,2) 1] by blast
  show ?case
    apply (unfold progress.simps Let_def)
    apply (rule LetPast(3))
    apply (rule pred_mapping_map_upd[OF _ 1])
    using fp by (auto intro!: cInf_lower2[of i])
next
  case (LetPast p \<phi>1 \<phi>2) case 2
  obtain i where fp: "i = progress \<sigma> (P((p, Formula.nfv \<phi>1) \<mapsto> i)) \<phi>1 j" "i \<le> j"
    using progress_fixpoint_ex'[OF LetPast(1,2)] 2 by blast
  obtain i' where fp': "i' = progress \<sigma> (P'((p, Formula.nfv \<phi>1) \<mapsto> i')) \<phi>1 j'" "i' \<le> j'"
    using progress_fixpoint_ex'[OF LetPast(1,2)] 2 by blast
  show ?case
    apply (unfold progress.simps Let_def)
    apply (rule LetPast(4)[OF 2(1)])
    using 2 fp apply (auto simp del: fun_upd_apply intro!: pred_mapping_map_upd cInf_lower2[of i])[]
    using 2 fp' apply (auto simp del: fun_upd_apply intro!: pred_mapping_map_upd cInf_lower2[of i'])[]
    apply (intro rel_mapping_map_upd cInf_mono 2)
    using fp' apply auto[2]
    subgoal for k
      apply clarify
      apply (subgoal_tac "\<exists>i \<le> min k j. i = progress \<sigma> (P((p, Formula.nfv \<phi>1) \<mapsto> i)) \<phi>1 j")
       apply auto[]
      apply (intro bounded_fixpoint_ex mono_onI)
      using LetPast 2 apply (simp del: fun_upd_apply)
      apply (cases "k \<le> j")
       apply clarsimp
       apply (erule ssubst)
      using LetPast 2 by (auto simp del: fun_upd_apply)
    done
qed (fastforce simp: Min_le_iff progress_regex_def split: option.splits)+

lemma progress_mono:
  "j \<le> j' \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow>
  Progress.progress \<sigma> P \<phi> j \<le> Progress.progress \<sigma> P \<phi> j'"
  by (rule progress_mono_gen) (auto elim: pred_mapping_mono simp: rel_mapping_reflp reflp_def)

lemma progress_le: "progress \<sigma> Map.empty \<phi> j \<le> j"
  using progress_le_gen[of _ Map.empty] by auto

lemma progress_0_gen[simp]:
  "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> progress \<sigma> P \<phi> 0 = 0"
  using progress_le_gen[of 0 P] by auto

lemma progress_0[simp]:
  "progress \<sigma> Map.empty \<phi> 0 = 0"
  by (auto simp: pred_mapping_alt)

lemma progress_fixpoint_ex: 
  "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> \<exists>i \<le> j. i = Progress.progress \<sigma> (P(p \<mapsto> i)) \<phi> j"
  by (blast intro!: progress_fixpoint_ex' progress_le_gen progress_mono_gen)

lemma not_contains_pred_progress[simp]: "\<not> contains_pred p \<phi> 
  \<Longrightarrow> progress \<sigma> (P(p \<mapsto> x)) \<phi> j = progress \<sigma> P \<phi> j"
  apply(induct p \<phi> arbitrary: P x rule: contains_pred.induct)
                   apply(simp_all add: progress_regex_def)
   apply (erule conjE)
   apply (erule disjE_Not2)
  subgoal by clarsimp metis
  subgoal by (metis fun_upd_twist)
  apply (erule disjE_Not2; clarsimp)
  using letpast_progress_def apply auto[1]
  apply (smt (z3) Collect_cong fun_upd_upd letpast_progress_def)
   apply (smt (z3) Collect_cong fun_upd_twist letpast_progress_def)
  by (auto simp: release_safe_bounded_def Formula.eventually_def
      intro!: arg_cong2[where f=min])
    (clarsimp simp: always_safe_bounded_def progress_eventually)

lemma progress_regex_le: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
  by (auto intro!: progress_le_gen simp: Min_le_iff progress_regex_def)


subsection \<open> Progress letpast \<close>

definition max_mapping :: "('b \<Rightarrow> 'a option) \<Rightarrow> ('b \<Rightarrow> 'a option) \<Rightarrow> 'b \<Rightarrow> ('a :: linorder) option" 
  where "max_mapping P P' x = (case (P x, P' x) of
    (None, None) \<Rightarrow> None
  | (Some x, None) \<Rightarrow> None
  | (None, Some x) \<Rightarrow> None
  | (Some x, Some y) \<Rightarrow> Some (max x y))"

definition Max_mapping :: "('b \<Rightarrow> 'a option) set \<Rightarrow> 'b \<Rightarrow> ('a :: linorder) option" where
  "Max_mapping Ps x = (if (\<forall>P \<in> Ps. P x \<noteq> None) then Some (Max ((\<lambda>P. the (P x)) ` Ps)) else None)"

lemma dom_max_mapping[simp]: "dom (max_mapping P1 P2) = dom P1 \<inter> dom P2"
  unfolding max_mapping_def by (auto split: option.splits)

lemma dom_Max_mapping[simp]: "dom (Max_mapping X) = (\<Inter>P \<in> X. dom P)"
  unfolding Max_mapping_def by (auto split: if_splits)

lemma Max_mapping_coboundedI:
  assumes "finite X" "\<forall>Q \<in> X. dom Q = dom P" "P \<in> X"
  shows "rel_mapping (\<le>) P (Max_mapping X)"
  unfolding rel_mapping_alt
proof (intro conjI ballI)
  from assms(3) have "X \<noteq> {}" by auto
  then show "dom P = dom (Max_mapping X)" using assms(2) by auto
next
  fix p
  assume "p \<in> dom P"
  with assms show "the (P p) \<le> the (Max_mapping X p)"
    by (force simp add: Max_mapping_def intro!: Max.coboundedI imageI)
qed

lemma range_mapping_max_mapping[simp]:
  "range_mapping i j1 P1 \<Longrightarrow> range_mapping i j2 P2 
  \<Longrightarrow> range_mapping i (max j1 j2) (max_mapping P1 P2)"
  by (auto simp: pred_mapping_alt dom_def set_eq_iff max_mapping_def split: option.splits)

lemma range_mapping_Max_mapping[simp]:
  "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<forall>x\<in>X. range_mapping i (j x) (P x) 
  \<Longrightarrow> range_mapping i (Max (j ` X)) (Max_mapping (P ` X))"
  by (force simp: pred_mapping_alt Max_mapping_def dom_def image_iff
      intro!: Max_ge_iff[THEN iffD2] split: if_splits)

lemma max_mapping_cobounded1: "dom P1 \<subseteq> dom P2 \<Longrightarrow> rel_mapping (\<le>) P1 (max_mapping P1 P2)"
  unfolding max_mapping_def rel_mapping_alt by (auto simp: dom_def split: option.splits)

lemma max_mapping_cobounded2: "dom P2 \<subseteq> dom P1 \<Longrightarrow> rel_mapping (\<le>) P2 (max_mapping P1 P2)"
  unfolding max_mapping_def rel_mapping_alt by (auto simp: dom_def split: option.splits)

lemma max_mapping_fun_upd2[simp]:
  "(max_mapping P1 (P2(p := y)))(p \<mapsto> x) = (max_mapping P1 P2)(p \<mapsto> x)"
  by (auto simp: max_mapping_def)

lemma rel_mapping_max_mapping_fun_upd: "dom P2 \<subseteq> dom P1 \<Longrightarrow> p \<in> dom P2 \<Longrightarrow> the (P2 p) \<le> y 
  \<Longrightarrow> rel_mapping (\<le>) P2 ((max_mapping P1 P2)(p \<mapsto> y))"
  by (auto simp: rel_mapping_alt max_mapping_def split: option.splits)

lemma not_contains_letpast_progress[simp]: 
  "\<not> contains_pred p \<phi> \<Longrightarrow> letpast_progress \<sigma> (P(p \<mapsto> x)) q \<phi> j = letpast_progress \<sigma> P q \<phi> j"
  by (cases "p = q") (simp_all add: letpast_progress_def fun_upd_twist[of p q])

lemma letpast_progress0: 
  "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> letpast_progress \<sigma> P p \<phi> 0 = 0"
  by (simp add: letpast_progress_def cInf_eq_minimum)

lemma letpast_progress_le:
  assumes "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "letpast_progress \<sigma> P p \<phi> j \<le> j"
proof -
  obtain i where "i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j" "i \<le> j"
    using progress_fixpoint_ex[OF assms] by blast
  then show ?thesis
    by (auto simp add: letpast_progress_def intro!: cInf_lower2[of i])
qed

lemma letpast_progress_fixpoint:
  assumes "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "progress \<sigma> (P(p \<mapsto> letpast_progress \<sigma> P p \<phi> j)) \<phi> j = letpast_progress \<sigma> P p \<phi> j"
proof -
  let ?A = "{i. i \<le> j \<and> i = progress \<sigma> (P(p \<mapsto> i)) \<phi> j}"
  have nonempty: "?A \<noteq> {}" using progress_fixpoint_ex[OF assms] by simp
  then have "letpast_progress \<sigma> P p \<phi> j = Min ?A"
    by (simp add: letpast_progress_def cInf_eq_Min)
  moreover have "Min ?A \<in> ?A"
    using nonempty by (intro Min_in) auto
  ultimately show ?thesis by simp
qed

lemma letpast_progress_mono:
  assumes "pred_mapping (\<lambda>x. x \<le> j1) P1" and "pred_mapping (\<lambda>x. x \<le> j2) P2" and "j1 \<le> j2"
    and "rel_mapping (\<le>) P1 P2"
  shows "letpast_progress \<sigma> P1 p \<phi> j1 \<le> letpast_progress \<sigma> P2 p \<phi> j2"
  unfolding letpast_progress_def
  apply (intro cInf_mono)
  using progress_fixpoint_ex[OF assms(2)] apply simp
  apply blast
   apply simp
  subgoal for k
    apply clarify
    apply (subgoal_tac "\<exists>i \<le> min k j1. i = progress \<sigma> (P1(p \<mapsto> i)) \<phi> j1")
     apply auto[]
    apply (intro bounded_fixpoint_ex mono_onI progress_mono_gen)
    using assms apply (simp_all del: fun_upd_apply)[4]
    apply (cases "k \<le> j1")
     apply clarsimp
     apply (erule ssubst)
    using assms by (auto simp add: progress_le_gen progress_mono_gen simp del: fun_upd_apply)
  done

lemma le_letpast_progress_preservation:
  assumes P: "pred_mapping (\<lambda>x. x \<le> j) P"
    and P': "pred_mapping (\<lambda>x. x \<le> j') P'"
    and PP': "rel_mapping (\<le>) P P'"
    and i: "i \<le> letpast_progress \<sigma> P p \<phi> j"
    and jj': "j \<le> j'"
  shows "progress \<sigma> (P(p \<mapsto> i)) \<phi> j \<le> letpast_progress \<sigma> P' p \<phi> j'"
  unfolding letpast_progress_def
  apply (rule cInf_greatest)
   apply simp
   apply (rule progress_fixpoint_ex[OF P'])
  apply clarsimp
  apply (subgoal_tac "i \<le> j")
   apply (rule order_trans)
    apply (rule progress_mono_gen[where P'="P'(p \<mapsto> i)", OF jj'])
  using P apply simp
  using P' jj' apply simp
  using PP' apply simp
   apply (rule ssubst, assumption)
   apply (rule progress_mono_gen[OF order_refl])
     apply (rule pred_mapping_map_upd[OF _ P'])
  using jj' apply simp
  using P' apply simp
   apply (rule rel_mapping_le_map_upd)
   apply (subgoal_tac "i \<le> letpast_progress \<sigma> P' p \<phi> j'")
    apply (subst (asm) letpast_progress_def)
    apply (subst (asm) le_cInf_iff)
      apply simp
      apply (rule progress_fixpoint_ex[OF P'])
     apply simp
    apply auto[]
   apply (rule order_trans[OF i])
   apply (rule letpast_progress_mono[OF P P' jj' PP'])
  using i letpast_progress_le[OF P] by (rule order_trans)

lemma safe_letpast_progress_upd':
  fixes \<phi> :: "'t Formula.formula"
  shows "safe_letpast p \<phi> \<le> NonFutuRec \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P 
  \<Longrightarrow> x \<le> j \<Longrightarrow> y = (if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j) 
  \<Longrightarrow> min y (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
proof (induction \<phi> arbitrary: P p x y)
  case (Let e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  let ?p\<phi> = "\<lambda>P. progress \<sigma> P \<phi> j"
  let ?p\<psi> = "\<lambda>P. progress \<sigma> P \<psi> j"
  define y\<psi> where "y\<psi> = (if safe_letpast p \<psi> = NonFutuRec \<and> p \<noteq> ?en then x else min (Suc x) j)"
  define y\<phi> where "y\<phi> = (if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j)"
  define y\<phi>\<psi> where "y\<phi>\<psi> = (if safe_letpast ?en \<psi> = NonFutuRec then y\<phi> else min (Suc y\<phi>) j)"

  have P\<phi>_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> P))"
    using Let.prems(2) by (simp add: progress_le_gen)
  have Pmin_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
    using Let.prems(2,3) by (simp add: min.coboundedI1 y\<phi>_def)
  have P\<phi>x_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x))))"
    using Let.prems(2,3) by (simp add: progress_le_gen)

  have "?p\<psi> (P(p \<mapsto> x, ?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> min y\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))))"
  proof (cases "?en = p")
    case True
    then show ?thesis by simp
  next
    case False
    then have "?p\<psi> (P(p \<mapsto> x, ?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) = ?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)), p \<mapsto> x))"
      by (simp add: fun_upd_twist[of p])
    also have "\<dots> \<ge> min y\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))))"
    proof (rule Let.IH(2)[of p _ x y\<psi>, OF _ P\<phi>x_le Let.prems(3)])
      show "safe_letpast p \<psi> \<le> NonFutuRec"
        using Let.prems(1) False by simp
      show "y\<psi> = (if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j)"
        using False by (simp add: y\<psi>_def)
    qed
    finally show ?thesis .
  qed
  moreover have "safe_letpast ?en \<psi> * safe_letpast p \<phi> \<le> NonFutuRec"
    using Let.prems(1) by simp
  then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> min y (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
  proof (cases rule: mult_le_NonFutuRec_cases)
    case unused1
    then show ?thesis by (simp add: safe_letpast_Unused)
  next
    case unused2
    then show ?thesis by (simp add: safe_letpast_Unused)
  next
    case NonFutuRec
    have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> ?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
    proof (rule progress_mono_gen[OF order_refl Pmin_le P\<phi>x_le rel_mapping_le_map_upd])
      show "min y\<phi> (?p\<phi> P) \<le> ?p\<phi> (P(p \<mapsto> x))"
        using NonFutuRec(2) Let.prems(2,3) y\<phi>_def by (rule Let.IH(1))
    qed
    moreover have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
    proof (cases "y\<phi> \<le> ?p\<phi> P")
      case True
      then have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) = ?p\<psi> (P(?en \<mapsto> y\<phi>))" by simp
      also have "\<dots> = ?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>))" by simp
      also have "y\<phi> \<le> j" using Let.prems(3) by (simp add: y\<phi>_def)
      then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>)) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
        using NonFutuRec(1) P\<phi>_le Let.prems(3) y\<phi>\<psi>_def by (intro Let.IH(2))
      finally show ?thesis .
    next
      case False
      then show ?thesis by simp
    qed
    moreover have "y \<le> y\<phi>\<psi>"
      using Let.prems(1,3,4)
      by (auto simp add: y\<phi>\<psi>_def y\<phi>_def mult_eq_NonFutuRec_iff sup.absorb1)
    ultimately show ?thesis by simp
  qed
  moreover have "y \<le> y\<psi>"
    using Let.prems(1,3,4)
    by (auto simp add: y\<psi>_def mult_eq_NonFutuRec_iff sup.absorb2)
  ultimately show ?case by (simp del: fun_upd_apply)
next
  case (LetPast e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  let ?p\<phi> = "\<lambda>P. letpast_progress \<sigma> P ?en \<phi> j"
  let ?p\<phi>1 = "\<lambda>P. progress \<sigma> P \<phi> j"
  let ?p\<psi> = "\<lambda>P. progress \<sigma> P \<psi> j"
  define y\<psi> where "y\<psi> = (if safe_letpast p \<psi> = NonFutuRec then x else min (Suc x) j)"
  define y\<phi> where "y\<phi> = (if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j)"
  define y\<phi>\<psi> where "y\<phi>\<psi> = (if safe_letpast ?en \<psi> = NonFutuRec then y\<phi> else min (Suc y\<phi>) j)"

  have P\<phi>_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> P))"
    using LetPast.prems(2) by (simp add: letpast_progress_le)
  have Pmin_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
    using LetPast.prems(2,3) by (simp add: min.coboundedI1 y\<phi>_def)
  have P\<phi>x_le: "pred_mapping (\<lambda>x. x \<le> j) (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x))))"
    using LetPast.prems(2,3) by (simp add: letpast_progress_le)

  show ?case
  proof (cases "?en = p")
    case True
    then show ?thesis by (simp add: letpast_progress_def del: fun_upd_apply)
  next
    case False
    have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)), p \<mapsto> x)) \<ge> min y\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))))"
    proof (rule LetPast.IH(2)[OF _ P\<phi>x_le LetPast.prems(3) y\<psi>_def])
      show "safe_letpast p \<psi> \<le> NonFutuRec"
        using LetPast.prems(1) False by simp
    qed
    moreover have "safe_letpast ?en \<psi> * safe_letpast p \<phi> \<le> NonFutuRec"
      using LetPast.prems(1) False by simp
    then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
    proof (cases rule: mult_le_NonFutuRec_cases)
      case unused1
      then show ?thesis by (simp add: safe_letpast_Unused)
    next
      case unused2
      then show ?thesis by (simp add: safe_letpast_Unused)
    next
      case NonFutuRec
      have "?p\<psi> (P(?en \<mapsto> ?p\<phi> (P(p \<mapsto> x)))) \<ge> ?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P)))"
      proof (rule progress_mono_gen[OF order_refl Pmin_le P\<phi>x_le rel_mapping_le_map_upd])
        have "min y\<phi> (?p\<phi> P) \<le> \<Sqinter> {i. i \<le> j \<and> i = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> i))}"
        proof (rule cInf_greatest)
          show "{i. i \<le> j \<and> i = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> i))} \<noteq> {}"
            using LetPast.prems(2,3) by (simp add: progress_fixpoint_ex)
        next
          fix fp
          assume fp: "fp \<in> {i. i \<le> j \<and> i = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> i))}"
          then have fp_unfold: "fp = ?p\<phi>1 (P(p \<mapsto> x, ?en \<mapsto> fp))" by simp
          then have "fp = ?p\<phi>1 (P(?en \<mapsto> fp, p \<mapsto> x))"
            using False by (simp add: fun_upd_twist[of p])
          moreover have "\<dots> \<ge> min y\<phi> (?p\<phi>1 (P(?en \<mapsto> fp)))"
            using NonFutuRec(2) LetPast.prems(2,3) fp
            by (intro LetPast.IH(1)) (simp_all add: y\<phi>_def del: fun_upd_apply)
          moreover have "?p\<phi>1 (P(?en \<mapsto> fp)) \<ge> ?p\<phi> P" if *: "?p\<phi>1 (P(?en \<mapsto> fp)) \<le> y\<phi>"
          proof -
            have "\<exists>fp'\<le>fp. fp' = ?p\<phi>1 (P(?en \<mapsto> fp'))"
              apply (rule bounded_fixpoint_ex)
               apply (intro mono_onI progress_mono_gen; simp)
              using LetPast.prems(2) fp apply simp
              using LetPast.prems(2) fp apply simp
              apply (intro allI impI)
              apply (subst fp_unfold)
              apply (rule order_trans)
               apply (rule progress_mono_gen[where P'="P(?en \<mapsto> fp)", OF order_refl])
              using LetPast.prems(2) fp apply simp
              using LetPast.prems(2) fp apply simp
               apply simp
              using False apply (simp only: fun_upd_twist[of p])
              apply (rule order_trans[rotated])
               apply (rule LetPast.IH(1)[OF _ _ _ y\<phi>_def])
                 apply (rule NonFutuRec)
              using LetPast.prems(2) fp apply (simp del: fun_upd_apply)
              apply (rule LetPast.prems(3))
              using * by (simp del: fun_upd_apply)
            then obtain fp' where fp': "fp' \<le> fp" "fp' = ?p\<phi>1 (P(?en \<mapsto> fp'))"
              by blast
            then have "?p\<phi>1 (P(?en \<mapsto> fp')) \<le> ?p\<phi>1 (P(?en \<mapsto> fp))"
              using LetPast.prems(2) fp by (intro progress_mono_gen) simp_all
            then show ?thesis
              unfolding letpast_progress_def using fp fp'
              by (auto intro!: cInf_lower2[of fp'])
          qed
          ultimately show "min y\<phi> (?p\<phi> P) \<le> fp" by linarith
        qed
        then show "min y\<phi> (?p\<phi> P) \<le> ?p\<phi> (P(p \<mapsto> x))"
          by (subst (2) letpast_progress_def)
      qed
      moreover have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
      proof (cases "y\<phi> \<le> ?p\<phi> P")
        case True
        then have "?p\<psi> (P(?en \<mapsto> min y\<phi> (?p\<phi> P))) = ?p\<psi> (P(?en \<mapsto> y\<phi>))" by simp
        also have "\<dots> = ?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>))" by simp
        also have "y\<phi> \<le> j" using LetPast.prems(3) by (simp add: y\<phi>_def)
        then have "?p\<psi> (P(?en \<mapsto> ?p\<phi> P, ?en \<mapsto> y\<phi>)) \<ge> min y\<phi>\<psi> (?p\<psi> (P(?en \<mapsto> ?p\<phi> P)))"
          using NonFutuRec(1) P\<phi>_le LetPast.prems(3) y\<phi>\<psi>_def by (intro LetPast.IH(2))
        finally show ?thesis .
      next
        case False
        then show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
    moreover have "y \<le> y\<psi>"
      using LetPast.prems(1,3,4) False
      by (simp add: y\<psi>_def sup.absorb2)
    moreover have "y \<le> y\<phi>\<psi>"
      using LetPast.prems(1,3,4) False
      by (auto simp add: y\<phi>\<psi>_def y\<phi>_def sup.absorb1 sup.absorb2)
    ultimately show ?thesis
      using False by (simp add: Let_def fun_upd_twist[of p] del: fun_upd_apply)
  qed
next
  case (Or \<phi> \<psi>)
  then show ?case
    apply (simp add: min_le_iff_disj del: fun_upd_apply split: if_splits)
     apply (smt (z3) le_antisym le_cases min_def not_less_eq_eq)
    by (smt (z3) min_def sup.absorb_iff2 sup.commute)
next
  case (And \<phi> \<psi>)
  then show ?case
    apply (simp add: min_le_iff_disj del: fun_upd_apply split: if_splits)
     apply (smt (z3) le_antisym le_cases min_def not_less_eq_eq)
    by (smt (z3) min_def sup.absorb_iff2 sup.commute)
next
  case (Ands l)
  {
    fix \<phi> :: "'t Formula.formula"
    let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
    assume "\<phi> \<in> set l"
    then have "min ?y\<phi> (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Ands.IH[of \<phi> p P x] Ands.prems
      by (simp add: Sup_rec_safety_le_iff del: fun_upd_apply)
    moreover have "y \<le> ?y\<phi>"
      using \<open>\<phi> \<in> set l\<close> Ands.prems(1,3,4)
      apply auto
      by (metis Sup_rec_safety_le_iff imageI order.eq_iff)
    moreover have "(MIN \<phi>'\<in>set l. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> P \<phi> j"
      using \<open>\<phi> \<in> set l\<close> by (simp add: Min_le_iff)
    ultimately have "min y (MIN \<phi>'\<in>set l. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      by simp
  }
  then show ?case by (simp del: fun_upd_apply)
next
  case (Prev I \<phi>)
  show ?case
    using Prev.IH[of p P x] Prev.prems
    apply (simp add: mult_le_NonFutuRec_iff mult_eq_NonFutuRec_iff del: fun_upd_apply)
    by (smt (z3) Suc_le_mono le_SucI min.cobounded1 min.coboundedI2 min_def 
        not_contains_pred_progress safe_letpast_Unused)
next
  case (Next I \<phi>)
  then show ?case
    by (simp add: mult_le_NonFutuRec_iff safe_letpast_Unused del: fun_upd_apply)
next
  case (Since \<phi> I \<psi>)
  show ?case 
  proof (cases "safe_letpast p (Formula.Since \<phi> I \<psi>) = NonFutuRec")
    case True
    then have "y = x"
      using Since.prems by simp
    moreover have "min x (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Since.prems
      by (auto intro!: order.trans[rotated, OF Since.IH(1)])
    moreover have "min x (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Since.prems
      by (auto simp add: mult_le_NonFutuRec_iff split: if_splits
          intro!: order.trans[rotated, OF Since.IH(2)])
    ultimately show ?thesis
      by (force simp del: fun_upd_apply)
  next
    case False
    then have "y = min (Suc x) j"
      using Since.prems by simp
    moreover have "safe_letpast p \<phi> \<noteq> NonFutuRec"
      using False Since.prems by (auto simp add: sup_eq_NonFutuRec_iff)
    then have "min (min (Suc x) j) (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Since.prems
      by (auto intro!: order.trans[rotated, OF Since.IH(1)])
    moreover have "memL I 0 \<Longrightarrow> safe_letpast p \<psi> \<noteq> NonFutuRec"
      using False Since.prems(1)
      by (auto simp add: sup_eq_NonFutuRec_iff)
    then have "if memL I 0
        then min (min (Suc x) j) (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j
        else min x (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Since.prems thm Since.IH(2)
      by (auto simp add: mult_le_NonFutuRec_iff split: if_splits
          intro!: order.trans[rotated, OF Since.IH(2)])
    ultimately show ?thesis
      apply (clarsimp simp del: fun_upd_apply)
      by (force simp del: fun_upd_apply)
  qed
next
  case (Until \<phi> I \<psi>)
  then show ?case
    by (simp add: mult_le_NonFutuRec_iff sup_eq_Unused_iff 
        safe_letpast_Unused del: fun_upd_apply)
next
  case (Trigger \<phi> I \<psi>)
  then show ?case
  proof (cases "safe_letpast p (Formula.Trigger \<phi> I \<psi>) = NonFutuRec")
    case True
    then have "y = x"
      using Trigger.prems by simp
    moreover have "min x (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      thm Trigger.IH(1,2)[of p P x x]
      using Trigger.prems
      by (auto intro!: order.trans[rotated, OF Trigger.IH(1)])
    moreover have "min x (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Trigger.prems
      by (auto simp add: mult_le_NonFutuRec_iff split: if_splits
          intro!: order.trans[rotated, OF Trigger.IH(2)])
    ultimately show ?thesis
      by (force simp del: fun_upd_apply)
  next
    case False
    then have "y = min (Suc x) j"
      using Trigger.prems by simp
    moreover have "safe_letpast p \<phi> \<noteq> NonFutuRec"
      using False Trigger.prems by (auto simp add: sup_eq_NonFutuRec_iff)
    then have "min (min (Suc x) j) (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using Trigger.prems
      by (auto intro!: order.trans[rotated, OF Trigger.IH(1)])
    moreover have "memL I 0 \<Longrightarrow> safe_letpast p \<psi> \<noteq> NonFutuRec"
      using False Trigger.prems(1)
      by (auto simp add: sup_eq_NonFutuRec_iff)
    then have "if memL I 0
        then min (min (Suc x) j) (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j
        else min x (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Trigger.prems
      by (auto simp add: mult_le_NonFutuRec_iff split: if_splits
          intro!: order.trans[rotated, OF Trigger.IH(2)])
    moreover have "safe_letpast p \<psi> \<noteq> NonFutuRec"
      using False Trigger.prems by (auto simp add: sup_eq_NonFutuRec_iff)
    then have "min (min (Suc x) j) (progress \<sigma> P \<psi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<psi> j"
      using Trigger.prems
      by (auto intro!: order.trans[rotated, OF Trigger.IH(2)] split: if_splits)
    ultimately show ?thesis
      by (auto simp del: fun_upd_apply split: if_splits)
  qed
next
  case (Release \<phi> I \<psi>)
  then show ?case
    by (simp add: mult_le_NonFutuRec_iff sup_eq_Unused_iff 
        safe_letpast_Unused del: fun_upd_apply)
next
  case (MatchF I r)
  then show ?case
    by (auto simp add: mult_le_NonFutuRec_iff Sup_eq_Unused_iff 
        safe_letpast_Unused progress_regex_def
        simp del: fun_upd_apply dest!: subset_singletonD image_eqD)
next
  case (MatchP I r)
  {
    fix \<phi> :: "'t Formula.formula"
    let ?y\<phi> = "if safe_letpast p \<phi> = NonFutuRec then x else min (Suc x) j"
    assume "\<phi> \<in> regex.atms r"
    then have "min ?y\<phi> (progress \<sigma> P \<phi> j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      using MatchP.IH[of \<phi> p P x] MatchP.prems
      by (simp add: Sup_rec_safety_le_iff del: fun_upd_apply)
    moreover have "y \<le> ?y\<phi>"
      using \<open>\<phi> \<in> regex.atms r\<close> MatchP.prems(1,3,4)
      apply auto
      by (metis Sup_rec_safety_le_iff imageI order.eq_iff)
    moreover have "(MIN \<phi>'\<in>regex.atms r. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> P \<phi> j"
      using \<open>\<phi> \<in> regex.atms r\<close> by (simp add: Min_le_iff)
    ultimately have "min y (MIN \<phi>'\<in>regex.atms r. progress \<sigma> P \<phi>' j) \<le> progress \<sigma> (P(p \<mapsto> x)) \<phi> j"
      by simp
  }
  then show ?case by (simp add: progress_regex_def del: fun_upd_apply)
qed simp_all


lemma safe_letpast_progress_upd:
  "safe_letpast p \<phi> \<le> PastRec \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> x \<le> j \<Longrightarrow>
  progress \<sigma> (P(p \<mapsto> x)) \<phi> j \<ge> min (Suc x) (progress \<sigma> P \<phi> j)"
  apply (subgoal_tac "progress \<sigma> (P(p \<mapsto> x)) \<phi> j \<ge> min (min (Suc x) j) (progress \<sigma> P \<phi> j)")
   apply (subgoal_tac "progress \<sigma> P \<phi> j \<le> j")
    apply simp
   apply (simp add: progress_le_gen)
  apply (rule safe_letpast_progress_upd')
  by (auto intro: order_trans)

lemma letpast_progress_PastRec:
  assumes past: "safe_letpast p \<phi> \<le> PastRec"
    and Pj: "pred_mapping (\<lambda>x. x \<le> j) P"
  shows "letpast_progress \<sigma> P p \<phi> j \<ge> min (progress \<sigma> P \<phi> j) j"
  unfolding letpast_progress_def
  apply (rule cInf_greatest)
  using progress_fixpoint_ex[OF Pj] apply simp
  apply blast
   apply clarify
  apply (rule ssubst, assumption)
  apply (frule safe_letpast_progress_upd[OF assms, of _ \<sigma>])
  by simp

lemma letpast_progress_upd_idem: "letpast_progress \<sigma> (P(p \<mapsto> x)) p \<phi> j = letpast_progress \<sigma> P p \<phi> j"
  by (simp add: letpast_progress_def)

lemma progress_Suc_letpast_progress_eq:
  assumes past: "safe_letpast p \<phi> \<le> PastRec"
    and Pj: "pred_mapping (\<lambda>x. x \<le> j) P"
    and Suc_i: "Suc i = letpast_progress \<sigma> P p \<phi> j"
  shows "progress \<sigma> (P(p \<mapsto> i)) \<phi> j = letpast_progress \<sigma> P p \<phi> j"
  apply (subgoal_tac "i \<le> j")
   apply (rule antisym)
    apply (rule order_trans[rotated])
     apply (rule letpast_progress_PastRec[OF past, where P="P(p \<mapsto> i)", unfolded letpast_progress_upd_idem])
  using Pj apply simp
  using Pj apply (simp add: progress_le_gen)
   apply (rule order_trans[rotated])
    apply (rule safe_letpast_progress_upd[OF past, where P="P(p \<mapsto> letpast_progress \<sigma> P p \<phi> j)", unfolded fun_upd_upd])
  using Pj apply (simp add: progress_le_gen letpast_progress_le)
    apply assumption
  using Pj apply (simp add: letpast_progress_fixpoint Suc_i)
  apply (rule order_trans[OF _ letpast_progress_le[OF Pj]])
  by (rule lessI[of i, unfolded Suc_i, THEN less_imp_le])

lemma letpast_progress_ge:
  assumes safe: "safe_letpast p \<phi> \<le> PastRec"
    and ge_\<phi>: "\<exists>P j. dom P = S \<and> range_mapping x j P \<and> x \<le> progress \<sigma> P \<phi> j"
  shows "\<exists>P j. dom P = S \<and> range_mapping x j P \<and> x \<le> letpast_progress \<sigma> P p \<phi> j"
  by (smt (z3) assms(1) ge_\<phi> letpast_progress_PastRec min.coboundedI2 
      min_def pred_mapping_mono_strong progress_le_gen)

lemma pred_mapping_max_mapping:
  "pred_mapping (\<lambda>x. x\<le>j1) P1 \<Longrightarrow> pred_mapping (\<lambda>x. x\<le>j2) P2 
  \<Longrightarrow> pred_mapping (\<lambda>x. x\<le>(max j1 j2)) (max_mapping P1 P2)"
  apply(auto simp: pred_mapping_alt max_mapping_def)
   apply (metis (full_types) domIff le_max_iff_disj option.discI option.sel)
  by (metis domI max.coboundedI2 option.sel)

lemma range_mapping_to_pred_mapping: "range_mapping a j P \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> j) P"
  by(auto simp add: pred_mapping_alt)

lemma letpast_progress_ignore_upd: 
  "letpast_progress \<sigma> (P(p := x)) p \<phi> j = letpast_progress \<sigma> P p \<phi> j"
  by (simp add: letpast_progress_def)

subsection \<open> Progress' formula-trace properties \<close>

lemma progress_custom_induct[case_names Pred Let LetPast 
    Eq Less LessEq Neg Or And Ands Exists Agg 
    Prev Next Since Until Trigger Release MatchP MatchF TP TS]:
  assumes Pred: "\<And>e ts. Q (formula.Pred e ts)"
    and Let: "\<And>p \<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Let p \<phi> \<psi>)"
    and LetPast: "\<And>p \<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.LetPast p \<phi> \<psi>)"
    and Eq: "\<And>t1 t2. Q (Formula.Eq t1 t2)"
    and Less: "\<And>t1 t2. Q (Formula.Less t1 t2)"
    and LessEq: "\<And>t1 t2. Q (Formula.LessEq t1 t2)"
    and Neg: "\<And>\<phi>. Q \<phi> \<Longrightarrow> Q (formula.Neg \<phi>)"
    and Or: "\<And>\<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Or \<phi> \<psi>)"
    and And: "\<And>\<phi> \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.And \<phi> \<psi>)"
    and Ands: "\<And>\<phi>s. (\<And>\<phi>. \<phi> \<in> set \<phi>s \<Longrightarrow> Q \<phi>) \<Longrightarrow> Q (formula.Ands \<phi>s)"
    and Exists: "\<And>t \<phi>. Q \<phi> \<Longrightarrow> Q (formula.Exists t \<phi>)"
    and Agg: "\<And>y \<omega> tys f \<phi>. Q \<phi> \<Longrightarrow> Q (Formula.Agg y \<omega> tys f \<phi>)"
    and Prev: "\<And>I \<phi>. Q \<phi> \<Longrightarrow> Q (formula.Prev I \<phi>)"
    and Next: "\<And>I \<phi>. Q \<phi> \<Longrightarrow> Q (formula.Next I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Since \<phi> I \<psi>)"
    and Until: "\<And>\<phi> I \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Until \<phi> I \<psi>)"
    and Trigger: "\<And>\<phi> I \<psi>. Q \<phi> \<Longrightarrow> Q \<psi> \<Longrightarrow> Q (formula.Trigger \<phi> I \<psi>)"
    and Release: "\<And>\<phi> I \<psi>. (mem I 0 \<or> \<not> bounded I \<Longrightarrow> Q \<phi>) \<Longrightarrow> (mem I 0 \<or> \<not> bounded I \<Longrightarrow> Q \<psi>) 
    \<Longrightarrow> (\<not> (mem I 0 \<or> \<not> bounded I) \<Longrightarrow> Q (release_safe_bounded \<phi> I \<psi>)) 
    \<Longrightarrow> Q (formula.Release \<phi> I \<psi>)"
    and MatchP: "(\<And>I r. (\<And>z. z \<in> regex.atms r \<Longrightarrow> Q z) \<Longrightarrow> Q (formula.MatchP I r))"
    and MatchF: "(\<And>I r. (\<And>z. z \<in> regex.atms r \<Longrightarrow> Q z) \<Longrightarrow> Q (formula.MatchF I r))"
    and TP: "\<And>t. Q (Formula.TP t)"
    and TS: "\<And>t. Q (Formula.TS t)"
  shows "Q \<phi>"
  by (induct \<phi>)
    (auto simp: release_safe_bounded_def Formula.eventually_def 
      Formula.TT_def always_safe_bounded_def once_def intro!: assms)

lemma progress_ge_gen:
  fixes \<phi> :: "'t Formula.formula"
  shows "Safety.future_bounded \<phi> \<Longrightarrow>
   \<exists>P j. dom P = S \<and> range_mapping i j P \<and> i \<le> progress \<sigma> P \<phi> j"
proof (induction \<phi> arbitrary: i S rule: progress_custom_induct)
  case (Pred e ts)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"])
      (auto split: option.splits if_splits simp: rel_mapping_alt pred_mapping_alt dom_def)
next
  case (Let p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  from Let.prems obtain P2 j2 where P2: "dom P2 = insert ?pn S" "range_mapping i j2 P2"
    "i \<le> progress \<sigma> P2 \<psi> j2"
    by (atomize_elim, intro Let(2)) auto
  from Let.prems obtain P1 j1 where P1: "dom P1 = S" "range_mapping (the (P2 ?pn)) j1 P1"
    "the (P2 ?pn) \<le> progress \<sigma> P1 \<phi> j1"
    by (atomize_elim, intro Let(1)) auto
  let ?P12 = "max_mapping P1 P2"
  from P2 have P12_bound: "pred_mapping (\<lambda>x. x \<le> max j1 j2) ?P12"
    apply (intro pred_mapping_mono[OF range_mapping_max_mapping[of i j1 P1 j2 P2]])
      apply (auto intro!: pred_mapping_mono[OF P2(2)] pred_mapping_mono[OF P1(2)])
    by (simp add: pred_mapping_alt)
  have le1: "progress \<sigma> P1 \<phi> j1 \<le> progress \<sigma> (?P12(?pn := P1 ?pn)) \<phi> (max j1 j2)"
    using P1 P2 P12_bound
    apply (intro progress_mono_gen)
    apply (auto simp: rel_mapping_alt max_mapping_def
      elim: pred_mapping_mono intro!: pred_mapping_fun_upd split: option.splits)
    by (metis (no_types, lifting) domI max.coboundedI1 option.sel pred_mapping_alt)
  have le2: "progress \<sigma> P2 \<psi> j2 \<le> progress \<sigma> (?P12(?pn \<mapsto> progress \<sigma> P1 \<phi> j1)) \<psi> (max j1 j2)"
    using P1 P2 P12_bound 
    by (intro progress_mono_gen) (auto simp: rel_mapping_alt max_mapping_def split: option.splits
      intro!: max.coboundedI1 progress_le_gen
      elim: pred_mapping_mono intro!: pred_mapping_map_upd)
  show ?case
    unfolding progress.simps
  proof (intro exI[of _ "?P12(?pn := P1 ?pn)"] exI[of _ "max j1 j2"] conjI)
    show "dom (?P12(?pn := P1 ?pn)) = S"
      using P1
      apply (auto simp: dom_def max_mapping_def split: option.splits)
      using P2(1) by auto
  next
    show "range_mapping i (max j1 j2) (?P12(?pn := P1 ?pn))"
      using P1 P2 
      by (force simp add: pred_mapping_alt dom_def max_mapping_def split: option.splits)
  next
    have "i \<le> progress \<sigma> P2 \<psi> j2" by fact
    also have "... \<le> progress \<sigma> (?P12(?pn \<mapsto> progress \<sigma> P1 \<phi> j1)) \<psi> (max j1 j2)"
      using le2 by blast
    also have "... \<le> progress \<sigma> 
      ((?P12(?pn := P1 ?pn))(?pn\<mapsto>progress \<sigma> (?P12(?pn := P1 ?pn)) \<phi> (max j1 j2))) \<psi> (max j1 j2)"
      using P12_bound P1 apply (auto intro!: progress_mono_gen pred_mapping_map_upd
        pred_mapping_fun_upd max.coboundedI1 progress_le_gen
      elim: pred_mapping_mono simp: le1 rel_mapping_alt split: option.splits)
      by (metis (no_types, lifting) domI option.sel pred_mapping_alt)
    finally show "i \<le> ..." .
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  from LetPast.prems obtain P2 j2 
    where P2: "dom P2 = insert ?pn S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<psi> j2"
    by (atomize_elim, intro LetPast(2)) auto
  from LetPast.prems obtain P1 j1 
    where P1: "dom P1 = insert ?pn S" "range_mapping (the (P2 ?pn)) j1 P1"
    "the (P2 ?pn) \<le>letpast_progress \<sigma> P1 ?pn \<phi> j1"
    apply(atomize_elim)
    apply(rule letpast_progress_ge)
    using LetPast(1, 3)
    apply(auto)
    done
  let ?P12 = "max_mapping P1 P2"
  from P2 have P12_bound: "pred_mapping (\<lambda>x. x \<le> max j1 j2) ?P12"
    apply (intro pred_mapping_mono[OF range_mapping_max_mapping[of i j1 P1 j2 P2]])
      apply (auto intro!: pred_mapping_mono[OF P2(2)] pred_mapping_mono[OF P1(2)])
    by (simp add: pred_mapping_alt)
  have le1: "progress \<sigma> (P1(?pn \<mapsto> min (Suc i) j1)) \<phi> j1 
    \<le> progress \<sigma> (?P12(?pn \<mapsto> min (Suc i) (max j1 j2))) \<phi> (max j1 j2)"
    using P1 P2 P12_bound 
    apply (intro progress_mono_gen)
    apply (auto simp: rel_mapping_alt max_mapping_def
      elim: pred_mapping_mono intro!: pred_mapping_fun_upd split: option.splits)
    done
  have le2: "progress \<sigma> P2 \<psi> j2 
    \<le> progress \<sigma> (?P12(?pn \<mapsto> letpast_progress \<sigma> P1 ?pn \<phi> j1)) \<psi> (max j1 j2)"
    using P1 P2 P12_bound 
    apply (intro progress_mono_gen)
    apply(auto simp: rel_mapping_alt max_mapping_def
      intro!: max.coboundedI1 progress_le_gen
      elim: pred_mapping_mono intro!: pred_mapping_map_upd)
     apply(auto simp:range_mapping_to_pred_mapping letpast_progress_le split: option.splits)
    done
  let ?P12' = "?P12(?pn := if ?pn \<in> S then P1 ?pn else None)"
  show ?case
    unfolding progress.simps Let_def
  proof (intro exI[of _ "?P12'"] exI[of _ "max j1 j2"] conjI)
    show "dom ?P12' = S"
      using P1 P2 apply (auto simp: dom_def max_mapping_def split: option.splits)
      using insert_absorb apply fastforce
      using insert_absorb apply fastforce
      using insert_absorb apply fastforce
      using P2(1) apply blast
      using P2(1) apply blast
      using insert_absorb apply fastforce
      using insert_absorb apply fastforce
      using P2(1) apply blast
      done
  next
    show "range_mapping i (max j1 j2) ?P12'"
      using P1 P2 apply (auto simp add: pred_mapping_alt dom_def max_mapping_def split: option.splits)
                 apply (metis P2(1) domI insert_absorb max.coboundedI2 option.sel)
                apply (metis P2(1) domI insert_absorb max.coboundedI1 option.sel)
               apply (metis P2(1) domI insert_absorb max.coboundedI2 option.sel)
              apply (metis P2(1) domI insert_absorb max.coboundedI2 option.sel)
             apply (metis P2(1) domI insert_absorb max.coboundedI1 option.sel)
            apply (metis P2(1) domI insert_absorb max.coboundedI2 option.sel)
           apply (metis P2(1) domIff insert_iff max.coboundedI2 option.discI option.sel)
          apply (metis P2(1) domIff insert_iff max.coboundedI1 option.discI option.sel)
         apply (metis P2(1) domIff insert_iff max.coboundedI2 option.discI option.sel)
        apply (metis P2(1) domIff insert_iff max.coboundedI2 option.discI option.sel)
       apply (metis P2(1) domIff insert_iff max.coboundedI1 option.discI option.sel)
      apply (metis P2(1) domIff insert_iff max.coboundedI2 option.discI option.sel)
      done
  next
    have "i \<le> progress \<sigma> P2 \<psi> j2" by fact
    also have "... \<le> progress \<sigma> (?P12(?pn \<mapsto> letpast_progress \<sigma> P1 ?pn \<phi> j1)) \<psi> (max j1 j2)"
      using le2 by blast
    also have "... \<le> progress \<sigma> (?P12'(?pn \<mapsto> letpast_progress \<sigma> ?P12' ?pn \<phi> (max j1 j2))) \<psi> (max j1 j2)"
      using P12_bound P1 P2 
      apply (auto intro!: progress_mono_gen pred_mapping_map_upd pred_mapping_fun_upd progress_le_gen)
           apply (simp add: letpast_progress_le max.coboundedI1 pred_mapping_mono_strong)
          apply (intro letpast_progress_le)
          apply (metis (no_types, lifting) domD insert_absorb max.coboundedI2 
          max.commute option.sel pred_mapping_alt pred_mapping_map_upd)
         apply (intro rel_mapping_le_map_upd letpast_progress_mono)
      using pred_mapping_mono_strong apply force
           apply (metis (no_types, lifting) domD insert_absorb max.coboundedI2 
          max.commute option.sel pred_mapping_alt pred_mapping_map_upd)
          apply simp
         apply (smt (z3) domD fun_upd_triv insert_absorb 
          max_mapping_cobounded1 nle_le rel_mapping_map_upd subsetI)
        apply (simp add: letpast_progress_le max.coboundedI1 pred_mapping_mono_strong)
       apply (intro letpast_progress_le)
      apply force
      apply (subst letpast_progress_ignore_upd[where x=None, symmetric])
      apply (intro rel_mapping_le_map_upd letpast_progress_mono)
         apply (simp add: pred_mapping_alt)
        apply (simp add: pred_mapping_alt)
       apply simp
      apply (auto simp add: rel_mapping_alt)
       apply (metis (no_types, lifting) insertCI insert_subset 
          max_mapping_cobounded1 rel_mapping_alt subset_insertI)+
      done
    also have "... \<le> progress \<sigma> (?P12'(?pn \<mapsto>(Inf {i. i \<le> max j1 j2 \<and> i = progress \<sigma> (?P12'(?pn \<mapsto> i)) \<phi> (max j1 j2)}))) \<psi> (max j1 j2)"
      unfolding letpast_progress_def by(auto)
    finally show "i \<le> ..." .
  qed
next
  case (Eq _ _)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (Less _ _)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (LessEq _ _)
  then show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (Or \<phi>1 \<phi>2)
  from Or(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using Or(1)[of S i] by auto
  moreover
  from Or(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using Or(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Or \<phi>1 \<phi>2) (max j1 j2)"
    by (auto 0 3 elim!: order.trans[OF _ progress_mono_gen] 
        intro: max_mapping_cobounded1 max_mapping_cobounded2 simp:range_mapping_to_pred_mapping)
        (auto simp: pred_mapping_max_mapping range_mapping_to_pred_mapping)
  with P1 P2 show ?case 
    by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) 
      auto
next
  case (And \<phi>1 \<phi>2)
  from And(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using And(1)[of S i] by auto
  moreover
  from And(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using And(2)[of S i] by auto
  ultimately have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.And \<phi>1 \<phi>2) (max j1 j2)"
    by (auto 0 3 elim!: order.trans[OF _ progress_mono_gen] 
        intro: max_mapping_cobounded1 max_mapping_cobounded2 simp:range_mapping_to_pred_mapping)
        (auto simp: pred_mapping_max_mapping range_mapping_to_pred_mapping)
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) auto
next
  case (Ands l)
  show ?case proof (cases "l = []")
    case True
    then show ?thesis
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"])
        (auto split: if_splits simp: pred_mapping_alt)
  next
    case False
    then obtain \<phi> where "\<phi> \<in> set l" by (cases l) auto
    from Ands.prems have "\<forall>\<phi>\<in>set l. Safety.future_bounded \<phi>"
      by (simp add: list.pred_set)
    { fix \<phi>
      assume "\<phi> \<in> set l"
      with Ands.prems obtain P j where "dom P = S" "range_mapping i j P" "i \<le> progress \<sigma> P \<phi> j"
        by (atomize_elim, intro Ands(1)[of \<phi> S i]) (auto simp: list.pred_set)
      hence "\<exists>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) 
        \<and> i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)" (is "\<exists>Pj. ?P Pj")
        by (intro exI[of _ "(P, j)"]) auto
    }
    hence "\<forall>\<phi>\<in>set l. \<exists>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) 
        \<and> i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)" (is "\<forall>\<phi>\<in>set l. \<exists>Pj. ?P Pj \<phi>")
      by blast
    with Ands(1) Ands.prems False have "\<exists>Pjf. \<forall>\<phi>\<in>set l. ?P (Pjf \<phi>) \<phi>"
      by (auto simp: Ball_def intro: choice)
    then obtain Pjf where Pjf: "\<forall>\<phi>\<in>set l. ?P (Pjf \<phi>) \<phi>" ..
    define Pf where "Pf = fst o Pjf"
    define jf where "jf = snd o Pjf"
    have *: "dom (Pf \<phi>) = S" "range_mapping i (jf \<phi>) (Pf \<phi>)" "i \<le> progress \<sigma> (Pf \<phi>) \<phi> (jf \<phi>)"
      if "\<phi> \<in> set l" for \<phi>
      using Pjf[THEN bspec, OF that] 
      unfolding Pf_def jf_def by auto
    with False show ?thesis
      unfolding progress.simps eq_False[THEN iffD2, OF False] if_False
      apply ((subst Min_ge_iff; simp add: False),
          intro exI[where x="MAX \<phi>\<in>set l. jf \<phi>"] exI[where x="Max_mapping (Pf ` set l)"]
          conjI ballI order.trans[OF *(3) progress_mono_gen] Max_mapping_coboundedI)
              apply(auto simp: False *[OF \<open>\<phi> \<in> set l\<close>] \<open>\<phi> \<in> set l\<close>)
      subgoal by (auto intro!: range_mapping_to_pred_mapping)
      by (auto intro!: range_mapping_to_pred_mapping range_mapping_Max_mapping)
  qed
next
  case (Prev I \<phi>)
  then obtain P j where "dom P = S" "range_mapping i j P" "i \<le> progress \<sigma> P \<phi> j"
    by (atomize_elim, intro Prev(1)) (auto simp: pred_mapping_alt dom_def)
  with Prev(2) have "dom P = S \<and> range_mapping i (max i j) P 
    \<and> i \<le> progress \<sigma> P (formula.Prev I \<phi>) (max i j)"
    by (auto simp: le_Suc_eq max_def pred_mapping_alt split: if_splits
        elim: order.trans[OF _ progress_mono])
  then show ?case by blast
next
  case (Next I \<phi>)
  then obtain P j where "dom P = S" "range_mapping (Suc i) j P" "Suc i \<le> progress \<sigma> P \<phi> j"
    by (atomize_elim, intro Next(1)) (auto simp: pred_mapping_alt dom_def)
  then show ?case
    by (intro exI[of _ P] exI[of _ j]) (auto 0 4 simp: pred_mapping_alt dom_def)
next
  case (Since \<phi>1 I \<phi>2)
  from Since(3) obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using Since(1)[of S i] by auto
  moreover
  from Since(3) obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using Since(2)[of S i] by auto
  ultimately have
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>1 (max j1 j2)"
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>2 (max j1 j2)"
    by (auto elim!: order.trans[OF _ progress_mono_gen] simp: max_mapping_cobounded1 max_mapping_cobounded2)
      (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
  then have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Since \<phi>1 I \<phi>2) (max j1 j2)"
    by simp
  with P1 P2 show ?case by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"])
      (auto elim!: pred_mapping_le intro: max_mapping_cobounded1)
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then obtain i' where "i < i'" and 1: "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  from Until.prems obtain P1 j1 where P1: "dom P1 = S" "range_mapping (Suc i') j1 P1" "Suc i' \<le> progress \<sigma> P1 \<phi>1 j1"
    by (atomize_elim, intro Until(1)) (auto simp: pred_mapping_alt dom_def)
  from Until.prems obtain P2 j2 where P2: "dom P2 = S" "range_mapping (Suc i') j2 P2" "Suc i' \<le> progress \<sigma> P2 \<phi>2 j2"
    by (atomize_elim, intro Until(2)) (auto simp: pred_mapping_alt dom_def)
  let ?P12 = "max_mapping P1 P2"
  have "i \<le> progress \<sigma> ?P12 (Formula.Until \<phi>1 I \<phi>2) (max j1 j2)"
    unfolding progress.simps
  proof (intro cInf_greatest, goal_cases nonempty greatest)
    case nonempty
    then show ?case
      by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
  next
    case (greatest x)
    from P1(2,3) have "i' < j1"
      by (auto simp: less_eq_Suc_le intro!: progress_le_gen elim!: order.trans pred_mapping_mono_strong)
    then have "i' < max j1 j2" by simp
    have "progress \<sigma> P1 \<phi>1 j1 \<le> progress \<sigma> ?P12 \<phi>1 (max j1 j2)"
      using P1 P2
      by (auto intro!: progress_mono_gen max_mapping_cobounded1)
         (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
    moreover have "progress \<sigma> P2 \<phi>2 j2 \<le> progress \<sigma> ?P12 \<phi>2 (max j1 j2)"
      using P1 P2
      by (auto intro!: progress_mono_gen max_mapping_cobounded2)
         (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
    ultimately have "i' \<le> min (progress \<sigma> ?P12 \<phi>1 (max j1 j2)) (progress \<sigma> ?P12 \<phi>2 (max j1 j2))"
      using P1(3) P2(3) by simp
    with greatest \<open>i' < max j1 j2\<close> have "memR I (\<tau> \<sigma> i' - \<tau> \<sigma> x)"
      by simp
    with 1 have "\<tau> \<sigma> i < \<tau> \<sigma> x"
      by (auto 0 3 elim: contrapos_np)
    then show ?case by (auto dest!: less_\<tau>D)
  qed
  with P1 P2 \<open>i < i'\<close> show ?case
    by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) (auto simp: range_mapping_relax)
next
  case (Trigger \<phi>1 I \<phi>2)
  hence f_bdd1: "Safety.future_bounded \<phi>1" 
    and f_bdd2: "Safety.future_bounded \<phi>2"
    by clarsimp+
  have size':
    "size' \<phi>1 \<le> size' \<phi>1 + size' \<phi>2"
    "size' \<phi>2 \<le> size' \<phi>1 + size' \<phi>2"
    by auto
  obtain P1 j1 where P1: "dom P1 = S" "range_mapping i j1 P1"  "i \<le> progress \<sigma> P1 \<phi>1 j1"
    using Trigger(1)[OF f_bdd1, of S i] by auto
  moreover
  obtain P2 j2 where P2: "dom P2 = S" "range_mapping i j2 P2" "i \<le> progress \<sigma> P2 \<phi>2 j2"
    using Trigger(2)[OF f_bdd2, of S i] by auto
  ultimately have
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>1 (max j1 j2)"
    "i \<le> progress \<sigma> (max_mapping P1 P2) \<phi>2 (max j1 j2)"
    by (auto elim!: order.trans[OF _ progress_mono_gen] simp: max_mapping_cobounded1 max_mapping_cobounded2)
      (auto simp: range_mapping_to_pred_mapping pred_mapping_max_mapping)
  then have "i \<le> progress \<sigma> (max_mapping P1 P2) (Formula.Trigger \<phi>1 I \<phi>2) (max j1 j2)"
    by simp
  with P1 P2 show ?case 
    by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"])
      (auto elim!: pred_mapping_le intro: max_mapping_cobounded1 split: if_splits)
next
  case (Release \<phi>1 I \<phi>2)
  from Release(4) have "bounded (flip_int_double_upper I)"
    by (transfer) auto
  then obtain m where "\<not> memR (flip_int_double_upper I) m"
    by (auto simp: bounded_memR)

  then obtain i' where "i < i'" and 1: "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  then have not_mem_I: "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using memR_flip_int_double_upper
    by auto

  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    obtain P1 j1 
      where P1: "dom P1 = S" "range_mapping (Suc i') j1 P1" "Suc i' \<le> progress \<sigma> P1 \<phi>1 j1"
      using Release(4) True
      by (atomize_elim, intro Release(1)) 
        (auto simp: pred_mapping_alt dom_def)
    obtain P2 j2 
      where P2: "dom P2 = S" "range_mapping (Suc i') j2 P2" "Suc i' \<le> progress \<sigma> P2 \<phi>2 j2"
      using Release(4) True
      by (atomize_elim, intro Release(2)) 
        (auto simp: pred_mapping_alt dom_def)
    let ?P12 = "max_mapping P1 P2"

    have "i \<le> progress \<sigma> ?P12 (Formula.Release \<phi>1 I \<phi>2) (max j1 j2)"
      unfolding progress.simps if_P[OF True]
    proof (intro cInf_greatest, goal_cases nonempty greatest)
      case nonempty
      then show ?case
        by (auto simp: trans_le_add1[OF \<tau>_mono] intro!: exI[of _ "max j1 j2"])
    next
      case (greatest x)
      from P1(2,3) have "i' < j1"
        by (auto simp: less_eq_Suc_le intro!: progress_le_gen elim!: order.trans pred_mapping_mono_strong)
      then have "i' < max j1 j2" by simp
      have "progress \<sigma> P1 \<phi>1 j1 \<le> progress \<sigma> ?P12 \<phi>1 (max j1 j2)"
        using P1(1) P2(1) pred_mapping_max_mapping[of j1 P1 j2 P2] 
          range_mapping_to_pred_mapping[OF P1(2)]
          range_mapping_to_pred_mapping[OF P2(2)]
        by (auto intro!: progress_mono_gen max_mapping_cobounded1)
      moreover have "progress \<sigma> P2 \<phi>2 j2 \<le> progress \<sigma> ?P12 \<phi>2 (max j1 j2)"
        using P1(1) P2(1) pred_mapping_max_mapping[of j1 P1 j2 P2] 
          range_mapping_to_pred_mapping[OF P1(2)]
          range_mapping_to_pred_mapping[OF P2(2)]
        by (auto intro!: progress_mono_gen max_mapping_cobounded2)
      ultimately have "i' \<le> min (progress \<sigma> ?P12 \<phi>1 (max j1 j2)) (progress \<sigma> ?P12 \<phi>2 (max j1 j2))"
        using P1(3) P2(3) by simp
      with greatest \<open>i' < max j1 j2\<close> have
        "memR (flip_int_double_upper I) (\<tau> \<sigma> i' - \<tau> \<sigma> x) \<or> memR (I) (\<tau> \<sigma> i' - \<tau> \<sigma> x)"
        by auto
      with 1 not_mem_I have "\<tau> \<sigma> i < \<tau> \<sigma> x"
        by (auto 0 3 elim: contrapos_np)
      then show ?case by (auto dest!: less_\<tau>D)
    qed
    then show ?thesis
      using P1 P2 \<open>i < i'\<close>
      by (intro exI[of _ "max_mapping P1 P2"] exI[of _ "max j1 j2"]) (auto simp: range_mapping_relax)
  next
    case False
    have future_bounded: "Safety.future_bounded (release_safe_bounded \<phi>1 I \<phi>2)"
      using Release(4)
      apply (auto simp add: release_safe_bounded_def)
      using False flip_int_less_lower_props memR_zero
      by blast
    show ?thesis 
      using Release(3)[OF False future_bounded] False by auto
  qed
next
  case (MatchP I r)
  then show ?case
  proof (cases "regex.atms r = {}")
    case True
    with MatchP.prems show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"] exI[of _ i])
        (auto split: if_splits simp: pred_mapping_alt regex.pred_set)
  next
    case False
    define pick where "pick = (\<lambda>\<phi> :: 't Formula.formula. SOME Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and>
       i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj))"
    let ?pickP = "fst o pick" let ?pickj = "snd o pick"
    from MatchP have pick: "\<phi> \<in> regex.atms r \<Longrightarrow> dom (?pickP \<phi>) = S \<and>
      range_mapping i (?pickj \<phi>) (?pickP \<phi>) \<and> i \<le> progress \<sigma> (?pickP \<phi>) \<phi> (?pickj \<phi>)" for \<phi>
      unfolding pick_def o_def future_bounded.simps regex.pred_set
      by (intro someI_ex[where P = "\<lambda>Pj. dom (fst Pj) = S \<and> range_mapping i (snd Pj) (fst Pj) \<and>
         i \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"]) auto
    from pick have pred_pick: "\<phi> \<in> regex.atms r \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> ?pickj \<phi>) (?pickP \<phi>)" for \<phi>
      by (force elim: pred_mapping_mono)
    with pick False show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "Max_mapping (?pickP ` regex.atms r)"] exI[of _ "Max (?pickj ` regex.atms r)"])
        (auto simp: Max_mapping_coboundedI range_mapping_Max_mapping[of _ 0, simplified]
          order_trans[OF pick[THEN conjunct2, THEN conjunct2] progress_mono_gen])
  qed
next
  case (MatchF I r)
  from MatchF.prems obtain m where "\<not> memR I m"
    by (auto simp: bounded_memR)
  then obtain i' where "i < i'" and i': "\<not> memR I (\<tau> \<sigma> i' - \<tau> \<sigma> i)"
    using ex_le_\<tau>[where x="\<tau> \<sigma> i + m" and s=\<sigma> and i="Suc i"]
    by atomize_elim (auto simp add: less_eq_Suc_le memR_antimono)
  have ix: "i \<le> x" if "memR I (\<tau> \<sigma> i' - \<tau> \<sigma> x)" for x
    using i' less_\<tau>D[of \<sigma> i x] that by (auto 0 3 simp: diff_le_mono2 elim: contrapos_np)
  show ?case
  proof (cases "regex.atms r = {}")
    case True
    with MatchF.prems ix show ?thesis
      unfolding progress.simps
      by (intro exI[of _ "\<lambda>e. if e \<in> S then Some (Suc i') else None"] exI[of _ "Suc i'"])
        (auto split: if_splits simp: pred_mapping_alt regex.pred_set add.commute less_Suc_eq
          intro!: cInf_greatest dest!: spec[of _ i'] less_imp_le[THEN \<tau>_mono, of _ i' \<sigma>])
  next
    case False
    then obtain \<phi> where \<phi>: "\<phi> \<in> regex.atms r" by auto
    define pick where "pick = (\<lambda>\<phi> :: 't Formula.formula. SOME Pj. dom (fst Pj) = S \<and> range_mapping (Suc i') (snd Pj) (fst Pj) \<and>
      Suc i' \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj))"
    define pickP where "pickP = fst o pick" define pickj where "pickj = snd o pick"
    from MatchF have pick: "\<phi> \<in> regex.atms r \<Longrightarrow> dom (pickP \<phi>) = S \<and>
    range_mapping (Suc i') (pickj \<phi>) (pickP \<phi>) \<and> Suc i' \<le> progress \<sigma> (pickP \<phi>) \<phi> (pickj \<phi>)" for \<phi>
      unfolding pick_def o_def future_bounded.simps regex.pred_set pickj_def pickP_def
      by (intro someI_ex[where P = "\<lambda>Pj. dom (fst Pj) = S \<and> range_mapping (Suc i') (snd Pj) (fst Pj) \<and>
       Suc i' \<le> progress \<sigma> (fst Pj) \<phi> (snd Pj)"]) auto
    from pick have pred_pick: "\<phi> \<in> regex.atms r \<Longrightarrow> pred_mapping (\<lambda>x. x \<le> pickj \<phi>) (pickP \<phi>)" for \<phi>
      by (force elim: pred_mapping_mono)
    let ?P = "Max_mapping (pickP ` regex.atms r)" let ?j = "Max (pickj ` regex.atms r)"
    from pick[OF \<phi>] False \<phi> have "Suc i' \<le> ?j"
      by (intro order_trans[OF pick[THEN conjunct2, THEN conjunct2], OF \<phi>] order_trans[OF progress_le_gen])
        (auto simp: Max_ge_iff dest: range_mapping_relax[of _ _ _ 0, OF _ _ order_refl, simplified])
    moreover
    note i' ix
    moreover
    from MatchF.prems have "Regex.pred_regex Safety.future_bounded r"
      by auto
    ultimately show ?thesis using \<tau>_mono[of _ ?j \<sigma>] less_\<tau>D[of \<sigma> i] pick pred_pick False
      by (intro exI[of _ "?j"]  exI[of _ "?P"])
        (auto 0 3 intro!: cInf_greatest range_mapping_Max_mapping[of _ 0, simplified]
          order_trans[OF le_SucI[OF order_refl] order_trans[OF pick[THEN conjunct2, THEN conjunct2] progress_mono_gen]]
          range_mapping_Max_mapping[OF _ _ ballI[OF range_mapping_relax[of "Suc i'" _ _ i, OF _ _ order_refl]]]
          simp: ac_simps Suc_le_eq trans_le_add2 Max_mapping_coboundedI progress_regex_def
          dest: spec[of _ "i'"] spec[of _ ?j])
  qed
next
  case (TP t)
  show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
next
  case (TS t)
  show ?case
    by (intro exI[of _ "\<lambda>e. if e \<in> S then Some i else None"]) 
      (auto split: if_splits simp: pred_mapping_alt)
qed auto

lemma progress_ge: "Safety.future_bounded \<phi> \<Longrightarrow> \<exists>j. i \<le> progress \<sigma> Map.empty \<phi> j"
  using progress_ge_gen[of \<phi> "{}" i \<sigma>]
  by auto

lemma progress_time_conv:
  assumes "\<forall>i<j. \<tau> \<sigma> i = \<tau> \<sigma>' i"
  shows "progress \<sigma> P \<phi> j = progress \<sigma>' P \<phi> j"
  using assms
proof (induction \<phi> arbitrary: P j)
next
  case(LetPast p \<phi> \<psi>)
  with LetPast show ?case
    by (auto simp: letpast_progress_def 
        simp del: fun_upd_apply)
next 
  case (Until \<phi>1 I \<phi>2)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with Until show ?case
  proof (cases "bounded I")
    case True
    then show ?thesis
    proof (cases "j")
      case (Suc n)
      with * Until show ?thesis
        using \<tau>_mono[THEN trans_le_add1]
        by (auto 6 0
            intro!: box_equals[OF arg_cong[where f=Inf]
              cInf_restrict_nat[symmetric, where x=n] 
              cInf_restrict_nat[symmetric, where x=n]])
    qed simp
  qed (simp add: bounded_memR)
next
  case (Release \<phi> I \<psi> P j)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with Release show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case mem: True
    show ?thesis
      using mem Release
    proof (cases "bounded I")
      case True
      then show ?thesis
        using mem
      proof (cases "j")
        case (Suc n)
        with * Release show ?thesis
          using \<tau>_mono[THEN trans_le_add1] mem
          by (auto 6 0
              intro!: box_equals[OF arg_cong[where f=Inf]
                cInf_restrict_nat[symmetric, where x=n] 
                cInf_restrict_nat[symmetric, where x=n]])
      qed (simp add: Release)
    qed (auto simp add: bounded_memR)
  next
    case False
    have obs: "progress \<sigma> P \<psi>' j = progress \<sigma>' P \<psi>' j 
    \<Longrightarrow> progress \<sigma> P (Formula.eventually J \<psi>') j = progress \<sigma>' P (Formula.eventually J \<psi>') j"
      for \<psi>':: "'c Formula.formula" and J
      using Release.prems
      by (auto simp: fun_eq_iff progress_eventually 
          intro!: arg_cong[where f="(\<lambda>X. \<Sqinter> X)"] 
          arg_cong[where f=Collect] iff_allI)
        (metis memR_nonzeroD less_\<tau>D  order.strict_trans zero_less_diff)+
    have "progress \<sigma> P Formula.TT j = progress \<sigma>' P Formula.TT j"
      by auto
    moreover have "progress \<sigma> P (formula.Until \<psi> (int_remove_lower_bound I) (formula.And \<psi> \<phi>)) j 
      = progress \<sigma>' P (formula.Until \<psi> (int_remove_lower_bound I) (formula.And \<psi> \<phi>)) j"
      using Release.prems
      by (auto simp: fun_eq_iff intro!: arg_cong[where f="(\<lambda>X. \<Sqinter> X)"] 
          arg_cong[where f=Collect])
        (metis Release.IH less_\<tau>D less_or_eq_imp_le memR_nonzeroD 
          order_less_le_trans zero_less_diff)+
    ultimately show ?thesis 
      using Release False obs
      by (auto simp: release_safe_bounded_def always_safe_bounded_def
          simp del: progress.simps(16)
          intro!: arg_cong2[where f=min] arg_cong[where f="\<lambda>x. x - Suc 0"])
  qed
next
  case (MatchP I r P j)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with MatchP show ?case using \<tau>_mono[THEN trans_le_add1]
    by (cases "bounded I"; cases j)
      ((auto 6 0 simp: progress_le_gen progress_regex_def intro!: box_equals[OF arg_cong[where f=Inf]
            cInf_restrict_nat[symmetric, where x="j-1"] cInf_restrict_nat[symmetric, where x="j-1"]]) [])+
next
  case (MatchF I r)
  have *: "i \<le> j - 1 \<longleftrightarrow> i < j" if "j \<noteq> 0" for i
    using that by auto
  with MatchF show ?case using \<tau>_mono[THEN trans_le_add1]
    by (cases "bounded I"; cases j)
      ((auto 6 0 simp: progress_le_gen progress_regex_def intro!: box_equals[OF arg_cong[where f=Inf]
            cInf_restrict_nat[symmetric, where x="j-1"] cInf_restrict_nat[symmetric, where x="j-1"]]) [])+
qed (auto simp: progress_regex_def)

lemma progress_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "progress \<sigma> P \<phi> (plen \<pi>) = progress \<sigma>' P \<phi> (plen \<pi>)"
  using assms by (auto intro: progress_time_conv \<tau>_prefix_conv)

lemma sat_prefix_conv_gen:
  fixes \<phi> :: "ty Formula.formula"
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "i < progress \<sigma> P \<phi> (plen \<pi>) \<Longrightarrow> dom V = dom V' \<Longrightarrow> dom P = dom V \<Longrightarrow>
    pred_mapping (\<lambda>x. x \<le> plen \<pi>) P \<Longrightarrow>
    (\<And>p n v i \<phi>. (p, n) \<in> dom V \<Longrightarrow> i < the (P (p, n)) \<Longrightarrow> n = length v \<Longrightarrow>
      the (V (p, n)) v i = the (V' (p, n)) v i) \<Longrightarrow>
    Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat \<sigma>' V' v i \<phi>"
proof (induction \<phi> arbitrary: P V V' v i rule: progress_custom_induct)
  case (Pred e ts)
  let ?en = "(e, length ts)"
  from Pred.prems(1,4) have "i < plen \<pi>"
    by (blast intro!: order.strict_trans2 progress_le_gen)
  show ?case proof (cases "V ?en")
    case None
    then have "V' ?en = None" using \<open>dom V = dom V'\<close> by auto
    with None \<Gamma>_prefix_conv[OF assms(1,2) \<open>i < plen \<pi>\<close>] show ?thesis by simp
  next
    case (Some a)
    obtain a' where "V' ?en = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    then have "i < the (P ?en)"
      using Pred.prems(1-3) by (auto split: option.splits)
    then have "the (V ?en) (map (Formula.eval_trm v) ts) i = the (V' ?en) (map (Formula.eval_trm v) ts) i"
      using Some by (intro Pred.prems(5)) (simp_all add: domI)
    with Some \<open>V' ?en = Some a'\<close> show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>))"
  show ?case 
    unfolding sat.simps 
  proof (rule Let.IH(2))
    from Let.prems show "i < progress \<sigma> (P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) \<psi> (plen \<pi>)"
      by simp
    from Let.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by simp
    from Let.prems show "dom (P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) = dom (?V V \<sigma>)"
      by simp
    from Let.prems show "pred_mapping (\<lambda>x. x \<le> plen \<pi>) (P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>)))"
      by (auto intro!: pred_mapping_map_upd elim!: progress_le_gen)
  next
    fix p' n v i \<phi>'
    assume 1: "(p', n) \<in> dom (?V V \<sigma>)" and 2: "i < the ((P(?pn \<mapsto> progress \<sigma> P \<phi> (plen \<pi>))) (p', n))"
      and 3: "n = length (v :: event_data list)"
    show "the (?V V \<sigma> (p', n)) v i = the (?V V' \<sigma>' (p', n)) v i"
    proof (cases "(p', n) = ?pn")
      case True
      with Let 2 show ?thesis by auto
    next
      case False
      then show ?thesis
        apply simp
        apply (intro conjI)
          apply auto[2]
        apply (rule Let.prems(5))
        using 1 2 3 by auto
    qed
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?pn = "(p, Formula.nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. (V(?pn \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>)))"
  show ?case unfolding sat.simps Let_def proof (rule LetPast.IH(2))
    from LetPast.prems show "i < progress \<sigma> (P(?pn \<mapsto> (Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)}))) \<psi> (plen \<pi>)"
      by (simp add: letpast_progress_def Let_def)
    from LetPast.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by simp
    from LetPast.prems show "dom (P(?pn \<mapsto>(Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)}))) = dom (?V V \<sigma>)"
      by simp
    from LetPast.prems show "pred_mapping (\<lambda>x. x \<le> plen \<pi>) (P(?pn \<mapsto>(Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)})))"
      by(auto simp add: pred_mapping_alt intro: letpast_progress_le[unfolded letpast_progress_def])
  next
    fix p' n v i \<phi>'
    assume 1: "(p', n) \<in> dom (?V V \<sigma>)" and 2: "i < the ((P(?pn \<mapsto>(Inf {i. i\<le>(plen \<pi>) \<and> i=progress \<sigma> (P(?pn \<mapsto> i)) \<phi> (plen \<pi>)}))) (p', n))"
      and 3: "n = length (v :: event_data list)"
    show "the (?V V \<sigma> (p', n)) v i = the (?V V' \<sigma>' (p', n)) v i"
    proof (cases "(p', n) = ?pn")
      case True
      with 2 have "i < letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>)"
        unfolding letpast_progress_def by simp
      then have i_less: "i < progress \<sigma> (P(?pn \<mapsto>letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>))) \<phi> (plen \<pi>)"
        using letpast_progress_fixpoint[OF LetPast(6)] by metis
      have P': "pred_mapping (\<lambda>x. x \<le> plen \<pi>) (P(?pn \<mapsto> letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>)))"
        using LetPast.prems(4) by (auto simp: letpast_progress_le)

      have "letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j =
            letpast_sat (\<lambda>X u k. Formula.sat \<sigma>' (V'(?pn \<mapsto> X)) u k \<phi>) w j"
        if "j \<le> i" for w j
        using that
      proof (induct "\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>" w j rule: letpast_sat.induct)
        case (1 w j)
        then have j_less: "j < progress \<sigma> (P(?pn \<mapsto>letpast_progress \<sigma> P ?pn \<phi> (plen \<pi>))) \<phi> (plen \<pi>)"
          using i_less by simp
        show ?case
          apply (subst (1 2) letpast_sat.simps)
          apply (rule LetPast.IH(1)[OF j_less _ _ P'])
          using LetPast.prems(2) apply (auto simp add: dom_def)[]
          using LetPast.prems(3) apply (auto simp add: dom_def)[]
          apply (simp del: fun_upd_apply)
          subgoal for p'' n' v' i'
            apply (cases "(p'', length v') = ?pn")
             apply simp
             apply (rule conj_cong[OF refl])
             apply (rule "1"(1))
              apply assumption
            using "1"(2) apply simp
            apply (subst (1 2) fun_upd_apply)
            apply (simp only: if_not_P if_False)
            apply (rule LetPast.prems(5))
            by auto
          done
      qed
      with True show ?thesis by simp
    next
      case False
      with 1 2 3 LetPast.prems(5) show ?thesis by fastforce
    qed
  qed
next
  case (Eq t1 t2)
  show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by auto
next
  case (Ands l)
  from Ands.prems have "\<forall>\<phi>\<in>set l. i < progress \<sigma> P \<phi> (plen \<pi>)"
    by (cases l) simp_all
  with Ands show ?case 
    unfolding sat_Ands by (auto 0 4)
next
  case (Exists \<phi>)
  then show ?case by simp
next
  case (Prev I \<phi>)
  with \<tau>_prefix_conv[OF assms(1,2)] show ?case
    by (cases i) (auto split: if_splits)
next
  case (Next I \<phi>)
  then have "Suc i < plen \<pi>"
    by (auto intro: order.strict_trans2[OF _ progress_le_gen[of _ P \<sigma> \<phi>]])
  with Next.prems \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro conj_cong Next) auto
next
  case (Since \<phi>1 I \<phi>2)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le_gen])
  with Since.prems \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro conj_cong ex_cong ball_cong Since.IH[where P=P])
      (auto split: if_splits, metis diff_self_eq_0 less_antisym order.strict_trans1)
next
  case (Until \<phi>1 I \<phi>2)
  from Until.prems have [simp]: "bounded I"
    by (cases "bounded I") (auto simp: bounded_memR Inf_UNIV_nat)
  from Until.prems obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    "j \<le> progress \<sigma> P \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma> P \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 1: "k < progress \<sigma> P \<phi>1 (plen \<pi>)" and 2: "k < progress \<sigma> P \<phi>2 (plen \<pi>)"
    if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    using that
    by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
  have 3: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    using 1[OF that] Until(6) 
    by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])

  from Until.prems have "i < progress \<sigma>' P (Formula.Until \<phi>1 I \<phi>2) (plen \<pi>)"
    unfolding progress_prefix_conv[OF assms(1,2)] by simp
  then obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
    "j \<le> progress \<sigma>' P \<phi>1 (plen \<pi>)" "j \<le> progress \<sigma>' P \<phi>2 (plen \<pi>)"
    by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
      dest!: le_cInf_iff[THEN iffD1, rotated -1])
  then have 11: "k < progress \<sigma> P \<phi>1 (plen \<pi>)" and 21: "k < progress \<sigma> P \<phi>2 (plen \<pi>)"
    if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    unfolding progress_prefix_conv[OF assms(1,2)]
    using that
    by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
  have 31: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    using 11[OF that] Until(6) by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])
  thm order.trans[OF _ progress_le_gen]

  show ?case unfolding sat.simps
  proof ((intro ex_cong iffI; elim conjE), goal_cases LR RL)
    case (LR j)
    with Until.IH(1)[OF 1] Until.IH(2)[OF 2] \<tau>_prefix_conv[OF assms(1,2) 3] Until.prems show ?case
      by (auto 0 4 simp: le_diff_conv add.commute memR_antimono 
          dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  next
    case (RL j)
    with Until.IH(1)[OF 11] Until.IH(2)[OF 21] \<tau>_prefix_conv[OF assms(1,2) 31] Until.prems show ?case
      by (auto 0 4 simp: le_diff_conv add.commute memR_antimono 
          dest: less_imp_le order.trans[OF \<tau>_mono, rotated])
  qed
next
  case (Trigger \<phi> I \<psi>)
  then have "i < plen \<pi>"
    by (auto elim!: order.strict_trans2[OF _ progress_le_gen])
  with Trigger.prems \<tau>_prefix_conv[OF assms(1,2)] 
  show ?case
    unfolding sat.simps
    thm conj_cong ex_cong iff_allI Trigger.IH[where P=P]
    apply (intro conj_cong ex_cong iff_allI Trigger.IH[where P=P])
    apply (auto split: if_splits)
           apply (smt (verit) Trigger.IH(2) diff_diff_cancel less_imp_diff_less)
    apply (smt (verit) Trigger.IH(1) diff_diff_cancel greaterThanAtMost_iff less_imp_diff_less)
    apply (smt (verit, best) Trigger.IH(2) diff_diff_cancel less_imp_diff_less)
    by (smt (verit) Trigger.IH(1) diff_diff_cancel greaterThanAtMost_iff less_imp_diff_less)
next
  case (Release \<phi> I \<psi>)

 have \<tau>_prefix_diff_conv: "\<And>k i. k < plen \<pi> \<Longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
  proof -
    fix k i
    assume assm: "k < plen \<pi>"
    {
      assume "i \<le> k"
      then have "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
        using assm \<tau>_prefix_conv[OF assms(1,2)]
        by auto
    }
    moreover {
      assume "i > k"
      then have
        "\<tau> \<sigma> k - \<tau> \<sigma> i = 0"
        "\<tau> \<sigma>' k - \<tau> \<sigma>' i = 0"
        by auto
      then have "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
        by auto
    }
    ultimately show "(\<tau> \<sigma> k - \<tau> \<sigma> i) = (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" 
      using not_le_imp_less by blast
  qed

  show ?case
  proof (cases "mem I 0 \<or> \<not> bounded I")
    case True
    have [simp]: "bounded (flip_int_double_upper I)"
      using True Release
      by (cases "bounded (flip_int_double_upper I)") 
        (auto simp: bounded_memR Inf_UNIV_nat)
  
    define A where "A = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> min (progress \<sigma> P \<psi> (plen \<pi>)) (progress \<sigma> P \<phi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
    define B where "B = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma> P \<psi> (plen \<pi>) \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
  
    define A' where "A' = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> min (progress \<sigma>' P \<psi> (plen \<pi>)) (progress \<sigma>' P \<phi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
    define B' where "B' = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma>' P \<psi> (plen \<pi>) \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
  
    have AA'_eq: "A = A'"
      using \<tau>_prefix_diff_conv
      unfolding A_def A'_def progress_prefix_conv[OF assms(1,2)]
      by auto
    have BB'_eq: "B = B'"
      using \<tau>_prefix_diff_conv
      unfolding B_def B'_def progress_prefix_conv[OF assms(1,2)]
      by auto
  
    have
      "(min (progress \<sigma> P \<psi> (plen \<pi>)) (progress \<sigma> P \<phi> (plen \<pi>))) \<in> A"
      "progress \<sigma> P \<psi> (plen \<pi>) \<in> B"
      unfolding A_def B_def
      by auto
    then have non_empty: 
      "A \<noteq> {}"
      "B \<noteq> {}"
      by auto
  
    have progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = min (Inf A) (Inf B)"
      using min_Inf[OF non_empty] True
      unfolding A_def B_def
      by auto
  
    have "k < progress \<sigma> P \<phi> (plen \<pi>) \<and> k < progress \<sigma> P \<psi> (plen \<pi>)"
    if memR: "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
    proof (cases "progress \<sigma> P \<phi> (plen \<pi>) \<le> progress \<sigma> P \<psi> (plen \<pi>)")
      case assm: True
      show ?thesis
      proof (cases "Inf A \<le> Inf B")
        case True
        then have release_progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf A"
          using progress_eq
          by auto
        then obtain j where
          "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          "j \<le> progress \<sigma> P \<phi> (plen \<pi>)"
          "j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          using Release
          unfolding A_def
          by atomize_elim 
            (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
              dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then show 1: "k < progress \<sigma> P \<phi> (plen \<pi>) \<and> k < progress \<sigma> P \<psi> (plen \<pi>)"
          using that
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
      next
        define J where "J = {j. \<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> j \<le> progress \<sigma> P \<psi> (plen \<pi>)}"
        define j where "j = Min J"
        case False
        then have release_progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B"
          using progress_eq
          by auto
        then obtain j' where
          "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma> j' - \<tau> \<sigma> i)"
          "j' \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          using Release
          unfolding B_def
          by atomize_elim 
            (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
              dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then have "\<not> memR (I) (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "j' \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          using memR_flip_int_double_upper
          by auto
        then have "j' \<in> J"
          unfolding J_def
          by auto
        then have J_props: "J \<noteq> {}" "finite J"
          unfolding J_def
          by auto
        then have "j \<in> J"
          unfolding j_def
          by auto
        then have j_props: "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
          unfolding J_def
          by auto
        have less_j_mem: "\<And>l. l<j \<Longrightarrow> memR I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        proof -
          fix l
          assume l_j: "l < j"
          {
            assume "\<not>memR I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
            then have "l \<in> J"
              using l_j j_props(2)
              unfolding J_def
              by auto
            then have "False"
              using l_j J_props
              unfolding j_def
              by auto
          }
          then show "memR I (\<tau> \<sigma> l - \<tau> \<sigma> i)" by auto
        qed
        have j_leq: "j \<le> progress \<sigma> P \<phi> (plen \<pi>)"
        proof -
          {
            assume j_g: "j > progress \<sigma> P \<phi> (plen \<pi>)"
            have "\<And>k. k < plen \<pi> 
              \<Longrightarrow> k \<le> min (progress \<sigma> P \<psi> (plen \<pi>)) (progress \<sigma> P \<phi> (plen \<pi>)) 
              \<Longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
            proof -
              fix k
              assume "k < plen \<pi>" 
                "k \<le> min (progress \<sigma> P \<psi> (plen \<pi>)) (progress \<sigma> P \<phi> (plen \<pi>))"
              then have "k < j" using j_g
                by auto
              then show "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
                using less_j_mem
                by auto
            qed
            then have "i \<in> A"
              unfolding A_def
              by auto
            then have "i \<ge> Inf A"
              by (simp add: cInf_lower)
            moreover have "i < Inf A"
              using Release(4) release_progress_eq False
              by auto
            ultimately have "False"
              by auto
          }
          then show ?thesis using not_le_imp_less by auto
        qed
        then show "k < progress \<sigma> P \<phi> (plen \<pi>) \<and> k < progress \<sigma> P \<psi> (plen \<pi>)"
          using that j_props
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
      qed
    next
      case assm: False
      then have A_eq: "A = {i. \<forall>k. k < (plen \<pi>) \<and> k \<le> (progress \<sigma> P \<psi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
        unfolding A_def
        by auto
      have "A \<subseteq> B"
      proof -
        {
          fix i
          assume "i \<in> A"
          then have i_props: "\<forall>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma> P \<psi> (plen \<pi>) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
            unfolding A_eq
            by auto
          then have "\<And>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma> P \<psi> (plen \<pi>) \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
            using memR_flip_int_double_upper not_le_imp_less
            by auto
          then have "i \<in> B"
            unfolding B_def
            by auto
        }
        then show ?thesis by blast
      qed
      then have "Inf B \<le> Inf A"
        using Inf_leq[OF non_empty(1), of B]
        by auto
      then have release_progress_eq: "progress \<sigma> P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B"
        using progress_eq
        by auto
      then have "\<exists>j. \<not> memR (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
        using Release
        unfolding B_def
        by (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
          dest!: le_cInf_iff[THEN iffD1, rotated -1])
      then obtain j where
        "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        "j \<le> progress \<sigma> P \<phi> (plen \<pi>)"
        "j \<le> progress \<sigma> P \<psi> (plen \<pi>)"
        using assm
        by auto
      then have 1: "k < progress \<sigma> P \<phi> (plen \<pi>)" and 2: "k < progress \<sigma> P \<psi> (plen \<pi>)"
        if "memR (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
        using that
        by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma> k j])
      then show ?thesis
        using memR_flip_int_double_upper memR
        by auto
    qed
    then have 1: "k < progress \<sigma> P \<phi> (plen \<pi>)" and 2: "k < progress \<sigma> P \<psi> (plen \<pi>)"
      if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using that
      by auto
  
    have "k < progress \<sigma>' P \<phi> (plen \<pi>) \<and> k < progress \<sigma>' P \<psi> (plen \<pi>)"
    if memR: "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
    proof (cases "progress \<sigma> P \<phi> (plen \<pi>) \<le> progress \<sigma> P \<psi> (plen \<pi>)")
      case assm: True
      show ?thesis
      proof (cases "Inf A \<le> Inf B")
        case True
        then have release_progress_eq: "progress \<sigma>' P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf A'"
          using progress_eq AA'_eq
          unfolding progress_prefix_conv[OF assms(1,2)]
          by auto
        then obtain j where
          "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
          "j \<le> progress \<sigma>' P \<phi> (plen \<pi>)"
          "j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          using Release(4)
          unfolding A'_def progress_prefix_conv[OF assms(1,2)]
          by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
            dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then show 1: "k < progress \<sigma>' P \<phi> (plen \<pi>) \<and> k < progress \<sigma>' P \<psi> (plen \<pi>)"
          using that
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
      next
        define J where "J = {j. \<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<and> j \<le> progress \<sigma>' P \<psi> (plen \<pi>)}"
        define j where "j = Min J"
        case False
        then have release_progress_eq: "progress \<sigma>' P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B'"
          using progress_eq BB'_eq
          unfolding progress_prefix_conv[OF assms(1,2)]
          by auto
        then obtain j' where
          "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma>' j' - \<tau> \<sigma>' i)"
          "j' \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          using Release(4)
          unfolding B'_def progress_prefix_conv[OF assms(1,2)]
          by atomize_elim (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
            dest!: le_cInf_iff[THEN iffD1, rotated -1])
        then have "\<not> memR (I) (\<tau> \<sigma>' j' - \<tau> \<sigma>' i)" "j' \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          using memR_flip_int_double_upper
          by auto
        then have "j' \<in> J"
          unfolding J_def
          by auto
        then have J_props: "J \<noteq> {}" "finite J"
          unfolding J_def
          by auto
        then have "j \<in> J"
          unfolding j_def
          by auto
        then have j_props: "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
          unfolding J_def
          by auto
        have less_j_mem: "\<And>l. l<j \<Longrightarrow> memR I (\<tau> \<sigma>' l - \<tau> \<sigma>' i)"
        proof -
          fix l
          assume l_j: "l < j"
          {
            assume "\<not>memR I (\<tau> \<sigma>' l - \<tau> \<sigma>' i)"
            then have "l \<in> J"
              using l_j j_props(2)
              unfolding J_def
              by auto
            then have "False"
              using l_j J_props
              unfolding j_def
              by auto
          }
          then show "memR I (\<tau> \<sigma>' l - \<tau> \<sigma>' i)" by auto
        qed
        have j_leq: "j \<le> progress \<sigma>' P \<phi> (plen \<pi>)"
        proof -
          {
            assume j_g: "j > progress \<sigma>' P \<phi> (plen \<pi>)"
            have "\<And>k. k < plen \<pi> 
              \<Longrightarrow> k \<le> min (progress \<sigma>' P \<psi> (plen \<pi>)) (progress \<sigma>' P \<phi> (plen \<pi>)) 
              \<Longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
            proof -
              fix k
              assume "k < plen \<pi>" 
                "k \<le> min (progress \<sigma>' P \<psi> (plen \<pi>)) (progress \<sigma>' P \<phi> (plen \<pi>))"
              then have "k < j" using j_g
                by auto
              then show "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
                using less_j_mem
                by auto
            qed
            then have "i \<in> A'"
              unfolding A'_def
              by auto
            then have "i \<ge> Inf A'"
              by (simp add: cInf_lower)
            moreover have "i < Inf A'"
              using Release(4) release_progress_eq False
              unfolding AA'_eq BB'_eq progress_prefix_conv[OF assms(1,2)]
              by auto
            ultimately have "False"
              by auto
          }
          then show ?thesis using not_le_imp_less by auto
        qed
        then show "k < progress \<sigma>' P \<phi> (plen \<pi>) \<and> k < progress \<sigma>' P \<psi> (plen \<pi>)"
          using that j_props
          by (auto 0 3 elim!: order.strict_trans2[rotated] elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
      qed
    next
      case assm: False
      then have A'_eq: "A' = {i. \<forall>k. k < (plen \<pi>) 
          \<and> k \<le> (progress \<sigma>' P \<psi> (plen \<pi>)) \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
        unfolding A'_def progress_prefix_conv[OF assms(1,2)]
        by auto
      have "A' \<subseteq> B'"
      proof -
        {
          fix i
          assume "i \<in> A'"
          then have i_props: "\<forall>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma>' P \<psi> (plen \<pi>) 
              \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
            unfolding A'_eq
            by auto
          then have "\<And>k. k < (plen \<pi>) \<and> k \<le> progress \<sigma>' P \<psi> (plen \<pi>) 
              \<longrightarrow> memR (flip_int_double_upper I) (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
            using memR_flip_int_double_upper not_le_imp_less
            by auto
          then have "i \<in> B'"
            unfolding B'_def
            by auto
        }
        then show ?thesis by blast
      qed
      then have "Inf B' \<le> Inf A'"
        using Inf_leq[OF non_empty(1), of B'] BB'_eq AA'_eq
        by auto
      then have release_progress_eq: "progress \<sigma>' P (formula.Release \<phi> I \<psi>) (plen \<pi>) = Inf B'"
        using progress_eq BB'_eq AA'_eq
        unfolding progress_prefix_conv[OF assms(1,2)]
        by auto
      then have "\<exists>j. \<not> memR (flip_int_double_upper I) (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<and> j 
        \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
        using Release(4)
        unfolding B'_def progress_prefix_conv[OF assms(1,2)]
        by (auto 0 4 simp add: less_eq_Suc_le not_le intro: Suc_leI dest: spec[of _ "i"]
          dest!: le_cInf_iff[THEN iffD1, rotated -1])
      then obtain j where
        "\<not> memR (flip_int_double_upper I) (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        "j \<le> progress \<sigma>' P \<phi> (plen \<pi>)"
        "j \<le> progress \<sigma>' P \<psi> (plen \<pi>)"
        using assm
        unfolding progress_prefix_conv[OF assms(1,2)]
        by auto
      then have 1: "k < progress \<sigma>' P \<phi> (plen \<pi>)" and 2: "k < progress \<sigma>' P \<psi> (plen \<pi>)"
        if "memR (flip_int_double_upper I) (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
        using that
        by (auto 0 3 elim!: order.strict_trans2[rotated] 
            elim: contrapos_np intro!: less_\<tau>D[of \<sigma>' k j])
      then show ?thesis
        using memR_flip_int_double_upper memR
        by auto
    qed
    then have 11: "k < progress \<sigma>' P \<phi> (plen \<pi>)" and 21: "k < progress \<sigma>' P \<psi> (plen \<pi>)"
      if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using that
      by auto
  
    have 3: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      using 1[OF that] Release(6-) 
      by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])
    have 31: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using 11[OF that] Release(6-)
      by (auto simp only: less_eq_Suc_le order.trans[OF _ progress_le_gen])
  
    have t_eq1: "\<And>j. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
      using \<tau>_prefix_conv[OF assms(1,2) 3] memR_flip_int_double_upper
      by auto
  
    have t_eq2: "\<And>j. memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
      using \<tau>_prefix_conv[OF assms(1,2) 31] memR_flip_int_double_upper
      by auto
    
    have sat_subformulas:
      "\<And>j v. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> Formula.sat \<sigma> V v j \<phi> = Formula.sat \<sigma>' V' v j \<phi>"
      "\<And>j v. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> Formula.sat \<sigma> V v j \<psi> = Formula.sat \<sigma>' V' v j \<psi>"
      using Release(2)[OF True 2] Release(3-) Release(1)[OF True 1] 
        memR_flip_int_double_upper
      by auto
  
    have "\<And>j k. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> k \<le> j \<Longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      using memR_antimono[of I]
      using \<tau>_mono diff_le_mono
      by blast
    then have "\<And>j k. memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> k \<le> j \<Longrightarrow> Formula.sat \<sigma> V v k \<phi> = Formula.sat \<sigma>' V' v k \<phi>"
      using sat_subformulas(1)
      by auto
  
    then have release_eq: "\<And>j. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (
        (Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)) =
        (Formula.sat \<sigma>' V' v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma>' V' v k \<phi>))
    )"
      using sat_subformulas(2)
      by auto
    
    show ?thesis
    proof (rule iffI)
      assume assm: "Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>)"
      {
        fix j
        assume assms: "j \<ge> i" "mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        then have memR: "memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" by auto
        have memRi: "memR I (\<tau> \<sigma>' i - \<tau> \<sigma>' i)" by auto
        have mem: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          using assms(2)[unfolded t_eq2[OF memR,symmetric] t_eq2[OF memRi,symmetric]]
          by auto
        have sat: "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using assm assms(1) mem
          by auto
        then have "Formula.sat \<sigma>' V' v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma>' V' v k \<phi>)"
          using mem release_eq[of j]
          by auto
      }
      then show "Formula.sat \<sigma>' V' v i (formula.Release \<phi> I \<psi>)"
        by auto
    next
      assume assm: "Formula.sat \<sigma>' V' v i (formula.Release \<phi> I \<psi>)"
      {
        fix j
        assume assms: "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        then have memR: "memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" by auto
        have memRi: "memR I (\<tau> \<sigma> i - \<tau> \<sigma> i)" by auto
        have mem: "mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
          using assms(2)[unfolded t_eq1[OF memR] t_eq1[OF memRi]]
          by auto
        have sat: "Formula.sat \<sigma>' V' v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma>' V' v k \<phi>)"
          using assm assms(1) mem
          by auto
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using assms(2) release_eq[of j]
          by auto
      }
      then show "Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>)"
        by auto
    qed
  next
    case False
    then have i_le: "i < progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) (plen \<pi>)"
      using Release(4)
      by auto

    have rewrite_conds: "bounded I" "\<not> mem I 0"
      using False
      by auto
    
    have sat_safe_bounded_eq: "\<And>v. Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I \<psi>) 
      = Formula.sat \<sigma>' V' v i (release_safe_bounded \<phi> I \<psi>)"
      using Release(3)[OF False i_le] Release(4-)
      by auto

    show ?thesis
    proof (cases "\<exists>j\<in>{i..<plen \<pi>}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
      case True
      then have "\<exists>j\<in>{i..<plen \<pi>}. mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using \<tau>_prefix_diff_conv
        by auto
      then have
        "Formula.sat \<sigma> V v i (Formula.eventually I Formula.TT)"
        "Formula.sat \<sigma>' V' v i (Formula.eventually I Formula.TT)"
        using True
        by auto
      then have r:
        "Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I \<psi>)"
        "Formula.sat \<sigma>' V' v i (formula.Release \<phi> I \<psi>) = Formula.sat \<sigma>' V' v i (release_safe_bounded \<phi> I \<psi>)"
        using sat_release_rewrite[OF rewrite_conds, of _ _ v i \<phi> \<psi>]
        by auto
      
      show ?thesis
        using sat_safe_bounded_eq[of v]
        unfolding r
        by blast
    next
      case int_props: False
      then have int_props:
        "\<forall>j\<in>{i..<plen \<pi>}. \<not>mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        "\<forall>j\<in>{i..<plen \<pi>}. \<not>mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using \<tau>_prefix_diff_conv
        by auto
      define event_TT where "event_TT = ((Formula.eventually I Formula.TT):: ty Formula.formula)"
      have "i < progress \<sigma> P (release_safe_bounded \<phi> I \<psi>) (plen \<pi>)"
        using False Release(4)
        by auto
      then have i_le: "i < progress \<sigma> P event_TT (plen \<pi>)"
        unfolding release_safe_bounded_def event_TT_def
        by auto
      moreover have "progress \<sigma> P event_TT (plen \<pi>) = progress \<sigma>' P event_TT (plen \<pi>)"
        by (meson assms(1) assms(2) progress_prefix_conv)
      ultimately have i_le': "i < progress \<sigma>' P event_TT (plen \<pi>)"
        by auto

      have "\<And>j. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<Longrightarrow> j < plen \<pi>"
      proof -
        fix j
        assume mem: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        {
          assume assm: "j \<ge> plen \<pi>"
          have "{i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} 
            = {i. \<forall>k. k < plen \<pi> \<and> k \<le> plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
            by auto
          have "\<And>k. k < plen \<pi> \<Longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          proof -
            fix k
            assume "k < plen \<pi>"
            then have "k < j"
              using assm
              by auto
            then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j"
              by auto
            then show "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
              using mem
              by auto
          qed
          then have "i \<in> {i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
            by auto
          then have "i \<ge> progress \<sigma> P event_TT (plen \<pi>)"
            unfolding progress_eventually progress_TT event_TT_def
            by (auto simp add: cInf_lower)
          then have "False"
            using i_le leD 
            by blast
        }
        then show "j < plen \<pi>"
          using not_le
          by blast
      qed
      then have "\<forall>j\<ge>plen \<pi>. \<not>mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        using leD
        by blast
      then have not_mem_\<sigma>: "\<forall>j\<ge>i. \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
        using int_props
        by auto

      have "\<And>j. mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i) \<Longrightarrow> j < plen \<pi>"
      proof -
        fix j
        assume mem: "mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        {
          assume assm: "j \<ge> plen \<pi>"
          have "{i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)} 
            = {i. \<forall>k. k < plen \<pi> \<and> k \<le> plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
            by auto
          have "\<And>k. k < plen \<pi> \<Longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
          proof -
            fix k
            assume "k < plen \<pi>"
            then have "k < j"
              using assm
              by auto
            then have "\<tau> \<sigma>' k \<le> \<tau> \<sigma>' j"
              by auto
            then show "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)"
              using mem
              by auto
          qed
          then have "i \<in> {i. \<forall>k. k < plen \<pi> \<longrightarrow> memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)}"
            by auto
          then have "i \<ge> progress \<sigma>' P event_TT (plen \<pi>)"
            unfolding progress_eventually progress_TT event_TT_def
            by (auto simp add: cInf_lower)
          then have "False"
            using i_le' leD
            by blast
        }
        then show "j < plen \<pi>"
          using not_le
          by blast
      qed
      then have "\<forall>j\<ge>plen \<pi>. \<not>mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using leD
        by blast
      then have not_mem_\<sigma>': "\<forall>j\<ge>i. \<not> mem I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)"
        using int_props
        by auto

      show ?thesis
        using not_mem_\<sigma> not_mem_\<sigma>'
        by auto
    qed
  qed
next
  case (MatchP I r)
  then have "i < plen \<pi>"
    by (force simp: pred_mapping_alt elim!: order.strict_trans2[OF _ progress_le_gen])
  with MatchP.prems \<tau>_prefix_conv[OF assms(1,2)] show ?case
    unfolding sat.simps
    by (intro ex_cong conj_cong match_cong_strong MatchP) 
      (auto simp: progress_regex_def split: if_splits)
next
  case (MatchF I r)
  from MatchF.prems have [simp]: "bounded I"
    by (cases "bounded I") 
      (auto simp: bounded_memR Inf_UNIV_nat)
  show ?case
  proof (cases "regex.atms r = {}")
    case True
    from MatchF.prems(1) obtain j where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "j \<le> plen \<pi>"
      by atomize_elim 
        (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 1: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
      by (meson \<tau>_mono diff_le_mono memR_antimono not_le_imp_less that)
    from MatchF.prems have "i < progress \<sigma>' P (Formula.MatchF I r) (plen \<pi>)"
      unfolding progress_prefix_conv[OF assms(1,2)] by blast
    then obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "j \<le> plen \<pi>"
      by atomize_elim 
        (auto 0 4 simp add: less_eq_Suc_le not_le dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 2: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      by (meson \<tau>_mono diff_le_mono memR_antimono not_le_imp_less that)
    from MatchF.prems(1,4) True show ?thesis
      unfolding sat.simps conj_commute[of "memL _ _"]
    proof (intro ex_cong conj_cong match_cong_strong, goal_cases memL memR sat)
      case (memL j)
      then show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 1, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (memR j)
      then show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    qed auto
  next
    case False
    from MatchF.prems(1) False obtain j 
      where "\<not> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "(\<forall>x\<in>regex.atms r. j \<le> progress \<sigma> P x (plen \<pi>))"
      by atomize_elim (auto 0 6 simp add: less_eq_Suc_le not_le progress_regex_def
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 1: "\<phi> \<in> regex.atms r \<Longrightarrow> k < progress \<sigma> P \<phi> (plen \<pi>)" 
      if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k \<phi>
      using that
      by (auto 0 3 elim!: contrapos_np[of _ "_ < _"] simp: diff_le_mono)
    then have 2: "k < plen \<pi>" if "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "regex.atms r \<noteq> {}" for k
      using that
      by (fastforce intro: order.strict_trans2[OF _ progress_le_gen[OF MatchF(5), of \<sigma>], of k])

    from MatchF.prems have "i < progress \<sigma>' P (Formula.MatchF I r) (plen \<pi>)"
      unfolding progress_prefix_conv[OF assms(1,2)] by blast
    with False obtain j where "\<not> memR I (\<tau> \<sigma>' j - \<tau> \<sigma>' i)" "(\<forall>x\<in>regex.atms r. j \<le> progress \<sigma>' P x (plen \<pi>))"
      by atomize_elim (auto 0 6 simp add: less_eq_Suc_le not_le progress_regex_def
        dest!: le_cInf_iff[THEN iffD1, rotated -1])
    then have 11:  "\<phi> \<in> regex.atms r \<Longrightarrow> k < progress \<sigma> P \<phi> (plen \<pi>)" 
      if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k \<phi>
      using that unfolding progress_prefix_conv[OF assms(1,2)]
      by (auto 0 3 elim!: contrapos_np[of _ "_ < _"] simp: diff_le_mono) 
    have 21: "k < plen \<pi>" if "memR I (\<tau> \<sigma>' k - \<tau> \<sigma>' i)" for k
      using 11[OF that(1)] False 
      by (fastforce intro: order.strict_trans2[OF _ progress_le_gen[OF MatchF(5), of \<sigma>], of k])
    show ?thesis unfolding sat.simps conj_commute[of "memL _ _"]
    proof ((intro ex_cong conj_cong match_cong_strong MatchF(1)[OF _ _ MatchF(3-6)]; assumption?), 
        goal_cases memR memL progress)
      case (memR j)
      with False show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 2, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (memL j)
      with False show ?case
        by (intro iffI)
          ((subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21, symmetric]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]),
            (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; 
              auto elim: order.trans[OF \<tau>_mono, rotated]))
    next
      case (progress j k z)
      with False show ?case
        by (elim 1[rotated])
          (subst (1 2) \<tau>_prefix_conv[OF assms(1,2) 21]; 
            auto simp: diff_le_mono memR_antimono elim!: contrapos_np[of _ False])
    qed
  qed
next
  case (TS t)
  with \<tau>_prefix_conv[OF assms] show ?case
    by simp
qed (auto)

lemma sat_prefix_conv:
  assumes "prefix_of \<pi> \<sigma>" and "prefix_of \<pi> \<sigma>'"
  shows "i < progress \<sigma> Map.empty \<phi> (plen \<pi>) \<Longrightarrow>
    Formula.sat \<sigma> Map.empty v i \<phi> \<longleftrightarrow> Formula.sat \<sigma>' Map.empty v i \<phi>"
  by (erule sat_prefix_conv_gen[OF assms]) auto

lemma progress_remove_neg[simp]: "progress \<sigma> P (remove_neg \<phi>) j = progress \<sigma> P \<phi> j"
  by (cases \<phi>) simp_all


(*<*)
end
(*>*)