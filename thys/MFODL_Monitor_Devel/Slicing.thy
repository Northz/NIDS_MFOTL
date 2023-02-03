(*<*)
theory Slicing
  imports Safety
begin
(*>*)

section \<open>Section 4.2\<close>

subsection \<open>Definition 1\<close>

text \<open>Corresponds to locale @{locale monitor} defined in theory
   @{theory "MFOTL_Monitor_Devel.Abstract_Monitor"}.\<close>

subsection \<open>Definition 2\<close>

locale slicer = monitor _ _ _ _ M for M :: "Formula.prefix \<Rightarrow> (nat \<times> event_data tuple) set" +
  fixes submonitor :: "'k :: finite \<Rightarrow> Formula.prefix \<Rightarrow> (nat \<times> event_data tuple) set"
  and   splitter :: "Formula.prefix \<Rightarrow> 'k \<Rightarrow> Formula.prefix"
  and   joiner :: "('k \<Rightarrow> (nat \<times> event_data tuple) set) \<Rightarrow> (nat \<times> event_data tuple) set"
assumes mono_splitter: "\<pi> \<in> prefixes \<Longrightarrow> \<pi>' \<in> prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> splitter \<pi> k \<le> splitter \<pi>' k"
  and   correct_slicer: "\<pi> \<in> prefixes \<Longrightarrow> joiner (\<lambda>k. submonitor k (splitter \<pi> k)) = M \<pi>"
  and   splitter_prefix: "\<pi> \<in> prefixes \<Longrightarrow> splitter \<pi> k \<in> prefixes"
begin

lemmas sound_slicer = Set.equalityD1[OF correct_slicer]
lemmas complete_slicer = Set.equalityD2[OF correct_slicer]

end

locale self_slicer = slicer _ _ _ _ M "\<lambda>k. M" splitter joiner
  for M splitter joiner

subsection \<open>Definition 3\<close>

locale event_separable_splitter =
  fixes event_splitter :: "Formula.event \<Rightarrow> 'k :: finite set"
begin

lift_definition splitter :: "Formula.prefix \<Rightarrow> 'k \<Rightarrow> Formula.prefix" is
  "\<lambda>\<pi> k. map (\<lambda>(D, t). ({e \<in> D. k \<in> event_splitter e}, t)) \<pi>"
  by (auto simp: o_def split_beta)

subsection \<open>Lemma 1\<close>

lemma mono_splitter: "\<pi> \<le> \<pi>' \<Longrightarrow> splitter \<pi> k \<le> splitter \<pi>' k"
  by transfer auto

end

section \<open>Section 4.3\<close>

abbreviation (input) "ok \<phi> v \<equiv> wf_tuple (Formula.nfv \<phi>) (Formula.fv \<phi>) v"

locale splitting_strategy =
  fixes \<phi> :: "'a Formula.formula" and strategy :: "event_data tuple \<Rightarrow> 'k :: finite set"
  assumes strategy_nonempty: "ok \<phi> v \<Longrightarrow> strategy v \<noteq> {}"
begin

definition slice_set where
  "slice_set k = {v. length v = Formula.nfv \<phi> \<and>
    (\<exists>v'. ok \<phi> v' \<and> (\<forall>i\<in>Formula.fv \<phi>. v' ! i = Some (v ! i)) \<and> k \<in> strategy v')}"

lemma slice_setI: "ok \<phi> v \<Longrightarrow> k \<in> strategy v \<Longrightarrow> map the v \<in> slice_set k"
  by (auto simp add: slice_set_def wf_tuple_def fvi_less_nfv)

lemma UN_slice_setI:
  assumes "length v = Formula.nfv \<phi>"
  shows "v \<in> \<Union>(range slice_set)"
proof -
  let ?v' = "tabulate (\<lambda>i. if i \<in> Formula.fv \<phi> then Some (v ! i) else None) 0 (Formula.nfv \<phi>)"
  have "ok \<phi> ?v'"
    by (simp add: wf_tuple_def)
  then obtain k where "k \<in> strategy ?v'"
    using strategy_nonempty by blast
  moreover have "\<forall>i\<in>Formula.fv \<phi>. ?v' ! i = Some (v ! i)"
    by (auto simp add: fvi_less_nfv)
  ultimately show ?thesis
    using assms \<open>ok \<phi> ?v'\<close> by (auto simp add: slice_set_def)
qed

end

subsection \<open>Definition 4\<close>

locale joint_data_slicer = monitor "Formula.nfv \<phi>" "Formula.fv \<phi>" traces "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" M +
  traces_downward_closed traces + splitting_strategy \<phi> strategy for \<phi> traces M strategy +
  assumes replace_prefix_traces: "\<pi> \<in> prefixes \<Longrightarrow> \<sigma> \<in> traces \<Longrightarrow> replace_prefix \<pi> \<sigma> \<in> traces"
begin

definition event_splitter where
  "event_splitter e = (\<Union>(strategy ` {v. ok \<phi> v \<and> Safety.matches (map the v) \<phi> e}))"

sublocale event_separable_splitter where event_splitter = event_splitter .

definition joiner where
  "joiner = (\<lambda>s. \<Union>k. s k \<inter> (UNIV :: nat set) \<times> {v. ok \<phi> v \<and> k \<in> strategy v})"

lemma splitter_pslice: "splitter \<pi> k = formula_slicer.pslice \<phi> (slice_set k) \<pi>"
  by transfer (auto simp add: event_splitter_def intro!: slice_setI,
      auto simp add: slice_set_def fv_less_nfv wf_tuple_def
      elim!: matches_cong[THEN iffD1, rotated])

lemma splitter_prefixes: "\<pi> \<in> prefixes \<Longrightarrow> splitter \<pi> k \<in> prefixes"
  unfolding splitter_pslice by blast

subsection \<open>Lemma 2\<close>

text \<open>Corresponds to the following theorem @{thm[source] sat_slice_strong} proved in theory
   @{theory "MFOTL_Monitor_Devel.Abstract_Monitor"}:

   @{thm sat_slice_strong[no_vars]}\<close>

subsection \<open>Theorem 1\<close>

sublocale joint_monitor: monitor "Formula.nfv \<phi>" "Formula.fv \<phi>" traces
  "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" "\<lambda>\<pi>. joiner (\<lambda>k. M (splitter \<pi> k))"
proof (standard, goal_cases mono wf_tuple sound complete)
  case (mono \<pi>' \<pi>)
  show ?case
    using mono_monitor[OF splitter_prefixes, OF mono(1) mono_splitter, OF mono(2)]
    by (auto simp: joiner_def)
next
  case (wf_tuple \<pi> i v)
  then obtain k where in_M: "(i, v) \<in> M (splitter \<pi> k)" and k: "k \<in> strategy v"
    unfolding joiner_def by auto
  then show "ok \<phi> v"
    using wf_tuple wf_monitor[OF splitter_prefixes] by blast
next
  case (sound \<sigma> i v \<pi>)
  then obtain k where in_M: "(i, v) \<in> M (splitter \<pi> k)" and k: "k \<in> strategy v"
    unfolding joiner_def by auto
  then have "ok \<phi> v"
    using sound wf_monitor[OF splitter_prefixes] by blast
  with k have slice_set: "map the v \<in> slice_set k"
    by (blast intro!: slice_setI)
  let ?\<sigma>' = "formula_slicer.slice \<phi> (slice_set k) \<sigma>"
  have "?\<sigma>' \<in> traces" and "prefix_of (splitter \<pi> k) ?\<sigma>'"
    using sound by (auto simp add: splitter_pslice)
  then have "sat_the ?\<sigma>' Map.empty v i \<phi>"
    using sound_monitor in_M by blast
  then show ?case
    using sound slice_set by (simp add: formula_slicer.sliceable)
next
  case (complete \<sigma> \<pi> v i)
  with strategy_nonempty obtain k where k: "k \<in> strategy v" by blast
  with k have slice_set: "map the v \<in> slice_set k"
    using \<open>ok \<phi> v\<close> by (blast intro!: slice_setI)
  have "sat_the \<sigma>' Map.empty v i \<phi>" if prefix: "prefix_of (formula_slicer.pslice \<phi> (slice_set k) \<pi>) \<sigma>'"
      and trace: "\<sigma>' \<in> traces" for \<sigma>'
  proof -
    have "sat_the \<sigma>' Map.empty v i \<phi> = sat_the (formula_slicer.slice \<phi> (slice_set k) \<sigma>') Map.empty v i \<phi>"
      using slice_set trace by (simp add: formula_slicer.sliceable)
    also have "\<dots> = sat_the (formula_slicer.slice \<phi> (slice_set k) (replace_prefix \<pi> \<sigma>')) Map.empty v i \<phi>"
      using prefix by (simp add: map_\<Gamma>_replace_prefix)
    also have "\<dots> = sat_the (replace_prefix \<pi> \<sigma>') Map.empty v i \<phi>"
      using complete prefix trace slice_set
      by (simp add: formula_slicer.sliceable replace_prefix_traces)
    also have "\<dots>"
      using complete prefix trace by (simp add: prefix_of_replace_prefix replace_prefix_traces)
    finally show ?thesis .
  qed
  then obtain \<pi>' where \<pi>': "prefix_of \<pi>' (formula_slicer.slice \<phi> (slice_set k) \<sigma>)" "(i, v) \<in> M \<pi>'"
    using complete by (atomize_elim, auto intro!: complete_monitor)
  then obtain \<pi>'' where "\<pi>' = formula_slicer.pslice \<phi> (slice_set k) \<pi>''" and \<pi>'': "prefix_of \<pi>'' \<sigma>"
    by (blast dest!: prefix_of_map_\<Gamma>_D)
  then have "(i, v) \<in> joiner (\<lambda>k. M (splitter \<pi>'' k))"
    using complete k \<pi>' by (auto simp: joiner_def splitter_pslice)
  with \<pi>'' show ?case by blast
qed

subsection \<open>Corollary 1\<close>

sublocale joint_slicer: slicer "Formula.nfv \<phi>" "Formula.fv \<phi>" traces
  "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" "\<lambda>\<pi>. joiner (\<lambda>k. M (splitter \<pi> k))"
  "\<lambda>_. M" splitter joiner
  by unfold_locales (auto simp add: mono_splitter splitter_prefixes)

end

subsection \<open>Definition 5\<close>

text \<open>Corresponds to locale @{locale sliceable_monitor} defined in theory
   @{theory "MFOTL_Monitor_Devel.Abstract_Monitor"}.\<close>

locale sliceable_joint_data_slicer = sliceable_monitor "Formula.nfv \<phi>" "Formula.fv \<phi>" traces
  "relevant_events \<phi>" "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" M + joint_data_slicer \<phi> traces M strategy
  for \<phi> traces M strategy
begin

lemma monitor_split: "\<pi> \<in> prefixes \<Longrightarrow> ok \<phi> v \<Longrightarrow> k \<in> strategy v \<Longrightarrow> (i, v) \<in> M (splitter \<pi> k) \<longleftrightarrow> (i, v) \<in> M \<pi>"
  unfolding splitter_pslice
  by (rule sliceable_M)
    (auto simp: wf_tuple_def fvi_less_nfv intro!: mem_restrI[rotated 2, where y="map the v"] slice_setI)

subsection \<open>Theorem 2\<close>

sublocale self_slicer "Formula.nfv \<phi>" "Formula.fv \<phi>" traces "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>"
  M splitter joiner
proof (standard, safe, goal_cases mono sound complete closed)
  case (sound \<pi> i v)
  then show ?case
    by (auto simp add: joiner_def monitor_split)
next
  case (complete \<pi> i v)
  then have "ok \<phi> v" using wf_monitor by blast
  with strategy_nonempty obtain k where k: "k \<in> strategy v" by blast
  then have "(i, v) \<in> M (splitter \<pi> k)" using complete \<open>ok \<phi> v\<close> by (simp add: monitor_split)
  with \<open>ok \<phi> v\<close> k show ?case by (auto simp add: joiner_def)
qed (simp_all add: mono_splitter splitter_prefixes)

end

section \<open>Towards Theorem 3\<close>

definition "compose_inputs p n A B = {(q, vs) \<in> B. p \<noteq> q \<or> n \<noteq> length vs} \<union>
  {(q, map (case_option None ((!) vs')) vs) | q vs vs'. (q, vs) \<in> A \<and> (p, vs') \<in> B \<and> length vs' = n}"

definition "unshift_opt b vs = map (case_option None (\<lambda>y::nat. if y < b then None else Some (y - b))) vs"

fun inputs :: "'a Formula.formula \<Rightarrow> (Formula.name \<times> nat option list) set" where
  "inputs (Formula.Pred r ts) = {(r, map (\<lambda>t. case t of Formula.Var x \<Rightarrow> Some x | _ \<Rightarrow> None) ts)}"
| "inputs (Formula.Let p \<phi> \<psi>) = compose_inputs p (Formula.nfv \<phi>) (inputs \<phi>) (inputs \<psi>)"
| "inputs (Formula.LetPast p \<phi> \<psi>) = compose_inputs p (Formula.nfv \<phi>)
    (lfp (\<lambda>A. compose_inputs p (Formula.nfv \<phi>) A (inputs \<phi>))) (inputs \<psi>)"
| "inputs (Formula.Eq t1 t2) = {}"
| "inputs (Formula.Less t1 t2) = {}"
| "inputs (Formula.LessEq t1 t2) = {}"
| "inputs (Formula.Neg \<phi>) = inputs \<phi>"
| "inputs (Formula.Or \<phi> \<psi>) = inputs \<phi> \<union> inputs \<psi>"
| "inputs (Formula.And \<phi> \<psi>) = inputs \<phi> \<union> inputs \<psi>"
| "inputs (Formula.Ands \<phi>s) = (\<Union>\<phi>\<in>set \<phi>s. inputs \<phi>)"
| "inputs (Formula.Exists t \<phi>) = apsnd (unshift_opt 1) ` inputs \<phi>"
| "inputs (Formula.Agg y \<omega> tys f \<phi>) = apsnd (unshift_opt (length tys)) ` inputs \<phi>"
| "inputs (Formula.Prev I \<phi>) = inputs \<phi>"
| "inputs (Formula.Next I \<phi>) = inputs \<phi>"
| "inputs (Formula.Since \<phi> I \<psi>) = inputs \<phi> \<union> inputs \<psi>"
| "inputs (Formula.Until \<phi> I \<psi>) = inputs \<phi> \<union> inputs \<psi>"
| "inputs (Formula.Trigger \<phi> I \<psi>) = inputs \<phi> \<union> inputs \<psi>"
| "inputs (Formula.Release \<phi> I \<psi>) = inputs \<phi> \<union> inputs \<psi>"
| "inputs (Formula.MatchP I r) = (\<Union>\<phi>\<in>Regex.atms r. inputs \<phi>)"
| "inputs (Formula.MatchF I r) = (\<Union>\<phi>\<in>Regex.atms r. inputs \<phi>)"
| "inputs (Formula.TP t) = {}"
| "inputs (Formula.TS t) = {}"

lemma Some_set_unshift_opt: "Some x \<in> set (unshift_opt b vs) \<longleftrightarrow> Some (x + b) \<in> set vs"
  by (fastforce simp add: unshift_opt_def split: option.splits if_splits)

lemma mono_compose_inputs: "mono (\<lambda>A. compose_inputs p (Formula.nfv \<phi>) A (inputs \<phi>))"
  by (auto simp add: mono_def compose_inputs_def)

lemma inputs_subset_fv: "(q, vs) \<in> inputs \<phi> \<Longrightarrow> Some x \<in> set vs \<Longrightarrow> x \<in> Formula.fv \<phi>"
proof (induction \<phi> arbitrary: q vs x)
  case (Pred r ts)
  then show ?case
    by (force split: trm.splits)
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (auto simp add: compose_inputs_def fvi_less_nfv split: option.splits)
next
  case (LetPast p \<phi> \<psi>)
  have "\<And>e. e \<in> lfp (\<lambda>A. compose_inputs p (Formula.nfv \<phi>) A (inputs \<phi>)) \<Longrightarrow>
      \<forall>x. Some x \<in> set (snd e) \<longrightarrow> x \<in> Formula.fv \<phi>"
  proof (erule lfp_induct_set[OF _ mono_compose_inputs]; clarsimp)
    fix q vs x
    assume "(q, vs) \<in> compose_inputs p (Formula.nfv \<phi>)
           (lfp (\<lambda>A. compose_inputs p (Formula.nfv \<phi>) A
                       (inputs \<phi>)) \<inter>
            {x. \<forall>xa. Some xa \<in> set (snd x) \<longrightarrow> xa \<in> fv \<phi>})
           (inputs \<phi>)" and "Some x \<in> set vs"
    then show "x \<in> Formula.fv \<phi>"
      using LetPast.IH(1)
      by (auto simp add: compose_inputs_def fvi_less_nfv split: option.splits)
  qed
  then show ?case
    using LetPast.IH(2) LetPast.prems
    by (auto simp add: compose_inputs_def fvi_less_nfv split: option.splits)
next
  case (Eq t1 t2)
  then show ?case by simp
next
  case (Less t1 t2)
  then show ?case by simp
next
  case (LessEq t1 t2)
  then show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi> \<psi>)
  then show ?case by auto
next
  case (And \<phi> \<psi>)
  then show ?case by auto
next
  case (Ands \<phi>s)
  then show ?case by fastforce
next
  case (Exists t \<phi>)
  then show ?case
    by (auto simp add: Some_set_unshift_opt fvi_Suc)
next
  case (Agg y \<omega> tys f \<phi>)
  then show ?case
    by (auto simp add: Some_set_unshift_opt fvi_plus[of _ 0 "length tys", simplified])
next
  case (Prev I \<phi>)
  then show ?case by simp
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  then show ?case by auto
next
  case (Until \<phi> I \<psi>)
  then show ?case by auto
next
  case (Trigger \<phi> I \<psi>)
  then show ?case by auto
next
  case (Release \<phi> I \<psi>)
  then show ?case by auto
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp add: fv_regex_alt)
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp add: fv_regex_alt)
next
  case (TP t)
  then show ?case by simp
next
  case (TS t)
  then show ?case by simp
qed

lemma length_unshift_opt[simp]: "length (unshift_opt b vs) = length vs"
  by (simp add: unshift_opt_def)

lemma matches_imp_input: "Safety.matches v \<phi> (q, as) \<Longrightarrow> \<exists>vs. (q, vs) \<in> inputs \<phi> \<and> length vs = length as"
proof (induction \<phi> arbitrary: v q as)
  case (Pred r ts)
  then show ?case by auto
next
  case (Let p \<phi> \<psi>)
  show ?case
  proof (cases "(p, Formula.nfv \<phi>) = (q, length as)")
    case True
    then show ?thesis
      using Let by (simp add: compose_inputs_def) (metis length_map)
  next
    case False
    then show ?thesis
      using Let by (clarsimp simp add: compose_inputs_def; metis length_map)
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?R = "\<lambda>e' e. Safety.matches (snd e') \<phi> e \<and> fst e' = p \<and> length (snd e') = Formula.nfv \<phi>"
  let ?F = "\<lambda>A. compose_inputs p (Formula.nfv \<phi>) A (inputs \<phi>)"
  obtain e' where diff: "p \<noteq> q \<or> Formula.nfv \<phi> \<noteq> length as"
    and loop: "?R\<^sup>*\<^sup>* e' (q, as)" and \<psi>: "Safety.matches v \<psi> e'"
    using LetPast.prems by auto
  show ?case proof (cases "e' = (q, as)")
    case True
    then have "Safety.matches v \<psi> (q, as)"
      using \<psi> by simp
    then show ?thesis
      using LetPast.IH(2) diff by (fastforce simp add: compose_inputs_def)
  next
    case False
    then obtain v' where "Safety.matches v' \<phi> (q, as)"
      using loop by (blast elim: rtranclp.cases)
    then obtain vs where "(q, vs) \<in> inputs \<phi>" and len: "length vs = length as"
      using LetPast.IH(1) by blast
    then have "(q, vs) \<in> ?F (lfp ?F)"
      using diff by (auto simp add: compose_inputs_def)
    then have *: "(q, vs) \<in> lfp ?F"
      by (simp add: lfp_fixpoint[OF mono_compose_inputs])
    have "fst e' = p" "length (snd e') = Formula.nfv \<phi>"
      using loop False by (auto dest!: rtranclpD tranclpD)
    then obtain vs' where 2: "(p, vs') \<in> inputs \<psi>" "length vs' = Formula.nfv \<phi>"
      using LetPast.IH(2)[of v p "snd e'"] \<psi> by auto
    then show ?thesis
      using * len by (force simp add: compose_inputs_def)
  qed
next
  case (Eq t1 t2)
  then show ?case by simp
next
  case (Less t1 t2)
  then show ?case by simp
next
  case (LessEq t1 t2)
  then show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi> \<psi>)
  then show ?case by fastforce
next
  case (And \<phi> \<psi>)
  then show ?case by fastforce
next
  case (Ands \<phi>s)
  then show ?case by fastforce
next
  case (Exists t \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> tys f \<phi>)
  then show ?case by force
next
  case (Prev I \<phi>)
  then show ?case by simp
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  then show ?case by fastforce
next
  case (Until \<phi> I \<psi>)
  then show ?case by fastforce
next
  case (Trigger \<phi> I \<psi>)
  then show ?case by fastforce
next
  case (Release \<phi> I \<psi>)
  then show ?case by fastforce
next
  case (MatchF I r)
  then show ?case by fastforce
next
  case (MatchP I r)
  then show ?case by fastforce
next
  case (TP t)
  then show ?case by simp
next
  case (TS t)
  then show ?case by simp
qed

lemma unique_inputs_matches: "Safety.matches v \<phi> (q, as) \<Longrightarrow>
  \<forall>x\<in>X. x < Formula.nfv \<phi> \<and> v ! x = z \<Longrightarrow> \<forall>k\<in>K. k < length as \<Longrightarrow>
  (\<And>vs k'. (q, vs) \<in> inputs \<phi> \<Longrightarrow> length vs = length as \<Longrightarrow> k' \<in> K \<Longrightarrow> vs ! k' \<in> Some ` X) \<Longrightarrow>
  k \<in> K \<Longrightarrow> as ! k = z"
proof (induction \<phi> arbitrary: v q as X K k)
  case (Pred r ts)
  then show ?case
    by (fastforce split: trm.splits)
next
  case (Let p \<phi> \<psi>)
  consider (left) v' where "Safety.matches v' \<phi> (q, as)" "Safety.matches v \<psi> (p, v')" "length v' = Formula.nfv \<phi>"
    | (right) "p \<noteq> q \<or> length as \<noteq> Formula.nfv \<phi>" "Safety.matches v \<psi> (q, as)"
    using Let.prems(1) by auto
  then show ?case proof cases
    case left
    then obtain vs' where input': "(p, vs') \<in> inputs \<psi>" "length vs' = Formula.nfv \<phi>"
      by (metis matches_imp_input)
    define Y where "Y = {y. \<exists>vs k'. (q, vs) \<in> inputs \<phi> \<and> length vs = length as \<and> k' \<in> K \<and> vs ! k' = Some y}"
    show ?thesis
      using left(1)
    proof (rule Let.IH(1))
      show "\<forall>y\<in>Y. y < Formula.nfv \<phi> \<and> v' ! y = z"
      proof safe
        fix y assume "y \<in> Y"
        then show "y < Formula.nfv \<phi>"
          using Let.prems(3) inputs_subset_fv fvi_less_nfv
          by (fastforce simp add: Y_def set_conv_nth eq_commute)
        show "v' ! y = z"
          using left(2)
        proof (rule Let.IH(2))
          show "\<forall>x\<in>X. x < Formula.nfv \<psi> \<and> v ! x = z"
            using Let.prems(2) by simp
          show "\<forall>k\<in>Y. k < length v'"
            using Let.prems(3) inputs_subset_fv fvi_less_nfv
            by (fastforce simp add: Y_def set_conv_nth eq_commute left(3))
          show "y \<in> Y" by fact
          fix us' y'
          assume "y' \<in> Y"
          then obtain us k' where **: "(q, us) \<in> inputs \<phi>" "length us = length as"
            "k' \<in> K" "us ! k' = Some y'"
            by (auto simp add: Y_def)
          moreover assume "(p, us') \<in> inputs \<psi>" "length us' = length v'"
          ultimately have "(q, map (case_option None ((!) us')) us) \<in> inputs (Formula.Let p \<phi> \<psi>)"
            by (auto simp add: compose_inputs_def left(3))
          then show "us' ! y' \<in> Some ` X"
            using Let.prems(3,4) ** by fastforce
        qed
      qed
      show "\<forall>k\<in>K. k < length as" by fact
      show "k \<in> K" by fact
      fix us k'
      assume 1: "(q, us) \<in> inputs \<phi>"
      then have "(q, map (case_option None ((!) vs')) us) \<in> inputs (Formula.Let p \<phi> \<psi>)"
        using input' by (auto simp add: compose_inputs_def)
      moreover assume 2: "k' \<in> K" "length us = length as"
      ultimately have "map (case_option None ((!) vs')) us ! k' \<in> Some ` X"
        using Let.prems(4) by auto
      then show "us ! k' \<in> Some ` Y"
        using 1 2 Let.prems(3) by (auto simp add: Y_def split: option.splits)
    qed
  next
    case right
    show ?thesis
      using right(2)
    proof (rule Let.IH(2))
      show "\<forall>x\<in>X. x < Formula.nfv \<psi> \<and> v ! x = z"
        using Let.prems(2) by simp
      show "\<forall>k\<in>K. k < length as" by fact
      show "k \<in> K" by fact
      fix us k'
      assume "(q, us) \<in> inputs \<psi>" "length us = length as"
      then have "(q, us) \<in> inputs (Formula.Let p \<phi> \<psi>)"
        using right by (auto simp add: compose_inputs_def)
      moreover assume "k' \<in> K"
      ultimately show "us ! k' \<in> Some ` X"
        using Let.prems(4) \<open>length us = length as\<close> by blast
    qed
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?R = "\<lambda>e' e. Safety.matches (snd e') \<phi> e \<and> fst e' = p \<and> length (snd e') = Formula.nfv \<phi>"
  let ?S = "\<lambda>u' u. Safety.matches u' \<phi> (p, u) \<and> length u' = Formula.nfv \<phi>"
  let ?F = "\<lambda>A. compose_inputs p (Formula.nfv \<phi>) A (inputs \<phi>)"
  obtain e' where diff: "p \<noteq> q \<or> Formula.nfv \<phi> \<noteq> length as"
    and loop: "?R\<^sup>*\<^sup>* e' (q, as)" and \<psi>: "Safety.matches v \<psi> e'"
    using LetPast.prems by auto
  show ?case proof (cases "e' = (q, as)")
    case True
    then have "Safety.matches v \<psi> (q, as)"
      using \<psi> by simp
    then show ?thesis
    proof (rule LetPast.IH(2)[OF _ _ LetPast.prems(3) _ LetPast.prems(5)])
      show "\<forall>x\<in>X. x < Formula.nfv \<psi> \<and> v ! x = z"
        using LetPast.prems(2) by simp
      fix us k'
      assume "(q, us) \<in> inputs \<psi>" "length us = length as"
      then have "(q, us) \<in> inputs (Formula.LetPast p \<phi> \<psi>)"
        using diff by (auto simp add: compose_inputs_def)
      moreover assume "k' \<in> K"
      ultimately show "us ! k' \<in> Some ` X"
        using LetPast.prems(4) \<open>length us = length as\<close> by blast
    qed
  next
    case False
    then have "?R\<^sup>+\<^sup>+ e' (q, as)"
      using loop by (meson rtranclpD)
    then obtain v0 where \<phi>0: "Safety.matches v0 \<phi> (q, as)"
      and len0: "length v0 = Formula.nfv \<phi>" and "?R\<^sup>*\<^sup>* e' (p, v0)"
      by (fastforce elim: tranclp.cases dest: tranclp_into_rtranclp)
    then obtain vn where "e' = (p, vn)"
      by (cases e') (auto elim: converse_rtranclpE)
    then have "?R\<^sup>*\<^sup>* (p, vn) (p, v0)" and \<psi>: "Safety.matches v \<psi> (p, vn)"
      using \<open>?R\<^sup>*\<^sup>* e' (p, v0)\<close> \<psi> by simp_all
    from this(1) have loop': "?S\<^sup>*\<^sup>* vn v0"
      by (induction "(p, v0)" arbitrary: v0 rule: rtranclp_induct)
        (auto intro: rtranclp.rtrancl_into_rtrancl)
    have len_n: "length vn = Formula.nfv \<phi>"
      using loop' len0 by (auto elim: converse_rtranclpE)
    let ?G = "\<lambda>Y. {y. \<exists>vs k'. ((q, vs) \<in> inputs \<phi> \<and> length vs = length as \<and> k' \<in> K \<or>
      (p, vs) \<in> inputs \<phi> \<and> length vs = Formula.nfv \<phi> \<and> k' \<in> Y) \<and> vs ! k' = Some y}"
    have mono_G: "mono ?G" by (auto intro: monoI)
    define Y where "Y = lfp ?G"
    have Y_less: "y < Formula.nfv \<phi>" if "y \<in> Y" for y
      using that mono_G unfolding Y_def
    proof (induction rule: lfp_induct_set[consumes 2])
      case (1 y)
      then show ?case
        using LetPast.prems(3) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
    have YD: "\<exists>us k'. (q, us) \<in> lfp ?F \<and> length us = length as \<and> k' \<in> K \<and> us ! k' = Some y" if "y \<in> Y" for y
      using that mono_G unfolding Y_def
    proof (induction rule: lfp_induct_set[consumes 2])
      case (1 y)
      then have "\<exists>us k'. (q, us) \<in> ?F (lfp ?F) \<and> length us = length as \<and> k' \<in> K \<and> us ! k' = Some y"
        using LetPast.prems(3) diff by (fastforce simp add: compose_inputs_def)
      then show ?case
        by (simp add: lfp_fixpoint[OF mono_compose_inputs])
    qed
    have YI: "y \<in> Y \<Longrightarrow> (p, vs) \<in> inputs \<phi> \<Longrightarrow> length vs = Formula.nfv \<phi> \<Longrightarrow> vs ! y = Some y' \<Longrightarrow> y' \<in> Y"
      for y vs y' unfolding Y_def
      by (subst lfp_unfold[OF mono_G]) auto

    show ?thesis
      using \<phi>0
    proof (rule LetPast.IH(1))
      show "\<forall>y\<in>Y. y < Formula.nfv \<phi> \<and> v0 ! y = z"
      proof safe
        fix y assume "y \<in> Y"
        then show "y < Formula.nfv \<phi>" by (rule Y_less)
        show "v0 ! y = z"
          using loop' len0 \<open>y \<in> Y\<close>
        proof (induction arbitrary: y rule: rtranclp_induct)
          case base
          show ?case
            using \<psi>
          proof (rule LetPast.IH(2))
            show "\<forall>x\<in>X. x < Formula.nfv \<psi> \<and> v ! x = z"
              using LetPast.prems(2) by simp
            show "\<forall>k\<in>Y. k < length vn"
              using Y_less len_n by simp
            show "y \<in> Y" by fact
            fix us' y'
            assume "y' \<in> Y"
            then obtain us k' where **: "(q, us) \<in> lfp ?F" "length us = length as"
              "k' \<in> K" "us ! k' = Some y'"
              by (blast dest!: YD)
            moreover note \<open>length us = length as\<close>
            moreover assume "(p, us') \<in> inputs \<psi>" "length us' = length vn"
            ultimately have "(q, map (case_option None ((!) us')) us) \<in> inputs (Formula.LetPast p \<phi> \<psi>)"
              using base by (auto simp add: compose_inputs_def)
            then show "us' ! y' \<in> Some ` X"
              using LetPast.prems(3,4) ** by fastforce
          qed
        next
          case (step vi' vi)
          then have "Safety.matches vi' \<phi> (p, vi)" by simp
          then show ?case
          proof (rule LetPast.IH(1))
            show "\<forall>x\<in>Y. x < Formula.nfv \<phi> \<and> vi' ! x = z"
              using step Y_less by auto
            show "\<forall>k\<in>Y. k < length vi"
              using step Y_less by auto
            show "y \<in> Y" by fact
            fix us' y'
            assume "y' \<in> Y"
            then obtain us k' where **: "(q, us) \<in> lfp ?F" "length us = length as"
              "k' \<in> K" "us ! k' = Some y'"
              by (blast dest!: YD)
            moreover note \<open>length us = length as\<close>
            moreover assume ***: "(p, us') \<in> inputs \<phi>" "length us' = length vi"
            ultimately have "(q, map (case_option None ((!) us')) us) \<in> ?F (lfp ?F)"
              using step by (auto simp add: compose_inputs_def)
            then have "(q, map (case_option None ((!) us')) us) \<in> lfp ?F"
              by (simp add: lfp_fixpoint[OF mono_compose_inputs])
            moreover obtain us'' where "(p, us'') \<in> inputs \<psi>" "length us'' = length vn"
              using \<psi> by (metis matches_imp_input)
            ultimately have "(q, map (case_option None ((!) us'') \<circ> case_option None ((!) us')) us) \<in> inputs (Formula.LetPast p \<phi> \<psi>)"
              using len_n by (auto simp add: compose_inputs_def)
            then have "case_option None ((!) us'') (case_option None ((!) us') (us ! k')) \<in> Some ` X"
              using LetPast.prems(3,4) ** by fastforce
            then obtain y'' where "us' ! y' = Some y''" "us'' ! y'' \<in> Some ` X"
              using ** by (auto split: option.splits)
            then have "y'' \<in> Y"
              using step.prems *** by (auto intro!: YI[OF \<open>y' \<in> Y\<close>])
            then show "us' ! y' \<in> Some ` Y"
              using \<open>us' ! y' = Some y''\<close> by simp
          qed
        qed
      qed
      show "\<forall>k\<in>K. k < length as" by fact
      show "k \<in> K" by fact
      fix us k'
      assume *: "(q, us) \<in> inputs \<phi>" "length us = length as" "k' \<in> K"
      then have "(q, us) \<in> ?F (lfp ?F)"
        using diff by (auto simp add: compose_inputs_def)
      then have "(q, us) \<in> lfp ?F"
        by (simp add: lfp_fixpoint[OF mono_compose_inputs])
      moreover obtain us'' where "(p, us'') \<in> inputs \<psi>" "length us'' = length vn"
        using \<psi> by (metis matches_imp_input)
      ultimately have "(q, map (case_option None ((!) us'')) us) \<in> inputs (Formula.LetPast p \<phi> \<psi>)"
        by (auto simp add: compose_inputs_def len_n)
      then obtain y where "us ! k' = Some y" "us'' ! y \<in> Some ` X"
        using LetPast.prems(3,4) * by (fastforce split: option.splits)
      then show "us ! k' \<in> Some ` Y"
        unfolding Y_def using *
        by (subst lfp_unfold[OF mono_G]) auto
    qed
  qed
next
  case (Eq t1 t2)
  then show ?case by simp
next
  case (Less t1 t2)
  then show ?case by simp
next
  case (LessEq t1 t2)
  then show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi> \<psi>)
  then consider (left) "Safety.matches v \<phi> (q, as)" | (right) "Safety.matches v \<psi> (q, as)"
    by auto
  then show ?case proof cases
    case left
    then show ?thesis
    proof (rule Or.IH(1)[OF _ _ Or.prems(3) _ Or.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<phi>}. x < Formula.nfv \<phi> \<and> v ! x = z"
        using Or.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<phi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<phi>}"
        using Or.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  next
    case right
    then show ?thesis
    proof (rule Or.IH(2)[OF _ _ Or.prems(3) _ Or.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<psi>}. x < Formula.nfv \<psi> \<and> v ! x = z"
        using Or.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<psi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<psi>}"
        using Or.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  qed
next
  case (And \<phi> \<psi>)
  then consider (left) "Safety.matches v \<phi> (q, as)" | (right) "Safety.matches v \<psi> (q, as)"
    by auto
  then show ?case proof cases
    case left
    then show ?thesis
    proof (rule And.IH(1)[OF _ _ And.prems(3) _ And.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<phi>}. x < Formula.nfv \<phi> \<and> v ! x = z"
        using And.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<phi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<phi>}"
        using And.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  next
    case right
    then show ?thesis
    proof (rule And.IH(2)[OF _ _ And.prems(3) _ And.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<psi>}. x < Formula.nfv \<psi> \<and> v ! x = z"
        using And.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<psi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<psi>}"
        using And.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  qed
next
  case (Ands \<phi>s)
  then obtain \<phi> where "\<phi> \<in> set \<phi>s" "Safety.matches v \<phi> (q, as)"
    by auto
  then show ?case
  proof (rule Ands.IH[OF _ _ _ Ands.prems(3) _ Ands.prems(5)])
    show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<phi>}. x < Formula.nfv \<phi> \<and> v ! x = z"
      using Ands.prems(2) by simp
    fix vs k'
    assume "(q, vs) \<in> inputs \<phi>" "length vs = length as" "k' \<in> K"
    then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<phi>}"
      using Ands.prems(3,4) inputs_subset_fv fvi_less_nfv \<open>\<phi> \<in> set \<phi>s\<close>
      by (fastforce simp add: set_conv_nth eq_commute)
  qed
next
  case (Exists t \<phi>)
  then obtain a where "Safety.matches (a # v) \<phi> (q, as)" by auto
  then show ?case
  proof (rule Exists.IH[OF _ _ Exists.prems(3) _ Exists.prems(5)])
    show "\<forall>x\<in>Suc ` X. x < Formula.nfv \<phi> \<and> (a # v) ! x = z"
      using Exists.prems(2) by (auto simp add: Formula.nfv_def Max_gr_iff iff: fvi_Suc)
    fix vs k'
    assume "(q, vs) \<in> inputs \<phi>" and *: "length vs = length as" "k' \<in> K"
    then have "\<exists>x\<in>X. unshift_opt (Suc 0) vs ! k' = Some x"
      using Exists.prems(4) by force
    then show "vs ! k' \<in> Some ` Suc ` X"
      using Exists.prems(3) *
      by (auto simp add: unshift_opt_def split: option.splits if_splits dest!: gr0_implies_Suc)
  qed
next
  case (Agg y \<omega> tys f \<phi>)
  then obtain zs where "Safety.matches (zs @ v) \<phi> (q, as)" "length zs = length tys"
    by auto
  from this(1) show ?case
  proof (rule Agg.IH[OF _ _ Agg.prems(3) _ Agg.prems(5)])
    show "\<forall>x\<in>{y \<in> {length tys..<Formula.nfv \<phi>}. y - length tys \<in> X}. x < Formula.nfv \<phi> \<and> (zs @ v) ! x = z"
      using Agg.prems(2) \<open>length zs = length tys\<close>
      by (auto simp add: Formula.nfv_def Max_gr_iff nth_append)
    fix vs k'
    assume "(q, vs) \<in> inputs \<phi>" and *: "length vs = length as" "k' \<in> K"
    then have "\<exists>x\<in>X. unshift_opt (length tys) vs ! k' = Some x"
      using Agg.prems(4) by force
    then show "vs ! k' \<in> Some ` {y \<in> {length tys..<Formula.nfv \<phi>}. y - length tys \<in> X}"
      using Agg.prems(3) *
      by (clarsimp simp add: unshift_opt_def split: option.splits if_splits)
        (metis (no_types, lifting) \<open>(q, vs) \<in> inputs \<phi>\<close> fvi_less_nfv image_eqI inputs_subset_fv
          linorder_not_less mem_Collect_eq nth_mem)
  qed
next
  case (Prev I \<phi>)
  then show ?case by simp
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  then consider (left) "Safety.matches v \<phi> (q, as)" | (right) "Safety.matches v \<psi> (q, as)"
    by auto
  then show ?case proof cases
    case left
    then show ?thesis
    proof (rule Since.IH(1)[OF _ _ Since.prems(3) _ Since.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<phi>}. x < Formula.nfv \<phi> \<and> v ! x = z"
        using Since.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<phi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<phi>}"
        using Since.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  next
    case right
    then show ?thesis
    proof (rule Since.IH(2)[OF _ _ Since.prems(3) _ Since.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<psi>}. x < Formula.nfv \<psi> \<and> v ! x = z"
        using Since.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<psi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<psi>}"
        using Since.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  qed
next
  case (Until \<phi> I \<psi>)
  then consider (left) "Safety.matches v \<phi> (q, as)" | (right) "Safety.matches v \<psi> (q, as)"
    by auto
  then show ?case proof cases
    case left
    then show ?thesis
    proof (rule Until.IH(1)[OF _ _ Until.prems(3) _ Until.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<phi>}. x < Formula.nfv \<phi> \<and> v ! x = z"
        using Until.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<phi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<phi>}"
        using Until.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  next
    case right
    then show ?thesis
    proof (rule Until.IH(2)[OF _ _ Until.prems(3) _ Until.prems(5)])
      show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<psi>}. x < Formula.nfv \<psi> \<and> v ! x = z"
        using Until.prems(2) by simp
      fix vs k'
      assume "(q, vs) \<in> inputs \<psi>" "length vs = length as" "k' \<in> K"
      then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<psi>}"
        using Until.prems(3,4) inputs_subset_fv fvi_less_nfv
        by (fastforce simp add: set_conv_nth eq_commute)
    qed
  qed
next
  case (Trigger \<phi> I \<psi>)
  show ?case
    sorry
next
  case (Release \<phi> I \<psi>)
  show ?case
    sorry
next
  case (MatchF I r)
  then obtain \<phi> where "\<phi> \<in> Regex.atms r" "Safety.matches v \<phi> (q, as)"
    by auto
  then show ?case
  proof (rule MatchF.IH[OF _ _ _ MatchF.prems(3) _ MatchF.prems(5)])
    show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<phi>}. x < Formula.nfv \<phi> \<and> v ! x = z"
      using MatchF.prems(2) by simp
    fix vs k'
    assume "(q, vs) \<in> inputs \<phi>" "length vs = length as" "k' \<in> K"
    then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<phi>}"
      using MatchF.prems(3,4) inputs_subset_fv fvi_less_nfv \<open>\<phi> \<in> Regex.atms r\<close>
      by (fastforce simp add: set_conv_nth eq_commute)
  qed
next
  case (MatchP I r)
  then obtain \<phi> where "\<phi> \<in> Regex.atms r" "Safety.matches v \<phi> (q, as)"
    by auto
  then show ?case
  proof (rule MatchP.IH[OF _ _ _ MatchP.prems(3) _ MatchP.prems(5)])
    show "\<forall>x\<in>{x \<in> X. x < Formula.nfv \<phi>}. x < Formula.nfv \<phi> \<and> v ! x = z"
      using MatchP.prems(2) by simp
    fix vs k'
    assume "(q, vs) \<in> inputs \<phi>" "length vs = length as" "k' \<in> K"
    then show "vs ! k' \<in> Some ` {x \<in> X. x < Formula.nfv \<phi>}"
      using MatchP.prems(3,4) inputs_subset_fv fvi_less_nfv \<open>\<phi> \<in> Regex.atms r\<close>
      by (fastforce simp add: set_conv_nth eq_commute)
  qed
next
  case (TP t)
  then show ?case by simp
next
  case (TS t)
  then show ?case by simp
qed


fun genvar :: "'a Formula.formula \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> Formula.name \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> bool" where
  "genvar (Formula.Pred r ts) pos x q n c k = (pos = c \<and> q = r \<and> n = length ts \<and> k < length ts \<and> ts ! k = Formula.Var x)"
| "genvar (Formula.Let p \<phi> \<psi>) pos x q n c k = ((\<exists>pos' y. genvar \<phi> pos' y q n c k \<and> genvar \<psi> pos x p (Formula.nfv \<phi>) pos' y) \<or>
    (p \<noteq> q \<or> n \<noteq> Formula.nfv \<phi>) \<and> genvar \<psi> pos x q n c k)"
| "genvar (Formula.LetPast p \<phi> \<psi>) pos x q n c k = ((p \<noteq> q \<or> n \<noteq> Formula.nfv \<phi>) \<and>
    ((\<exists>pos' y. lfp (\<lambda>g pos' y.
        genvar \<phi> pos' y q n c k \<or> (\<exists>pos'' y'. pos'' \<and> g pos'' y' \<and> genvar \<phi> pos' y p (Formula.nfv \<phi>) pos'' y')) pos' y \<and>
      genvar \<psi> pos x p (Formula.nfv \<phi>) pos' y) \<or>
    genvar \<psi> pos x q n c k))"
| "genvar (Formula.Eq t1 t2) pos x q n c k = False"
| "genvar (Formula.Less t1 t2) pos x q n c k = False"
| "genvar (Formula.LessEq t1 t2) pos x q n c k = False"
| "genvar (Formula.Neg \<phi>) pos x q n c k = genvar \<phi> (\<not> pos) x q n c k"
| "genvar (Formula.Or \<phi> \<psi>) pos x q n c k = (if pos then (\<and>) else (\<or>)) (genvar \<phi> pos x q n c k) (genvar \<psi> pos x q n c k)"
| "genvar (Formula.And \<phi> \<psi>) pos x q n c k = (if pos then (\<or>) else (\<and>)) (genvar \<phi> pos x q n c k) (genvar \<psi> pos x q n c k)"
| "genvar (Formula.Ands \<phi>s) pos x q n c k = (if pos then (\<exists>\<phi>\<in>set \<phi>s. genvar \<phi> pos x q n c k) else (\<forall>\<phi>\<in>set \<phi>s. genvar \<phi> pos x q n c k))"
| "genvar (Formula.Exists t \<phi>) pos x q n c k = genvar \<phi> pos (Suc x) q n c k"
(* TODO: The condition that x must be free in Agg should be derivable. *)
| "genvar (Formula.Agg y \<omega> tys f \<phi>) pos x q n c k = (pos \<and> x + length tys \<in> Formula.fv \<phi> \<and>
    genvar \<phi> pos (x + length tys) q n c k)"
| "genvar (Formula.Prev I \<phi>) pos x q n c k = (pos \<and> genvar \<phi> pos x q n c k)"
| "genvar (Formula.Next I \<phi>) pos x q n c k = ((pos \<or> I = all) \<and> genvar \<phi> pos x q n c k)"
(* The following cases could be made more precise. *)
| "genvar (Formula.Since \<phi> I \<psi>) pos x q n c k = ((pos \<or> mem I 0) \<and> genvar \<psi> pos x q n c k)"
| "genvar (Formula.Until \<phi> I \<psi>) pos x q n c k = ((pos \<or> mem I 0) \<and> genvar \<psi> pos x q n c k)"
| "genvar (Formula.Trigger \<phi> I \<psi>) pos x q n c k = ((pos \<or> mem I 0) \<and> genvar \<psi> pos x q n c k)"
| "genvar (Formula.Release \<phi> I \<psi>) pos x q n c k = ((pos \<or> mem I 0) \<and> genvar \<psi> pos x q n c k)"
| "genvar (Formula.MatchP I r) pos x q n c k = False"
| "genvar (Formula.MatchF I r) pos x q n c k = False"
| "genvar (Formula.TP t) pos x q n c k = False"
| "genvar (Formula.TS t) pos x q n c k = False"

lemma memL_all[simp]: "memL all x"
  by transfer simp

lemma memR_all[simp]: "memR all x"
  by transfer simp

lemma genvar_sat:
  assumes "genvar \<phi> (Formula.sat \<sigma> V v i \<phi>) x q n c k" and "length v \<ge> Formula.nfv \<phi>"
  obtains vs as j where
    "(q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as j = c"
    "(q, n) \<notin> dom V \<longrightarrow> (q, as) \<in> \<Gamma> \<sigma> j = c"
    "length as = n" "k < n" "as ! k = v ! x"
  using assms
proof (induction \<phi> arbitrary: V v i x q n c k thesis)
  case (Pred r ts)
  then show ?case
    by (auto simp add: domIff split: option.splits)
next
  case (Let p \<phi> \<psi>)
  define pos where "pos = Formula.sat \<sigma> V v i (Formula.Let p \<phi> \<psi>)"
  consider (left) pos' y where "genvar \<phi> pos' y q n c k" "genvar \<psi> pos x p (Formula.nfv \<phi>) pos' y"
    | (right) "p \<noteq> q \<or> n \<noteq> Formula.nfv \<phi>" "genvar \<psi> pos x q n c k"
    using Let.prems(2) by (auto simp add: pos_def)
  then show ?case proof cases
    case left
    obtain as j where "y < Formula.nfv \<phi>" "length as = Formula.nfv \<phi>" "as ! y = v ! x"
      and pos': "pos' = Formula.sat \<sigma> V as j \<phi>"
      apply (rule Let.IH(2)[rotated, OF left(2)[unfolded pos_def, simplified]])
      using Let.prems by (auto simp add: domIff)
    obtain as' j' where "k < n"
      "(q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as' j' = c"
      "(q, n) \<notin> dom V \<longrightarrow> (q, as') \<in> \<Gamma> \<sigma> j' = c"
      "length as' = n" "as' ! k = as ! y"
      apply (rule Let.IH(1)[rotated, OF left(1)[unfolded pos', simplified]])
      using \<open>length as = Formula.nfv \<phi>\<close> by simp_all
    show ?thesis proof (rule Let.prems(1))
      show "k < n" by fact
      show "(q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as' j' = c" by fact
      show "as' ! k = v ! x"
        using \<open>as' ! k = as ! y\<close> \<open>as ! y = v ! x\<close> by simp
    qed fact+
  next
    case right
    obtain as' j' where "k < n"
      "(q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as' j' = c"
      "(q, n) \<notin> dom V \<longrightarrow> (q, as') \<in> \<Gamma> \<sigma> j' = c"
      "length as' = n" "as' ! k = v ! x"
      apply (rule Let.IH(2)[rotated, OF right(2)[unfolded pos_def, simplified]])
      using Let.prems apply simp
      using Let.prems right(1) by (simp add: domIff split: if_splits)
    with right(1) show ?thesis
      by (intro Let.prems(1)) (auto simp add: compose_inputs_def)
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?F = "\<lambda>A. compose_inputs p (Formula.nfv \<phi>) A (inputs \<phi>)"
  let ?G = "\<lambda>g pos' y. genvar \<phi> pos' y q n c k \<or> (\<exists>pos'' y'. pos'' \<and> g pos'' y' \<and> genvar \<phi> pos' y p (Formula.nfv \<phi>) pos'' y')"
  have mono_G: "mono ?G"
    by (auto intro: monoI)
  have diff: "p \<noteq> q \<or> n \<noteq> Formula.nfv \<phi>"
    using LetPast.prems(2) by simp
  define pos where "pos = Formula.sat \<sigma> V v i (Formula.LetPast p \<phi> \<psi>)"
  consider (left) pos' y where "lfp ?G pos' y" "genvar \<psi> pos x p (Formula.nfv \<phi>) pos' y"
    | (right) "genvar \<psi> pos x q n c k"
    using LetPast.prems(2) by (auto simp add: pos_def)
  then show ?case proof cases
    case left
    obtain as j where "y < Formula.nfv \<phi>" "length as = Formula.nfv \<phi>" "as ! y = v ! x"
      and pos': "pos' = letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) as j"
      apply (rule LetPast.IH(2)[rotated, OF left(2)[unfolded pos_def, simplified sat.simps Let_def]])
      using LetPast.prems by (auto simp add: domIff)
    have "lfp ?G \<le> (\<lambda>pos' y. \<forall>as j. pos' = letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) as j \<longrightarrow>
        length as = Formula.nfv \<phi> \<longrightarrow>
        (\<exists>as' j'.
          ((q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as' j' = c) \<and>
          ((q, n) \<notin> dom V \<longrightarrow> (q, as') \<in> \<Gamma> \<sigma> j' = c) \<and>
          length as' = n \<and> k < n \<and> as' ! k = as ! y))"
      apply (rule lfp_induct[OF mono_G])
      apply clarsimp
      apply (erule disjE)
      subgoal for y as j
        apply (rule LetPast.IH(1)[rotated])
          apply (subst (asm) letpast_sat.simps)
          apply assumption
         apply simp
        using diff apply (simp del: fun_upd_apply cong: conj_cong)
        apply (auto simp add: compose_inputs_def split: if_splits)
        done
      apply clarsimp
      subgoal premises h for y as j pos'' y'
        apply (rule LetPast.IH(1)[rotated, where V="V((p, Formula.nfv \<phi>) \<mapsto>
          \<lambda>w j'. j' < j \<and>
             letpast_sat
              (\<lambda>X u k.
                  Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>)
              w j')" and v=as and i=j])
          apply (insert h(2,5))
          apply (subst (asm) letpast_sat.simps)
          apply (simp del: fun_upd_apply)
        using h(1) apply simp
        using diff apply (simp del: fun_upd_apply cong: conj_cong)
        apply clarsimp
        subgoal for as' j'
          apply (rule h(4)[rule_format, THEN exE])
            apply (rule exI[where x=j'], assumption)
           apply (auto simp add: compose_inputs_def)
          done
        done
      done
    then obtain as' j' where "k < n"
      "(q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as' j' = c"
      "(q, n) \<notin> dom V \<longrightarrow> (q, as') \<in> \<Gamma> \<sigma> j' = c"
      "length as' = n" "as' ! k = as ! y"
      using left(1) pos' \<open>length as = Formula.nfv \<phi>\<close> by blast
    show ?thesis proof (rule LetPast.prems(1))
      show "k < n" by fact
      show "(q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as' j' = c" by fact
      show "as' ! k = v ! x"
        using \<open>as' ! k = as ! y\<close> \<open>as ! y = v ! x\<close> by simp
    qed fact+
  next
    case right
    obtain as' j' where "k < n"
      "(q, n) \<in> dom V \<longrightarrow> the (V (q, n)) as' j' = c"
      "(q, n) \<notin> dom V \<longrightarrow> (q, as') \<in> \<Gamma> \<sigma> j' = c"
      "length as' = n" "as' ! k = v ! x"
      apply (rule LetPast.IH(2)[rotated, OF right[unfolded pos_def, simplified sat.simps Let_def]])
      using LetPast.prems apply simp
      using LetPast.prems right(1) by (simp add: domIff split: if_splits)
    with right diff show ?thesis
      by (intro LetPast.prems(1)) (auto simp add: compose_inputs_def)
  qed
next
  case (Eq t1 t2)
  then show ?case by simp
next
  case (Less t1 t2)
  then show ?case by simp
next
  case (LessEq t1 t2)
  then show ?case by simp
next
  case (Neg \<phi>)
  then show ?case by clarsimp blast
next
  case (Or \<phi> \<psi>)
  show ?case
    using Or.IH[of q n V c k v x thesis i] Or.prems
    by (auto split: if_splits)
next
  case (And \<phi> \<psi>)
  show ?case
    using And.IH[of q n V c k v x thesis i] And.prems
    by (auto split: if_splits)
next
  case (Ands \<phi>s)
  show ?case
    using Ands.IH[of _ q n V c k v x thesis i] Ands.prems
    apply (auto split: if_splits)
    apply (subgoal_tac "\<not> (\<forall>x\<in>set \<phi>s. Formula.sat \<sigma> V v i x)")
    by auto
next
  case (Exists t \<phi>)
  have 1: "Formula.nfv \<phi> \<le> Suc (length v)"
    using Exists.prems(3)
    by (simp add: Formula.nfv_def) (metis fvi_Suc Suc_le_D not_less_eq_eq)
  show ?case proof (cases "\<exists>z. Formula.sat \<sigma> V (z # v) i \<phi>")
    case True
    then obtain z where 2: "Formula.sat \<sigma> V (z # v) i \<phi>" "genvar \<phi> True (Suc x) q n c k"
      using Exists.prems(2) by auto
    show ?thesis
      apply (rule Exists.IH[rotated])
        apply (subst 2)
        apply (rule 2)
       apply (simp add: 1)
      apply (rule Exists.prems(1))
      by simp_all
  next
    case False
    then obtain z where 2: "\<not> Formula.sat \<sigma> V (z # v) i \<phi>" "genvar \<phi> False (Suc x) q n c k"
      using Exists.prems(2) by auto
    show ?thesis
      apply (rule Exists.IH[rotated])
        apply (subst 2)
        apply (rule 2)
       apply (simp add: 1)
      apply (rule Exists.prems(1))
      by simp_all
  qed
next
  case (Agg y \<omega> tys f \<phi>)
  have 1: "Formula.nfv \<phi> \<le> length tys + length v"
    using Agg.prems(3)
    apply (auto simp add: Formula.nfv_def)
    subgoal for x
      apply (cases "x \<le> length tys")
       apply simp
      apply (drule bspec[where x="x - length tys"], rule UnI1)
       apply (metis fvi_iff_fv le_add_diff_inverse2 nat_le_linear)
      by linarith
    done
  obtain zs where 2: "length zs = length tys" "Formula.sat \<sigma> V (zs @ v) i \<phi>"
    "genvar \<phi> True (x + length tys) q n c k"
    using Agg.prems(2)
    apply (auto simp add: subset_iff)
    subgoal for zs
      apply (subgoal_tac "((\<forall>a x. length x = length tys \<longrightarrow>
             Formula.sat \<sigma> V (x @ v) i \<phi> \<longrightarrow>
             Formula.eval_trm (x @ v) f \<noteq> a) \<longrightarrow>
             (\<forall>t. t \<in> fv \<phi> \<longrightarrow> t < length tys))")
      by auto
    done
  show ?case
    apply (rule Agg.IH[rotated])
      apply (subst 2)
      apply (rule 2)
     apply (simp add: 2)
     apply (rule 1)
    apply (rule Agg.prems(1))
    using 2 by (simp_all add: nth_append)
next
  case (Prev I \<phi>)
  show ?case
    apply (cases i)
    using Prev apply simp
    subgoal for i'
      using Prev.IH[of q n V c k v x thesis i'] Prev.prems
      by auto
    done
next
  case (Next I \<phi>)
  show ?case
    using Next.IH[of q n V c k v x thesis "Suc i"] Next.prems
    by auto
next
  case (Since \<phi> I \<psi>)
  show ?case
    using Since.prems(2-)
    apply clarsimp
    apply (erule disjE)
     apply clarsimp
    subgoal for j
      apply (rule Since.IH(2)[rotated, of V v j x q n c k])
        apply simp
       apply simp
      apply (rule Since.prems(1))
      by simp_all
    apply (cases "\<exists>j\<le>i. memL I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> memR I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and>
      Formula.sat \<sigma> V v j \<psi> \<and> (\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<phi>)")
     apply clarsimp
    subgoal for j
      apply (rule Since.IH(2)[rotated, of V v j x q n c k])
        apply simp
       apply simp
      apply (rule Since.prems(1))
      by simp_all
    apply (subgoal_tac "\<not> Formula.sat \<sigma> V v i \<psi>")
     apply clarsimp
     apply (rule Since.IH(2)[rotated, of V v i x q n c k])
       apply simp
      apply simp
     apply (rule Since.prems(1))
    by auto
next
  case (Until \<phi> I \<psi>)
  show ?case
    using Until.prems(2-)
    apply clarsimp
    apply (erule disjE)
     apply clarsimp
    subgoal for j
      apply (rule Until.IH(2)[rotated, of V v j x q n c k])
        apply simp
       apply simp
      apply (rule Until.prems(1))
      by simp_all
    apply (cases "\<exists>j\<ge>i. memL I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> memR I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and>
      Formula.sat \<sigma> V v j \<psi> \<and> (\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>)")
     apply clarsimp
    subgoal for j
      apply (rule Until.IH(2)[rotated, of V v j x q n c k])
        apply simp
       apply simp
      apply (rule Until.prems(1))
      by simp_all
    apply (subgoal_tac "\<not> Formula.sat \<sigma> V v i \<psi>")
     apply clarsimp
     apply (rule Until.IH(2)[rotated, of V v i x q n c k])
       apply simp
      apply simp
     apply (rule Until.prems(1))
    by auto
next
  case (Trigger \<phi> I \<psi>)
  show ?case
    sorry
next
  case (Release \<phi> I \<psi>)
  show ?case
    sorry
next
  case (MatchF I r)
  then show ?case by simp
next
  case (MatchP I r)
  then show ?case by simp
next
  case (TP t)
  then show ?case by simp
next
  case (TS t)
  then show ?case by simp
qed


definition guarded_by_unique_inputs :: "'a Formula.formula \<Rightarrow> bool" where
  "guarded_by_unique_inputs \<phi> \<longleftrightarrow> (\<forall>x\<in>Formula.fv \<phi>. \<exists>q n k. genvar \<phi> True x q n True k \<and>
    (\<forall>vs. (q, vs) \<in> inputs \<phi> \<longrightarrow> length vs = n \<longrightarrow> vs ! k = Some x))"

definition envs_product where
  "envs_product A S \<longleftrightarrow> (\<exists>F. (\<forall>v\<in>S. \<forall>a\<in>A. v ! a \<in> F a) \<and>
    (\<forall>g. (\<forall>a\<in>A. g a \<in> F a) \<longrightarrow> (\<exists>v\<in>S. \<forall>a\<in>A. v ! a = g a)))"

lemma in_listset_nth: "x \<in> listset As \<Longrightarrow> i < length As \<Longrightarrow> x ! i \<in> As ! i"
  by (induction As arbitrary: x i) (auto simp: set_Cons_def nth_Cons split: nat.split)

lemma all_nth_in_listset: "length x = length As \<Longrightarrow> (\<And>i. i < length As \<Longrightarrow> x ! i \<in> As ! i) \<Longrightarrow> x \<in> listset As"
  by (induction x As rule: list_induct2) (fastforce simp: set_Cons_def nth_Cons)+

lemma envs_product_listset: "envs_product {0..<length As} (listset As)"
  by (force simp add: envs_product_def in_listset_nth
      intro!: exI[where x="(!) As"] all_nth_in_listset[where x="map _ [0..<length As]"])

lemma sat_slice_inversion:
  assumes "guarded_by_unique_inputs \<phi>" and "envs_product (Formula.fv \<phi>) S"
    and "length v \<ge> Formula.nfv \<phi>"
    and "Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> S) \<sigma>) Map.empty v i \<phi>"
  shows "\<exists>v'\<in>S. \<forall>x\<in>Formula.fv \<phi>. v' ! x = v ! x"
proof -
  have "\<exists>v'\<in>S. v' ! x = v ! x" if x: "x \<in> Formula.fv \<phi>" for x
  proof -
    obtain q n k where "genvar \<phi> True x q n True k"
      and unique: "\<And>vs. (q, vs) \<in> inputs \<phi> \<Longrightarrow> length vs = n \<Longrightarrow> vs ! k = Some x"
      using assms(1) x by (auto simp add: guarded_by_unique_inputs_def)
    then obtain v' as where
      "v' \<in> S" "Safety.matches v' \<phi> (q, as)" "length as = n" "k < n" "as ! k = v ! x"
      using assms(3,4) genvar_sat[of \<phi> "map_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> S) \<sigma>" Map.empty v i x q n True k]
      apply (auto simp add: set_eq_iff)
      by (metis (opaque_lifting))
    note \<open>as ! k = v ! x\<close>
    also have "as ! k = v' ! x"
      using \<open>Safety.matches v' \<phi> (q, as)\<close>
    proof (rule unique_inputs_matches)
      show "\<forall>xa\<in>{x}. xa < Formula.nfv \<phi> \<and> v' ! xa = v' ! x"
        using x fvi_less_nfv by auto
      show "\<forall>ka\<in>{k}. ka < length as"
        using \<open>k < n\<close> \<open>length as = n\<close> by simp
      show "k \<in> {k}" by simp
      fix us k'
      assume "(q, us) \<in> inputs \<phi>" "length us = length as" "k' \<in> {k}"
      then show "us ! k' \<in> Some ` {x}"
        using unique \<open>length as = n\<close> by auto
    qed
    finally have "v' ! x = v ! x" .
    then show "\<exists>v'\<in>S. v' ! x = v ! x"
      using \<open>v' \<in> S\<close> by blast
  qed
  then show "\<exists>v'\<in>S. \<forall>x\<in>Formula.fv \<phi>. v' ! x = v ! x"
    using assms(2) by (clarsimp simp add: envs_product_def) metis
qed

subsection \<open>Lemma 3\<close>

locale skip_inter = joint_data_slicer +
  assumes guarded: "guarded_by_unique_inputs \<phi>"
  and mergeable: "envs_product (Formula.fv \<phi>) (slice_set k)"
begin

subsection \<open>Definition of J'\<close>

definition "skip_joiner = (\<lambda>s. \<Union>k. s k)"

subsection \<open>Theorem 3\<close>

lemma skip_joiner:
  assumes "\<pi> \<in> prefixes"
  shows "joiner (\<lambda>k. M (splitter \<pi> k)) = skip_joiner (\<lambda>k. M (splitter \<pi> k))"
  (is "?L = ?R")
proof safe
  fix i v
  assume "(i, v) \<in> ?R"
  then obtain k where in_M: "(i, v) \<in> M (splitter \<pi> k)"
    unfolding skip_joiner_def by blast
  obtain \<sigma> where "\<sigma> \<in> traces" "prefix_of \<pi> \<sigma>"
    using assms by (auto simp add: prefixes_def)
  with sound_monitor[OF _ in_M] wf_monitor[OF _ in_M] have
    sat: "Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> (slice_set k)) \<sigma>) Map.empty (map the v) i \<phi>"
    and "ok \<phi> v"
    by (auto simp: splitter_pslice)
  then obtain w where "ok \<phi> w" "k \<in> strategy w" "\<forall>x\<in>Formula.fv \<phi>. v ! x = w ! x"
    using sat_slice_inversion[OF guarded mergeable _ sat] fv_less_nfv
    by (auto simp add: slice_set_def wf_tuple_def)
  then have "k \<in> strategy v"
    using \<open>ok \<phi> v\<close>
    by (metis (mono_tags, lifting) wf_tuple_cong fv_less_nfv nth_map wf_tuple_length)
  with in_M \<open>ok \<phi> v\<close> show "(i, v) \<in> ?L" unfolding joiner_def
    by blast
qed (auto simp: joiner_def skip_joiner_def)

sublocale skip_joint_slicer: slicer "Formula.nfv \<phi>" "Formula.fv \<phi>" traces
  "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" "\<lambda>\<pi>. skip_joiner (\<lambda>k. M (splitter \<pi> k))"
  "\<lambda>_. M" splitter skip_joiner
  apply unfold_locales
        apply (subst skip_joiner[symmetric], blast)+
        apply (fact joint_monitor.mono_monitor)
       apply (subst (asm) skip_joiner[symmetric], blast)
       apply (fact joint_monitor.wf_monitor)
      apply (subst (asm) skip_joiner[symmetric], blast)
      apply (fact joint_monitor.sound_monitor)
     apply (rule ex_cong[THEN iffD1])
      apply (subst skip_joiner[symmetric])
       apply blast
      apply (rule refl)
     apply (fact joint_monitor.complete_monitor)
    apply (fact joint_slicer.mono_splitter)
   apply (rule refl)
  apply (fact joint_slicer.splitter_prefix)
  done

end

(*<*)
end
(*>*)