(*<*)
theory Correct_Trigger
  imports Correct_Until
begin
(*>*)


subsection \<open> Trigger \<close>

lemma proj_tuple_nth:
  assumes "i < length t" "bs!i" "length bs = length t"
  shows "(proj_tuple bs t)!i = t ! i"
  using assms
proof (induction bs t arbitrary: i rule: proj_tuple.induct)
  case (2 bs a as)
  then show ?case by (cases i) (auto)
next
  case (3 bs a as)
  then show ?case by (cases i) (auto)
qed (auto)


subsubsection \<open> Buffers \<close> (* TODO: replace these with those for until *)

lemma mbuf2T_take_eqD:
  assumes "mbuf2T_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 R [min ja jb..<j] nts'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2T_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      split: prod.split)

lemma mbuf2T_take_add':
  assumes eq: "mbuf2T_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and pre_buf: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "wf_ts \<sigma> P' j' \<phi> \<psi> nts'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def wf_ts_def
  by (auto intro!: mbuf2T_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> _ _ rm]
      progress_le_gen)

lemma mbuf2T_take_induct[consumes 5, case_names base step]:
  assumes "mbuf2T_take f z buf nts = (z', buf', nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
    and "U i z"
    and "\<And>k x y t z. i \<le> k \<Longrightarrow> Suc k \<le> ja \<Longrightarrow> Suc k \<le> jb \<Longrightarrow>
      P k x \<Longrightarrow> Q k y \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f x y t z)"
  shows "U (min ja jb) z'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf nts arbitrary: i z' buf' nts' rule: mbuf2T_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated] split: prod.split)

lemma mbuf2T_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbuf2T_take f z (mbuf2_add xs ys buf) nts = (z', buf', nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and pre_buf: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
    and base: "U (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) z"
    and step: "\<And>k X Y z. min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) \<le> k \<Longrightarrow>
      Suc k \<le> progress \<sigma> P' \<phi> j' \<Longrightarrow> Suc k \<le> progress \<sigma> P' \<psi> j' \<Longrightarrow>
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<phi>) X \<Longrightarrow>
      qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<psi>) Y \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f X Y (\<tau> \<sigma> k) z)"
  shows "U (min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')) z'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def
  by (blast intro!: mbuf2T_take_induct[OF eq] wf_mbuf2_add[OF _ xs ys]
      progress_mono_gen[OF \<open>j \<le> j'\<close> _ _ rm]
      progress_le_gen base step)

definition wf_dfvs where "
  wf_dfvs dfvs \<sigma> I i \<phi> = (if (\<forall>j\<le>i. \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)) then
    dfvs = {}
  else
    dfvs = fv \<phi>
  )"

definition wf_mbuft2' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat 
  \<Rightarrow> event_data list set \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula 
  \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula \<Rightarrow> event_data mbuft2 \<Rightarrow> bool" 
  where "wf_mbuft2' \<sigma> P V j n R \<phi> \<alpha> I \<beta> buf 
  \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j))
    (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)
    (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
    (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) 
      \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r) buf"

lemma wf_mbuf2'_UNIV_alt: "wf_mbuf2' \<sigma> P V j n UNIV \<phi> \<psi> buf \<longleftrightarrow> (case buf of (xs, ys) \<Rightarrow>
  list_all2 (\<lambda>i (r). wf_table n (fv \<phi>) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
    [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) ..< (progress \<sigma> P \<phi> j)] xs \<and>
  list_all2 (\<lambda>i (r). wf_table n (fv \<psi>) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
    [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) ..< (progress \<sigma> P \<psi> j)] ys)"
  unfolding wf_mbuf2'_def wf_mbuf2_def
  by (simp add: mem_restr_UNIV[THEN eqTrueI, abs_def] split: prod.split)

lemma mbuft2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuft2' \<sigma> P V j n R \<phi> \<alpha> I \<beta> buf"
    and rm: "rel_mapping (\<le>) P P'"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and xs: "list_all2 (\<lambda>i r. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
      [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j'] ys"
    and "j \<le> j'"
  shows "wf_mbuft2' \<sigma> P' V j' n R \<phi> \<alpha> I \<beta> buf'"
  and "list_all2 (\<lambda>i Z. \<exists>X V_Y Y.
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
      wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and>
      Z = f X (V_Y, Y))
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j')] zs"
proof -
  have progress:
    "Progress.progress \<sigma> P \<phi> j \<le> Progress.progress \<sigma> P' \<phi> j'"
    "Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j \<le> Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j'"
    using progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm] 
      progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm, of _ "(formula.Trigger \<alpha> I \<beta>)"] .

  have wf_add: "wf_mbuf2 (min (Progress.progress \<sigma> P \<phi> j) (Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)) (Progress.progress \<sigma> P' \<phi> j') (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j')
   (\<lambda>i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
   (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r) (mbuf2_add xs ys buf)"
    using wf_mbuf2_add[OF pre[unfolded wf_mbuft2'_def] xs ys progress]
    by auto

  show
    "wf_mbuft2' \<sigma> P' V j' n R \<phi> \<alpha> I \<beta> buf'"
    "list_all2 (\<lambda>i Z. \<exists>X V_Y Y.
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
      wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and>
      Z = f X (V_Y, Y))
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) j')] zs"
    unfolding wf_mbuft2'_def
    using mbuf2_take_eqD[OF eq wf_add]
    by auto
qed

lemma mbuf2t_take_add':
  assumes eq: "mbuf2t_take f z (mbuf2_add xs ys buf) t nts = (z', buf', nt, nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and pre_buf: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j'] nts"
    and xs: "list_all2 (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "wf_ts \<sigma> P' j' \<phi> \<psi> nts'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def wf_ts_def
  by (auto intro!: mbuf2t_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm]
      progress_le_gen)


subsubsection \<open> Invariants \<close>

definition (in mtaux) wf_trigger_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> event_data list set \<Rightarrow> args \<Rightarrow>
  ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> 'mtaux \<Rightarrow> nat \<Rightarrow> bool" 
  where "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux ne 
  \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> 
    \<and> (\<exists>cur auxlist. 
      valid_mtaux args cur aux (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist) 
      \<and> cur = (if ne = 0 then 0 else \<tau> \<sigma> (ne - 1)) \<and>
    sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist \<and>
    length auxlist = ne \<and>
    (\<forall>(i, (t, l, r)) \<in> set (zip [0..<length auxlist] auxlist). ne \<noteq> 0 \<and> t = \<tau> \<sigma> i \<and> t \<le> \<tau> \<sigma> (ne - 1) \<and>
      qtable (args_n args) (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) l  \<and>
      qtable (args_n args) (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r) \<and>
    (\<forall>i. ne \<noteq> 0 \<and> i \<le> (ne - 1) \<longrightarrow>
      (\<exists>X. (\<tau> \<sigma> i, X) = auxlist!i)))"

lemma (in maux) update_trigger:
  assumes wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
  assumes qtable_X: "qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<gamma>) X"
  assumes qtable_Y: "qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<beta>) Y"
  assumes args_n: "args_n args = n"
  assumes args_L: "args_L args = fv \<gamma>"
  assumes args_R: "args_R args = fv \<beta>"
  shows "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
proof -
  have table:
    "table (args_n args) (args_L args) X"
    "table (args_n args) (args_R args) Y"
    using qtable_X qtable_Y args_n args_L args_R
    unfolding qtable_def
    by auto

  obtain cur auxlist where wf_trigger_before:
    "Formula.fv \<gamma> \<subseteq> Formula.fv \<beta>"
    "valid_mtaux args cur aux (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist)"
    "cur = (if k = 0 then 0 else \<tau> \<sigma> (k - 1))"
    "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist"
    "length auxlist = k"
    "\<forall>(i, (t, l, r)) \<in> set (zip [0..<length auxlist] auxlist).
      k \<noteq> 0 \<and>
      t = \<tau> \<sigma> i \<and>
      t \<le> \<tau> \<sigma> (k - 1) \<and>
      qtable (args_n args) (Formula.fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l  \<and>
      qtable (args_n args) (Formula.fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
     "
    "\<forall>i.
        k \<noteq> 0 \<and>
        i \<le> (k - 1)
        \<longrightarrow>
        (\<exists>X. (\<tau> \<sigma> i, X) = auxlist!i)
    "
    using wf_trigger
    unfolding wf_trigger_aux_def
    by auto

  define cur' where "cur' = \<tau> \<sigma> k"
  define auxlist' where "auxlist' = auxlist @ [(cur', X, Y)]"

  have "\<tau> \<sigma> (k - 1) \<le> \<tau> \<sigma> k"
    by auto
  moreover have "\<forall>x \<in> set auxlist. fst x \<le> \<tau> \<sigma> (k-1)"
    using wf_trigger_before(6) zip_P[of auxlist "\<lambda>x. fst x \<le> \<tau> \<sigma> (k-1)"]
    by auto
  ultimately have auxlist_leq: "\<forall>x \<in> set auxlist. fst x \<le> \<tau> \<sigma> k"
    using le_trans by blast
  then have sorted_auxlist': "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'"
    using wf_trigger_before(4)
    unfolding auxlist'_def cur'_def
    by (simp add: sorted_wrt_append)
  then have sorted:
    "sorted (map fst auxlist)"
    "sorted (map fst auxlist')"
    using wf_trigger_before(4)
    by (auto simp add: sorted_map)

  have auxlist_len: "length auxlist' = Suc k"
    using wf_trigger_before(5)
    unfolding auxlist'_def
    by auto

  have auxlist_props:
    "\<forall>(i, (t, l, r)) \<in> set (zip [0..<length auxlist'] auxlist').
      Suc k \<noteq> 0 \<and>
      t = \<tau> \<sigma> i \<and>
      t \<le> \<tau> \<sigma> k \<and>
      qtable (args_n args) (Formula.fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l  \<and>
      qtable (args_n args) (Formula.fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
     "
  proof -
    {
      fix i t l r
      assume assm: "(i, (t, l, r)) \<in> set (zip [0..<length auxlist'] auxlist')"
      then have i_mem: "i \<in> {0..<length auxlist'}"
        using set_zip_leftD
        by fastforce
      have
        "Suc k \<noteq> 0 \<and>
        t = \<tau> \<sigma> i \<and>
        t \<le> \<tau> \<sigma> k \<and>
        qtable (args_n args) (Formula.fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l  \<and>
        qtable (args_n args) (Formula.fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r"
      proof (cases "i < length auxlist")
        case True
        then have "(i, (t, l, r)) \<in> set (zip [0..<length auxlist] auxlist)"
          using assm zip_idx[of auxlist']
          unfolding auxlist'_def
          by simp
        then have
          "t = \<tau> \<sigma> i \<and>
           t \<le> \<tau> \<sigma> (k - 1) \<and>
           qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
           qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r"
          using wf_trigger_before(6)
          by auto
        then show ?thesis
          using True wf_trigger_before(5)
          by auto
      next
        case False
        then have i_eq: "i = length auxlist"
          using i_mem
          unfolding auxlist'_def
          by auto
        then have "(t, l, r) = (cur', X, Y)"
          using assm zip_idx[of auxlist']
          unfolding auxlist'_def
          by auto
        then show ?thesis
          using qtable_X qtable_Y args_n wf_trigger_before(5) i_eq
          unfolding cur'_def
          by auto
      qed
    }
    then show ?thesis by auto
  qed

  have auxlist_mem:
    "\<forall>i.
        Suc k \<noteq> 0 \<and>
        i \<le> k
        \<longrightarrow>
        (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
    "
  proof -
    {
      fix i
      assume assms: "Suc k \<noteq> 0" "i \<le> k"
      then have "(\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)"
      proof (cases "i < k")
        case True
        then have "\<exists>X. (\<tau> \<sigma> i, X) = auxlist!i"
          using wf_trigger_before(7)
          by auto
        then obtain X' where "(\<tau> \<sigma> i, X') = auxlist!i"
          by auto
        then have "(\<tau> \<sigma> i, X') = auxlist'!i"
          using nth_append[of auxlist "[(cur', X, Y)]" i] wf_trigger_before(5) True
          unfolding auxlist'_def
          by auto
        then show ?thesis
          using exI[of "\<lambda>X'. (\<tau> \<sigma> i, X') = auxlist' ! i"]
          by auto
      next
        case False
        then have "i = length auxlist' - 1" using assms wf_trigger_before(5) unfolding auxlist'_def by auto
        then have "(cur', X, Y) = auxlist' ! i"
          unfolding auxlist'_def
          by auto
        then show ?thesis
          unfolding cur'_def
          using exI[of "\<lambda>X'. (\<tau> \<sigma> i, X') = auxlist' ! i" "(X, Y)"] assms(2) False
          by auto
      qed
    }
    then show ?thesis by auto
  qed

  have "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur' - t))) =
        (\<lambda>(t, _). memR (args_ivl args) (cur - t) \<and> memR (args_ivl args) (cur' - t))"
    by auto
  moreover have "(\<lambda>(t, _). memR (args_ivl args) (cur - t) \<and> memR (args_ivl args) (cur' - t)) = (\<lambda>(t, _). memR (args_ivl args) (cur' - t))"
    using wf_trigger_before(3)
    unfolding cur'_def
    by (metis memR_impl_pred memR_zero zero_diff)
  ultimately have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (cur' - t))) = (\<lambda>(t, _). memR (args_ivl args) (cur' - t))"
    by metis

  have filter_simp:"(filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist) @ [(cur', X, Y)]) =
        (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (auxlist @ [(cur', X, Y)]))"
    unfolding filter_filter
    by (auto simp add: filter_simp)

  have "valid_mtaux args cur' (update_mtaux args cur' X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist) @ [(cur', X, Y)])"
    using wf_trigger_before(3) valid_update_mtaux[of cur cur' args X Y aux "(filter (\<lambda>(t, _). memR (args_ivl args) (cur - t)) auxlist)", OF _ table wf_trigger_before(2)]
    unfolding cur'_def
    by auto
  then have "valid_mtaux args cur' (update_mtaux args cur' X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) (auxlist'))"
    unfolding auxlist'_def
    using filter_simp
    by auto
  then have valid_mtaux:
    "Formula.fv \<gamma> \<subseteq> Formula.fv \<beta>"
    "valid_mtaux args cur' (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (cur' - t)) auxlist')"
    "cur' = (if (Suc k) = 0 then 0 else \<tau> \<sigma> k)"
    using wf_trigger_before(1)
    unfolding auxlist'_def cur'_def Let_def
    by (auto simp add: filter_simp split: if_splits prod.splits)

  then show "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
    using sorted_auxlist' auxlist_props auxlist_mem auxlist_len
    unfolding wf_trigger_aux_def diff_Suc_1
    by blast
qed

lemma (in maux) trigger_sat_equiv:
  assumes restr: "mem_restr R x"
  assumes wf_x: "wf_tuple (args_n args) (args_R args) x"
  assumes pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = formula.Neg \<gamma>"
  assumes args_n: "args_n args = n"
  assumes args_ivl: "args_ivl args = I"
  assumes args_L: "args_L args = fv \<gamma>"
  assumes args_R: "args_R args = fv \<beta>"
  assumes fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>"
  assumes fv_l_n: "\<forall>x\<in>fv \<beta>. x < n"
  assumes valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
  assumes sorted: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'"
  assumes auxlist_len: "length auxlist' = Suc k"
  assumes auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
       Suc k \<noteq> 0 \<and>
       t = \<tau> \<sigma> i \<and>
       t \<le> \<tau> \<sigma> k \<and>
       qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
       qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
    )"
   assumes auxlist_mem: "(\<forall>i.
        Suc k \<noteq> 0 \<and>
        i \<le> k
        \<longrightarrow>
        (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
    )"
   assumes non_empty: "length (filter (\<lambda> (t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') > 0"
   shows "x \<in> snd (trigger_results args (\<tau> \<sigma> k) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')) = Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
proof -
  have sorted: "sorted (map fst auxlist')"
    using sorted sorted_map
    by blast

  define offset where "offset = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
  then have offset_leq: "offset \<le> length auxlist'"
    by auto

  define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
  then have auxlist''_eq: "auxlist'' = drop offset auxlist'"
    using drop_filter_memR[OF sorted, of "args_ivl args" "\<tau> \<sigma> k"]
    unfolding offset_def
    by auto

  have auxlist'_filter_sum: "length (filter (\<lambda>(t, _). memR (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist') + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist') = length auxlist'"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) ((\<tau> \<sigma> k) - t))" auxlist']
    by (simp add: case_prod_beta')

  have idx_shift: "\<And>i. i < length auxlist'' \<Longrightarrow> auxlist''!i = auxlist'!(offset + i) \<and> offset + i < length auxlist'"
    unfolding auxlist''_eq
    using nth_drop[OF offset_leq]
    by auto

  have idx_shift_rev: "\<And>i. i <length auxlist' \<Longrightarrow> memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist'!i))) \<Longrightarrow> auxlist'!i = auxlist''!(i - offset) \<and> (i - offset) \<in> {0..<length auxlist''}"
  proof -
    fix i
    assume assms: "i <length auxlist'" "memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist'!i)))"
    have i_mem: "i \<in> {0..<length auxlist'}"
      using assms(1)
      by auto

    have "i < length auxlist'' + offset"
      using assms auxlist'_filter_sum
      unfolding auxlist''_def offset_def
      by auto
    moreover have "i \<ge> offset"
    proof -
      {
        assume "i < offset"
        then have "auxlist'!i \<in> set (take offset auxlist')"
          using i_mem
          by (metis atLeastLessThan_iff image_eqI nth_image offset_leq)
        moreover have "take offset auxlist' = filter (\<lambda>(t, _). \<not> memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist'"
          using take_filter_not_memR[OF sorted, of "args_ivl args" "\<tau> \<sigma> k"]
          unfolding offset_def
          by auto
        ultimately have "auxlist'!i \<in> set (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
          by auto
        then have "\<not> memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist'!i)))"
          by auto
        then have "False" using assms(2) by auto
      }
      then show ?thesis using not_le_imp_less by blast
    qed
    ultimately have "i \<in> {offset..<length auxlist'' + offset}"
      by auto
    then have
      "(i - offset) \<in> {0..<length auxlist''}"
      "auxlist''!(i - offset) = auxlist'!i"
      using idx_shift
      by auto
    then show "auxlist'!i = auxlist''!(i - offset) \<and> (i - offset) \<in> {0..<length auxlist''}"
      by auto
  qed

  have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
    unfolding auxlist''_def filter_filter
    by (metis (mono_tags, lifting) case_prod_beta')

  define z where "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"



  have z_eq: "z = {
    tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
      (\<forall>i \<in> {0..<(length auxlist'')}.
        let (t, l, r) = auxlist''!i in
        mem (args_ivl args) ((\<tau> \<sigma> k) - t) \<longrightarrow> 
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist'')}.
            join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
          )
        )
      )
    }"
    using non_empty filter_inv
    unfolding z_def
    by auto

  have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> " using fvi_subset by (auto split: if_splits)

  define proj_x where "proj_x = proj_tuple (join_mask (args_n args) (args_L args)) x"
  have len_x: "length x = args_n args"
    using wf_x
    unfolding wf_tuple_def
    by auto
  
  have restr_proj_x: "mem_restr R proj_x"
    using restr
    unfolding proj_x_def proj_tuple_join_mask_restrict[OF len_x]
    by simp

  have len_x_eq: "length (join_mask (args_n args) (args_L args)) = length x"
    using wf_x
    unfolding wf_tuple_def join_mask_def
    by auto

  have join_mask_fv_\<gamma>:
    "i < length (proj_tuple (join_mask (args_n args) (fv \<gamma>)) x) \<and> i < length x \<and> join_mask (args_n args) (fv \<gamma>) ! i"
    if mem: "i \<in> fv \<gamma>" for i
    using wf_x args_n args_R args_L fvi_subset fv_l_n mem
    unfolding wf_tuple_def join_mask_def
    by (auto simp add: proj_tuple_alt split: if_splits)

  have wf_proj_x: "wf_tuple (args_n args) (fv \<gamma>) proj_x"
    using wf_x
    unfolding proj_x_def proj_tuple_join_mask_restrict[OF len_x] args_R args_L
    by (simp add: fv_subset wf_tuple_restrict_simple)

  have proj_sat_equiv: "\<And>j''. Formula.sat \<sigma> V (map the x) j'' \<gamma> = Formula.sat \<sigma> V (map the proj_x) j'' \<gamma>"
    apply (rule sat_fv_cong)
    using nth_map wf_x args_L args_R fv_l_n fvi_subset proj_tuple_nth[OF _ _ len_x_eq]
    unfolding proj_x_def
    by (auto simp add: wf_tuple_def dest!: join_mask_fv_\<gamma>)

  have "x \<in> z = Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
  proof (rule iffI)
    assume assm: "x \<in> z"
    then have auxlist_trigger: "(\<forall>i \<in> {0..<(length auxlist'')}.
        let (t, l, r) = auxlist''!i in
        mem (args_ivl args) ((\<tau> \<sigma> k) - t) \<longrightarrow> 
        (
          x \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist'')}.
            join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) x)
          )
        )
      )"
      using z_eq
      by auto
    {
      fix i
      assume i_props: "i \<le> k" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have "\<exists>X. (\<tau> \<sigma> i, X) = auxlist' ! i"
        using allE[OF auxlist_mem, of i]
        by auto
      then obtain l r where lr_props: "(\<tau> \<sigma> i, l, r) = auxlist' ! i"
        by auto
      then have memR: "memR (args_ivl args) (\<tau> \<sigma> k - (fst (auxlist' ! i)))"
        using i_props[folded args_ivl]
        by (metis fstI)

      have i_mem: "i < length auxlist'"
        using i_props(1) auxlist_len
        by auto

      define j where "j = i - offset"

      have j_props:
        "auxlist' ! i = auxlist'' ! j"
        "j \<in> {0..<length auxlist''}"
        using idx_shift_rev[OF i_mem memR]
        unfolding j_def
        by auto

      then have lr_j_props:
        "auxlist'' ! j = (\<tau> \<sigma> i, l, r)"
        "mem (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using i_props(2) lr_props args_ivl
        by auto

      have "(let (t, l, r) = auxlist'' ! j
            in mem (args_ivl args) (\<tau> \<sigma> k - t) \<longrightarrow>
            x \<in> r \<or> (\<exists>j\<in>{j<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))
        )"
        using ballE[OF auxlist_trigger, of j] j_props(2)
        by blast
      then have "x \<in> r \<or> (\<exists>j\<in>{j<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))"
        using lr_j_props
        by auto
      moreover {
        assume x_mem: "x \<in> r"
        have "(i, \<tau> \<sigma> i, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
          using lr_props i_mem in_set_conv_nth
          by fastforce
        then have "qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r"
          using auxlist_props
          by auto
        then have "Formula.sat \<sigma> V (map the x) i \<beta>"
          using x_mem restr 
          unfolding qtable_def
          by auto
      }
      moreover {
        assume "\<exists>k\<in>{j<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! k)) (proj_tuple (join_mask (args_n args) (args_L args)) x)"
        then obtain j' where j'_props:
          "j'\<in>{j<..<length auxlist''}"
          "join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j')) (proj_tuple (join_mask (args_n args) (args_L args)) x)"
          by blast

        define j'' where "j'' = offset + j'"

        have "length auxlist'' = length auxlist' - offset"
          using auxlist'_filter_sum
          unfolding offset_def auxlist''_def
          by auto
        then have "j'\<in>{i - offset<..<length auxlist' - offset}"
          using j'_props(1)
          unfolding j_def
          by auto
        then have j''_mem: "j'' \<in> {i<..<length auxlist'}"
          unfolding j''_def
          by auto

        obtain t l r where tlr_eq: "(t, l, r) = auxlist'' ! j'"
          by (metis prod.collapse)
        moreover have "((fst \<circ> snd) (auxlist'' ! j')) = l"
          by (metis comp_def fst_conv snd_conv tlr_eq)
        ultimately have join_cond: "join_cond (args_pos args) l (proj_tuple (join_mask (args_n args) (args_L args)) x)"
          using j'_props(2)
          by auto
        
        have j'_l: "j'<length auxlist''"
          using j'_props
          by auto
        have k_shift: "auxlist'' ! j' = auxlist' ! (j'')"
          using idx_shift[OF j'_l]
          unfolding j''_def
          by auto
        then have tlr_eq': "(t, l, r) = auxlist' ! (j'')"
          using tlr_eq
          by auto
        then have "(j'', t, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
          using j'_l j''_mem
          using in_set_zip
          by fastforce
        then have qtable: "qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j'' \<gamma>) l"
          using auxlist_props
          by auto

        have "Formula.sat \<sigma> V (map the x) j'' \<alpha>"
        proof (cases "args_pos args")
          case True
          have mem: "proj_x \<in> l"
            using True join_cond
            unfolding proj_x_def
            by auto
          then have "Formula.sat \<sigma> V (map the proj_x) j'' \<gamma>"
            using qtable restr_proj_x
            unfolding qtable_def
            by auto
          then show ?thesis
            using proj_sat_equiv True pos
            by auto
        next
          case False
          then have not_mem: "proj_x \<notin> l"
            using join_cond
            unfolding proj_x_def
            by auto
          
          have "\<not>Formula.sat \<sigma> V (map the x) j'' \<gamma> "
            using not_mem qtable restr_proj_x proj_sat_equiv wf_proj_x
            unfolding qtable_def
            by blast
          then show ?thesis
            using False pos
            by auto
        qed
        moreover have "j'' \<in> {i <.. k}"
          using j''_mem auxlist_len
          by auto
        ultimately have "\<exists>k \<in> {i <.. k}. Formula.sat \<sigma> V (map the x) k \<alpha>"
          by auto
      }
      ultimately have "Formula.sat \<sigma> V (map the x) i \<beta> \<or> (\<exists>k \<in> {i <.. k}. Formula.sat \<sigma> V (map the x) k \<alpha>)"
        by auto
    }
    then show "Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
      by auto
  next
    assume assm: "Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)"
    then have sat: "\<forall>j\<le>k. (mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)) \<longrightarrow> (Formula.sat \<sigma> V (map the x) j \<beta> \<or> (\<exists>k \<in> {j <.. k}. Formula.sat \<sigma> V (map the x) k \<alpha>))"
      by auto

    have wf: "wf_tuple (args_n args) (args_R args) x"
      using wf_x
      by auto

    have "\<forall>i\<in>{0..<length auxlist''}.
      let (t, l, r) = auxlist'' ! i in
        mem (args_ivl args) (\<tau> \<sigma> k - t) \<longrightarrow>
        x \<in> r \<or>
        (\<exists>j\<in>{i<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))"
    proof -
      {
        fix i
        define t where "t = fst (auxlist'' ! i)"
        define l where "l = (fst o snd) (auxlist'' ! i)"
        define r where "r = (snd o snd) (auxlist'' ! i)"
        define i' where "i' = offset + i"

        assume assm: "i\<in>{0..<length auxlist''}" "mem (args_ivl args) (\<tau> \<sigma> k - t)"
        
        have i'_props:
          "auxlist'' ! i = auxlist' ! i'"
          "i' < length auxlist'"
          using idx_shift[of i] assm(1)
          unfolding i'_def
          by auto
        moreover have "(t,l,r) = auxlist'' ! i"
          unfolding t_def l_def r_def
          by auto
        moreover obtain X' where X'_props: "(\<tau> \<sigma> i', X') = auxlist' ! i'"
          using allE[OF auxlist_mem, of i' "\<exists>X. (\<tau> \<sigma> i', X) = auxlist' ! i'"] auxlist_len i'_props(2)
          by auto
        ultimately have tlr_props:
          "t = \<tau> \<sigma> i'"
          "(t, l, r) = auxlist' ! i'"
          by (metis fst_conv, metis)
        then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i')"
          using assm(2) args_ivl
          by auto
        then have "Formula.sat \<sigma> V (map the x) i' \<beta> \<or> (\<exists>k\<in>{i'<..k}. Formula.sat \<sigma> V (map the x) k \<alpha>)"
          using sat i'_props(2) auxlist_len
          by auto
        moreover {
          assume assm: "Formula.sat \<sigma> V (map the x) i' \<beta>"
          have "(i', t, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
            using i'_props tlr_props(2) in_set_zip
            by fastforce
          then have "qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i' \<beta>) r"
            using auxlist_props
            by auto
          then have "x \<in> r"
            using wf_x[unfolded args_R] restr assm
            unfolding qtable_def
            by auto
        }
        moreover {
          assume "\<exists>k\<in>{i'<..k}. Formula.sat \<sigma> V (map the x) k \<alpha>"
          then obtain j where j_props: "j\<in>{i'<..k}" "Formula.sat \<sigma> V (map the x) j \<alpha>"
            by auto
          obtain t l r where tlr_def: "(t, l, r) = auxlist' ! j"
            by (metis prod_cases3)
          moreover have j_l: "j < length auxlist'"
            using j_props(1) auxlist_len
            by auto
          ultimately have "(j, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist')"
            using in_set_zip by fastforce
          then have qtable: "qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<gamma>) l"
            using auxlist_props
            by auto

          define j' where "j' = j - offset"

          have "length auxlist'' + offset = Suc k"
            using auxlist'_filter_sum auxlist_len
            unfolding offset_def auxlist''_def
            by auto
          then have "j\<in>{offset + i<..<length auxlist'' + offset}"
            using j_props(1)
            unfolding i'_def
            by auto
          then have j'_mem: "j' \<in> {i<..<length auxlist''}"
            unfolding j'_def
            by auto
          then have "auxlist'' ! j' = auxlist' ! j"
            using idx_shift
            unfolding j'_def
            by auto
          then have tlr_eq: "(t, l, r) = auxlist'' ! j'"
            using tlr_def
            by auto

          have "\<exists>j\<in>{i<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x)"
          proof (cases "args_pos args")
            case True
            then have sat: "Formula.sat \<sigma> V (map the proj_x) j \<gamma>"
              using j_props pos proj_sat_equiv
              by auto
            then have "proj_x \<in> l"
              using qtable restr_proj_x wf_proj_x
              unfolding qtable_def
              by auto
            then have "proj_x \<in> ((fst \<circ> snd) (auxlist'' ! j'))"
              using tlr_eq
              by (metis comp_def fst_conv snd_conv)
            then have "\<exists>j\<in>{i<..<length auxlist''}. proj_x \<in> ((fst \<circ> snd) (auxlist'' ! j))"
              using j'_mem
              by auto
            then show ?thesis
              using True
              unfolding proj_x_def
              by auto
          next
            case False
            then have sat: "Formula.sat \<sigma> V (map the proj_x) j (Formula.Neg \<gamma>)"
              using j_props pos proj_sat_equiv
              by auto
            then have "proj_x \<notin> l"
              using qtable restr_proj_x wf_proj_x
              unfolding qtable_def
              by auto
            then have "proj_x \<notin> ((fst \<circ> snd) (auxlist'' ! j'))"
              using tlr_eq
              by (metis comp_def fst_conv snd_conv)
            then have "\<exists>j\<in>{i<..<length auxlist''}. proj_x \<notin> ((fst \<circ> snd) (auxlist'' ! j))"
              using j'_mem
              by auto
            then show ?thesis
              using False
              unfolding proj_x_def
              by auto
          qed
        }
        ultimately have "x \<in> r \<or>
         (\<exists>j\<in>{i<..<length auxlist''}. join_cond (args_pos args) ((fst \<circ> snd) (auxlist'' ! j)) (proj_tuple (join_mask (args_n args) (args_L args)) x))"
          by blast
      }
      then show ?thesis
        unfolding Let_def
        by (auto split: prod.splits) fastforce
    qed
    then show "x \<in> z"
      using wf
      unfolding z_eq
      by auto
  qed
  moreover have "fv \<beta> = fst (trigger_results args (\<tau> \<sigma> k) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist'))"
    using non_empty args_R filter_inv
    unfolding auxlist''_def trigger_results.simps
    by auto
  ultimately show ?thesis
    using non_empty
    unfolding z_def auxlist''_def
    by auto
qed



(*<*)
end
(*>*)