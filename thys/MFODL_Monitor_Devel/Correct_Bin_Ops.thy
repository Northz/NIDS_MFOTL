(*<*)
theory Correct_Bin_Ops
  imports
    Monitor 
    Progress
begin
(*>*)


section \<open> Correctness \<close>


subsection \<open> Monitor's binary buffers \<close>

definition wf_mbuf2 where
  "wf_mbuf2 i ja jb P Q buf \<longleftrightarrow> i \<le> ja \<and> i \<le> jb \<and> (case buf of (xs, ys) \<Rightarrow>
    list_all2 P [i..<ja] xs \<and> list_all2 Q [i..<jb] ys)"

lemma wf_mbuf2_add:
  assumes "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 P [ja..<ja'] xs"
    and "list_all2 Q [jb..<jb'] ys"
    and "ja \<le> ja'" "jb \<le> jb'"
  shows "wf_mbuf2 i ja' jb' P Q (mbuf2_add xs ys buf)"
  using assms unfolding wf_mbuf2_def
  by (auto 0 3 simp: list_all2_append2 upt_append dest: list_all2_lengthD
      intro: exI[where x="[i..<ja]"] exI[where x="[ja..<ja']"]
      exI[where x="[i..<jb]"] exI[where x="[jb..<jb']"] split: prod.splits)

lemma mbuf2_take_eqD:
  assumes "mbuf2_take f buf = (xs, buf')"
    and "wf_mbuf2 i ja jb P Q buf"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 (\<lambda>i z. \<exists>x y. P i x \<and> Q i y \<and> z = f x y) [i..<min ja jb] xs"
  using assms unfolding wf_mbuf2_def
  by (induction f buf arbitrary: i xs buf' rule: mbuf2_take.induct)
    (fastforce simp add: list_all2_Cons2 upt_eq_Cons_conv min_absorb1 min_absorb2 split: prod.splits)+

definition wf_mbuf2' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
  ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> event_data mbuf2 \<Rightarrow> bool" where
  "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf \<longleftrightarrow> wf_mbuf2 (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j))
    (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)
    (\<lambda>i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
    (\<lambda>i (r). qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r) buf"

lemma wf_mbuf2'_0: "pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> wf_mbuf2' \<sigma> P V 0 n R \<phi> \<psi> ([], [])"
  unfolding wf_mbuf2'_def wf_mbuf2_def by simp

lemma mbuf2_take_add':
  assumes eq: "mbuf2_take f (mbuf2_add xs ys buf) = (zs, buf')"
    and pre: "wf_mbuf2' \<sigma> P V j n R \<phi> \<psi> buf"
    and rm: "rel_mapping (\<le>) P P'"
    and xs: "list_all2 (\<lambda>i r. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r)
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> j'] xs"
    and ys: "list_all2 (\<lambda>i r. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) r)
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> j'] ys"
    and "j \<le> j'"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
  shows "wf_mbuf2' \<sigma> P' V j' n R \<phi> \<psi> buf'"
    and "list_all2 (\<lambda>i Z. \<exists>X Y.
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
      qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) Y \<and>
      Z = f X Y)
      [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')] zs"
  using pre rm unfolding wf_mbuf2'_def
  by (force intro!: mbuf2_take_eqD[OF eq] wf_mbuf2_add[OF _ xs ys] progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm])+


subsection \<open> Binary operators' qtable \<close>

lemma qtable_bin_join:
  assumes "qtable n A P Q1 X" "qtable n B P Q2 Y" "\<not> b \<Longrightarrow> B \<subseteq> A" "C = A \<union> B"
    "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> P (restrict A x) \<and> P (restrict B x)"
    "\<And>x. b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> Q2 (restrict B x)"
    "\<And>x. \<not> b \<Longrightarrow> wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow> Q1 (restrict A x) \<and> \<not> Q2 (restrict B x)"
  shows "qtable n C P Q (bin_join n A X b B Y)"
  using qtable_join[OF assms] bin_join_table[of n A X B Y b] assms(1,2)
  by (auto simp add: qtable_def)

lemma qtable_mmulti_join:
  assumes pos: "list_all3 (\<lambda>A Qi X. qtable n A P Qi X \<and> wf_set n A) A_pos Q_pos L_pos"
    and neg: "list_all3 (\<lambda>A Qi X. qtable n A P Qi X \<and> wf_set n A) A_neg Q_neg L_neg"
    and C_eq: "C = \<Union>(set A_pos)" and L_eq: "L = L_pos @ L_neg"
    and "A_pos \<noteq> []" and fv_subset: "\<Union>(set A_neg) \<subseteq> \<Union>(set A_pos)"
    and restrict_pos: "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> list_all (\<lambda>A. P (restrict A x)) A_pos"
    and restrict_neg: "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> list_all (\<lambda>A. P (restrict A x)) A_neg"
    and Qs: "\<And>x. wf_tuple n C x \<Longrightarrow> P x \<Longrightarrow> Q x \<longleftrightarrow>
      list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos Q_pos \<and>
      list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg Q_neg"
  shows "qtable n C P Q (mmulti_join n A_pos A_neg L)"
proof (rule qtableI)
  from pos have 1: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_pos L_pos"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  moreover from neg have "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) A_neg L_neg"
    by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth qtable_def)
  ultimately have L: "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) (L_pos @ L_neg)"
    by (rule list_all2_appendI)
  note in_join_iff = mmulti_join_correct[OF \<open>A_pos \<noteq> []\<close> L]
  from 1 have take_eq: "take (length A_pos) (L_pos @ L_neg) = L_pos"
    by (auto dest!: list_all2_lengthD)
  from 1 have drop_eq: "drop (length A_pos) (L_pos @ L_neg) = L_neg"
    by (auto dest!: list_all2_lengthD)

  note mmulti_join.simps[simp del]
  show "table n C (mmulti_join n A_pos A_neg L)"
    unfolding C_eq L_eq table_def by (simp add: in_join_iff)
  show "Q x" if "x \<in> mmulti_join n A_pos A_neg L" "wf_tuple n C x" "P x" for x
    using that(2,3)
  proof (rule Qs[THEN iffD2, OF _ _ conjI])
    have pos': "list_all2 (\<lambda>A. (\<in>) (restrict A x)) A_pos L_pos"
      and neg': "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) A_neg L_neg"
      using that(1) unfolding L_eq in_join_iff take_eq drop_eq by simp_all
    show "list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos Q_pos"
      using pos pos' restrict_pos that(2,3)
      by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def)
    have fv_subset': "\<And>i. i < length A_neg \<Longrightarrow> A_neg ! i \<subseteq> C"
      using fv_subset unfolding C_eq by (auto simp: Sup_le_iff)
    show "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg Q_neg"
      using neg neg' restrict_neg that(2,3)
      by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def
          wf_tuple_restrict_simple[OF _ fv_subset'])
  qed
  show "x \<in> mmulti_join n A_pos A_neg L" if "wf_tuple n C x" "P x" "Q x" for x
    unfolding L_eq in_join_iff take_eq drop_eq
  proof (intro conjI)
    from that have pos': "list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos Q_pos"
      and neg': "list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg Q_neg"
      using Qs[THEN iffD1] by auto
    show "wf_tuple n (\<Union>A\<in>set A_pos. A) x"
      using \<open>wf_tuple n C x\<close> unfolding C_eq by simp
    show "list_all2 (\<lambda>A. (\<in>) (restrict A x)) A_pos L_pos"
      using pos pos' restrict_pos that(1,2)
      by (simp add: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def
          C_eq wf_tuple_restrict_simple[OF _ Sup_upper])
    show "list_all2 (\<lambda>A. (\<notin>) (restrict A x)) A_neg L_neg"
      using neg neg' restrict_neg that(1,2)
      by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length qtable_def)
  qed
qed

(*<*)
end
(*>*)