(*<*)
theory Correct_Until
  imports 
    Correct_Bin_Ops 
    Correct_Agg
begin
(*>*)


subsection \<open> Until \<close>


subsubsection \<open> Well-formed envs \<close>

declare progress_le_gen[simp]

definition "wf_envs S \<sigma> j \<delta> P P' V db =
  (dom V = dom P \<and>
   Mapping.keys db \<supseteq> dom P \<union> (\<Union>k \<in> {j ..< j + \<delta>}. {(p, n). \<exists>x. (p, x) \<in> \<Gamma> \<sigma> k \<and> n = length x}) \<and>
   rel_mapping (\<le>) P P' \<and>
   pred_mapping (\<lambda>i. i \<le> j) P \<and>
   pred_mapping (\<lambda>i. i \<le> j + \<delta>) P' \<and>
   (\<forall>p \<in> Mapping.keys db - dom P. the (Mapping.lookup db p) = map (\<lambda>k. map Some ` {ts. (fst p, ts) \<in> \<Gamma> \<sigma> k \<and> length ts = snd p}) [j ..< j + \<delta>]) \<and>
   (\<forall>p \<in> dom P. list_all2 (\<lambda>i X. X = map Some ` {v. length v = snd p \<and> the (V p) v i}) [the (P p)..<the (P' p)] (the (Mapping.lookup db p))) \<and>
   wty_envs S \<sigma> V)"

lemma wf_envs_mk_db: "wty_trace S \<sigma> \<Longrightarrow> wf_envs S \<sigma> j 1 Map.empty Map.empty Map.empty (mk_db (\<Gamma> \<sigma> j))"
  unfolding wf_envs_def mk_db_def
  by transfer (force split: if_splits simp: image_iff rel_mapping_alt)

lemma wf_envs_empty: "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow>
  wf_envs S \<sigma> (j + \<delta>) 0 P' P' V (Mapping.map_values (\<lambda>_ _. []) db)"
  by (auto 0 4 simp: wf_envs_def rel_mapping_alt set_eq_iff domIff lookup_map_values
      map_option_case keys_dom_lookup subset_iff split: option.splits)

lemma wf_envs_update:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
    and m_eq: "m = Formula.nfv \<phi>"
    and in_fv: "{0 ..< m} \<subseteq> fv \<phi>"
    and xs: "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>) (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    and safe: "safe_formula \<phi>"
    and wty: "S, E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> progress \<sigma> P \<phi> j)) (P'((p, m) \<mapsto> progress \<sigma> P' \<phi> (j + \<delta>)))
    (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>))
    (Mapping.update (p, m) xs db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 3
  from assms show ?case
    by (auto simp: wf_envs_def pred_mapping_alt progress_le progress_mono_gen
        intro!: rel_mapping_map_upd)
next
  case (6 p')
  with assms show ?case by (cases "p' \<in> dom P") (auto simp: wf_envs_def lookup_update')
next
  case (7 p')
  from xs in_fv have "list_all2 (\<lambda>x y. y = map Some ` {v. length v = m \<and> Formula.sat \<sigma> V v x \<phi>})
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    apply (elim list.rel_mono_strong)
    apply(auto 0 3 simp: wf_tuple_def nth_append
        elim!: in_qtableE in_qtableI intro!: image_eqI[where x="map the _"])
    apply (subst list.map_id[symmetric])
    apply (rule map_cong[OF refl])
    apply simp
    by (metis atLeastLessThan_iff in_set_conv_nth le0 option.collapse subsetD)
  moreover have "list_all2 (\<lambda>i X. X = map Some ` {v. length v = snd p' \<and> the (V p') v i}) [the (P p')..<the (P' p')] (the (Mapping.lookup db p'))"
    if "(p, m) \<noteq> p'"
  proof -
    from that 7 have "p' \<in> dom P" by simp
    with wf_envs show ?thesis by (simp add: wf_envs_def)
  qed
  ultimately show ?case
    by (auto simp add: list.rel_map image_iff lookup_update')
next
  case 8
  from wf_envs have "wty_envs S \<sigma> V" by (simp add: wf_envs_def)
  then show ?case unfolding wty_envs_def
    using ty_of_sat_safe[OF safe wty] in_fv 
    by (auto simp: wty_envs_def wty_event_def wty_tuple_def list_all2_conv_all_nth m_eq domIff)
qed (use assms in \<open>auto simp: wf_envs_def subset_iff\<close>)

lemma wf_envs_update_sup:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
    and m_eq: "m = Formula.nfv \<phi>"
    and in_fv: "{0 ..< m} \<subseteq> fv \<phi>"
    and xs': "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>) (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto>  X)) v i \<phi>) (map the v) i))
      [letpast_progress \<sigma> P (p, m) \<phi> j..<letpast_progress \<sigma> P' (p, m) \<phi> (j+\<delta>)] xs'"
    and safe: "safe_formula \<phi>"
    and wty: "S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> (letpast_progress \<sigma> P (p, m) \<phi> j))) (P'((p, m) \<mapsto> (letpast_progress \<sigma> P' (p, m) \<phi> (j+\<delta>))))
    (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>)))
    (Mapping.update (p, m) xs' db)"
  unfolding wf_envs_def
proof (intro conjI ballI, goal_cases)
  case 4
  with assms show ?case
    by(auto simp add: letpast_progress_le wf_envs_def)
next
  case 5
  with assms show ?case
    by(auto simp add: letpast_progress_le wf_envs_def)
next
  case 3
  from assms show ?case
    by (auto simp: wf_envs_def pred_mapping_alt progress_le progress_mono_gen
        intro!: rel_mapping_map_upd letpast_progress_mono)
next
  case (6 p')
  with assms show ?case by (cases "p' \<in> dom P") (auto simp: wf_envs_def lookup_update')
next
  case (7 p')
  from xs' in_fv have "list_all2 (\<lambda>x y. y =
      map Some ` {v. length v = m \<and> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>) v x})
      [letpast_progress \<sigma> P (p, m) \<phi> j..<letpast_progress \<sigma> P' (p, m) \<phi> (j+\<delta>)] xs'"
    apply (elim list.rel_mono_strong)
    apply(auto 0 3 simp: wf_tuple_def nth_append
        elim!: in_qtableE in_qtableI intro!: image_eqI[where x="map the _"])
    apply (subst list.map_id[symmetric])
    apply (rule map_cong[OF refl])
    apply simp
    by (metis atLeastLessThan_iff in_set_conv_nth le0 option.collapse subsetD)
  moreover have "list_all2 (\<lambda>i X. X = map Some ` {v. length v = snd p' \<and> the (V p') v i}) [the (P p')..<the (P' p')] (the (Mapping.lookup db p'))"
    if "(p, m) \<noteq> p'"
  proof -
    from that 7 have "p' \<in> dom P" by simp
    with wf_envs show ?thesis by (simp add: wf_envs_def)
  qed
  ultimately show ?case
    by (auto simp add: list.rel_map lookup_update')
next
  case 8
  have wty_envs: "wty_envs S \<sigma> V" using wf_envs by (auto simp:wf_envs_def)
  show ?case using wty_envs_letpast_update[OF in_fv[unfolded m_eq] safe wty[unfolded m_eq] wty_envs] m_eq by auto
qed (use assms in \<open>auto simp: wf_envs_def subset_iff\<close>)

lemma wf_envs_update2:
  assumes wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
    and m_eq: "m = Formula.nfv \<phi>"
    and in_fv: "{0 ..< m} \<subseteq> fv \<phi>"
    and rel: "rel_mapping (\<le>) P P'"
    and "i\<le>i'"
    and "i\<le>j"
    and "i'\<le>j+\<delta>"
    and xs: "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>) (mem_restr UNIV)
      (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>) (map the v) i))
      [i..<i'] xs"
    and safe: "safe_formula \<phi>"
    and wty: "S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>)), E \<turnstile> \<phi>"
  shows "wf_envs (S((p, m) \<mapsto> tabulate E 0 (Formula.nfv \<phi>))) \<sigma> j \<delta> (P((p, m) \<mapsto> i)) (P'((p, m) \<mapsto> i'))
    (V((p, m) \<mapsto> \<lambda>w j. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>) w j))
    (Mapping.update (p, m) xs db)"
  unfolding wf_envs_def 
proof (intro conjI ballI, goal_cases)
  case 3
  from assms show ?case
    by (auto)
next
  case (6 p')
  with assms show ?case by (cases "p' \<in> dom P") (auto simp: wf_envs_def lookup_update')
next
  case (7 p')
  from xs in_fv have "list_all2 (\<lambda>x y. y = map Some ` {v. length v = m \<and> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(p' \<mapsto> X)) v i \<phi>) v x})
      [i..<i'] xs" if "(p, m) = p'"
    using that
    apply (elim list.rel_mono_strong)
    apply(auto 0 3 simp: wf_tuple_def nth_append
        elim!: in_qtableE in_qtableI intro!: image_eqI[where x="map the _"])
    apply (subst list.map_id[symmetric])
    apply (rule map_cong[OF refl])
    apply simp
    by (metis atLeastLessThan_iff in_set_conv_nth le0 option.collapse subsetD)
  moreover have "list_all2 (\<lambda>i X. X = map Some ` {v. length v = snd p' \<and> the (V p') v i}) [the (P p')..<the (P' p')] (the (Mapping.lookup db p'))"
    if "(p, m) \<noteq> p'"
  proof -
    from that 7 have "p' \<in> dom P" by simp
    with wf_envs show ?thesis by (simp add: wf_envs_def)
  qed
  ultimately show ?case
    by (auto simp add: list.rel_map image_iff lookup_update')
next
  case (8)
  have wty_envs: "wty_envs S \<sigma> V" using wf_envs by (auto simp:wf_envs_def)
  show ?case using wty_envs_letpast_update in_fv wty safe m_eq wty_envs by auto 
qed (use assms in \<open>auto simp: wf_envs_def subset_iff\<close>)

lemma wf_envs_P_simps[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> pred_mapping (\<lambda>i. i \<le> j) P"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> rel_mapping (\<le>) P P'"
  unfolding wf_envs_def by auto

lemma wf_envs_progress_le[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P \<phi> j \<le> j"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) \<le> j + \<delta>"
  unfolding wf_envs_def by auto

lemma wf_envs_progress_regex_le[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P' r (j + \<delta>) \<le> j + \<delta>"
  unfolding wf_envs_def by (auto simp: progress_regex_le)

lemma wf_envs_progress_mono[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> (j+\<delta>)"
  unfolding wf_envs_def
  by (auto simp: progress_mono_gen)


subsubsection \<open> Buffers \<close>

lemma mbuf2t_take_induct[consumes 5, case_names base step]:
  assumes "mbuf2t_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
    and "U i z"
    and "\<And>k x y t z. i \<le> k \<Longrightarrow> Suc k \<le> ja \<Longrightarrow> Suc k \<le> jb \<Longrightarrow>
      P k x \<Longrightarrow> Q k y \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f x y t z)"
  shows "U (min ja jb) z'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbuf2t_take.induct)
    (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated] split: prod.split)

lemma mbuf2t_take_add_induct'[consumes 6, case_names base step]:
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
    and base: "U (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) z"
    and step: "\<And>k X Y z. min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j) \<le> k \<Longrightarrow>
      Suc k \<le> progress \<sigma> P' \<phi> j' \<Longrightarrow> Suc k \<le> progress \<sigma> P' \<psi> j' \<Longrightarrow>
      qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<phi>) X \<Longrightarrow>
      qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<psi>) Y \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f X Y (\<tau> \<sigma> k) z)"
  shows "U (min (progress \<sigma> P' \<phi> j') (progress \<sigma> P' \<psi> j')) z'"
  using pre_buf pre_nts bounded rm unfolding wf_mbuf2'_def
  by (blast intro!: mbuf2t_take_induct[OF eq] wf_mbuf2_add[OF _ xs ys] 
      progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm]
      progress_le_gen base step)

lemma mbuf2t_take_nt:
  assumes "mbuf2t_take f z buf t nts = (z', buf', nt, nts')"
  shows "nt = hd (nts' @ rev nts @ [t])"
  using assms
  by (induction f z buf t nts arbitrary: z' buf' nt nts' rule: mbuf2t_take.induct)
     (auto simp add: hd_app split: list.splits)

lemma mbuf2t_take_eqD:
  assumes "mbuf2t_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbuf2 i ja jb P Q buf"
    and "list_all2 R [i..<j] nts"
    and "ja \<le> j" "jb \<le> j"
  shows "wf_mbuf2 (min ja jb) ja jb P Q buf'"
    and "list_all2 R [min ja jb..<j] nts'"
  using assms unfolding wf_mbuf2_def
  by (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbuf2t_take.induct)
     (auto simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le min_absorb1 min_absorb2
      split: prod.split)


subsubsection \<open> Invariants \<close>

definition wf_ts :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> ts list \<Rightarrow> bool" 
  where "wf_ts \<sigma> P j \<phi> \<psi> ts 
  \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)..<j] ts"

lemma wf_ts_0: "wf_ts \<sigma> P 0 \<phi> \<psi> []"
  unfolding wf_ts_def by simp

definition wf_until_auxlist :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow> bool \<Rightarrow>
    ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula \<Rightarrow> event_data muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne \<longleftrightarrow>
    list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. if pos then (\<forall>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)) r1 \<and>
      qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length auxlist \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and>
          Formula.sat \<sigma> V (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (map the v) k \<phi> else \<not> Formula.sat \<sigma> V (map the v) k \<phi>))) r2)
      auxlist [ne..<ne+length auxlist]"

definition (in muaux) wf_until_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> event_data list set \<Rightarrow> args \<Rightarrow>
  ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> 'muaux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_until_aux \<sigma> V R args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and>
    valid_aggargs (args_n args) (Formula.fv \<psi>) (args_agg args) \<and>
    (\<exists>cur auxlist. valid_muaux args cur aux auxlist \<and>
      cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1)) \<and>
      wf_until_auxlist \<sigma> V (args_n args) R (args_pos args) \<phi> (args_ivl args) \<psi> auxlist ne)"

lemma (in muaux) wf_until_aux_Nil: "Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow>
  valid_aggargs n (Formula.fv \<psi>') agg \<Longrightarrow> 
  wf_until_aux \<sigma> V R (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') b agg) \<phi>' \<psi>' (init_muaux (init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') b agg)) 0"
  unfolding wf_until_aux_def wf_until_auxlist_def by (auto intro: valid_init_muaux) (simp add:init_args_def)

lemma (in muaux) wf_until_aux_UNIV_alt:
  "wf_until_aux \<sigma> V UNIV args \<phi> \<psi> aux ne \<longleftrightarrow> Formula.fv \<phi> \<subseteq> Formula.fv \<psi> \<and>
    valid_aggargs (args_n args) (Formula.fv \<psi>) (args_agg args) \<and>
    (\<exists>cur auxlist. valid_muaux args cur aux auxlist \<and>
      cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1)) \<and>
      list_all2 (\<lambda>x i. case x of (t, r1, r2) \<Rightarrow> t = \<tau> \<sigma> i \<and>
      wf_table (args_n args) (Formula.fv \<phi>) (\<lambda>v. if (args_pos args)
          then (\<forall>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)
          else (\<exists>k\<in>{i..<ne+length auxlist}. Formula.sat \<sigma> V (map the v) k \<phi>)) r1 \<and>
      wf_table (args_n args) (Formula.fv \<psi>) (\<lambda>v. \<exists>j. i \<le> j \<and> j < ne + length auxlist \<and> mem (args_ivl args) (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and>
          Formula.sat \<sigma> V (map the v) j \<psi> \<and>
          (\<forall>k\<in>{i..<j}. if (args_pos args) then Formula.sat \<sigma> V (map the v) k \<phi> else \<not> Formula.sat \<sigma> V (map the v) k \<phi>)) r2)
      auxlist [ne..<ne+length auxlist])"
  unfolding wf_until_aux_def wf_until_auxlist_def qtable_mem_restr_UNIV ..

lemma length_update_until: "length (update_until args rel1 rel2 nt aux) = Suc (length aux)"
  unfolding update_until_def by simp

lemma wf_update_until_auxlist:
  assumes pre: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne"
    and qtable1: "qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length auxlist) \<phi>) rel1"
    and qtable2: "qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length auxlist) \<psi>) rel2"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_pos: "args_pos args = pos"
  shows "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> (update_until args rel1 rel2 (\<tau> \<sigma> (ne + length auxlist)) auxlist) ne"
  unfolding wf_until_auxlist_def length_update_until
  unfolding update_until_def list.rel_map add_Suc_right upt.simps eqTrueI[OF le_add1] if_True
proof (rule list_all2_appendI, unfold list.rel_map, goal_cases old new)
  case old
  show ?case
  proof (rule list.rel_mono_strong[OF assms(1)[unfolded wf_until_auxlist_def]]; safe, goal_cases mono1 mono2)
    case (mono1 i X Y v)
    then show ?case
      by (fastforce simp: args_ivl args_n args_pos sat_the_restrict less_Suc_eq
          elim!: qtable_join[OF _ qtable1] qtable_union[OF _ qtable1])
  next
    case (mono2 i X Y v)
    then show ?case using fvi_subset
      by (auto 0 3 simp: args_ivl args_n args_pos sat_the_restrict less_Suc_eq split: if_splits
          elim!: qtable_union[OF _ qtable_join_fixed[OF qtable2]]
          elim: qtable_cong[OF _ refl] intro: exI[of _ "ne + length auxlist"]) (* slow 8 sec*)
  qed
next
  case new
  then show ?case
    by (auto intro!: qtable_empty qtable1 qtable2[THEN qtable_cong] exI[of _ "ne + length auxlist"]
        simp: args_ivl args_n args_pos less_Suc_eq zero_enat_def[symmetric])
qed

lemma (in muaux) wf_update_until:
  assumes pre: "wf_until_aux \<sigma> V R args \<phi> \<psi> aux ne"
    and qtable1: "qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length_muaux args aux) \<phi>) rel1"
    and qtable2: "qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length_muaux args aux) \<psi>) rel2"
    and fvi_subset: "Formula.fv \<phi> \<subseteq> Formula.fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>"
    and args_R: "args_R args = Formula.fv \<psi>"
    and args_pos: "args_pos args = pos"
  shows "wf_until_aux \<sigma> V R args \<phi> \<psi> (add_new_muaux args rel1 rel2 (\<tau> \<sigma> (ne + length_muaux args aux)) aux) ne \<and>
      length_muaux args (add_new_muaux args rel1 rel2 (\<tau> \<sigma> (ne + length_muaux args aux)) aux) = Suc (length_muaux args aux)"
proof -
  from pre obtain cur auxlist where valid_aux: "valid_muaux args cur aux auxlist" and
    cur: "cur = (if ne + length auxlist = 0 then 0 else \<tau> \<sigma> (ne + length auxlist - 1))" and
    pre_list: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist ne"
    unfolding wf_until_aux_def args_ivl args_n args_pos by auto
  have length_aux: "length_muaux args aux = length auxlist"
    using valid_length_muaux[OF valid_aux] .
  define nt where "nt \<equiv> \<tau> \<sigma> (ne + length_muaux args aux)"
  have nt_mono: "cur \<le> nt"
    unfolding cur nt_def length_aux by simp
  define auxlist' where "auxlist' \<equiv> update_until args rel1 rel2 (\<tau> \<sigma> (ne + length auxlist)) auxlist"
  have length_auxlist': "length auxlist' = Suc (length auxlist)"
    unfolding auxlist'_def by (auto simp add: length_update_until)
  have tab1: "table (args_n args) (args_L args) rel1"
    using qtable1 unfolding args_n[symmetric] args_L[symmetric] by (auto simp add: qtable_def)
  have tab2: "table (args_n args) (args_R args) rel2"
    using qtable2 unfolding args_n[symmetric] args_R[symmetric] by (auto simp add: qtable_def)
  have fv_sub: "fv \<phi> \<subseteq> fv \<psi>"
    using pre unfolding wf_until_aux_def by auto
  moreover have valid_add_new_auxlist: "valid_muaux args nt (add_new_muaux args rel1 rel2 nt aux) auxlist'"
    using valid_add_new_muaux[OF valid_aux tab1 tab2 nt_mono]
    unfolding auxlist'_def nt_def length_aux .
  moreover have "length_muaux args (add_new_muaux args rel1 rel2 nt aux) = Suc (length_muaux args aux)"
    using valid_length_muaux[OF valid_add_new_auxlist] unfolding length_auxlist' length_aux[symmetric] .
  moreover have "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> auxlist' ne"
    using wf_update_until_auxlist[OF pre_list qtable1[unfolded length_aux] qtable2[unfolded length_aux] fv_sub args_ivl args_n args_pos]
    unfolding auxlist'_def .
  moreover have "\<tau> \<sigma> (ne + length auxlist) = (if ne + length auxlist' = 0 then 0 else \<tau> \<sigma> (ne + length auxlist' - 1))"
    unfolding cur length_auxlist' by auto
  ultimately show ?thesis
    using pre
    unfolding wf_until_aux_def nt_def length_aux args_ivl args_n args_pos by fast
qed

lemma wf_until_aux_Cons: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> (a # aux) ne \<Longrightarrow>
  wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> aux (Suc ne)"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc cong: if_cong)

lemma wf_until_aux_Cons1: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)

lemma wf_until_aux_Cons3: "wf_until_auxlist \<sigma> V n R pos \<phi> I \<psi> ((t, a1, a2) # aux) ne \<Longrightarrow>
  qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux) \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> ne)) \<and>
    Formula.sat \<sigma> V (map the v) j \<psi> \<and> (\<forall>k\<in>{ne..<j}. if pos then Formula.sat \<sigma> V (map the v) k \<phi> else \<not> Formula.sat \<sigma> V (map the v) k \<phi>))) a2"
  unfolding wf_until_auxlist_def
  by (simp add: upt_conv_Cons del: upt_Suc)

definition "Untilp pos \<phi> I \<psi> \<equiv> Formula.Until (if pos then \<phi> else Formula.Neg \<phi>) I \<psi>"

lemma (in maux) update_until':
  "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux'' (Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
  Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs =
  Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
  Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs + length_muaux args aux'' =
  min (Progress.progress \<sigma> P' \<phi>''' (j + \<delta>)) (Progress.progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
  list_all2 (\<lambda>i. qtable (agg_n args) (fv (packagg args (Untilp pos \<phi>'' I \<psi>''))) (mem_restr R')
    (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (Untilp pos \<phi>'' I \<psi>''))))
    [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
     Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs] zs \<and>
  nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (Progress.progress \<sigma> P' \<phi>'' (j + \<delta>)) (Progress.progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
  if q1: "list_all2 (\<lambda>i. qtable n (fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>''))
    [Progress.progress \<sigma> P \<phi>'' j..<Progress.progress \<sigma> P' \<phi>'' (j + \<delta>)] xs"
  and q2: "list_all2 (\<lambda>i. qtable n (fv \<psi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>''))
    [Progress.progress \<sigma> P \<psi>'' j..<Progress.progress \<sigma> P' \<psi>'' (j + \<delta>)] ys"
  and eq1: "mbuf2t_take (add_new_muaux args) aux (mbuf2_add xs ys buf) t (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = (aux', buf', nt, nts')"
  and eq2: "eval_muaux args nt aux' = (zs, aux'')"
  and pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
  and wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db"
  and fvi_sub: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
  and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
  and nts: "wf_ts \<sigma> P j \<phi>'' \<psi>'' nts"
  and aux: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
  and args_ivl: "args_ivl args = I"
  and args_n: "args_n args = n"
  and args_L: "args_L args = Formula.fv \<phi>''"
  and args_R: "args_R args = Formula.fv \<psi>''"
  and args_pos: "pos = args_pos args"
  and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))))"
  and nt0: "nt = lookahead_ts nts' nts (map (\<tau> \<sigma>) [j ..< j + \<delta>]) t"
  and length_aux: "progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length_muaux args aux = min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
  and nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
  and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
  and valid_aggargs: "valid_aggargs n (fv \<psi>'') (args_agg args)"
proof -
  note sat.simps[simp del] progress_simps[simp del]
  define ne where "ne \<equiv> progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j"
  have \<phi>''': "progress \<sigma> P \<phi>''' j = progress \<sigma> P \<phi>'' j"  "progress \<sigma> P' \<phi>''' j = progress \<sigma> P' \<phi>'' j" for j
    using pos by (simp_all add: progress.simps split: if_splits)
  have update1: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j) \<and>
      ne + length_muaux args aux' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
    using q1 q2 nts_snoc length_aux aux fvi_sub 
    unfolding \<phi>'''
    by (elim mbuf2t_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF wf_envs] buf])
      (auto simp: args_n args_L args_R ne_def wf_update_until split: option.splits)
  then obtain cur auxlist' where valid_aux': "valid_muaux args cur aux' auxlist'" and
    cur: "cur = (if ne + length auxlist' = 0 then 0 else \<tau> \<sigma> (ne + length auxlist' - 1))" and
    wf_auxlist': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
    unfolding wf_until_aux_def ne_def args_ivl args_n args_pos by auto
  have length_aux': "length_muaux args aux' = length auxlist'"
    using valid_length_muaux[OF valid_aux'] .
  have nts': "wf_ts \<sigma> P' (j + \<delta>) \<phi>'' \<psi>'' nts'"
    using q1 q2 wf_envs nts_snoc
    unfolding wf_ts_def
    by (intro mbuf2t_take_eqD(2)[OF eq1]) (auto intro: wf_mbuf2_add buf[unfolded wf_mbuf2'_def])
  have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
    using nts nts' unfolding mbuf2t_take_nt[OF eq1] t
    apply (auto simp: hd_append hd_rev last_map wf_ts_def)
    using list_all2_hdD(1) list_all2_hdD(2) apply fastforce
    using list_all2_lastD  apply fastforce
      apply (metis (mono_tags) list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
     apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
    apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
    done
  define zs'' where "zs'' = fst (eval_until I nt auxlist')"
  define auxlist'' where "auxlist'' = snd (eval_until I nt auxlist')"
  have current_w_le: "cur \<le> nt"
  proof (cases nts')
    case Nil
    have p_le: "min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<le> j + \<delta>"
      using wf_envs_progress_le[OF wf_envs]
      by (auto simp: min_def le_diff_conv)
    then show ?thesis
      unfolding cur conjunct2[OF update1, unfolded length_aux'] nt
      using Nil by (auto simp: \<phi>''' intro!: \<tau>_mono)
  next
    case (Cons nt x)
    have progress_\<phi>''': "progress \<sigma> P' \<phi>'' (j + \<delta>) = progress \<sigma> P' \<phi>''' (j + \<delta>)"
      using pos by (auto simp add: progress.simps split: if_splits)
    have p_le: "min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<le> j + \<delta>"
      using wf_envs_progress_le[OF wf_envs]
      by (auto simp: min_def le_diff_conv)
    then show ?thesis
      unfolding cur conjunct2[OF update1, unfolded length_aux'] Cons progress_\<phi>''' nt
      by (auto split: if_splits list.splits intro!: \<tau>_mono)
  qed
  have valid_aux'': "valid_muaux args cur aux'' auxlist''"
    using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
    by (auto simp add: args_ivl zs''_def auxlist''_def)
  have length_aux'': "length_muaux args aux'' = length auxlist''"
    using valid_length_muaux[OF valid_aux''] .
  have eq2': "eval_until I nt auxlist' = (zs'', auxlist'')"
    by (auto simp: zs''_def auxlist''_def)
  have length_aux'_aux'': "length_muaux args aux' = length zs'' + length_muaux args aux''"
    using eval_until_length[OF eq2'] unfolding length_aux' length_aux'' .
  have "i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' i \<Longrightarrow>
      i + length auxlist' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist'' (progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
        i + length zs'' = progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
        i + length zs'' + length auxlist'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
        list_all2 (\<lambda>i. qtable n (Formula.fv \<psi>'') (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Untilp pos \<phi>'' I \<psi>'')))
          [i..<i + length zs''] zs''" for i
    using eq2'
  proof (induction auxlist' arbitrary: zs'' auxlist'' i)
    case Nil
    then show ?case
      by (auto dest!: antisym[OF progress_Until_le])
  next
    case (Cons a aux')
    obtain t a1 a2 where "a = (t, a1, a2)" by (cases a)
    from Cons.prems(2) have aux': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux' (Suc i)"
      by (rule wf_until_aux_Cons)
    from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
      unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons1)
    from Cons.prems(2) have 3: "qtable n (Formula.fv \<psi>'') (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Formula.sat \<sigma> V (map the v) j \<psi>'' \<and>
        (\<forall>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (map the v) k \<phi>'' else \<not> Formula.sat \<sigma> V (map the v) k \<phi>''))) a2"
      unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons3)
    from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' =
          min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
      by simp
    have "i \<ge> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
      if "memR I (nt - t)"
      using that nts' unfolding wf_ts_def progress.simps nt
      by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv \<phi>'''
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
    moreover
    have "Suc i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
      if "\<not> memR I (nt - t)"
    proof -
      have \<tau>_min:  "\<tau> \<sigma> (min (j + \<delta> - 1) k) = min (\<tau> \<sigma> (j + \<delta> - 1)) (\<tau> \<sigma> k)" for k
        by (simp add: min_of_mono monoI)
      have le_progress_iff[simp]: "j + \<delta> \<le> progress \<sigma> P' \<phi> (j + \<delta>) \<longleftrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) = (j + \<delta>)" for \<phi> :: "'t Formula.formula"
        using wf_envs_progress_le[OF wf_envs, of \<phi>] by auto
      let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
      let ?min = "min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))"
      have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> (j + \<delta>)"
        by (rule \<tau>_mono) auto
      from that have "?X \<noteq> {}"
        by (auto simp: \<phi>''' intro!: exI[of _ "progress \<sigma> P' \<phi>'' (j + \<delta>)"])
      show ?thesis
        using that nts' Suc_i_aux' unfolding wf_ts_def progress.simps nt
        by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
          (auto 0 3 simp: 1 \<phi>''' list_all2_Cons2 upt_eq_Cons_conv
            simp del: upt_Suc split: list.splits if_splits
            dest!: spec[of _ "?min"]
            intro: diff_le_mono diff_le_mono2 order_trans[OF diff_le_mono diff_le_mono2] \<tau>_mono
            elim!: contrapos_np[of _ "Suc i \<le> _"])
    qed
    moreover have *: "k < progress \<sigma> P' \<psi> (j + \<delta>)" if
      "\<not> memR I (nt - \<tau> \<sigma> i)"
      "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "\<psi> = \<psi>'' \<or> \<psi> = \<phi>''" for k \<psi>
      using that nts' unfolding wf_ts_def nt
      by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
    ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
      unfolding \<open>a = (t, a1, a2)\<close>
      by (auto simp: \<phi>''' 1 sat.simps upt_conv_Cons Untilp_def dest!: Cons.IH[OF _ aux' Suc_i_aux']
          simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])
  qed
  note wf_aux'' = this[OF wf_envs_progress_mono[OF wf_envs]
      wf_auxlist' conjunct2[OF update1, unfolded ne_def length_aux']] 
  have zs_def: "zs = map (eval_args_agg args) zs''"
    using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
    unfolding eval_args_agg_def
    by (auto simp add: args_ivl zs''_def auxlist''_def split: option.splits)
  have len_zs'': "length zs'' = length zs"
    by (auto simp: zs_def)
  have fv: "fv (Untilp pos \<phi>'' I \<psi>'') = fv \<psi>''"
    using fvi_sub
    by (auto simp: Untilp_def)
  have "list_all2 (\<lambda>i. qtable n (fv \<psi>'') (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Untilp pos \<phi>'' I \<psi>'')))
      [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
       Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)] zs''"
    using wf_aux''
    by auto
  then have list_all2_zs: "list_all2 (\<lambda>i. qtable (agg_n args) (fv (packagg args (Untilp pos \<phi>'' I \<psi>''))) (mem_restr R')
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (Untilp pos \<phi>'' I \<psi>''))))
      [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
       Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)] zs"
    unfolding zs_def list_all2_map2
    apply (rule list_all2_mono)
    apply (rule qtable_eval_args_agg[of _ _ R])
      apply (auto simp: mr args_n fv valid_aggargs)

    done
  have "progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length auxlist' =
      progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist''"
    using wf_aux'' valid_aux'' length_aux'_aux''
    by (auto simp add: ne_def length_aux' length_aux'')
  then have "cur =
      (if progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' = 0 then 0
      else \<tau> \<sigma> (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' - 1))"
    unfolding cur ne_def by auto
  then show "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux'' (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs = progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs + length_muaux args aux'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
      list_all2 (\<lambda>i. qtable (agg_n args) (fv (packagg args (Untilp pos \<phi>'' I \<psi>''))) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (Untilp pos \<phi>'' I \<psi>''))))
      [progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs] zs \<and>
      nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
    using aux wf_aux'' valid_aux'' fvi_sub list_all2_zs
    unfolding wf_until_aux_def length_aux'' args_ivl args_n args_pos nt len_zs''
    by (auto simp only: length_aux'')
qed

(*<*)
end
(*>*)