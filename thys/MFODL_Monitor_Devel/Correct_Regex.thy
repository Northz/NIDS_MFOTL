(*<*)
theory Correct_Regex
  imports Correct_Agg
begin
(*>*)

subsubsection \<open>Move \<close>

lemma progress_regex_le: "pred_mapping (\<lambda>x. x \<le> j) P \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
  by (auto intro!: progress_le_gen simp: Min_le_iff progress_regex_def)

lemma hd_app: "hd (xs @ ys) = (case xs of [] \<Rightarrow> hd ys | x # _ \<Rightarrow> x)"
  by (cases xs) auto

lemma upt_append: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma case_Neg_in_iff: "x \<in> (case y of formula.Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<longleftrightarrow> y = formula.Neg x"
  by (cases y) auto

lemma list_all2_hdD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P i (hd xs)" "i < j"
  using assms unfolding list_all2_conv_all_nth
  by (auto simp: hd_conv_nth intro: zero_less_diff[THEN iffD1] dest!: spec[of _ 0])

inductive list_all3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool" 
  for P :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool)" 
  where "list_all3 P [] [] []"
  | "P a1 a2 a3 \<Longrightarrow> list_all3 P q1 q2 q3 \<Longrightarrow> list_all3 P (a1 # q1) (a2 # q2) (a3 # q3)"

lemma list_all3_list_all2D: "list_all3 P xs ys zs \<Longrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  by (induct xs ys zs rule: list_all3.induct) auto

lemma list_all2_list_all3I: "length xs = length ys \<Longrightarrow> list_all2 (case_prod P) (zip xs ys) zs \<Longrightarrow>
  list_all3 P xs ys zs"
  by (induct xs ys arbitrary: zs rule: list_induct2)
    (auto simp: list_all2_Cons1 intro: list_all3.intros)

lemma list_all3_list_all2_eq: "list_all3 P xs ys zs \<longleftrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  using list_all2_list_all3I list_all3_list_all2D by blast

lemma list_all3_mapD: "list_all3 P (map f xs) (map g ys) (map h zs) \<Longrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  by (induct "map f xs" "map g ys" "map h zs" arbitrary: xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_mapI: "list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs \<Longrightarrow>
  list_all3 P (map f xs) (map g ys) (map h zs)"
  by (induct xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_map_iff: "list_all3 P (map f xs) (map g ys) (map h zs) \<longleftrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  using list_all3_mapD list_all3_mapI by blast

lemmas list_all3_map =
  list_all3_map_iff[where g=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and g=id, unfolded list.map_id id_apply]

lemma list_all3_conv_all_nth:
  "list_all3 P xs ys zs =
  (length xs = length ys \<and> length ys = length zs \<and> (\<forall>i < length xs. P (xs!i) (ys!i) (zs!i)))"
  by (auto simp add: list_all3_list_all2_eq list_all2_conv_all_nth)

lemma list_all3_refl [intro?]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x x x) \<Longrightarrow> list_all3 P xs xs xs"
  by (simp add: list_all3_conv_all_nth)

lemma list_all3_list_all2_conv: "list_all3 R xs xs ys = list_all2 (\<lambda>x. R x x) xs ys"
  by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth)

lemma list_all3_Nil[simp]:
  "list_all3 P xs ys [] \<longleftrightarrow> xs = [] \<and> ys = []"
  "list_all3 P xs [] zs \<longleftrightarrow> xs = [] \<and> zs = []"
  "list_all3 P [] ys zs \<longleftrightarrow> ys = [] \<and> zs = []"
  unfolding list_all3_conv_all_nth by auto

lemma list_all3_Cons:
  "list_all3 P xs ys (z # zs) \<longleftrightarrow> (\<exists>x xs' y ys'. xs = x # xs' \<and> ys = y # ys' \<and> P x y z \<and> list_all3 P xs' ys' zs)"
  "list_all3 P xs (y # ys) zs \<longleftrightarrow> (\<exists>x xs' z zs'. xs = x # xs' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs' ys zs')"
  "list_all3 P (x # xs) ys zs \<longleftrightarrow> (\<exists>y ys' z zs'. ys = y # ys' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs ys' zs')"
  unfolding list_all3_conv_all_nth
  by (auto simp: length_Suc_conv Suc_length_conv nth_Cons split: nat.splits)

lemma list_all3_mono_strong: "list_all3 P xs ys zs \<Longrightarrow>
  (\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> P x y z \<Longrightarrow> Q x y z) \<Longrightarrow>
  list_all3 Q xs ys zs"
  by (induct xs ys zs rule: list_all3.induct) (auto intro: list_all3.intros)

lemma list_all3_list_all2I: "list_all3 (\<lambda>x y z. Q x z) xs ys zs \<Longrightarrow> list_all2 Q xs zs"
  by (induct xs ys zs rule: list_all3.induct) auto


subsubsection \<open> Regex \<close>

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

lemma wf_envs_progress_mono[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress \<sigma> P \<phi> j \<le> progress \<sigma> P' \<phi> (j+\<delta>)"
  unfolding wf_envs_def
  by (auto simp: progress_mono_gen)

definition wf_ts_regex :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> ty Formula.formula Regex.regex \<Rightarrow> ts list \<Rightarrow> bool" 
  where "wf_ts_regex \<sigma> P j r ts \<longleftrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j] ts"

definition wf_mbufn :: "nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> event_data table \<Rightarrow> bool) list \<Rightarrow> event_data mbufn \<Rightarrow> bool" where
  "wf_mbufn i js Ps buf \<longleftrightarrow> list_all3 (\<lambda>P j xs. i \<le> j \<and> list_all2 P [i..<j] xs) Ps js buf"

lemma wf_mbufn_add:
  assumes "wf_mbufn i js Ps buf"
    and "list_all3 list_all2 Ps (List.map2 (\<lambda>j j'. [j..<j']) js js') xss"
    and "list_all2 (\<le>) js js'"
  shows "wf_mbufn i js' Ps (mbufn_add xss buf)"
  unfolding wf_mbufn_def list_all3_conv_all_nth
proof safe
  show "length Ps = length js'" "length js' = length (mbufn_add xss buf)"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth by auto
next
  fix k assume k: "k < length Ps"
  then show "i \<le> js' ! k"
    using assms unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto 0 4 dest: spec[of _ i])
  from k have " [i..<js' ! k] =  [i..<js ! k] @ [js ! k ..<js' ! k]" and
    "length [i..<js ! k] = length (buf ! k)"
    using assms(1,3) unfolding wf_mbufn_def list_all3_conv_all_nth list_all2_conv_all_nth
    by (auto simp: upt_append)
  with k show "list_all2 (Ps ! k) [i..<js' ! k] (mbufn_add xss buf ! k)"
    using assms[unfolded wf_mbufn_def list_all3_conv_all_nth]
    by (auto simp add: list_all2_append)
qed

lemma wf_mbufn_notin_set:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<notin> set buf \<Longrightarrow> j \<in> set js \<Longrightarrow> i < j"
  using assms unfolding wf_mbufn_def list_all3_conv_all_nth
  by (cases "i \<in> set js") (auto intro: le_neq_implies_less simp: in_set_conv_nth)

lemma wf_mbufn_map_tl:
  "wf_mbufn i js Ps buf \<Longrightarrow> [] \<notin> set buf \<Longrightarrow> wf_mbufn (Suc i) js Ps (map tl buf)"
  by (auto simp: wf_mbufn_def list_all3_map Suc_le_eq
      dest: rel_funD[OF tl_transfer]  elim!: list_all3_mono_strong le_neq_implies_less)

definition wf_mbufn' :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat 
  \<Rightarrow> event_data list set \<Rightarrow> ty Formula.formula Regex.regex 
  \<Rightarrow> event_data mbufn \<Rightarrow> bool" 
  where "wf_mbufn' \<sigma>  P V j n R r buf 
  \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
    wf_mbufn (progress_regex \<sigma> P r j) (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s)
    (map (\<lambda>\<phi> i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r) \<phi>s)
    buf)"

lemma wf_mbufn'_0: "to_mregex r = (mr, \<phi>s) \<Longrightarrow> pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow> wf_mbufn' \<sigma> P V 0 n R r (replicate (length \<phi>s) [])"
  unfolding wf_mbufn'_def wf_mbufn_def map_replicate_const[symmetric]
  by (auto simp: list_all3_map intro: list_all3_refl simp: Min_eq_iff progress_regex_def)

definition Mini where
  "Mini i js = (if js = [] then i else Min (set js))"

lemma wf_mbufn_in_set_Mini:
  assumes "wf_mbufn i js Ps buf"
  shows "[] \<in> set buf \<Longrightarrow> Mini i js = i"
  unfolding in_set_conv_nth
proof (elim exE conjE)
  fix k
  have "i \<le> j" if "j \<in> set js" for j
    using that assms unfolding wf_mbufn_def list_all3_conv_all_nth in_set_conv_nth by auto
  moreover assume "k < length buf" "buf ! k = []"
  ultimately show ?thesis using assms
    unfolding Mini_def wf_mbufn_def list_all3_conv_all_nth
    by (auto 0 4 dest!: spec[of _ k] intro: Min_eqI simp: in_set_conv_nth)
qed

lemma mbufn_take_induct[consumes 3, case_names base step]:
  assumes "mbufn_take f z buf = (z', buf')"
    and "wf_mbufn i js Ps buf"
    and "U i z"
    and "\<And>k xs z. i \<le> k \<Longrightarrow> Suc k \<le> Mini i js \<Longrightarrow>
      list_all2 (\<lambda>P x. P k x) Ps xs \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs z)"
  shows "U (Mini i js) z'"
  using assms unfolding wf_mbufn_def
proof (induction f z buf arbitrary: i z' buf' rule: mbufn_take.induct)
  case rec: (1 f z buf)
  show ?case proof (cases "buf = []")
    case True
    with rec.prems show ?thesis unfolding Mini_def by simp
  next
    case nonempty: False
    show ?thesis proof (cases "[] \<in> set buf")
      case True
      from rec.prems(2) have "\<forall>j\<in>set js. i \<le> j"
        by (auto simp: in_set_conv_nth list_all3_conv_all_nth)
      moreover from True rec.prems(2) have "i \<in> set js"
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      ultimately have "Mini i js = i"
        unfolding Mini_def
        by (auto intro!: antisym[OF Min.coboundedI Min.boundedI])
      with rec.prems nonempty True show ?thesis by simp
    next
      case False
      with nonempty rec.prems(2) have more: "Suc i \<le> Mini i js"
        using diff_is_0_eq not_le unfolding Mini_def
        by (fastforce simp: in_set_conv_nth list_all3_conv_all_nth list_all2_iff)
      then have "Mini i js = Mini (Suc i) js" unfolding Mini_def by auto
      show ?thesis
        unfolding \<open>Mini i js = Mini (Suc i) js\<close>
      proof (rule rec.IH)
        show "\<not> (buf = [] \<or> [] \<in> set buf)" using nonempty False by simp
        show "mbufn_take f (f (map hd buf) z) (map tl buf) = (z', buf')"
          using nonempty False rec.prems by simp
        show "list_all3 (\<lambda>P j xs. Suc i \<le> j \<and> list_all2 P [Suc i..<j] xs) Ps js (map tl buf)"
          using False rec.prems
          by (auto simp: list_all3_map elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "U (Suc i) (f (map hd buf) z)"
          using more False rec.prems
          by (auto 0 4 simp: list_all3_map intro!: rec.prems(4) list_all3_list_all2I
              elim!: list_all3_mono_strong dest: list.rel_sel[THEN iffD1])
        show "\<And>k xs z. Suc i \<le> k \<Longrightarrow> Suc k \<le> Mini (Suc i) js \<Longrightarrow>
          list_all2 (\<lambda>P. P k) Ps xs \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs z)"
          by (rule rec.prems(4)) (auto simp: Mini_def)
      qed
    qed
  qed
qed

lemma mbufnt_take_induct[consumes 5, case_names base step]:
  assumes "mbufnt_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "U i z"
    and "\<And>k xs t z. i \<le> k \<Longrightarrow> Suc k \<le> Mini j js \<Longrightarrow>
      list_all2 (\<lambda>P x. P k x) Ps xs \<Longrightarrow> R k t \<Longrightarrow> U k z \<Longrightarrow> U (Suc k) (f xs t z)"
  shows "U (Mini (i + length nts) js) z'"
  using assms
proof (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbufnt_take.induct)
  case (1 f z buf t nts)
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  note mbufnt_take.simps[simp del]
  from 1(2-6) have "i = Min (set js)" if "js \<noteq> []" "nts = []"
    using that unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)]
    by (fastforce simp: Mini_def list_all3_Cons neq_Nil_conv)
  with 1(2-7) list_all2_hdD[OF 1(4)] show ?case
    unfolding wf_mbufn_def using wf_mbufn_in_set_Mini[OF 1(3)] wf_mbufn_notin_set[OF 1(3)]
    by (subst (asm) mbufnt_take.simps)
      (auto simp add: Mini_def list.rel_map Suc_le_eq
        elim!: arg_cong2[of _ _ _ _ U, OF _ refl, THEN iffD1, rotated]
        list_all3_mono_strong[THEN list_all3_list_all2I[of _ _ js]] list_all2_hdD
        dest!: 1(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(3)] * _ 1(7)] split: prod.split if_splits)
qed

lemma mbufnt_take_nt:
  assumes "mbufnt_take f z buf t nts = (z', buf', nt, nts')"
  shows "nt = hd (nts' @ rev nts @ [t])"
  using assms
  by (induction f z buf t nts arbitrary: z' buf' nt nts' rule: mbufnt_take.induct)
     (auto simp add: hd_app split: list.splits if_splits)

lemma mbufnt_take_eqD:
  assumes "mbufnt_take f z buf t nts = (z', buf', nt, nts')"
    and "wf_mbufn i js Ps buf"
    and "list_all2 R [i..<j] nts"
    and "\<And>k. k \<in> set js \<Longrightarrow> k \<le> j"
    and "k = Mini (i + length nts) js"
  shows "wf_mbufn k js Ps buf'"
    and "list_all2 R [k..<j] nts'"
  using assms(1-4) unfolding assms(5)
proof (induction f z buf t nts arbitrary: i z' buf' nt nts' rule: mbufnt_take.induct)
  case IH: (1 f z buf t nts)
  note mbufnt_take.simps[simp del]
  case 1
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  from 1 show ?case
    using wf_mbufn_in_set_Mini[OF 1(2)]
    by (subst (asm) mbufnt_take.simps)
      (force simp: Mini_def wf_mbufn_def split: if_splits prod.splits elim!: list_all3_mono_strong
        dest!: IH(1)[rotated, OF _ wf_mbufn_map_tl[OF 1(2)] *])
  case 2
  then have *: "list_all2 R [Suc i..<j] (tl nts)"
    by (auto simp: list.rel_sel[of R "[i..<j]" nts, simplified])
  have [simp]: "Suc (i + (length nts - Suc 0)) = i + length nts" if "nts \<noteq> []"
    using that by (fastforce simp flip: length_greater_0_conv)
  with 2 show ?case
    using wf_mbufn_in_set_Mini[OF 2(2)] wf_mbufn_notin_set[OF 2(2)]
    by (subst (asm) mbufnt_take.simps) (force simp: Mini_def wf_mbufn_def
        dest!: IH(2)[rotated, OF _ wf_mbufn_map_tl[OF 2(2)] *]
        split: if_splits prod.splits)
qed

definition wf_matchP_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    \<I> \<Rightarrow> ty Formula.formula Regex.regex \<Rightarrow> event_data mr\<delta>aux \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchP_aux \<sigma> V n R I r aux ne \<longleftrightarrow> sorted_wrt (\<lambda>x y. fst x > fst y) aux \<and>
    (\<forall>t X. (t, X) \<in> set aux \<longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> (ne-1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
      (\<forall>ms \<in> RPDs mr. qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne-1)
         (Formula.MatchP (point (\<tau> \<sigma> (ne-1) - t)) (from_mregex ms \<phi>s)))
         (lookup X ms)))) \<and>
    (\<forall>t. ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> (ne-1) - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<longrightarrow>
      (\<exists>X. (t, X) \<in> set aux))"

lemma wf_matchP_aux_Nil: "wf_matchP_aux \<sigma> V n R I r [] 0"
  unfolding wf_matchP_aux_def by simp

definition wf_matchF_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
    \<I> \<Rightarrow> ty Formula.formula Regex.regex \<Rightarrow> event_data ml\<delta>aux \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_matchF_aux \<sigma> V n R I r aux ne k \<longleftrightarrow> (case to_mregex r of (mr, \<phi>s) \<Rightarrow>
      list_all2 (\<lambda>x i. case x of (t, rels, rel) \<Rightarrow> t = \<tau> \<sigma> i \<and>
        list_all2 (\<lambda>\<phi>. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v.
          Formula.sat \<sigma> V (map the v) i \<phi>)) \<phi>s rels \<and>
        qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < ne + length aux + k \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and>
          Regex.match (Formula.sat \<sigma> V (map the v)) r i j)) rel)
    aux [ne..<ne+length aux])"

lemma wf_matchF_aux_Nil: "wf_matchF_aux \<sigma> V n R I r [] 0 k"
  unfolding wf_matchF_aux_def by simp

definition wf_matchF_invar where
  "wf_matchF_invar \<sigma> V n R I r st i =
     (case st of (aux, Y) \<Rightarrow> aux \<noteq> [] \<and> wf_matchF_aux \<sigma> V n R I r aux i 0 \<and>
     (case to_mregex r of (mr, \<phi>s) \<Rightarrow> \<forall>ms \<in> LPDs mr.
       qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v.
         Regex.match (Formula.sat \<sigma> V (map the v)) (from_mregex ms \<phi>s) i (i + length aux - 1)) (lookup Y ms)))"

lemma fv_regex_from_mregex:
  "ok (length \<phi>s) mr \<Longrightarrow> fv_regex (from_mregex mr \<phi>s) \<subseteq> (\<Union>\<phi> \<in> set \<phi>s. fv \<phi>)"
  by (induct mr) (auto simp: Bex_def in_set_conv_nth)+

lemma eps_the_restrict: "fv_regex r \<subseteq> A \<Longrightarrow> Regex.eps (Formula.sat \<sigma> V (map the (restrict A v))) i r = Regex.eps (Formula.sat \<sigma> V (map the v)) i r"
  by (rule eps_fv_cong) (auto intro!: map_the_restrict)

lemma qtable_\<epsilon>_lax:
  assumes "ok (length \<phi>s) mr"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
    and "fv_regex (from_mregex mr \<phi>s) \<subseteq> A" and "qtable n A (mem_restr R) Q guard"
  shows "qtable n A (mem_restr R)
   (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<phi>s) \<and> Q v) (\<epsilon>_lax guard rels mr)"
  using assms
proof (induct mr)
  case (MPlus mr1 mr2)
  from MPlus(3-6) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  then have "fv_regex (from_mregex mr1 \<phi>s) \<subseteq> A" "fv_regex (from_mregex mr2 \<phi>s) \<subseteq> A"
    using fv_regex_from_mregex[of \<phi>s mr1] fv_regex_from_mregex[of \<phi>s mr2] by (auto simp: subset_eq)
  with MTimes(3-6) show ?case
    by (auto simp: eps_the_restrict restrict_idle intro!: qtable_join[OF MTimes(1,2)])
qed (auto split: prod.splits if_splits simp: qtable_empty_iff list_all2_conv_all_nth
    in_set_conv_nth restrict_idle sat_the_restrict
    intro: in_qtableI qtableI elim!: qtable_join[where A=A and C=A])

lemma qtable_r\<epsilon>_strict:
  assumes "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr" "A = fv_regex (from_mregex mr \<phi>s)"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
  shows "qtable n A (mem_restr R) (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<phi>s)) (r\<epsilon>_strict n rels mr)"
  using assms
proof (hypsubst, induct Past Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case (Skip n)
  then show ?case
    by (cases mr) (auto simp: qtable_empty_iff qtable_unit_table split: if_splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) (auto simp: list_all2_conv_all_nth qtable_empty_unit_table
        dest!: qtable_nonempty_empty_table split: if_splits)
next
  case (Plus r s)
  then show ?case
    by (cases mr) (fastforce intro: qtable_union split: if_splits)+
next
  case (TimesP r s)
  then show ?case
    by (cases mr) (auto intro: qtable_cong[OF qtable_\<epsilon>_lax] split: if_splits)+
next
  case (Star r)
  then show ?case
    by (cases mr) (auto simp: qtable_unit_table split: if_splits)
qed

lemma qtable_l\<epsilon>_strict:
  assumes "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s)" "ok (length \<phi>s) mr" "A = fv_regex (from_mregex mr \<phi>s)"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
  shows "qtable n A (mem_restr R) (\<lambda>v. Regex.eps (Formula.sat \<sigma> V (map the v)) i (from_mregex mr \<phi>s)) (l\<epsilon>_strict n rels mr)"
  using assms
proof (hypsubst, induct Futu Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case (Skip n)
  then show ?case
    by (cases mr) (auto simp: qtable_empty_iff qtable_unit_table split: if_splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) (auto simp: list_all2_conv_all_nth qtable_empty_unit_table
        dest!: qtable_nonempty_empty_table split: if_splits)
next
  case (Plus r s)
  then show ?case
    by (cases mr) (fastforce intro: qtable_union split: if_splits)+
next
  case (TimesF r s)
  then show ?case
    by (cases mr) (auto intro: qtable_cong[OF qtable_\<epsilon>_lax] split: if_splits)+
next
  case (Star r)
  then show ?case
    by (cases mr) (auto simp: qtable_unit_table split: if_splits)
qed

lemma rtranclp_False: "(\<lambda>i j. False)\<^sup>*\<^sup>* = (=)"
proof -
  have "(\<lambda>i j. False)\<^sup>*\<^sup>* i j \<Longrightarrow> i = j" for i j :: 'a
    by (induct i j rule: rtranclp.induct) auto
  then show ?thesis
    by (auto intro: exI[of _ 0])
qed

inductive ok_rctxt for \<phi>s where
  "ok_rctxt \<phi>s id id"
| "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_rctxt \<phi>s (\<lambda>t. \<kappa> (MTimes mr t)) (\<lambda>t. \<kappa>' (Regex.Times (from_mregex mr \<phi>s) t))"

lemma ok_rctxt_swap: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_rctxt.induct) auto

lemma ok_rctxt_cong: "ok_rctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat \<sigma> V v) s \<Longrightarrow>
  Regex.match (Formula.sat \<sigma> V v) (\<kappa>' r) i j = Regex.match (Formula.sat \<sigma> V v) (\<kappa>' s) i j"
  by (induct \<kappa> \<kappa>' arbitrary: r s rule: ok_rctxt.induct) simp_all

lemma qtable_r\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> A"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<phi>) rel) \<phi>s rels"
    and "ok_rctxt \<phi>s \<kappa> \<kappa>'"
    and "\<forall>ms \<in> \<kappa> ` RPD mr. qtable n A (mem_restr R) (\<lambda>v. Q (map the v) (from_mregex ms \<phi>s)) (lookup rel ms)"
  shows "qtable n A (mem_restr R)
  (\<lambda>v. \<exists>s \<in> Regex.rpd\<kappa> \<kappa>' (Formula.sat \<sigma> V (map the v)) j (from_mregex mr \<phi>s). Q (map the v) s)
  (r\<delta> \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MSkip
  then show ?case
    by (auto simp: rtranclp_False ok_rctxt_swap qtable_empty_iff
        elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']] split: nat.splits)
next
  case (MPlus mr1 mr2)
  from MPlus(3-7) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-7) show ?case
    by (auto intro!: qtable_union[OF MTimes(2) qtable_\<epsilon>_lax[OF _ _ _ MTimes(1)]]
        elim!: ok_rctxt.intros(2) simp: MTimesL_def Ball_def)
next
  case (MStar mr)
  from MStar(2-6) show ?case
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_rctxt.intros simp: MTimesL_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_r\<delta> = qtable_r\<delta>\<kappa>[OF _ _ _ ok_rctxt.intros(1), unfolded rpd\<kappa>_rpd image_id id_apply]

inductive ok_lctxt for \<phi>s where
  "ok_lctxt \<phi>s id id"
| "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> ok_lctxt \<phi>s (\<lambda>t. \<kappa> (MTimes t mr)) (\<lambda>t. \<kappa>' (Regex.Times t (from_mregex mr \<phi>s)))"

lemma ok_lctxt_swap: "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> from_mregex (\<kappa> mr) \<phi>s = \<kappa>' (from_mregex mr \<phi>s)"
  by (induct \<kappa> \<kappa>' arbitrary: mr rule: ok_lctxt.induct) auto

lemma ok_lctxt_cong: "ok_lctxt \<phi>s \<kappa> \<kappa>' \<Longrightarrow> Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat \<sigma> V v) s \<Longrightarrow>
  Regex.match (Formula.sat \<sigma> V v) (\<kappa>' r) i j = Regex.match (Formula.sat \<sigma> V v) (\<kappa>' s) i j"
  by (induct \<kappa> \<kappa>' arbitrary: r s rule: ok_lctxt.induct) simp_all

lemma qtable_l\<delta>\<kappa>:
  assumes "ok (length \<phi>s) mr" "fv_regex (from_mregex mr \<phi>s) \<subseteq> A"
    and "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<phi>) rel) \<phi>s rels"
    and "ok_lctxt \<phi>s \<kappa> \<kappa>'"
    and "\<forall>ms \<in> \<kappa> ` LPD mr. qtable n A (mem_restr R) (\<lambda>v. Q (map the v) (from_mregex ms \<phi>s)) (lookup rel ms)"
  shows "qtable n A (mem_restr R)
  (\<lambda>v. \<exists>s \<in> Regex.lpd\<kappa> \<kappa>' (Formula.sat \<sigma> V (map the v)) j (from_mregex mr \<phi>s). Q (map the v) s)
  (l\<delta> \<kappa> rel rels mr)"
  using assms
proof (induct mr arbitrary: \<kappa> \<kappa>')
  case MSkip
  then show ?case
    by (auto simp: rtranclp_False ok_lctxt_swap qtable_empty_iff
        elim!: qtable_cong[OF _ _ ok_rctxt_cong[of _ \<kappa> \<kappa>']] split: nat.splits)
next
  case (MPlus mr1 mr2)
  from MPlus(3-7) show ?case
    by (auto intro!: qtable_union[OF MPlus(1,2)])
next
  case (MTimes mr1 mr2)
  from MTimes(3-7) show ?case
    by (auto intro!: qtable_union[OF MTimes(1) qtable_\<epsilon>_lax[OF _ _ _ MTimes(2)]]
        elim!: ok_lctxt.intros(2) simp: MTimesR_def Ball_def)
next
  case (MStar mr)
  from MStar(2-6) show ?case
    by (auto intro!: qtable_cong[OF MStar(1)] intro: ok_lctxt.intros simp: MTimesR_def Ball_def)
qed (auto simp: qtable_empty_iff)

lemmas qtable_l\<delta> = qtable_l\<delta>\<kappa>[OF _ _ _ ok_lctxt.intros(1), unfolded lpd\<kappa>_lpd image_id id_apply]

lemma RPD_fv_regex_le:
  "ms \<in> RPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (auto simp: MTimesL_def split: nat.splits)+

lemma RPD_safe: "Regex.safe_regex fv rgx_safe_pred Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPD mr \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Past g (from_mregex ms \<phi>s)"
proof (induct Past g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test g \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MPlus mr ms)
    with Plus(3-5) show ?thesis
      by (auto dest!: Plus(1,2))
  qed auto
next
  case (TimesP g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MTimes mr ms)
    with TimesP(3-5) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesL_def dest: RPD_fv_regex_le TimesP(1,2))
  qed auto
next
  case (Star g r)
  then show ?case
  proof (cases mr)
    case (MStar x6)
    with Star(2-4) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesL_def dest: RPD_fv_regex_le
          elim!: safe_cosafe[rotated] dest!: Star(1))
  qed auto
qed

lemma RPDi_safe: "Regex.safe_regex fv rgx_safe_pred Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDi n mr ==> Regex.safe_regex fv rgx_safe_pred Past g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: RPD_safe)

lemma RPDs_safe: "Regex.safe_regex fv rgx_safe_pred Past g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDs mr ==> Regex.safe_regex fv rgx_safe_pred Past g (from_mregex ms \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe)

lemma RPD_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Past Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case (Skip n)
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (TimesP r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesL_def dest: RPD_fv_regex_le split: modality.splits)
next
  case (Star r)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesL_def dest: RPD_fv_regex_le)
qed

lemma RPDi_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: RPD_safe_fv_regex RPD_safe)

lemma RPDs_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> RPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding RPDs_def by (auto dest: RPDi_safe_fv_regex)

lemma RPD_ok: "ok m mr \<Longrightarrow> ms \<in> RPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesL_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesL_def)
qed (auto split: nat.splits)

lemma RPDi_ok: "ok m mr \<Longrightarrow> ms \<in> RPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: RPD_ok)

lemma RPDs_ok: "ok m mr \<Longrightarrow> ms \<in> RPDs mr \<Longrightarrow> ok m ms"
  unfolding RPDs_def by (auto intro: RPDi_ok)

lemma LPD_fv_regex_le:
  "ms \<in> LPD mr \<Longrightarrow> fv_regex (from_mregex ms \<phi>s) \<subseteq> fv_regex (from_mregex mr \<phi>s)"
  by (induct mr arbitrary: ms) (auto simp: MTimesR_def split: nat.splits)+

lemma LPD_safe: "Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPD mr \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex ms \<phi>s)"
proof (induct Futu g "from_mregex mr \<phi>s" arbitrary: mr ms rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test g \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MPlus mr ms)
    with Plus(3-5) show ?thesis
      by (auto dest!: Plus(1,2))
  qed auto
next
  case (TimesF g r s mrs)
  then show ?case
  proof (cases mrs)
    case (MTimes mr ms)
    with TimesF(3-5) show ?thesis
      by (cases g) 
        (auto 0 4 simp: MTimesR_def dest: LPD_fv_regex_le 
          split: modality.splits dest: TimesF(1,2))
  qed auto
next
  case (Star g r)
  then show ?case
  proof (cases mr)
    case (MStar x6)
    with Star(2-4) show ?thesis
      by (cases g) (auto 0 4 simp: MTimesR_def dest: LPD_fv_regex_le
          elim!: safe_cosafe[rotated] dest!: Star(1))
  qed auto
qed

lemma LPDi_safe: "Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDi n mr ==> Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex ms \<phi>s)"
  by (induct n arbitrary: ms mr) (auto dest: LPD_safe)

lemma LPDs_safe: "Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDs mr ==> Regex.safe_regex fv rgx_safe_pred Futu g (from_mregex ms \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe)

lemma LPD_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPD mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
proof (induct Futu Strict "from_mregex mr \<phi>s" arbitrary: mr rule: safe_regex_induct)
  case Skip
  then show ?case
    by (cases mr) (auto split: nat.splits)
next
  case (Test \<phi>)
  then show ?case
    by (cases mr) auto
next
  case (Plus r s)
  then show ?case
    by (cases mr) auto
next
  case (TimesF r s)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesR_def dest: LPD_fv_regex_le split: modality.splits)
next
  case (Star r)
  then show ?case
    by (cases mr) (auto 0 3 simp: MTimesR_def dest: LPD_fv_regex_le)
qed

lemma LPDi_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDi n mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  by (induct n arbitrary: ms mr) (auto 5 0 dest: LPD_safe_fv_regex LPD_safe)

lemma LPDs_safe_fv_regex: "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex mr \<phi>s) \<Longrightarrow>
  ms \<in> LPDs mr ==> fv_regex (from_mregex ms \<phi>s) = fv_regex (from_mregex mr \<phi>s)"
  unfolding LPDs_def by (auto dest: LPDi_safe_fv_regex)

lemma LPD_ok: "ok m mr \<Longrightarrow> ms \<in> LPD mr \<Longrightarrow> ok m ms"
proof (induct mr arbitrary: ms)
  case (MPlus mr1 mr2)
  from MPlus(3,4) show ?case
    by (auto elim: MPlus(1,2))
next
  case (MTimes mr1 mr2)
  from MTimes(3,4) show ?case
    by (auto elim: MTimes(1,2) simp: MTimesR_def)
next
  case (MStar mr)
  from MStar(2,3) show ?case
    by (auto elim: MStar(1) simp: MTimesR_def)
qed (auto split: nat.splits)

lemma LPDi_ok: "ok m mr \<Longrightarrow> ms \<in> LPDi n mr \<Longrightarrow> ok m ms"
  by (induct n arbitrary: ms mr) (auto intro: LPD_ok)

lemma LPDs_ok: "ok m mr \<Longrightarrow> ms \<in> LPDs mr \<Longrightarrow> ok m ms"
  unfolding LPDs_def by (auto intro: LPDi_ok)

lemma update_matchP:
  assumes pre: "wf_matchP_aux \<sigma> V n R I r aux ne"
    and safe: "Regex.safe_regex fv rgx_safe_pred Past Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne \<phi>) rel) \<phi>s rels"
    and result_eq: "(rel, aux') = update_matchP n I mr mrs rels (\<tau> \<sigma> ne) aux"
  shows "wf_matchP_aux \<sigma> V n R I r aux' (Suc ne)"
    and "qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Formula.MatchP I r)) rel"
proof -
  let ?wf_tuple = "\<lambda>v. wf_tuple n (Formula.fv_regex r) v"
  let ?update = "\<lambda>rel t. mrtabulate mrs (\<lambda>mr.
    r\<delta> id rel rels mr \<union> (if t = \<tau> \<sigma> ne then r\<epsilon>_strict n rels mr else {}))"
  note sat.simps[simp del]

  define aux0 where "aux0 = [(t, ?update rel t). (t, rel) \<leftarrow> aux, memR I (\<tau> \<sigma> ne - t)]"
  have sorted_aux0: "sorted_wrt (\<lambda>x y. fst x > fst y) aux0"
    using pre[unfolded wf_matchP_aux_def, THEN conjunct1]
    unfolding aux0_def
    by (induction aux) (auto simp add: sorted_wrt_append)
  { fix ms
    assume "ms \<in> RPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "Regex.safe_regex fv rgx_safe_pred Past Strict (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "RPD ms \<subseteq> RPDs mr"
      using safe RPDs_safe RPDs_safe_fv_regex mr from_mregex_to_mregex RPDs_ok to_mregex_ok RPDs_trans
      by fastforce+
  } note * = this
  have **: "\<tau> \<sigma> ne - (\<tau> \<sigma> i + \<tau> \<sigma> ne - \<tau> \<sigma> (ne - Suc 0)) = \<tau> \<sigma> (ne - Suc 0) - \<tau> \<sigma> i" for i
    by (metis (no_types, lifting) Nat.diff_diff_right \<tau>_mono add.commute add_diff_cancel_left diff_le_self le_add2 order_trans)
  have ***: "\<tau> \<sigma> i = \<tau> \<sigma> ne"
    if  "\<tau> \<sigma> ne \<le> \<tau> \<sigma> i" "\<tau> \<sigma> i \<le> \<tau> \<sigma> (ne - Suc 0)" "ne > 0" for i
    by (metis (no_types, lifting) Suc_pred \<tau>_mono diff_le_self le_\<tau>_less le_antisym not_less_eq that)
  then have in_aux0_1: "(t, X) \<in> set aux0 \<Longrightarrow> ne \<noteq> 0 \<and> t \<le> \<tau> \<sigma> ne \<and> memR I (\<tau> \<sigma> ne - t) \<and>
      (\<exists>i. \<tau> \<sigma> i = t) \<and>
      (\<forall>ms\<in>RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne
         (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms))" for t X
    unfolding aux0_def using safe mr mrs
    by (auto simp: lookup_tabulate map_of_map_restrict restrict_map_def finite_RPDs * ** RPDs_trans diff_le_mono2
        intro!: sat_MatchP_rec[of \<sigma> _ _ ne, THEN iffD2]
        qtable_union[OF qtable_r\<delta>[OF _ _ qtables] qtable_r\<epsilon>_strict[OF _ _ _ qtables],
          of ms "fv_regex r" "\<lambda>v r. Formula.sat \<sigma> V v (ne - Suc 0) (Formula.MatchP (point 0) r)" _ ms for ms]
        qtable_cong[OF qtable_r\<delta>[OF _ _ qtables],
          of ms "fv_regex r" "\<lambda>v r. Formula.sat \<sigma> V v (ne - Suc 0) (Formula.MatchP (point (\<tau> \<sigma> (ne - Suc 0) - \<tau> \<sigma> i)) r)"
          _ _  "(\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Formula.MatchP (point (\<tau> \<sigma> ne - \<tau> \<sigma> i))  (from_mregex ms \<phi>s)))" for ms i]
        dest!: assms(1)[unfolded wf_matchP_aux_def, THEN conjunct2, THEN conjunct1, rule_format]
        sat_MatchP_rec["of" \<sigma> _ _ ne, THEN iffD1]
        elim!: bspec order.trans[OF _ \<tau>_mono] bexI[rotated] split: option.splits if_splits) (* slow 7 sec *)
  then have in_aux0_le_\<tau>: "(t, X) \<in> set aux0 \<Longrightarrow> t \<le> \<tau> \<sigma> ne" for t X
    by (meson \<tau>_mono diff_le_self le_trans)
  have in_aux0_2: "ne \<noteq> 0 \<Longrightarrow> t \<le> \<tau> \<sigma> (ne-1) \<Longrightarrow> memR I (\<tau> \<sigma> ne - t) \<Longrightarrow> \<exists>i. \<tau> \<sigma> i = t \<Longrightarrow>
    \<exists>X. (t, X) \<in> set aux0" for t
  proof -
    fix t
    assume "ne \<noteq> 0" "t \<le> \<tau> \<sigma> (ne-1)" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
    then obtain X where "(t, X) \<in> set aux"
      by (atomize_elim, intro assms(1)[unfolded wf_matchP_aux_def, THEN conjunct2, THEN conjunct2, rule_format])
        (auto simp: gr0_conv_Suc elim!: order_trans[rotated] intro!: diff_le_mono \<tau>_mono)
    with \<open>memR I (\<tau> \<sigma> ne - t)\<close> have "(t, ?update X t) \<in> set aux0"
      unfolding aux0_def by (auto simp: id_def elim!: bexI[rotated] intro!: exI[of _ X])
    then show "\<exists>X. (t, X) \<in> set aux0"
      by blast
  qed
  have aux0_Nil: "aux0 = [] \<Longrightarrow> ne = 0 \<or> ne \<noteq> 0 \<and> (\<forall>t. t \<le> \<tau> \<sigma> (ne-1) \<and> memR I (\<tau> \<sigma> ne - t) \<longrightarrow>
        (\<nexists>i. \<tau> \<sigma> i = t))"
    using in_aux0_2 by (cases "ne = 0") (auto)

  have aux'_eq: "aux' = (case aux0 of
      [] \<Rightarrow> [(\<tau> \<sigma> ne, mrtabulate mrs (r\<epsilon>_strict n rels))]
    | x # aux' \<Rightarrow> (if fst x = \<tau> \<sigma> ne then x # aux'
       else (\<tau> \<sigma> ne, mrtabulate mrs (r\<epsilon>_strict n rels)) # x # aux'))"
    using result_eq unfolding aux0_def update_matchP_def Let_def by simp
  have sorted_aux': "sorted_wrt (\<lambda>x y. fst x > fst y) aux'"
    unfolding aux'_eq
    using sorted_aux0 in_aux0_le_\<tau> by (cases aux0) (fastforce)+

  have in_aux'_1: "t \<le> \<tau> \<sigma> ne \<and> memR I (\<tau> \<sigma> ne - t) \<and> (\<exists>i. \<tau> \<sigma> i = t) \<and>
     (\<forall>ms\<in>RPDs mr. qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v.
        Formula.sat \<sigma> V (map the v) ne (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms))"
    if aux': "(t, X) \<in> set aux'" for t X
  proof (cases aux0)
    case Nil
    with aux' show ?thesis
      unfolding aux'_eq using safe mrs qtables aux0_Nil *
      by (auto simp: zero_enat_def[symmetric] sat_MatchP_rec[where i=ne]
          lookup_tabulate finite_RPDs split: option.splits
          intro!: qtable_cong[OF qtable_r\<epsilon>_strict]
          dest: spec[of _ "\<tau> \<sigma> (ne-1)"])
  next
    case (Cons a as)
    show ?thesis
    proof (cases "t = \<tau> \<sigma> ne")
      case t: True
      show ?thesis
      proof (cases "fst a = \<tau> \<sigma> ne")
        case True
        with aux' Cons t have "X = snd a"
          unfolding aux'_eq using sorted_aux0 by auto
        moreover from in_aux0_1[of "fst a" "snd a"] Cons have "ne \<noteq> 0"
          "fst a \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - fst a)" "\<exists>i. \<tau> \<sigma> i = fst a"
          "\<forall>ms \<in> RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne
            (Formula.MatchP (point (\<tau> \<sigma> ne - fst a)) (from_mregex ms \<phi>s))) (lookup (snd a) ms)"
          by auto
        ultimately show ?thesis using t True
          by auto
      next
        case False
        with aux' Cons t have "X = mrtabulate mrs (r\<epsilon>_strict n rels)"
          unfolding aux'_eq using sorted_aux0 in_aux0_le_\<tau>[of "fst a" "snd a"] by auto
        with aux' Cons t False show ?thesis
          unfolding aux'_eq using safe mrs qtables * in_aux0_2[of "\<tau> \<sigma> (ne-1)"] in_aux0_le_\<tau>[of "fst a" "snd a"] sorted_aux0
          by (auto simp: sat_MatchP_rec[where i=ne] zero_enat_def[symmetric] enat_0_iff not_le
              lookup_tabulate finite_RPDs split: option.splits
              intro!: qtable_cong[OF qtable_r\<epsilon>_strict] dest!: le_\<tau>_less meta_mp)
      qed
    next
      case False
      with aux' Cons have "(t, X) \<in> set aux0"
        unfolding aux'_eq by (auto split: if_splits)
      then have "ne \<noteq> 0" "t \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t"
        "\<forall>ms \<in> RPDs mr. qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne
          (Formula.MatchP (point (\<tau> \<sigma> ne - t)) (from_mregex ms \<phi>s))) (lookup X ms)"
        using in_aux0_1 by blast+
      with False aux' Cons show ?thesis
        unfolding aux'_eq by auto
    qed
  qed

  have in_aux'_2: "\<exists>X. (t, X) \<in> set aux'" if "t \<le> \<tau> \<sigma> ne" "memR I (\<tau> \<sigma> ne - t)" "\<exists>i. \<tau> \<sigma> i = t" for t
  proof (cases "t = \<tau> \<sigma> ne")
    case True
    then show ?thesis
    proof (cases aux0)
      case Nil
      with True show ?thesis unfolding aux'_eq by simp
    next
      case (Cons a as)
      with True show ?thesis unfolding aux'_eq using eq_fst_iff[of t a]
        by (cases "fst a = \<tau> \<sigma> ne") auto
    qed
  next
    case False
    with that have "ne \<noteq> 0"
      using le_\<tau>_less neq0_conv by blast
    moreover from False that have  "t \<le> \<tau> \<sigma> (ne-1)"
      by (metis One_nat_def Suc_leI Suc_pred \<tau>_mono diff_is_0_eq' order.antisym neq0_conv not_le)
    ultimately obtain X where "(t, X) \<in> set aux0" using \<open>memR I (\<tau> \<sigma> ne - t)\<close> \<open>\<exists>i. \<tau> \<sigma> i = t\<close>
      by atomize_elim (auto intro!: in_aux0_2)
    then show ?thesis unfolding aux'_eq using False
      by (auto intro: exI[of _ X] split: list.split)
  qed

  show "wf_matchP_aux \<sigma> V n R I r aux' (Suc ne)"
    unfolding wf_matchP_aux_def using mr
    by (auto dest: in_aux'_1 intro: sorted_aux' in_aux'_2)

  have rel_eq: "rel = foldr (\<union>) [lookup rel mr. (t, rel) \<leftarrow> aux', memL I (\<tau> \<sigma> ne - t)] {}"
    unfolding aux'_eq aux0_def
    using result_eq by (simp add: update_matchP_def Let_def)
  have rel_alt: "rel = (\<Union>(t, rel) \<in> set aux'. if memL I (\<tau> \<sigma> ne - t) then lookup rel mr else empty_table)"
    unfolding rel_eq foldr_union
    by (auto simp add: prod.case_eq_if)
  show "qtable n (fv_regex r) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (Formula.MatchP I r)) rel"
    unfolding rel_alt
  proof (rule qtable_Union[where Qi="\<lambda>(t, X) v.
    memL I (\<tau> \<sigma> ne - t) \<and> Formula.sat \<sigma> V (map the v) ne (Formula.MatchP (point (\<tau> \<sigma> ne - t)) r)"],
        goal_cases finite qtable equiv)
    case (equiv v)
    show ?case
    proof (rule iffI, erule sat_MatchP_point, goal_cases left right)
      case (left j)
      then show ?case using in_aux'_2[of "\<tau> \<sigma> j", OF _ _ exI, OF _ _ refl] by auto
    next
      case right
      then show ?case by (auto elim!: sat_MatchP_pointD dest: in_aux'_1)
    qed
  qed (auto dest!: in_aux'_1 intro!: qtable_empty dest!: bspec[OF _ RPDs_refl]
      simp: from_mregex_eq[OF safe mr])
qed

lemma length_update_matchF_base:
  "length (fst (update_matchF_base I mr mrs nt entry st)) = Suc 0"
  by (auto simp: Let_def update_matchF_base_def)

lemma length_update_matchF_step:
  "length (fst (update_matchF_step I mr mrs nt entry st)) = Suc (length (fst st))"
  by (auto simp: Let_def update_matchF_step_def split: prod.splits)

lemma length_foldr_update_matchF_step:
  "length (fst (foldr (update_matchF_step I mr mrs nt) aux base)) = length aux + length (fst base)"
  by (induct aux arbitrary: base) (auto simp: Let_def length_update_matchF_step)

lemma length_update_matchF: "length (update_matchF n I mr mrs rels nt aux) = Suc (length aux)"
  unfolding update_matchF_def update_matchF_base_def length_foldr_update_matchF_step
  by (auto simp: Let_def)

lemma wf_update_matchF_base_invar:
  assumes safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) j \<phi>) rel) \<phi>s rels"
  shows "wf_matchF_invar \<sigma> V n R I r (update_matchF_base n I mr mrs rels (\<tau> \<sigma> j)) j"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  { fix ms
    assume "ms \<in> LPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "LPD ms \<subseteq> LPDs mr"
      using safe LPDs_safe LPDs_safe_fv_regex mr from_mregex_to_mregex LPDs_ok to_mregex_ok LPDs_trans
      by fastforce+
  } note * = this
  show ?thesis
    unfolding wf_matchF_invar_def wf_matchF_aux_def update_matchF_base_def mr prod.case Let_def mrs
    using safe
    by (auto simp: * from_mregex qtables qtable_empty_iff zero_enat_def[symmetric]
        lookup_tabulate finite_LPDs eps_match less_Suc_eq LPDs_refl
        intro!: qtable_cong[OF qtable_l\<epsilon>_strict[where \<phi>s=\<phi>s]] intro: qtables exI[of _ j]
        split: option.splits)
qed

lemma wf_matchF_invar_step:
  assumes wf: "wf_matchF_invar \<sigma> V n R I r st (Suc i)"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel) \<phi>s rels"
    and rel: "qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. i \<le> j \<and> j < i + length (fst st) \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and>
          Regex.match (Formula.sat \<sigma> V (map the v)) r i j)) rel"
    and entry: "entry = (\<tau> \<sigma> i, rels, rel)"
    and nt: "nt = \<tau> \<sigma> (i + length (fst st))"
  shows "wf_matchF_invar \<sigma> V n R I r (update_matchF_step I mr mrs nt entry st) i"
proof -
  have from_mregex: "from_mregex mr \<phi>s = r"
    using safe mr using from_mregex_eq by blast
  { fix ms
    assume "ms \<in> LPDs mr"
    then have "fv_regex (from_mregex ms \<phi>s) = fv_regex r"
      "Regex.safe_regex fv rgx_safe_pred Futu Strict (from_mregex ms \<phi>s)" "ok (length \<phi>s) ms" "LPD ms \<subseteq> LPDs mr"
      using safe LPDs_safe LPDs_safe_fv_regex mr from_mregex_to_mregex LPDs_ok to_mregex_ok LPDs_trans
      by fastforce+
  } note * = this
  { fix aux X ms
    assume "st = (aux, X)" "ms \<in> LPDs mr"
    with wf mr have "qtable n (fv_regex r) (mem_restr R)
      (\<lambda>v. Regex.match (Formula.sat \<sigma> V (map the v)) (from_mregex ms \<phi>s) i (i + length aux))
      (l\<delta> (\<lambda>x. x) X rels ms)"
      by (intro qtable_cong[OF qtable_l\<delta>[where \<phi>s=\<phi>s and A="fv_regex r" and
              Q="\<lambda>v r. Regex.match (Formula.sat \<sigma> V v) r (Suc i) (i + length aux)", OF _ _ qtables]])
        (auto simp: wf_matchF_invar_def * LPDs_trans lpd_match[of i] elim!: bspec)
  } note l\<delta> = this
  have "lookup (mrtabulate mrs f) ms = f ms" if "ms \<in> LPDs mr" for ms and f :: "mregex \<Rightarrow> 'a table"
    using that mrs  by (fastforce simp: lookup_tabulate finite_LPDs split: option.splits)+
  then show ?thesis
    using wf mr mrs entry nt LPDs_trans
    by (auto 0 3 simp: Let_def wf_matchF_invar_def update_matchF_step_def wf_matchF_aux_def mr * LPDs_refl
        list_all2_Cons1 append_eq_Cons_conv upt_eq_Cons_conv Suc_le_eq qtables
        lookup_tabulate finite_LPDs id_def l\<delta> from_mregex less_Suc_eq
        intro!: qtable_union[OF rel l\<delta>] qtable_cong[OF rel]
        intro: exI[of _ "i + length _"]
        split: if_splits prod.splits)
qed

lemma wf_update_matchF_invar:
  assumes pre: "wf_matchF_aux \<sigma> V n R I r aux ne (length (fst st) - 1)"
    and wf: "wf_matchF_invar \<sigma> V n R I r st (ne + length aux)"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and j: "j = ne + length aux + length (fst st) - 1"
  shows "wf_matchF_invar \<sigma> V n R I r (foldr (update_matchF_step I mr mrs (\<tau> \<sigma> j)) aux st) ne"
  using pre wf unfolding j
proof (induct aux arbitrary: ne)
  case (Cons entry aux)
  from Cons(1)[of "Suc ne"] Cons(2,3) show ?case
    unfolding foldr.simps o_apply
    by (intro wf_matchF_invar_step[where rels = "fst (snd entry)" and rel = "snd (snd entry)"])
      (auto simp: safe mr mrs wf_matchF_aux_def wf_matchF_invar_def list_all2_Cons1 append_eq_Cons_conv
        Suc_le_eq upt_eq_Cons_conv length_foldr_update_matchF_step add.assoc split: if_splits)
qed simp


lemma wf_update_matchF:
  assumes pre: "wf_matchF_aux \<sigma> V n R I r aux ne 0"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and nt: "nt = \<tau> \<sigma> (ne + length aux)"
    and qtables: "list_all2 (\<lambda>\<phi> rel. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) (ne + length aux) \<phi>) rel) \<phi>s rels"
  shows "wf_matchF_aux \<sigma> V n R I r (update_matchF n I mr mrs rels nt aux) ne 0"
  unfolding update_matchF_def using wf_update_matchF_base_invar[OF safe mr mrs qtables, of I]
  unfolding nt
  by (intro wf_update_matchF_invar[OF _ _ safe mr mrs, unfolded wf_matchF_invar_def split_beta, THEN conjunct2, THEN conjunct1])
    (auto simp: length_update_matchF_base wf_matchF_invar_def update_matchF_base_def Let_def pre)

lemma wf_matchF_aux_Cons1: "wf_matchF_aux \<sigma> V n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow> t = \<tau> \<sigma> ne"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

lemma wf_matchF_aux_Cons3: "wf_matchF_aux \<sigma> V n R I r ((t, rels, rel) # aux) ne i \<Longrightarrow>
  qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v. (\<exists>j. ne \<le> j \<and> j < Suc (ne + length aux + i) \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> ne)) \<and>
    Regex.match (Formula.sat \<sigma> V (map the v)) r ne j)) rel"
  unfolding wf_matchF_aux_def
  by (simp add: upt_conv_Cons del: upt_Suc split: prod.splits)

lemma ok_0_atms: "ok 0 mr \<Longrightarrow> regex.atms (from_mregex mr []) = {}"
  by (induct mr) auto

lemma ok_0_progress: "ok 0 mr \<Longrightarrow> progress_regex \<sigma> P (from_mregex mr []) j = j"
  by (drule ok_0_atms) (auto simp: progress_regex_def)

lemma atms_empty_safe_atms: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> safe_atms r = {} \<longleftrightarrow> regex.atms r = {}"
  by (induct r rule: safe_regex_induct) (auto split: if_splits simp: case_Neg_iff)

lemma atms_empty_progress: "Regex.safe_regex fv rgx_safe_pred m g r \<Longrightarrow> safe_atms r = {} 
  \<Longrightarrow> progress_regex \<sigma> P r j = j"
  by (drule atms_empty_safe_atms) (auto simp: progress_regex_def)

lemma to_mregex_empty_progress: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> to_mregex r = (mr, []) \<Longrightarrow> progress_regex \<sigma> P r j = j"
  using from_mregex_eq ok_0_progress to_mregex_ok atms_empty_safe_atms by fastforce

lemma wf_envs_progress_regex_le[simp]:
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P r j \<le> j"
   "wf_envs S \<sigma> j \<delta> P P' V db \<Longrightarrow> progress_regex \<sigma> P' r (j + \<delta>) \<le> j + \<delta>"
  unfolding wf_envs_def by (auto simp: progress_regex_le)

lemma atms_nonempty_progress:
  "Regex.safe_regex fv rgx_safe_pred m g r \<Longrightarrow> safe_atms r \<noteq> {} 
  \<Longrightarrow> (\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` safe_atms r = (\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` regex.atms r"
  by (frule atms_empty_safe_atms; simp)
    (auto 0 3 simp: safe_atms_def image_iff case_Neg_in_iff 
      elim!: disjE_Not2 dest: safe_regex_safe_formula)

lemma to_mregex_nonempty_progress: "Regex.safe_regex fv rgx_safe_pred m g r 
  \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow> \<phi>s \<noteq> [] 
  \<Longrightarrow> progress_regex \<sigma> P r j = (MIN \<phi>\<in>set \<phi>s. progress \<sigma> P \<phi> j)"
  using atms_nonempty_progress[of m g r \<sigma> P] to_mregex_ok[of r mr \<phi>s]
  unfolding progress_regex_def by fastforce

lemma to_mregex_progress: "Regex.safe_regex fv rgx_safe_pred m g r \<Longrightarrow> to_mregex r = (mr, \<phi>s) \<Longrightarrow>
  progress_regex \<sigma> P r j = (if \<phi>s = [] then j else (MIN \<phi>\<in>set \<phi>s. progress \<sigma> P \<phi> j))"
  using to_mregex_nonempty_progress[of m g r mr \<phi>s \<sigma> P] to_mregex_empty_progress[of m g r mr \<sigma> P]
  unfolding progress_regex_def by auto

lemma progress_MatchF_le: "progress \<sigma> P (Formula.MatchF I r) j \<le> progress_regex \<sigma> P r j"
  by (auto simp: trans_le_add1 progress_regex_def intro!: cInf_lower)

lemma mbufnt_take_add':
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) t nts = (z', buf', nt, nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and safe: "Regex.safe_regex fv rgx_safe_pred m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> P' \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
  shows "wf_mbufn' \<sigma> P' V j' n R r buf'"
    and "wf_ts_regex \<sigma> P' j' r nts'"
  using pre_buf pre_nts bounded rm mr safe xss \<open>j \<le> j'\<close>  unfolding wf_mbufn'_def wf_ts_regex_def
  using atms_empty_progress[of m g r] to_mregex_ok[OF mr]
  by (auto 0 3 simp: list.rel_map to_mregex_empty_progress to_mregex_nonempty_progress Mini_def
      intro: progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm] list.rel_refl_strong progress_le_gen
      dest: list_all2_lengthD elim!: mbufnt_take_eqD[OF eq wf_mbufn_add])

lemma mbufnt_take_add_induct'[consumes 6, case_names base step]:
  assumes eq: "mbufnt_take f z (mbufn_add xss buf) t nts = (z', buf', nt, nts')"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j') P'"
    and rm: "rel_mapping (\<le>) P P'"
    and safe: "Regex.safe_regex fv rgx_safe_pred m g r"
    and mr: "to_mregex r = (mr, \<phi>s)"
    and pre_buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and pre_nts: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..<j'] nts"
    and xss: "list_all3 list_all2
     (map (\<lambda>\<phi> i (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) r) \<phi>s)
     (map2 upt (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) \<phi>s) (map (\<lambda>\<phi>. progress \<sigma> P' \<phi> j') \<phi>s)) xss"
    and "j \<le> j'"
    and base: "U (progress_regex \<sigma> P r j) z"
    and step: "\<And>k Xs z. progress_regex \<sigma> P r j \<le> k \<Longrightarrow> Suc k \<le> progress_regex \<sigma> P' r j' \<Longrightarrow>
      list_all2 (\<lambda>\<phi> (r). qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k \<phi>) r) \<phi>s Xs \<Longrightarrow>
      U k z \<Longrightarrow> U (Suc k) (f Xs (\<tau> \<sigma> k) z)"
  shows "U (progress_regex \<sigma> P' r j') z'"
  using pre_buf pre_nts bounded rm \<open>j \<le> j'\<close> to_mregex_progress[OF safe mr, of \<sigma> P' j'] 
    to_mregex_empty_progress[OF safe, of mr \<sigma> P j] base
  unfolding wf_mbufn'_def mr prod.case
  by (fastforce dest!: mbufnt_take_induct[OF eq wf_mbufn_add[OF _ xss] pre_nts, of U]
      simp: list.rel_map le_imp_diff_is_add ac_simps Mini_def
      intro: progress_mono_gen[OF \<open>j \<le> j'\<close> bounded rm] list.rel_refl_strong progress_le_gen
      intro!: base step  dest: list_all2_lengthD split: if_splits)

(*<*)
end
(*>*)