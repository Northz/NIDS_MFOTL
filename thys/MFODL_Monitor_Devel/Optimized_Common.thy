(*<*)
theory Optimized_Common
  imports Queue Monitor Wf_Table
begin
(*>*)

lemma Mapping_lookup_filter_keys: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  Mapping.lookup (Mapping.filter f m) k = Mapping.lookup m k"
  by (metis default_def insert_subset keys_default keys_filter lookup_default lookup_default_filter)

lemma Mapping_filter_keys: "(\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys (Mapping.filter f m). P (Mapping.lookup (Mapping.filter f m) k))"
  using Mapping_lookup_filter_keys Mapping.keys_filter by fastforce

lemma Mapping_filter_keys_le: "(\<And>x. P x \<Longrightarrow> P' x) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow> (\<forall>k \<in> Mapping.keys m. P' (Mapping.lookup m k))"
  by auto

lemma Mapping_keys_intro: "Mapping.lookup f x \<noteq> None \<Longrightarrow> x \<in> Mapping.keys f"
  by (simp add: domIff keys_dom_lookup)

definition mapping_delete_set :: "('a, 'b) mapping \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" where
  "mapping_delete_set m X = Mapping.filter (join_filter_cond False X) m"

lemma delete_set_lookup: "Mapping.lookup (mapping_delete_set m X) a = (if a \<in> X then
  None else Mapping.lookup m a)"
  by (auto simp: mapping_delete_set_def Mapping.lookup_filter split: option.splits)

lemma delete_set_keys[simp]: "Mapping.keys (mapping_delete_set m X) = Mapping.keys m - X"
  by (auto simp add: delete_set_lookup intro!: Mapping_keys_intro
      dest!: Mapping.in_keysD split: if_splits)

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

lemma Mapping_lookup_upd_set: "Mapping.lookup (upd_set m f X) a =
  (if a \<in> X then Some (f a) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set.rep_eq)

lemma Mapping_upd_set_keys: "Mapping.keys (upd_set m f X) = Mapping.keys m \<union> X"
  by (auto simp add: Mapping_lookup_upd_set dest!: Mapping.in_keysD intro: Mapping_keys_intro)

lemma fold_append_queue_rep: "linearize (fold (\<lambda>x q. append_queue x q) xs q) = linearize q @ xs"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma Max_Un_absorb:
  assumes "finite X" "X \<noteq> {}" "finite Y" "(\<And>x y. y \<in> Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<le> x)"
  shows "Max (X \<union> Y) = Max X"
proof -
  have Max_X_in_X: "Max X \<in> X"
    using Max_in[OF assms(1,2)] .
  have Max_X_in_XY: "Max X \<in> X \<union> Y"
    using Max_in[OF assms(1,2)] by auto
  have fin: "finite (X \<union> Y)"
    using assms(1,3) by auto
  have Y_le_Max_X: "\<And>y. y \<in> Y \<Longrightarrow> y \<le> Max X"
    using assms(4)[OF _ Max_X_in_X] .
  have XY_le_Max_X: "\<And>y. y \<in> X \<union> Y \<Longrightarrow> y \<le> Max X"
    using Max_ge[OF assms(1)] Y_le_Max_X by auto
  show ?thesis
    using Max_eqI[OF fin XY_le_Max_X Max_X_in_XY] by auto
qed

lemma Mapping_lookup_fold_upd_set_idle: "{(t, X) \<in> set xs. as \<in> Z X t} = {} \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as = Mapping.lookup m as"
proof (induction xs arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain x1 x2 where "x = (x1, x2)" by (cases x)
  have "Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs (upd_set m (\<lambda>_. x1) (Z x2 x1))) as =
    Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as"
    using Cons by auto
  also have "Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as = Mapping.lookup m as"
    using Cons.prems by (auto simp: \<open>x = (x1, x2)\<close> Mapping_lookup_upd_set)
  finally show ?case by (simp add: \<open>x = (x1, x2)\<close>)
qed

lemma Mapping_lookup_fold_upd_set_max: "{(t, X) \<in> set xs. as \<in> Z X t} \<noteq> {} \<Longrightarrow>
  sorted (map fst xs) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as =
  Some (Max (fst ` {(t, X) \<in> set xs. as \<in> Z X t}))"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain t X where tX_def: "x = (t, X)"
    by (cases x) auto
  have set_fst_eq: "(fst ` {(t, X). (t, X) \<in> set (x # xs) \<and> as \<in> Z X t}) =
    ((fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t}) \<union>
    (if as \<in> Z X t then {t} else {}))"
    using image_iff by (fastforce simp add: tX_def split: if_splits)
  show ?case
  proof (cases "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<noteq> {}")
    case True
    have "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<subseteq> set xs"
      by auto
    then have fin: "finite (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      by (simp add: finite_subset)
    have "Max (insert t (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})) =
      Max (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      using Max_Un_absorb[OF fin, of "{t}"] True Cons(3) tX_def by auto
    then show ?thesis
      using Cons True unfolding set_fst_eq by auto
  next
    case False
    then have empty: "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} = {}"
      by auto
    then have "as \<in> Z X t"
      using Cons(2) set_fst_eq by fastforce
    then show ?thesis
      using Mapping_lookup_fold_upd_set_idle[OF empty] unfolding set_fst_eq empty
      by (auto simp add: Mapping_lookup_upd_set tX_def)
  qed
qed simp

fun upd_set_keys where "upd_set_keys Z (t, X) (m, Y) = (upd_set m (\<lambda>_. t) (Z X t), Y \<union> Z X t)"

declare upd_set_keys.simps[simp del]

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"
abbreviation "filter_cond' X' ts t' \<equiv> (\<lambda>as. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

lemma dropWhile_filter:
  "sorted (map fst xs) \<Longrightarrow>
  dropWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). memR I (nt - t)) xs"
  by (induction xs) (auto 0 3 intro!: filter_id_conv[THEN iffD2, symmetric])

lemma dropWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow>
  dropWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memL I (nt - t)) xs"
  by (induction xs)
    (auto 0 3 simp: memL_mono diff_le_mono intro!: filter_id_conv[THEN iffD2, symmetric])

lemma takeWhile_filter:
  "sorted (map fst xs) \<Longrightarrow>
  takeWhile (\<lambda>(t, X). \<not> memR I (nt - t)) xs = filter (\<lambda>(t, X). \<not> memR I (nt - t)) xs"
  by (induction xs)
    (auto 0 3 simp: memR_antimono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma takeWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow>
  takeWhile (\<lambda>(t, X). memL I (nt - t)) xs = filter (\<lambda>(t, X). memL I (nt - t)) xs"
  by (induction xs) (auto 0 3 simp: memL_mono intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma fold_Mapping_filter_None: "Mapping.lookup ts as = None \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter
  (filter_cond (f X) ts t) ts) ds ts) as = None"
  by (induction ds arbitrary: ts) (auto simp add: Mapping.lookup_filter)

lemma Mapping_lookup_filter_Some_P: "Mapping.lookup (Mapping.filter P m) k = Some v \<Longrightarrow> P k v"
  by (auto simp add: Mapping.lookup_filter split: option.splits if_splits)

lemma Mapping_lookup_filter_None: "(\<And>v. \<not>P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = None"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_Some: "(\<And>v. P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_not_None: "Mapping.lookup (Mapping.filter P m) k \<noteq> None \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma fold_Mapping_filter_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> (f X) \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond (f X) ts t) ts) ds ts) as = None"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using
        fold_Mapping_filter_None[of "Mapping.filter (filter_cond (f X') ts t') ts" as f ds]
        Mapping_lookup_filter_not_None[of "filter_cond (f X') ts t'" ts as]
        fold_Mapping_filter_None[OF Mapping_lookup_filter_None, of _ as f ds ts]
      by (cases "Mapping.lookup (Mapping.filter (filter_cond (f X') ts t') ts) as = None") auto
  qed
qed simp

lemma fold_Mapping_filter_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> f X) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond (f X) ts t) ts) ds ts) as = Some t"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  then show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using Mapping_lookup_filter_Some[of "filter_cond (f X') ts t'" as ts] by auto
  qed
qed simp

fun filter_set where "filter_set (t, X) (m, Y) =
  (let m' = Mapping.filter (filter_cond X m t) m in (m', Y \<union> (Mapping.keys m - Mapping.keys m')))"

declare filter_set.simps[simp del]

lemma filter_set_sub: "filter_set (t, X) (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> X"
  by (auto simp: filter_set.simps Let_def Mapping_lookup_filter_Some domIff keys_dom_lookup)

lemma fold_filter_set_sub: "fold filter_set xs (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> \<Union>(snd ` set xs)"
proof (induction xs arbitrary: m Y)
  case (Cons a xs)
  show ?case
    using Cons(2)
    by (cases a; cases "filter_set a (m, Y)") (auto dest: Cons(1) filter_set_sub)
qed auto

lemma fold_filter_set_None: "Mapping.lookup ts as = None \<Longrightarrow>
  fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = None \<and> (as \<in> Y' \<longleftrightarrow> as \<in> Y)"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "as \<in> Y'' \<longleftrightarrow> as \<in> Y"
        using Cons(2) step
        by (auto simp: Pair filter_set.simps Let_def keys_is_none_rep)
      then show ?thesis
        using Cons(1)[OF None] Cons(2,3)
        by (auto simp: step)
    next
      case (Some t'')
      have False
        using Cons(2) Some step Mapping_lookup_filter_not_None
        by (force simp: Pair filter_set.simps Let_def)
      then show ?thesis ..
    qed
  qed
qed simp

lemma fold_filter_set_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> X \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow> fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = None \<and> as \<in> Y'"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "as \<in> Y''"
        using Cons(2) None step
        by (auto simp: Pair filter_set.simps Let_def Mapping_keys_intro keys_is_none_rep)
      then have "fold filter_set ds (ts'', Y'') = (ts', Y') \<Longrightarrow> as \<in> Y'"
        by (induction ds arbitrary: ts'' Y'') (auto simp: filter_set.simps Let_def)
      moreover have "fold filter_set ds (ts'', Y'') = (ts', Y') \<Longrightarrow> Mapping.lookup ts' as = None"
        using None Mapping_lookup_filter_not_None
        by (induction ds arbitrary: ts'' Y'') (fastforce simp: filter_set.simps Let_def)+
      ultimately show ?thesis
        using Cons(5)
        by (auto simp: step)
    next
      case (Some t'')
      have lookup_ts'': "Mapping.lookup ts'' as = Some t"
        using Cons(2) step Some Mapping_lookup_filter_not_None
        by (fastforce simp: Pair filter_set.simps Let_def Mapping_lookup_filter_None)
      have set_ds: "(t, X) \<in> set ds"
        using Cons(2,3,4) step Some
        by (auto simp: filter_set.simps Let_def Mapping_lookup_filter_None)
      show ?thesis
        using Cons lookup_ts'' set_ds
        by (auto simp: step)
    qed
  qed
qed simp

lemma fold_filter_set_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> X) \<Longrightarrow> fold filter_set ds (ts, Y) = (ts', Y') \<Longrightarrow>
  Mapping.lookup ts' as = Some t \<and> (as \<in> Y' \<longleftrightarrow> as \<in> Y)"
proof (induction ds arbitrary: ts Y)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    obtain ts'' Y'' where step: "filter_set a (ts, Y) = (ts'', Y'')"
      by fastforce
    show ?thesis
    proof (cases "Mapping.lookup ts'' as")
      case None
      have "False"
        using Cons(2,3) None step
        by (auto simp: Pair filter_set.simps Let_def) (smt (z3) Mapping_lookup_filter_Some option.distinct(1) option.inject)
      then show ?thesis ..
    next
      case (Some t'')
      have lookup_ts'': "Mapping.lookup ts'' as = Some t"
        using Cons(2) step Some Mapping_lookup_filter_not_None
        by (fastforce simp: Pair filter_set.simps Let_def Mapping_lookup_filter_None)
      have "as \<in> Y'' \<longleftrightarrow> as \<in> Y"
        using step Mapping_keys_intro Some
        by (force simp: Pair filter_set.simps Let_def)
      then show ?thesis
        using Cons(1)[OF lookup_ts''] Cons(3,4)
        by (auto simp: step)
    qed
  qed
qed simp

lemma upd_set_keys_sub: "upd_set_keys Z (t, X) (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> Z X t"
  by (auto simp: upd_set_keys.simps Mapping_lookup_filter_Some domIff keys_dom_lookup)

lemma fold_upd_set_keys_sub:
  assumes Z_sub: "\<And>X t. Z X t \<subseteq> X"
  shows "fold (upd_set_keys Z) xs (m, Y) = (m', Y') \<Longrightarrow> Y' \<subseteq> Y \<union> \<Union>(snd ` set xs)"
proof (induction xs arbitrary: m Y)
  case (Cons a xs)
  show ?case
    using Cons(2) Z_sub
    by (cases a; cases "upd_set_keys Z a (m, Y)") (fastforce dest: Cons(1) upd_set_keys_sub)
qed auto

lemma fold_upd_set_keys:
  assumes "fold (upd_set_keys Z) mv (ts, {}) = (ts', Y)"
  shows "ts' = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    "Mapping.keys ts' = Mapping.keys ts \<union> Y"
proof -
  have fst_fold_upd_set_keys: "fst (fold (upd_set_keys Z) mv (ts, Y0)) = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    for Y0 :: "'a set"
    by (induction mv arbitrary: ts Y0) (auto simp: upd_set_keys.simps)
  show "ts' = fold (\<lambda>(t, X) ts. upd_set ts (\<lambda>_. t) (Z X t)) mv ts"
    using fst_fold_upd_set_keys[where ?Y0.0="{}"]
    by (auto simp: assms)
  have keys_fold_upd_set_keys: "Y0 \<subseteq> Y \<and> Mapping.keys ts \<subseteq> Mapping.keys ts' \<and> Mapping.keys ts' \<union> Y0 = Mapping.keys ts \<union> Y" if "fold (upd_set_keys Z) mv (ts, Y0) = (ts', Y)" for Y0
    using that
  proof (induction mv arbitrary: ts Y0)
    case (Cons a mv)
    show ?case
    proof (cases a)
      case (Pair t' X')
      show ?thesis
        using Cons(2)
        apply (simp add: Pair upd_set_keys.simps)
        apply (drule Cons(1))
        apply (auto simp: Mapping_upd_set_keys)
        done
    qed
  qed simp
  show "Mapping.keys ts' = Mapping.keys ts \<union> Y"
    using keys_fold_upd_set_keys[OF assms]
    by auto
qed

lemma image_snd: "(a, b) \<in> X \<Longrightarrow> b \<in> snd ` X"
  by force

definition ts_tuple_rel_f :: "('b \<Rightarrow> 'a table) \<Rightarrow> (ts \<times> 'b) set \<Rightarrow> (ts \<times> 'a tuple) set" where
  "ts_tuple_rel_f f ys = {(t, as). \<exists>X. as \<in> (f X) \<and> (t, X) \<in> ys}"

abbreviation "ts_tuple_rel ys \<equiv> ts_tuple_rel_f id ys"

lemma finite_fst_ts_tuple_rel: "finite (fst ` {tas \<in> ts_tuple_rel_f f (set xs). P tas})"
proof -
  have "fst ` {tas \<in> ts_tuple_rel_f f (set xs). P tas} \<subseteq> fst ` ts_tuple_rel_f f (set xs)"
    by auto
  moreover have "\<dots> \<subseteq> set (map fst xs)"
    by (force simp add: ts_tuple_rel_f_def)
  finally show ?thesis
    using finite_subset by blast
qed

lemma ts_tuple_rel_ext_Cons: "tas \<in> ts_tuple_rel_f f {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_ext_Cons': "tas \<in> ts_tuple_rel_f f (set tass) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_intro: "as \<in> f X \<Longrightarrow> (t, X) \<in> ys \<Longrightarrow> (t, as) \<in> ts_tuple_rel_f f ys"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_dest: "(t, as) \<in> ts_tuple_rel_f f ys \<Longrightarrow> \<exists>X. (t, X) \<in> ys \<and> as \<in> f X"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_Un: "ts_tuple_rel_f f (ys \<union> zs) = ts_tuple_rel_f f ys \<union> ts_tuple_rel_f f zs"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_ext: "tas \<in> ts_tuple_rel_f f {(nt, X)} \<Longrightarrow>
  \<forall> A B. f A \<union> f B = f (A \<union> B) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, Y \<union> X) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel_f f {(nt, X)}" "\<forall> A B. f A \<union> f B = f (A \<union> B)"
  then obtain as where tas_def: "tas = (nt, as)" "as \<in> f X"
    by (cases tas) (auto simp add: ts_tuple_rel_f_def)
  then have "as \<in> f (Y \<union> X)"
    using assm(2)
    by auto
  then show "tas \<in> ts_tuple_rel_f f (set ((nt, Y \<union> X) # tass))"
    unfolding tas_def(1)
    by (rule ts_tuple_rel_intro) auto
qed

lemma ts_tuple_rel_ext': "tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass)) \<Longrightarrow>
  \<forall> A B. f A \<union> f B = f (A \<union> B) \<Longrightarrow>
  tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel_f f (set ((nt, X) # tass))" "\<forall> A B. f A \<union> f B = f (A \<union> B)"
  then have "tas \<in> ts_tuple_rel_f f {(nt, X)} \<union> ts_tuple_rel_f f (set tass)"
    using ts_tuple_rel_Un by force
  then show "tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
  proof
    assume "tas \<in> ts_tuple_rel_f f {(nt, X)}"
    then show ?thesis
      using assm(2)
      by (auto simp: Un_commute dest!: ts_tuple_rel_ext)
  next
    assume "tas \<in> ts_tuple_rel_f f (set tass)"
    then have "tas \<in> ts_tuple_rel_f f (set ((nt, X \<union> Y) # tass))"
      by (rule ts_tuple_rel_ext_Cons')
    then show ?thesis by simp
  qed
qed

lemma ts_tuple_rel_mono: "ys \<subseteq> zs \<Longrightarrow> ts_tuple_rel_f f ys \<subseteq> ts_tuple_rel_f f zs"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_filter: "ts_tuple_rel_f f (set (filter (\<lambda>(t, X). P t) xs)) =
  {(t, X) \<in> ts_tuple_rel_f f (set xs). P t}"
  by (auto simp add: ts_tuple_rel_f_def)

lemma ts_tuple_rel_set_filter: "x \<in> ts_tuple_rel_f f (set (filter P xs)) \<Longrightarrow>
  x \<in> ts_tuple_rel_f f (set xs)"
  by (auto simp add: ts_tuple_rel_f_def)

definition valid_tuple :: "(('a tuple, ts) mapping) \<Rightarrow> (ts \<times> 'a tuple) \<Rightarrow> bool" where
  "valid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
  | Some t' \<Rightarrow> t \<ge> t')"

definition safe_max :: "'a :: linorder set \<Rightarrow> 'a option" where
  "safe_max X = (if X = {} then None else Some (Max X))"

lemma safe_max_empty: "safe_max X = None \<longleftrightarrow> X = {}"
  by (simp add: safe_max_def)

lemma safe_max_empty_dest: "safe_max X = None \<Longrightarrow> X = {}"
  by (simp add: safe_max_def split: if_splits)

lemma safe_max_Some_intro: "x \<in> X \<Longrightarrow> \<exists>y. safe_max X = Some y"
  using safe_max_empty by auto

lemma safe_max_Some_dest_in: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> x \<in> X"
  using Max_in by (auto simp add: safe_max_def split: if_splits)

lemma safe_max_Some_dest_le: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> y \<in> X \<Longrightarrow> y \<le> x"
  using Max_ge by (auto simp add: safe_max_def split: if_splits)

definition newest_tuple_in_mapping :: "
  ('b \<Rightarrow> 'a table) \<Rightarrow>
  (ts \<times> 'b) queue \<Rightarrow>
  (('a tuple, ts) mapping) \<Rightarrow>
  ((ts \<times> 'a tuple) \<Rightarrow> bool) \<Rightarrow>
  bool"
  where
  "newest_tuple_in_mapping entry_to_db data_in tuple_in P = (\<forall>tuple.
    \<comment> \<open>iff something is present in the mapping then the value corresponds
       to the maximum timestamp of a db containing the tuple\<close>
    Mapping.lookup tuple_in tuple =
    safe_max (
      fst ` {
       tas \<in> ts_tuple_rel_f entry_to_db (set (linearize data_in)).
       P tas \<and> tuple = snd tas
      }
    )
  )"

lemma fold_pair_fst: "fst (fold (\<lambda> a (x, y). (f1 a x, f2 a x y)) as (x, y)) = fold (\<lambda> a (x). (f1 a x)) as (x)"
proof (induction as arbitrary: rule: rev_induct)
  case (snoc a as)
  then show ?case
    by (smt (z3) fold.simps(1) fold.simps(2) fold_append fst_conv id_o o_apply split_beta)
qed (auto)

lemma Mapping_update_keys: "Mapping.keys (Mapping.update a b m) = Mapping.keys m \<union> {a}"
  by transfer auto

lemma drop_is_Cons_take: "drop n xs = y # ys \<Longrightarrow> take (Suc n) xs = take n xs @ [y]"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases n) simp_all
qed

lemma list_all_split: "list_all (\<lambda>(x, y). f x y \<and> g x y) xs \<longleftrightarrow> list_all (\<lambda>(x, y). f x y) xs \<and> list_all (\<lambda>(x, y). g x y) xs"
  by (smt (z3) Ball_set case_prodI2 old.prod.case)

lemma list_all2_weaken: "list_all2 f xs ys \<Longrightarrow>
  (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x y \<Longrightarrow> f' x y) \<Longrightarrow> list_all2 f' xs ys"
  by (induction xs ys rule: list_all2_induct) auto

declare Map_To_Mapping.map_apply_def[simp]

lemma Mapping_lookup_delete: "Mapping.lookup (Mapping.delete k m) k' =
  (if k = k' then None else Mapping.lookup m k')"
  by transfer auto

lemma hd_le_set: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd xs \<le> x"
  by (cases xs) auto

lemma Mapping_lookup_combineE: "Mapping.lookup (Mapping.combine f m m') k = Some v \<Longrightarrow>
  (Mapping.lookup m k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (Mapping.lookup m' k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (\<And>v' v''. Mapping.lookup m k = Some v' \<Longrightarrow> Mapping.lookup m' k = Some v'' \<Longrightarrow>
  f v' v'' = v \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding Mapping.lookup_combine
  by (auto simp add: combine_options_def split: option.splits)

lemma Mapping_keys_filterI: "Mapping.lookup m k = Some v \<Longrightarrow> f k v \<Longrightarrow>
  k \<in> Mapping.keys (Mapping.filter f m)"
  by transfer (auto split: option.splits if_splits)

lemma Mapping_keys_filterD: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  \<exists>v. Mapping.lookup m k = Some v \<and> f k v"
  by transfer (auto split: option.splits if_splits)

lemma list_appendE: "xs = ys @ zs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  (x \<in> set ys \<Longrightarrow> P) \<Longrightarrow> (x \<in> set zs \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

(*<*)
end
(*>*)