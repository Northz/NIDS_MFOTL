(*<*)
theory Correct_Un_Ops
  imports
    Monitor 
    Progress
begin
(*>*)


subsection \<open> Correctness of atoms and unary Operators \<close>


subsubsection \<open> Inequalities \<close>

fun formula_of_constraint :: "Formula.trm \<times> bool \<times> mconstraint \<times> Formula.trm \<Rightarrow> ty Formula.formula" where
  "formula_of_constraint (t1, True, MEq, t2) = Formula.Eq t1 t2"
| "formula_of_constraint (t1, True, MLess, t2) = Formula.Less t1 t2"
| "formula_of_constraint (t1, True, MLessEq, t2) = Formula.LessEq t1 t2"
| "formula_of_constraint (t1, False, MEq, t2) = Formula.Neg (Formula.Eq t1 t2)"
| "formula_of_constraint (t1, False, MLess, t2) = Formula.Neg (Formula.Less t1 t2)"
| "formula_of_constraint (t1, False, MLessEq, t2) = Formula.Neg (Formula.LessEq t1 t2)"

lemma fv_formula_of_constraint: "fv (formula_of_constraint (t1, p, c, t2)) = fv_trm t1 \<union> fv_trm t2"
  by (induction "(t1, p, c, t2)" rule: formula_of_constraint.induct) simp_all

lemma progress_constraint: "progress \<sigma> P (formula_of_constraint c) j = j"
  by (induction rule: formula_of_constraint.induct) simp_all

lemma eval_constraint_sat_eq: "wf_tuple n A x \<Longrightarrow> fv_trm t1 \<subseteq> A \<Longrightarrow> fv_trm t2 \<subseteq> A \<Longrightarrow>
  \<forall>i\<in>A. i < n \<Longrightarrow> eval_constraint (t1, p, c, t2) x =
    Formula.sat \<sigma> V (map the x) i (formula_of_constraint (t1, p, c, t2))"
  by (induction "(t1, p, c, t2)" rule: formula_of_constraint.induct)
    (simp_all add: meval_trm_eval_trm)

lemma formula_of_constraint_neq_release_safe_bdd: 
  "formula_of_constraint (t1, b, op, t2) \<noteq> release_safe_bounded \<phi>' I \<psi>'"
  by (induction rule: formula_of_constraint.induct)
    (auto simp: release_safe_bounded_def)


subsubsection \<open> Predicates \<close>

lemma match_wf_tuple: "Some f = match ts xs \<Longrightarrow>
  wf_tuple n (\<Union>t\<in>set ts. Formula.fv_trm t) (Table.tabulate f 0 n)"
  by (induction ts xs arbitrary: f rule: match.induct)
    (fastforce simp: wf_tuple_def split: if_splits option.splits)+

lemma match_fvi_trm_None: "Some f = match ts xs \<Longrightarrow> \<forall>t\<in>set ts. x \<notin> Formula.fv_trm t \<Longrightarrow> f x = None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_fvi_trm_Some: "Some f = match ts xs \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> Formula.fv_trm t \<Longrightarrow> f x \<noteq> None"
  by (induction ts xs arbitrary: f rule: match.induct) (auto split: if_splits option.splits)

lemma match_eval_trm: "\<forall>t\<in>set ts. \<forall>i\<in>Formula.fv_trm t. i < n \<Longrightarrow> Some f = match ts (map Some xs) \<Longrightarrow>
    map (Formula.eval_trm (Table.tabulate (\<lambda>i. the (f i)) 0 n)) ts = xs"
proof (induction ts "map Some xs" arbitrary: f xs rule: match.induct)
  case (3 x ts y ys)
  then obtain xs' where 1: "ys = map Some xs'" and 2: "xs = y # xs'" by auto
  from 3(1)[OF 1, symmetric] 3(3,4) show ?case
    unfolding 3(2)[symmetric] 2
    by (auto 0 3 dest: match_fvi_trm_Some sym split: option.splits if_splits intro!: eval_trm_fv_cong)
qed (auto split: if_splits)

lemma ex_match: "wf_tuple n (\<Union>t\<in>set ts. Formula.fv_trm t) v \<Longrightarrow>
  \<forall>t\<in>set ts. (\<forall>x\<in>Formula.fv_trm t. x < n) \<and> (Formula.is_Var t \<or> Formula.is_Const t) \<Longrightarrow>
  \<exists>f. match ts (map (Some \<circ> Formula.eval_trm (map the v)) ts) = Some f \<and> v = Table.tabulate f 0 n"
proof (induction ts "map (Some \<circ> Formula.eval_trm (map the v)) ts" arbitrary: v rule: match.induct)
  case (3 x ts y ys)
  then show ?case
  proof (cases "x \<in> (\<Union>t\<in>set ts. Formula.fv_trm t)")
    case True
    with 3 show ?thesis
      by (auto simp: insert_absorb dest!: wf_tuple_tabulate_Some meta_spec[of _ v])
  next
    case False
    with 3(3,4) have
      *: "map (Some \<circ> Formula.eval_trm (map the v)) ts = map (Some \<circ> Formula.eval_trm (map the (v[x := None]))) ts"
      by (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_fv_cong)
    from False 3(2-4) obtain f where
      "match ts (map (Some \<circ> Formula.eval_trm (map the v)) ts) = Some f" "v[x := None] = Table.tabulate f 0 n"
      unfolding *
      by (atomize_elim, intro 3(1)[of "v[x := None]"])
        (auto simp: wf_tuple_def nth_list_update intro!: eval_trm_fv_cong)
    moreover from False this have "f x = None" "length v = n"
      by (auto dest: match_fvi_trm_None[OF sym] arg_cong[of _ _ length])
    ultimately show ?thesis using 3(3)
      by (auto simp: list_eq_iff_nth_eq wf_tuple_def)
  qed
qed (auto simp: wf_tuple_def intro: nth_equalityI)

lemma simple_match_skip[simp]: "m < x \<Longrightarrow>
  simple_match n m (Formula.Var x # ts) (y # ys) = None # simple_match n (Suc m) (Formula.Var x # ts) (y # ys)"
  by (subst simple_match.simps) (simp del: simple_match.simps)

lemma simple_match_copy[simp]: "\<not> m < x \<Longrightarrow>
  simple_match n m (Formula.Var x # ts) (y # ys) = y # simple_match n (Suc m) ts ys"
  by (subst simple_match.simps) (simp del: simple_match.simps)

lemma is_simple_pattern_fv: "is_simple_pattern ts x \<Longrightarrow> t \<in> set ts \<Longrightarrow> y \<in> fv_trm t \<Longrightarrow> x \<le> y"
  by (induction ts x rule: is_simple_pattern.induct) auto

lemma wf_tuple_simple_match_gen: "is_simple_pattern ts m \<Longrightarrow> \<forall>t\<in>set ts. (\<forall>x\<in>Formula.fv_trm t. x < n) \<Longrightarrow>
  (\<forall>y\<in>set ys. y \<noteq> None) \<Longrightarrow> length ys = length ts \<Longrightarrow>
  wf_tuple (n - m) (\<Union>t\<in>set ts. (\<lambda>x. x - m) ` Formula.fv_trm t) (simple_match n m ts ys)"
  apply (induction n m ts ys rule: simple_match.induct)
                      apply (simp add: wf_tuple_empty_iff)
  subgoal for n m x ts y ys
    supply simple_match.simps[simp del]
    apply (cases "m < x")
    apply (clarsimp simp add: image_iff not_le)
     apply (intro conjI)
      apply (meson Suc_leD is_simple_pattern_fv less_le_trans)
     apply (intro exI[where x="n - Suc m"] conjI)
      apply (metis Suc_diff_Suc Suc_lessD less_trans_Suc)
     apply (subgoal_tac "0 \<notin> insert (x - m) (\<Union>x\<in>set ts. (\<lambda>x. x - m) ` fv_trm x)")
      apply (simp add: image_Union image_image)
     apply safe[]
      apply linarith
     apply (metis Suc_leD is_simple_pattern_fv le_zero_eq less_le_trans not_le zero_less_diff)
    apply (erule thin_rl)
    apply clarsimp
    apply (rule exI[where x="n - Suc m"])
    apply (intro conjI)
     apply simp
    apply (subgoal_tac "0 \<notin> (\<Union>xa\<in>set ts. (\<lambda>xa. xa - x) ` fv_trm xa)")
     apply (simp add: image_Union image_image)
    apply safe
    by (metis Suc_diff_le Zero_neq_Suc diff_is_0_eq is_simple_pattern_fv)
  by simp_all

lemma wf_tuple_simple_match: "is_simple_pattern ts 0 \<Longrightarrow> \<forall>t\<in>set ts. (\<forall>x\<in>Formula.fv_trm t. x < n) \<Longrightarrow>
  (\<forall>y\<in>set ys. y \<noteq> None) \<Longrightarrow> length ys = length ts \<Longrightarrow>
  wf_tuple n (\<Union>t\<in>set ts. Formula.fv_trm t) (simple_match n 0 ts ys)"
  using wf_tuple_simple_match_gen[where m=0] by simp

lemma eval_trm_simple_match_gen: "\<forall>t\<in>set ts. \<forall>i\<in>Formula.fv_trm t. i < n \<Longrightarrow>
  is_simple_pattern ts m \<Longrightarrow> length ys = length ts \<Longrightarrow>
  map (Formula.eval_trm (map the (replicate m None @ simple_match n m ts (map Some ys)))) ts = ys"
  apply (induction n m ts "map Some ys" arbitrary: ys rule: simple_match.induct)
                      apply simp
  subgoal for n m x ts y ys ys'
    supply simple_match.simps[simp del]
    apply (cases "m < x")
     apply (clarsimp simp add: replicate_app_Cons_same)
    apply clarsimp
    apply (intro conjI)
     apply (metis length_replicate nth_append_length)
    apply (erule trans[rotated])
    apply (rule map_cong[OF refl])
    apply (rule eval_trm_fv_cong)
    apply clarsimp
    apply (drule (2) is_simple_pattern_fv)
    apply (simp add: nth_append)
    by linarith
  by simp_all

lemma eval_trm_simple_match: "\<forall>t\<in>set ts. \<forall>i\<in>Formula.fv_trm t. i < n \<Longrightarrow>
  is_simple_pattern ts 0 \<Longrightarrow> length ys = length ts \<Longrightarrow>
  map (Formula.eval_trm (map the (simple_match n 0 ts (map Some ys)))) ts = ys"
  using eval_trm_simple_match_gen[where m=0] by simp

lemma simple_match_eval_trm_gen: "\<forall>t\<in>set ts. \<forall>i\<in>Formula.fv_trm t. i < n \<Longrightarrow>
  is_simple_pattern ts m \<Longrightarrow>
  wf_tuple (n - m) (\<Union>t\<in>set ts. (\<lambda>x. x - m) ` Formula.fv_trm t) v \<Longrightarrow>
  simple_match n m ts (map (Some \<circ> Formula.eval_trm (map the (replicate m None @ v))) ts) = v"
  apply (induction n m ts "map (Some \<circ> Formula.eval_trm (map the (replicate m None @ v))) ts" arbitrary: v rule: simple_match.induct)
                      apply (simp add: wf_tuple_empty_iff)
  subgoal for n m x ts y ys v
    supply simple_match.simps[simp del]
    apply (cases "m < x")
     apply clarsimp
     apply (subgoal_tac "\<exists>v'. v = None # v'")
      apply (subgoal_tac "n - m = Suc (n - Suc m)")
       apply (clarsimp simp add: replicate_app_Cons_same image_Union image_image)
      apply (metis Suc_diff_Suc Suc_lessD less_trans_Suc)
     apply (subgoal_tac "length v > 0 \<and> v ! 0 = None")
      apply (metis list.set_cases nth_Cons_0 nth_mem)
     apply (auto simp add: wf_tuple_def)[]
     apply (meson Suc_leD is_simple_pattern_fv less_le_trans not_le)
    apply (erule thin_rl)
    apply (subgoal_tac "\<exists>z v'. v = Some z # v'")
     apply (clarsimp simp add: nth_append)
    subgoal for z v' m'
      apply (drule meta_spec[where x=v'])
      apply (drule meta_mp)
       apply (intro ballI eval_trm_fv_cong)
       apply (drule (2) is_simple_pattern_fv)
       apply (simp add: nth_append)
       apply linarith
      apply (drule meta_mp)
       apply (subgoal_tac "m' = n - Suc x")
        apply (subgoal_tac "0 \<notin> (\<Union>xa\<in>set ts. (\<lambda>xa. xa - x) ` fv_trm xa)")
         apply (simp add: image_Union image_image)
        apply safe[]
        apply (metis diff_is_0_eq is_simple_pattern_fv lessI less_irrefl less_le_trans)
       apply (metis Suc_diff_Suc nat.inject)
      apply (erule trans[rotated])
      apply (rule arg_cong[where f="\<lambda>ys. simple_match n (Suc x) ts ys"])
      apply (unfold comp_apply)
      apply (intro map_cong[OF refl] arg_cong[where f=Some] eval_trm_fv_cong ballI)
      apply (drule (2) is_simple_pattern_fv)
      apply (simp add: nth_append)
      by linarith
    apply (subgoal_tac "length v > 0 \<and> v ! 0 \<noteq> None")
     apply (clarsimp simp add: neq_Nil_conv)
    by (auto simp add: wf_tuple_def)
  by simp_all

lemma simple_match_eval_trm: "\<forall>t\<in>set ts. \<forall>i\<in>Formula.fv_trm t. i < n \<Longrightarrow>
  is_simple_pattern ts 0 \<Longrightarrow>
  wf_tuple n (\<Union>t\<in>set ts. Formula.fv_trm t) v \<Longrightarrow>
  simple_match n 0 ts (map (Some \<circ> Formula.eval_trm (map the v)) ts) = v"
  using simple_match_eval_trm_gen[where m=0] by simp

lemma pred_mode_of_eq_simps[simp]:
  "(pred_mode_of n ts = Copy) \<longleftrightarrow> is_copy_pattern n ts"
  "(pred_mode_of n ts = Simple) \<longleftrightarrow> \<not> is_copy_pattern n ts \<and> is_simple_pattern ts 0"
  "(pred_mode_of n ts = Match) \<longleftrightarrow> \<not> is_copy_pattern n ts \<and> \<not> is_simple_pattern ts 0"
  unfolding pred_mode_of_def by simp_all

lemma qtable_copy_pattern:
  assumes "X = fv (Formula.Pred p ts)" and "is_copy_pattern n ts"
  shows "V (p, length ts) = Some P \<Longrightarrow> 
  R = map Some ` {v. length v = length ts \<and> the (V (p, length ts)) v i} \<Longrightarrow>
  qtable n X (mem_restr UU) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Pred p ts)) R"
    and "V (p, length ts) = None \<Longrightarrow> 
  R = map Some ` {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts}  \<Longrightarrow>
  qtable n X (mem_restr UU) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Pred p ts)) R"
  using assms
  by (auto simp: image_iff table_def
      wf_tuple_def is_copy_pattern_def comp_def map_nth 
      intro!: qtableI exI[of _ "map ((!) (map the _)) [0..<length _]"] nth_equalityI)

lemma qtable_simple_pattern:
  assumes "X = fv (Formula.Pred p ts)" and "\<forall>x\<in>X. x < n" 
    and "is_simple_pattern ts 0"
  shows "V (p, length ts) = Some P \<Longrightarrow> 
  R = simple_match n 0 ts ` (map Some ` {v. length v = length ts \<and> P v i}) \<Longrightarrow>
  qtable n X (mem_restr UU) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Pred p ts)) R"
    and "V (p, length ts) = None \<Longrightarrow> 
  R = simple_match n 0 ts ` (map Some ` {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts}) \<Longrightarrow> 
  qtable n X (mem_restr UU) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Pred p ts)) R"
  using assms
  by (auto simp: image_iff table_def
      eval_trm_simple_match simple_match_eval_trm wf_tuple_simple_match
      intro!: qtableI exI[of _ "map (eval_trm_option _) ts"])

lemma qtable_no_pattern:
  assumes "X = fv (Formula.Pred p ts)" and "\<forall>x\<in>X. x < n" and "\<forall>t\<in>set ts. trm.is_Var t \<or> trm.is_Const t"
    and "\<not> is_copy_pattern n ts" and "\<not> is_simple_pattern ts 0"
  shows "V (p, length ts) = Some P \<Longrightarrow> 
  R = (\<lambda>x. tabulate x 0 n) ` Option.these (match ts ` (map Some ` {v. length v = length ts \<and> P v i})) \<Longrightarrow>
  qtable n X (mem_restr UU) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Pred p ts)) R"
    and "V (p, length ts) = None \<Longrightarrow> 
  R = (\<lambda>x. tabulate x 0 n) ` Option.these (match ts ` (map Some ` {v. (p, v) \<in> \<Gamma> \<sigma> i \<and> length v = length ts})) \<Longrightarrow>
  qtable n X (mem_restr UU) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Pred p ts)) R"
  using assms
proof (auto intro!: qtableI, goal_cases)
  case (3 v)
  then show ?case 
    using ex_match[of n ts v] 
    by (auto simp: in_these_eq image_iff
        intro!: bexI[where P="\<lambda>x. _ = tabulate x 0 n"])
      (metis length_map list.map_comp)
next
  case (6 v)
  then show ?case 
    using ex_match[of n ts v] 
    by (auto simp: in_these_eq image_iff
        intro!: bexI[where P="\<lambda>x. _ = tabulate x 0 n"])
      (metis length_map list.map_comp)
qed (auto simp: table_def in_these_eq match_eval_trm image_iff
        elim!: match_wf_tuple[of _ ts "(map Some _)" n])


subsubsection \<open> Equalities \<close>

lemma eq_rel_eval_trm: "v \<in> eq_rel n t1 t2 \<Longrightarrow> is_simple_eq t1 t2 \<Longrightarrow>
  \<forall>x\<in>Formula.fv_trm t1 \<union> Formula.fv_trm t2. x < n \<Longrightarrow>
  Formula.eval_trm (map the v) t1 = Formula.eval_trm (map the v) t2"
  by (cases t1; cases t2) (simp_all add: is_simple_eq_def singleton_table_def split: if_splits)

lemma in_eq_rel: "wf_tuple n (Formula.fv_trm t1 \<union> Formula.fv_trm t2) v \<Longrightarrow>
  is_simple_eq t1 t2 \<Longrightarrow>
  Formula.eval_trm (map the v) t1 = Formula.eval_trm (map the v) t2 \<Longrightarrow>
  v \<in> eq_rel n t1 t2"
  by (cases t1; cases t2)
    (auto simp: is_simple_eq_def singleton_table_def wf_tuple_def unit_table_def
      intro!: nth_equalityI split: if_splits)

lemma table_eq_rel: "is_simple_eq t1 t2 \<Longrightarrow>
  table n (Formula.fv_trm t1 \<union> Formula.fv_trm t2) (eq_rel n t1 t2)"
  by (cases t1; cases t2; simp add: is_simple_eq_def)

lemma wf_tuple_in_simple_eq_rel:
  "is_simple_eq t1 t2 \<Longrightarrow> v \<in> eq_rel n t1 t2 \<Longrightarrow> wf_tuple n (fv_trm t1 \<union> fv_trm t2) v"
  by (auto simp: is_simple_eq_def trm.is_Const_def trm.is_Var_def split: if_splits)

lemma in_eq_rel_iff: "\<forall>x\<in>fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>fv_trm t2. x < n \<Longrightarrow> is_simple_eq t1 t2 
  \<Longrightarrow> (v \<in> eq_rel n t1 t2) 
    \<longleftrightarrow> (Formula.eval_trm (map the v) t1 = Formula.eval_trm (map the v) t2  
      \<and> wf_tuple n (fv_trm t1 \<union> fv_trm t2) v)"
  by (intro iffI conjI eq_rel_eval_trm wf_tuple_in_simple_eq_rel; clarsimp?)
    (auto intro: in_eq_rel)

lemma qtable_eq_relI: "\<forall>x\<in>fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>fv_trm t2. x < n \<Longrightarrow> is_simple_eq t1 t2 
  \<Longrightarrow> qtable n (fv_trm t1 \<union> fv_trm t2) (mem_restr U) 
    (\<lambda>v. Formula.eval_trm (map the v) t1 = Formula.eval_trm (map the v) t2) (eq_rel n t1 t2)"
  unfolding qtable_iff
  using in_eq_rel_iff[of t1 n t2]
  by (auto simp: table_def)


subsubsection \<open> Existential \<close>

lemma wf_tuple_Suc_fviD: "wf_tuple (Suc n) (Formula.fvi b \<phi>) v \<Longrightarrow> wf_tuple n (Formula.fvi (Suc b) \<phi>) (tl v)"
  unfolding wf_tuple_def by (simp add: fvi_Suc nth_tl)

lemma table_fvi_tl: "table (Suc n) (Formula.fvi b \<phi>) X \<Longrightarrow> table n (Formula.fvi (Suc b) \<phi>) (tl ` X)"
  unfolding table_def by (auto intro: wf_tuple_Suc_fviD)

lemma wf_tuple_Suc_fvi_SomeI: "0 \<in> Formula.fvi b \<phi> \<Longrightarrow> wf_tuple n (Formula.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (Formula.fvi b \<phi>) (Some x # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma wf_tuple_Suc_fvi_NoneI: "0 \<notin> Formula.fvi b \<phi> \<Longrightarrow> wf_tuple n (Formula.fvi (Suc b) \<phi>) v \<Longrightarrow>
  wf_tuple (Suc n) (Formula.fvi b \<phi>) (None # v)"
  unfolding wf_tuple_def
  by (auto simp: fvi_Suc less_Suc_eq_0_disj)

lemma qtable_project_fv: "qtable (Suc n) (fv \<phi>) (mem_restr (lift_envs R)) P X \<Longrightarrow>
    qtable n (Formula.fvi (Suc 0) \<phi>) (mem_restr R)
      (\<lambda>v. \<exists>x. P ((if 0 \<in> fv \<phi> then Some x else None) # v)) (tl ` X)"
  using neq0_conv by (fastforce simp: image_iff Bex_def fvi_Suc elim!: qtable_cong dest!: qtable_project)


subsubsection \<open> Next and Previous \<close>

lemma mprev_next_NilE[elim!]: "mprev_next I xs ts = (ys, [], []) \<Longrightarrow>
  (xs = [] \<Longrightarrow> ts = [] \<Longrightarrow> ys = [] \<Longrightarrow> R) \<Longrightarrow> R"
  by (induct I xs ts arbitrary: ys rule: mprev_next.induct) (auto split: prod.splits)

lemma mprev: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> i \<le> j' \<Longrightarrow> i \<le> j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then P i X else X = empty_table)
    [i..<min j' (if i = j then j else j-1)] ys \<and>
  list_all2 P [min j' (if i = j then j else j-1)..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min j' (if i = j then j else j-1)..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min j' (if i = j then j else j-1) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min j' (j-1) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
        elim!: list.rel_mono_strong split: prod.splits if_splits)
qed (auto simp: gr0_conv_Suc)

lemma mnext: "mprev_next I xs ts = (ys, xs', ts') \<Longrightarrow>
  list_all2 P [Suc i..<j'] xs \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [i..<j] ts \<Longrightarrow> Suc i \<le> j' \<Longrightarrow> i \<le> j \<Longrightarrow>
  list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then P (Suc i) X else X = empty_table)
    [i..<min (j'-1) ((if i = j then j else j-1))] ys \<and>
  list_all2 P [Suc (min (j'-1) ((if i = j then j else j-1)))..<j'] xs' \<and>
  list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (j'-1) ((if i = j then j else j-1))..<j] ts'"
proof (induction I xs ts arbitrary: i ys xs' ts' rule: mprev_next.induct)
  case (1 I ts)
  then have "min (j' - 1) ((if i = j then j else j-1)) = i" by auto
  with 1 show ?case by auto
next
  case (3 I v v' t)
  then have "min (j' - 1) ((if i = j then j else j-1)) = i" by (auto simp: list_all2_Cons2 upt_eq_Cons_conv)
  with 3 show ?case by auto
next
  case (4 I x xs t t' ts)
  from 4(1)[of "tl ys" xs' ts' "Suc i"] 4(2-6) show ?case
    by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv Suc_less_eq2
        elim!: list.rel_mono_strong split: prod.splits if_splits) (* slow 10 sec *)
qed auto

(*<*)
end
(*>*)