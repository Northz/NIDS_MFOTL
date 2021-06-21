(*<*)
theory Trigger_Release_Rewrites
  imports
    Event_Data
    Formula
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
begin
(*>*)


fun map_formula :: "(Formula.formula \<Rightarrow> Formula.formula) \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula" where
  "map_formula f (Formula.Pred r ts) = f (Formula.Pred r ts)"
| "map_formula f (Formula.Let p \<phi> \<psi>) = f (
    Formula.Let p (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Eq t1 t2) = f (Formula.Eq t1 t2)"
| "map_formula f (Formula.Less t1 t2) = f (Formula.Less t1 t2)"
| "map_formula f (Formula.LessEq t1 t2) = f (Formula.LessEq t1 t2)"
| "map_formula f (Formula.Neg \<phi>) = f (Formula.Neg (map_formula f \<phi>))"
| "map_formula f (Formula.Or \<phi> \<psi>) = f (
    Formula.Or (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.And \<phi> \<psi>) = f (
    Formula.And (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Ands \<phi>s) = f (
    Formula.Ands (map (map_formula f) \<phi>s)
  )"
| "map_formula f (Formula.Exists \<phi>) = f (Formula.Exists (map_formula f \<phi>))"
| "map_formula f (Formula.Agg y \<omega> b f' \<phi>) = f (
    Formula.Agg y \<omega> b f' (map_formula f \<phi>)
  )"
| "map_formula f (Formula.Prev I \<phi>) = f (Formula.Prev I (map_formula f \<phi>))"
| "map_formula f (Formula.Next I \<phi>) = f (Formula.Next I (map_formula f \<phi>))"
| "map_formula f (Formula.Since \<phi> I \<psi>) = f (
    Formula.Since (map_formula f \<phi>) I ( map_formula f \<psi>)
  )"
| "map_formula f (Formula.Until \<phi> I \<psi>) = f (
    Formula.Until (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Trigger \<phi> I \<psi>) = f (
    Formula.Trigger (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Release \<phi> I \<psi>) = f (
    Formula.Release (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.MatchF I r) = f (Formula.MatchF I r)"
| "map_formula f (Formula.MatchP I r) = f (Formula.MatchP I r)"

lemma map_formula_fvi:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  shows "Formula.fvi b (map_formula f \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi> arbitrary: b) qed (auto simp add: assms release_safe_0_def always_safe_0_def fvi.simps(17))

(*lemma map_formula_safe:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  assumes "\<And>\<phi>. safe_formula (f \<phi>) = safe_formula \<phi>"
  assumes "\<And>\<phi>. \<not>safe_formula \<phi> \<Longrightarrow> f \<phi> = \<phi>"
  shows "safe_formula (map_formula f \<phi>) = safe_formula \<phi>"
proof (induction \<phi> rule: safe_formula.induct)
  case (6 p \<phi> \<psi>)
  then show ?case by (auto simp add: map_formula_fvi[OF assms(1)] assms(2-3))
next
  case ("7_1" v va)
  then show ?case
    using map_formula_fvi[OF assms(1)] assms
    sorry
    
next
  case ("7_2" v va vb)
  then show ?case sorry
next
  case ("7_3" vb va)
  then show ?case sorry
next
  case ("7_4" vb vc va)
  then show ?case sorry
next
  case ("7_5" vb vc va)
  then show ?case sorry
next
  case ("7_6" vb va)
  then show ?case sorry
next
  case ("7_7" vb vc va)
  then show ?case sorry
next
  case ("7_8" vb vc va)
  then show ?case sorry
next
  case ("7_9" vb vc va)
  then show ?case sorry
next
  case ("7_10" vb va)
  then show ?case sorry
next
  case ("7_11" vb va)
  then show ?case sorry
next
  case ("7_12" v vb)
  then show ?case sorry
next
  case ("7_13" v vb vc)
  then show ?case sorry
next
  case ("7_14" v vb vc)
then show ?case sorry
next
  case ("7_15" v vb)
  then show ?case sorry
next
  case ("7_16" v vb vc)
  then show ?case sorry
next
  case ("7_17" v vb vc)
  then show ?case sorry
next
  case ("7_18" v vb vc)
  then show ?case sorry
next
  case ("7_19" v vb)
  then show ?case sorry
next
  case ("7_20" v vb)
  then show ?case sorry
next
  case ("7_21" v va)
  then show ?case sorry
next
  case ("7_22" v va)
  then show ?case sorry
next
  case ("7_23" v)
  then show ?case sorry
next
  case ("7_24" v va)
  then show ?case sorry
next
  case ("7_25" v va)
  then show ?case sorry
next
  case ("7_26" v)
  then show ?case sorry
next
  case ("7_27" v)
  then show ?case sorry
next
  case ("7_28" v va vb vc vd)
  then show ?case sorry
next
  case ("7_29" v va)
  then show ?case sorry
next
  case ("7_30" v va)
  then show ?case sorry
next
  case ("7_31" v va vb)
  then show ?case sorry
next
  case ("7_32" v va vb)
  then show ?case sorry
next
  case ("7_33" v va vb)
  then show ?case sorry
next
  case ("7_34" v va vb)
  then show ?case sorry
next
  case ("7_35" v va)
  then show ?case sorry
next
  case ("7_36" v va)
  then show ?case sorry
next
  case (8 \<phi> \<psi>)
  then show ?case sorry
next
  case (9 \<phi> \<psi>)
  then show ?case sorry
next
  case (10 l)
  then show ?case sorry
next
  case (11 \<phi>)
  then show ?case sorry
next
  case (12 y \<omega> b f \<phi>)
  then show ?case sorry
next
  case (13 I \<phi>)
  then show ?case sorry
next
  case (14 I \<phi>)
  then show ?case sorry
next
  case (15 \<phi> I \<psi>)
  then show ?case sorry
next
  case (16 \<phi> I \<psi>)
  then show ?case sorry
next
  case (17 \<phi> I \<psi>)
  then show ?case sorry
next
  case (18 \<phi> I \<psi>)
  then show ?case sorry

qed (auto simp add: map_formula_fvi[OF assms(1)] assms(2-3))*)
 

lemma map_formula_sat:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  assumes "\<And>\<sigma> V v i \<phi>. Formula.sat \<sigma> V v i (f \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  shows "\<And>\<sigma> V v i. Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (map_formula f \<phi>)"
using assms proof (induction \<phi>)
  case assm: (Let p \<phi>' \<psi>')
  from assms have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
    using Formula.nfv_def map_formula_fvi
    by auto
  {
    fix \<sigma> V v i
    have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi>' \<and> Formula.sat \<sigma> V v i \<phi>'})) v i \<psi>'"
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi>' \<and> Formula.sat \<sigma> V v i \<phi>'})) v i (map_formula f \<psi>')"
      using assm
      by blast
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Let p \<phi>' \<psi>'))"
      using assm nfv_eq assms
      by auto
  }
  then show ?case by blast
next
  case assm: (Agg y \<omega> b f' \<phi>')
  {
    fix \<sigma> V v i
    define M where "M = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = b \<and>
        Formula.sat \<sigma> V (zs @ v) i \<phi>' \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    define M' where "M' = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = b \<and>
        Formula.sat \<sigma> V (zs @ v) i (map_formula f \<phi>') \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    have M_eq: "M = M'" using M_def M'_def assm by auto
    have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
      using assms Formula.nfv_def map_formula_fvi
      by auto
    have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = (
      (M = {} \<longrightarrow> fv \<phi>' \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M
    )"
      using M_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = (
      (M' = {} \<longrightarrow> fv (map_formula f \<phi>') \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M')"
      using assms assm M_eq nfv_eq map_formula_fvi
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' (map_formula f \<phi>'))"
      using M'_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Agg y \<omega> b f' \<phi>'))"
      using assms by auto
  }
  then show ?case by blast
qed (auto split: nat.split)


fun rewrite_trigger :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite_trigger (Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)) = (
    if (mem I 0) then
      \<comment> \<open>the rewrite function already was applied recursively, hence the trigger should already be rewritten\<close>
      Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)
    else (
      if (bounded I) then
        and_trigger_safe_bounded \<phi> \<alpha> I \<beta>
      else
        and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>
    )
  )"
| "rewrite_trigger (Formula.Trigger \<alpha> I \<beta>) = (
    if (mem I 0) then
      trigger_safe_0 \<alpha> I \<beta>
    else (
      Formula.Trigger \<alpha> I \<beta>
    )
  )"
| "rewrite_trigger f = f"

lemma historically_safe_0_fvi[simp]: "Formula.fvi b (historically_safe_0 I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_0_def split: if_splits)

lemma historically_safe_unbounded_fvi[simp]: "Formula.fvi b (historically_safe_unbounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_bounded_fvi[simp]: "Formula.fvi b (historically_safe_bounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma trigger_safe_0_fvi[simp]: "Formula.fvi b (trigger_safe_0 \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_0_def split: if_splits)

lemma trigger_safe_unbounded_fvi[simp]: "Formula.fvi b (trigger_safe_unbounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_unbounded_def)

lemma trigger_safe_bounded_fvi[simp]: "Formula.fvi b (trigger_safe_bounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_bounded_def)

lemma rewrite_trigger_fvi[simp]: "Formula.fvi b (rewrite_trigger \<phi>) = Formula.fvi b \<phi>"
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And
        using Trigger
        by auto
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          unfolding and_trigger_safe_bounded_def once_def trigger_safe_bounded_def eventually_def historically_safe_bounded_def Formula.TT_def Formula.FF_def
          by auto
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          unfolding and_trigger_safe_unbounded_def once_def trigger_safe_unbounded_def eventually_def historically_safe_unbounded_def Formula.TT_def Formula.FF_def
          by auto
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      unfolding Trigger rewrite
      using trigger_safe_0_fvi[of b \<alpha> I \<beta>]
      by auto
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis unfolding Trigger by auto
  qed
qed (auto)

lemma rewrite_trigger_sat[simp]: "Formula.sat \<sigma> V v i (rewrite_trigger \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And Trigger
        by auto
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          using sat_and_trigger_bounded_rewrite[OF True not_mem]
          by auto
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          using sat_and_trigger_unbounded_rewrite[OF False not_mem]
          by auto
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      unfolding Trigger rewrite
      using sat_trigger_rewrite_0[OF True]
      by auto
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis unfolding Trigger by auto
  qed
qed (auto)

lemma trigger_not_safe_assignment: "\<not> safe_assignment (fv \<phi>) (formula.Trigger \<alpha> I \<beta>)"
  unfolding safe_assignment_def
  by auto

lemma rewrite_trigger_safe_formula[simp]: 
  assumes safe: "safe_formula \<phi>"
  shows "safe_formula (rewrite_trigger \<phi>)"
using assms
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  using assms
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        using safe Trigger trigger_not_safe_assignment
        unfolding And
        by (auto split: if_splits simp add: safe_formula_dual_def)
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          using safe trigger_not_safe_assignment
          unfolding And Trigger and_trigger_safe_bounded_def trigger_safe_bounded_def
          by (auto split: if_splits simp add: safe_formula_dual_def)
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          using safe trigger_not_safe_assignment
          unfolding And Trigger and_trigger_safe_unbounded_def trigger_safe_unbounded_def
          by (auto split: if_splits simp add: safe_formula_dual_def)
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      using safe
      unfolding Trigger rewrite trigger_safe_0_def
      by (auto simp add: safe_formula_dual_def split: if_splits) (auto split: formula.splits)
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis
      using safe
      unfolding Trigger
      by auto
  qed
qed (auto)

definition new_string :: "string set \<Rightarrow> string" where
  "new_string s = undefined"

lemma new_string_sound: "finite X \<Longrightarrow> new_string X \<notin> X"
  sorry

thm rewrite_trigger_fvi rewrite_trigger_sat rewrite_trigger_safe_formula

end
