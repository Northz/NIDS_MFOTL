(*<*)
theory Trigger_Release_Rewrites
  imports
    Event_Data
    Formula
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
begin
(*>*)





(* verify that the derived rewrite formulas are safe *)

(* this would be the safety in full generality (for the current implementation).
  for simplicity safe_assignment, is_contraint and nested triggers
   are currently disallowed
*)
definition safe_formula_dual' where "
  safe_formula_dual' b \<phi> I \<psi> = (if (mem I 0) then
    (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> (
      safe_formula \<phi> \<or> safe_assignment (fv \<psi>) \<phi> \<or> is_constraint \<phi> \<or>
      (case \<phi> of formula.Neg x \<Rightarrow> safe_formula x | formula.Trigger x xa xb \<Rightarrow> safe_formula_dual True safe_formula x xa xb
        | _ \<Rightarrow> False)
    ))
      else
    b \<and> (safe_formula \<phi> \<and> safe_formula \<psi> \<and> fv \<phi> = fv \<psi>))
"

(* trigger *)

(* [0, b] *)
lemma
  assumes "safe_formula (Formula.Trigger \<phi> I \<psi>)"
  shows "safe_formula (trigger_safe_0 \<phi> I \<psi>)"
  using assms
  by (auto simp add: trigger_safe_0_def safe_formula_dual_def split: if_splits)
     (auto split: formula.splits)

lemma "mem I 0 \<Longrightarrow>
  safe_formula_dual' False \<phi> I \<psi> = safe_formula (trigger_safe_0 \<phi> I \<psi>)"
  by (auto simp add: trigger_safe_0_def safe_formula_dual'_def split: if_splits)


lemma "Formula.future_bounded (trigger_safe_0 \<phi> I \<psi>) = (Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: trigger_safe_0_def)

(* [a, \<infinity>] *)

lemma
  assumes "safe_formula_dual True safe_formula \<phi> I \<psi>"
  assumes "\<not> mem I 0"
  shows "safe_formula (trigger_safe_unbounded \<phi> I \<psi>)"
  using assms
  by (auto simp add: trigger_safe_unbounded_def once_def historically_safe_unbounded_def safe_formula_dual_def)

lemma "Formula.future_bounded (trigger_safe_unbounded \<phi> I \<psi>) = (Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: trigger_safe_unbounded_def)

(* release *)

(* [0, b] *)

lemma "mem I 0 \<Longrightarrow>
  safe_formula_dual' False \<phi> I \<psi> = safe_formula (release_safe_0 \<phi> I \<psi>)"
  by (auto simp add: release_safe_0_def safe_formula_dual'_def split: if_splits)

lemma "Formula.future_bounded (release_safe_0 \<phi> I \<psi>) = (bounded I \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: release_safe_0_def)

(* [a, b] *)





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
  assumes "\<forall>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  shows "\<forall>b. Formula.fvi b (map_formula f \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi>) qed (auto simp add: assms release_safe_0_def always_safe_0_def)


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
      case \<phi> of (Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))) \<Rightarrow> (
        if I = I' \<and> v1 = 0 \<and> v2 = 0 \<and> v3 = 0 \<and> v4 = 0 then
          if (bounded I) then
            trigger_safe_bounded \<alpha> I \<beta>
          else
            trigger_safe_unbounded \<alpha> I \<beta>
        else
          Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)
        )
      | _ \<Rightarrow> Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)
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
      then show ?thesis
        proof (cases "case \<phi> of (Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))) \<Rightarrow> True | _ \<Rightarrow> False")
          case True
          then obtain v1 v2 v3 v4 I' where \<phi>_eq:
            "\<phi> = Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))"
            by (auto split: formula.splits trm.splits)
          show ?thesis
          proof (cases "I = I' \<and> v1 = 0 \<and> v2 = 0 \<and> v3 = 0 \<and> v4 = 0")
            case var_eqs: True
            then have \<phi>_eq': "\<phi> = once I Formula.TT"
              unfolding \<phi>_eq once_def Formula.TT_def Formula.FF_def
              by auto
            show ?thesis
            proof (cases "bounded I")
              case True
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_bounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                by auto
            next
              case False
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_unbounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                by auto
            qed
          next
            case False
            then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
              using not_mem
              unfolding Trigger \<phi>_eq rewrite_trigger.simps
              by auto
            then show ?thesis
              unfolding And Trigger
              by auto
          qed
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
          using not_mem
          unfolding Trigger rewrite_trigger.simps
          by (auto split: formula.splits trm.splits)
        then show ?thesis
          unfolding And Trigger
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
      then show ?thesis
        proof (cases "case \<phi> of (Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))) \<Rightarrow> True | _ \<Rightarrow> False")
          case True
          then obtain v1 v2 v3 v4 I' where \<phi>_eq:
            "\<phi> = Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))"
            by (auto split: formula.splits trm.splits)
          show ?thesis
          proof (cases "I = I' \<and> v1 = 0 \<and> v2 = 0 \<and> v3 = 0 \<and> v4 = 0")
            case var_eqs: True
            then have \<phi>_eq': "\<phi> = once I Formula.TT"
              unfolding \<phi>_eq once_def Formula.TT_def Formula.FF_def
              by auto
            show ?thesis
            proof (cases "bounded I")
              case True
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_bounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                using sat_trigger_rewrite_bounded[OF not_mem True]
                by auto
            next
              case False
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_unbounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                using sat_trigger_rewrite_unbounded[OF not_mem False]
                by auto
            qed
          next
            case False
            then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
              using not_mem
              unfolding Trigger \<phi>_eq rewrite_trigger.simps
              by auto
            then show ?thesis
              unfolding And Trigger
              by auto
          qed
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
          using not_mem
          unfolding Trigger rewrite_trigger.simps
          by (auto split: formula.splits trm.splits)
        then show ?thesis
          unfolding And Trigger
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


thm map_formula_sat[OF rewrite_trigger_fvi rewrite_trigger_sat]