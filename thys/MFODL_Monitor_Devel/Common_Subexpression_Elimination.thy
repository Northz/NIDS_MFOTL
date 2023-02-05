theory Common_Subexpression_Elimination
  imports Safety
begin

lemma size_regex_estimation[termination_simp]: "x \<in> atms r \<Longrightarrow> y < f x \<Longrightarrow> (\<And>x. f x \<le> f (Formula.Neg x)) \<Longrightarrow> y < Regex.size_regex f r"
  apply (induct r)
      apply (auto split: if_splits formula.splits)
  apply (meson less_SucI order_less_le_trans)
  apply (meson less_SucI order_less_le_trans)
  done

lemma size_regex_estimation'[termination_simp]: "x \<in> atms r \<Longrightarrow> y \<le> f x \<Longrightarrow> (\<And>x. f x \<le> f (Formula.Neg x)) \<Longrightarrow> y \<le> Regex.size_regex f r"
  apply (induct r)
      apply (auto split: if_splits formula.splits)
  using order.trans le_Suc_eq apply auto
  done

text \<open>Non-atomic shareable subexpressions\<close>

fun nasub where
  "nasub (Formula.Let p \<phi> \<psi>) = {Formula.Let p \<phi> \<psi>} \<union> nasub \<phi> \<union>
    {\<alpha> \<in> nasub \<psi>. \<not> contains_pred (p, Formula.nfv \<phi>) \<alpha>}"
| "nasub (Formula.LetPast p \<phi> \<psi>) = {Formula.LetPast p \<phi> \<psi>} \<union>
     {\<alpha> \<in> nasub \<phi> \<union> nasub \<psi>. \<not> contains_pred (p, Formula.nfv \<phi>) \<alpha>}"
| "nasub (Formula.Neg \<phi>) = {Formula.Neg \<phi>} \<union> nasub \<phi>"
| "nasub (Formula.Or \<phi> \<psi>) = {Formula.Or \<phi> \<psi>} \<union> nasub \<phi> \<union> nasub \<psi>"
| "nasub (Formula.And \<phi> \<psi>) = {Formula.And \<phi> \<psi>} \<union> nasub \<phi> \<union> 
     (if safe_formula \<psi> then nasub \<psi> else nasub (remove_neg \<psi>))"
| "nasub (Formula.Ands l) = (let
    (pos, neg0) = partition safe_formula l;
    neg = map remove_neg neg0
  in {Formula.Ands l} \<union> (\<Union>\<phi> \<in> set pos \<union> set neg. nasub \<phi>))"
| "nasub (Formula.Exists t \<phi>) = {Formula.Exists t \<phi>} \<union> nasub \<phi>"
| "nasub (Formula.Agg y \<omega> tys f \<phi>) = {Formula.Agg y \<omega> tys f \<phi>} \<union> nasub \<phi>"
| "nasub (Formula.Prev I \<phi>) = {Formula.Prev I \<phi>} \<union> nasub \<phi>"
| "nasub (Formula.Next I \<phi>) = {Formula.Next I \<phi>} \<union> nasub \<phi>"
| "nasub (Formula.Since \<phi> I \<psi>) = {Formula.Since \<phi> I \<psi>} \<union>
     (if safe_formula \<phi> then nasub \<phi> else nasub (remove_neg \<phi>)) \<union> nasub \<psi>"
| "nasub (Formula.Until \<phi> I \<psi>) = {Formula.Until \<phi> I \<psi>} \<union>
     (if safe_formula \<phi> then nasub \<phi> else nasub (remove_neg \<phi>)) \<union> nasub \<psi>"
| "nasub (Formula.MatchP I r) = {Formula.MatchP I r} \<union> (\<Union>\<phi> \<in> atms r. nasub \<phi>)"
| "nasub (Formula.MatchF I r) = {Formula.MatchF I r} \<union> (\<Union>\<phi> \<in> atms r. nasub \<phi>)"
| "nasub \<phi> = {}"

fun cse where
  "cse (Formula.Let p \<phi> \<psi>) = undefined"
| "cse (Formula.LetPast p \<phi> \<psi>) = undefined"
| "cse (Formula.Neg \<phi>) = Formula.Neg (cse \<phi>)"
| "cse (Formula.Or \<phi> \<psi>) = undefined"
| "cse (Formula.And \<phi> \<psi>) = undefined"
| "cse (Formula.Ands l) = undefined"
| "cse (Formula.Exists t \<phi>) = Formula.Exists t (cse \<phi>)"
| "cse (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (cse \<phi>)"
| "cse (Formula.Prev I \<phi>) = Formula.Prev I (cse \<phi>)"
| "cse (Formula.Next I \<phi>) = Formula.Next I (cse \<phi>)"
| "cse (Formula.Since \<phi> I \<psi>) = undefined"
| "cse (Formula.Until \<phi> I \<psi>) = undefined"
| "cse (Formula.MatchP I r) = undefined"
| "cse (Formula.MatchF I r) = undefined"
| "cse \<phi> = \<phi>"

end