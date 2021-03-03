(*<*)
theory Formula
  imports
    Event_Data
    Regex
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
    "MFOTL_Monitor_Devel.Abstract_Monitor"
    "HOL-Library.Mapping"
    Containers.Set_Impl
begin
(*>*)

section \<open>Metric first-order dynamic logic\<close>

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

context begin

subsection \<open>Formulas and satisfiability\<close>

qualified type_synonym name = string8
qualified type_synonym event = "(name \<times> event_data list)"
qualified type_synonym database = "(name, event_data list set list) mapping"
qualified type_synonym prefix = "(name \<times> event_data list) prefix"
qualified type_synonym trace = "(name \<times> event_data list) trace"

qualified type_synonym env = "event_data list"

subsubsection \<open>Syntax\<close>

qualified datatype trm = is_Var: Var nat | is_Const: Const event_data
  | Plus trm trm | Minus trm trm | UMinus trm | Mult trm trm | Div trm trm | Mod trm trm
  | F2i trm | I2f trm

qualified primrec fvi_trm :: "nat \<Rightarrow> trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"
| "fvi_trm b (Plus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Minus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (UMinus x) = fvi_trm b x"
| "fvi_trm b (Mult x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Div x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Mod x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (F2i x) = fvi_trm b x"
| "fvi_trm b (I2f x) = fvi_trm b x"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "env \<Rightarrow> trm \<Rightarrow> event_data" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"
| "eval_trm v (Plus x y) = eval_trm v x + eval_trm v y"
| "eval_trm v (Minus x y) = eval_trm v x - eval_trm v y"
| "eval_trm v (UMinus x) = - eval_trm v x"
| "eval_trm v (Mult x y) = eval_trm v x * eval_trm v y"
| "eval_trm v (Div x y) = eval_trm v x div eval_trm v y"
| "eval_trm v (Mod x y) = eval_trm v x mod eval_trm v y"
| "eval_trm v (F2i x) = EInt (integer_of_event_data (eval_trm v x))"
| "eval_trm v (I2f x) = EFloat (double_of_event_data (eval_trm v x))"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (induction t) simp_all


qualified datatype agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
qualified type_synonym agg_op = "agg_type \<times> event_data"

definition flatten_multiset :: "(event_data \<times> enat) set \<Rightarrow> event_data list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x) (csorted_list_of_set M))"

fun eval_agg_op :: "agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op (Agg_Cnt, y0) M = EInt (integer_of_int (length (flatten_multiset M)))"
| "eval_agg_op (Agg_Min, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl min x xs)"
| "eval_agg_op (Agg_Max, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl max x xs)"
| "eval_agg_op (Agg_Sum, y0) M = foldl plus y0 (flatten_multiset M)"
| "eval_agg_op (Agg_Avg, y0) M = EFloat (let xs = flatten_multiset M in case xs of
      [] \<Rightarrow> 0
    | _ \<Rightarrow> double_of_event_data (foldl plus (EInt 0) xs) / double_of_int (length xs))"
| "eval_agg_op (Agg_Med, y0) M = EFloat (let xs = flatten_multiset M; u = length xs in
    if u = 0 then 0 else
      let u' = u div 2 in
      if even u then
        (double_of_event_data (xs ! (u'-1)) + double_of_event_data (xs ! u') / double_of_int 2)
      else double_of_event_data (xs ! u'))"

qualified datatype (discs_sels) formula = Pred name "trm list"
  | Let name formula formula
  | Eq trm trm | Less trm trm | LessEq trm trm
  | Neg formula | Or formula formula | And formula formula | Ands "formula list" | Exists formula
  | Agg nat agg_op nat trm formula
  | Prev \<I> formula | Next \<I> formula
  | Since formula \<I> formula | Until formula \<I> formula
  | Trigger formula \<I> formula | Release formula \<I> formula
  | MatchF \<I> "formula Regex.regex" | MatchP \<I> "formula Regex.regex"

qualified definition "FF = Exists (Neg (Eq (Var 0) (Var 0)))"
qualified definition "TT \<equiv> Neg FF"

qualified fun fvi :: "nat \<Rightarrow> formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Let p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Less t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (LessEq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> b' f \<phi>) = fvi (b + b') \<phi> \<union> fvi_trm (b + b') f \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Trigger \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Release \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"

abbreviation "fv \<equiv> fvi 0"
abbreviation "fv_regex \<equiv> Regex.fv_regex fv"

lemma fv_abbrevs[simp]: "fv TT = {}" "fv FF = {}"
  unfolding TT_def FF_def by auto

lemma fv_subset_Ands: "\<phi> \<in> set \<phi>s \<Longrightarrow> fv \<phi> \<subseteq> fv (Ands \<phi>s)"
  by auto

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (induction t) simp_all

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> b' f \<phi>)
  have *: "b + c + b' = b + b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  using fvi_plus[where c=1] by simp

lemma fvi_plus_bound:
  assumes "\<forall>i\<in>fvi (b + c) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < c + n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  show "i < c + n"
  proof (cases "i < c")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain i' where "i = i' + c"
      using nat_le_iff_add by (auto simp: not_less)
    with assms \<open>i \<in> fvi b \<phi>\<close> show ?thesis by (simp add: fvi_plus)
  qed
qed

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
  using assms fvi_plus_bound[where c=1] by simp

lemma fvi_iff_fv: "x \<in> fvi b \<phi> \<longleftrightarrow> x + b \<in> fv \<phi>"
  using fvi_plus[where b=0 and c=b] by simp_all

qualified definition nfv :: "formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "formula \<Rightarrow> env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Let p \<phi> \<psi>) = nfv \<psi>"
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = Regex.nfv_regex fv r"
  "nfv (MatchF I r) = Regex.nfv_regex fv r"
  "nfv_regex (Regex.Skip n) = 0"
  "nfv_regex (Regex.Test \<phi>) = Max (insert 0 (Suc ` fv \<phi>))"
  "nfv_regex (Regex.Plus r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Times r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Star r) = nfv_regex r"
  unfolding nfv_def Regex.nfv_regex_def by (simp_all add: image_Un Max_Un[symmetric])

lemma nfv_Ands[simp]: "nfv (Ands l) = Max (insert 0 (nfv ` set l))"
proof (induction l)
  case Nil
  then show ?case unfolding nfv_def by simp
next
  case (Cons a l)
  have "fv (Ands (a # l)) = fv a \<union> fv (Ands l)" by simp
  then have "nfv (Ands (a # l)) = max (nfv a) (nfv (Ands l))"
    unfolding nfv_def
    by (auto simp: image_Un Max.union[symmetric])
  with Cons.IH show ?case
    by (cases l) auto
qed

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

lemma fvi_less_nfv_regex: "\<forall>i\<in>fv_regex \<phi>. i < nfv_regex \<phi>"
  unfolding Regex.nfv_regex_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

subsubsection \<open>Future reach\<close>

qualified fun future_bounded :: "formula \<Rightarrow> bool" where
  "future_bounded (Pred _ _) = True"
| "future_bounded (Let p \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Eq _ _) = True"
| "future_bounded (Less _ _) = True"
| "future_bounded (LessEq _ _) = True"
| "future_bounded (Neg \<phi>) = future_bounded \<phi>"
| "future_bounded (Or \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (And \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Ands l) = list_all future_bounded l"
| "future_bounded (Exists \<phi>) = future_bounded \<phi>"
| "future_bounded (Agg y \<omega> b f \<phi>) = future_bounded \<phi>"
| "future_bounded (Prev I \<phi>) = future_bounded \<phi>"
| "future_bounded (Next I \<phi>) = future_bounded \<phi>"
| "future_bounded (Since \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Until \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (Trigger \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Release \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (MatchP I r) = Regex.pred_regex future_bounded r"
| "future_bounded (MatchF I r) = (Regex.pred_regex future_bounded r \<and> bounded I)"


subsubsection \<open>Semantics\<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

qualified fun sat :: "trace \<Rightarrow> (name \<rightharpoonup> nat \<Rightarrow> event_data list set) \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" where
  "sat \<sigma> V v i (Pred r ts) = (case V r of
       None \<Rightarrow> (r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> map (eval_trm v) ts \<in> X i)"
| "sat \<sigma> V v i (Let p \<phi> \<psi>) =
    sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = nfv \<phi> \<and> sat \<sigma> V v i \<phi>})) v i \<psi>"
| "sat \<sigma> V v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> V v i (Less t1 t2) = (eval_trm v t1 < eval_trm v t2)"
| "sat \<sigma> V v i (LessEq t1 t2) = (eval_trm v t1 \<le> eval_trm v t2)"
| "sat \<sigma> V v i (Neg \<phi>) = (\<not> sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Or \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<or> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (And \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Exists \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
| "sat \<sigma> V v i (Agg y \<omega> b f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
| "sat \<sigma> V v i (Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> V v (Suc i) \<phi>)"
| "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = (\<forall>j\<le>i. (mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (Release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> V v) r j i)"
| "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> V v) r i j)"

lemma sat_abbrevs[simp]:
  "sat \<sigma> V v i TT" "\<not> sat \<sigma> V v i FF"
  unfolding TT_def FF_def by auto

lemma sat_Ands: "sat \<sigma> V v i (Ands l) \<longleftrightarrow> (\<forall>\<phi>\<in>set l. sat \<sigma> V v i \<phi>)"
  by (simp add: list_all_iff)

lemma sat_Until_rec: "sat \<sigma> V v i (Until \<phi> I \<psi>) \<longleftrightarrow>
  memL I 0 \<and> sat \<sigma> V v i \<psi> \<or>
  (memR I (\<Delta> \<sigma> (i + 1)) \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "memR I (\<Delta> \<sigma> (i + 1))"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
      by (auto intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "memR I (\<Delta> \<sigma> (i + 1))" and now: "sat \<sigma> V v i \<phi>" and
   "next": "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  from "next" obtain j where j: "i + 1 \<le> j" "mem ((subtract (\<Delta> \<sigma> (i + 1)) I)) (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1))"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i + 1 ..< j}. sat \<sigma> V v k \<phi>"
    by (auto simp: diff_le_mono memL_mono)
  from \<Delta> j(1,2) have "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    by auto
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem I 0 \<and> sat \<sigma> V v i \<psi> \<or>
  (i > 0 \<and> memR I (\<Delta> \<sigma> i) \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "memR I (\<Delta> \<sigma> i)"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
      by (auto intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "memR I (\<Delta> \<sigma> i)" and now: "sat \<sigma> V v i \<phi>" and
   "prev": "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (subtract (\<Delta> \<sigma> i) I) (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j)"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i - 1}. sat \<sigma> V v k \<phi>"
    by (auto simp: diff_le_mono2 memL_mono)
  from \<Delta> i j(1,2) have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    by auto
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_MatchF_rec: "sat \<sigma> V v i (MatchF I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  memR I (\<Delta> \<sigma> (i + 1)) \<and> (\<exists>s \<in> Regex.lpd (sat \<sigma> V v) i r. sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" and "Regex.match (sat \<sigma> V v) r i j" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "i < j")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r i j\<close> lpd_match[of i j "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.lpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s (i + 1) j" by auto
    with True j have ?R2
      by (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans[rotated])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "memR I (\<Delta> \<sigma> (i + 1))"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.lpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s)"
  then obtain j where "j > i" "Regex.match (sat \<sigma> V v) s (i + 1) j"
    "mem (subtract (\<Delta> \<sigma> (i + 1)) I) (\<tau> \<sigma> j - \<tau> \<sigma> (Suc i))"
    by (auto simp: diff_le_mono memL_mono Suc_le_eq)
  ultimately show ?L
    by (auto simp: le_diff_conv lpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_MatchP_rec: "sat \<sigma> V v i (MatchP I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  i > 0 \<and> memR I (\<Delta> \<sigma> i) \<and> (\<exists>s \<in> Regex.rpd (sat \<sigma> V v) i r. sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" and "Regex.match (sat \<sigma> V v) r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r j i\<close> rpd_match[of j i "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.rpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s j (i - 1)" by auto
    with True j have ?R2
      by (auto simp: diff_le_mono2 intro!: exI[of _ j])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "memR I (\<Delta> \<sigma> i)"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.rpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "Regex.match (sat \<sigma> V v) s j (i - 1)"
    "mem (subtract (\<Delta> \<sigma> i) I) (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (auto simp: rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_Since_0: "sat \<sigma> V v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> memL I 0 \<and> sat \<sigma> V v 0 \<psi>"
  by auto

lemma sat_MatchP_0: "sat \<sigma> V v 0 (MatchP I r) \<longleftrightarrow> memL I 0 \<and> Regex.eps (sat \<sigma> V v) 0 r"
  by (auto simp: eps_match)

lemma sat_Since_point: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow> sat \<sigma> V v i (Since \<phi> (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi>) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_MatchP_point: "sat \<sigma> V v i (MatchP I r) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow> sat \<sigma> V v i (MatchP (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) r) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "sat \<sigma> V v i (Since \<phi> (point t) \<psi>) \<Longrightarrow> mem I t \<Longrightarrow> sat \<sigma> V v i (Since \<phi> I \<psi>)"
  by auto

lemma sat_MatchP_pointD: "sat \<sigma> V v i (MatchP (point t) r) \<Longrightarrow> mem I t \<Longrightarrow> sat \<sigma> V v i (MatchP I r)"
  by auto

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
proof (induct \<phi> arbitrary: V v v' i rule: formula.induct)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]] split: option.splits)
next
  case (Let p b \<phi> \<psi>)
  then show ?case
    by auto
next
  case (Eq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Less x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (LessEq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case using sat_Ands by blast
next
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> V (zs @ v) i \<phi> = sat \<sigma> V (zs @ v') i \<phi>" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  moreover have "eval_trm (zs @ v) f = eval_trm (zs @ v') f" if "length zs = b" for zs
    using that Agg.prems by (auto intro!: eval_trm_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        simp: nth_append fvi_iff_fv(1)[where b=b] fvi_trm_iff_fv_trm[where b="length zs"])
  ultimately show ?case
    by (simp cong: conj_cong)
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (Trigger \<phi> I \<psi>)
  show ?case
    using Trigger(1, 2)[of v v'] Trigger(3)
    by auto
next
  case (Release \<phi> I \<psi>)
  show ?case
    using Release(1, 2)[of v v'] Release(3)
    by auto
qed (auto 10 0 split: nat.splits intro!: iff_exI)

lemma match_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
  by (rule match_fv_cong, rule sat_fv_cong) (auto simp: fv_regex_alt)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.eps (sat \<sigma> V v) i r = Regex.eps (sat \<sigma> V v') i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])

subsubsection \<open>Trigger / Release\<close>


lemma interval_geq:
  fixes i j :: nat
  assumes "memL I a"
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
  assumes "j \<le> k"
  assumes "a \<le> (\<tau> \<sigma> i - \<tau> \<sigma> k)"
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  from assms(3) assms(4) have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" by auto
  then have "(\<tau> \<sigma> i - \<tau> \<sigma> j) \<ge> (\<tau> \<sigma> i - \<tau> \<sigma> k)" by linarith
  then have "memR I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    using assms(1) assms(2) assms(4)
    by auto
  thus ?thesis by auto
qed

lemma interval_leq:
  fixes i j :: nat
  assumes "memL I a"
  assumes "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  assumes "k \<le> j"
  assumes "a \<le> (\<tau> \<sigma> k - \<tau> \<sigma> i)"
  shows "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
proof -
  from assms(3) assms(4) have "\<tau> \<sigma> j \<ge> \<tau> \<sigma> k" by auto
  then have "(\<tau> \<sigma> j - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> k - \<tau> \<sigma> i)" by linarith
  with assms(1) assms(2) assms(4) have "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> memL I (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
  thus ?thesis by auto
qed

lemma "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Since (Neg \<phi>) I (Neg \<psi>)))"
  by auto

definition once :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "once I \<phi> = Since TT I \<phi>"

lemma sat_once[simp] : "sat \<sigma> V v i (once I \<phi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: once_def)

definition historically :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically I \<phi> = (Neg (once I (Neg \<phi>)))"

lemma sat_historically[simp] : "sat \<sigma> V v i (historically I \<phi>) = (\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  by (auto simp: historically_def)

definition sometimes :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "sometimes I \<phi> = Until TT I \<phi>"

lemma sat_sometimes[simp] : "sat \<sigma> V v i (sometimes I \<phi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: sometimes_def)

definition always :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "always I \<phi> = (Neg (sometimes I (Neg \<phi>)))"

lemma sat_always[simp] : "sat \<sigma> V v i (always I \<phi>) = (\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  by (auto simp: always_def)

lemma interval_all: "mem all i"
proof -               
  have "memL = fst o Rep_\<I>" using memL_def map_fun_def[of Rep_\<I> id fst] by auto
  then have "memL all = fst (Rep_\<I> all)" using comp_apply[of fst Rep_\<I> all] by auto
  then have memL: "memL all = (\<lambda>_. True)" using Interval.all.rep_eq by simp

  have "memR = (fst o snd) o Rep_\<I>" using memR_def map_fun_def[of Rep_\<I> id "fst o snd"] by auto
  then have "memR all = (fst o snd) (Rep_\<I> all)" using comp_apply[of "fst o snd" Rep_\<I> all] by auto
  then have memR: "memR all = (\<lambda>_. True)" using Interval.all.rep_eq by simp

  show ?thesis using memL memR by auto
qed

definition "first = Neg (Prev all TT)"

lemma first_sat[simp] : "sat \<sigma> V v i first = (i=0)"
  using interval_all by (auto simp: first_def split: nat.split)

lemma interval_bounds:
  fixes a:: nat
  fixes b:: enat
  fixes I::\<I>
  assumes "a \<le> b"
  assumes "I = interval a b"
  shows "memL I = (\<lambda>i. a \<le> i) \<and> memR I = (\<lambda>i. enat i \<le> b) \<and> (bounded I = (b \<noteq> \<infinity>))"
  using assms
  by transfer auto

lift_definition flip_int :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if bounded I then ((\<lambda>i. \<not>memR I i), (\<lambda>i. True), False) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

lift_definition flip_int_less_lower :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if \<not>memL I 0 then ((\<lambda>i. True), (\<lambda>i. \<not>memL I i), True) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

lift_definition int_remove_lower_bound :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. ((\<lambda>i. True), (\<lambda>i. memR I i), bounded I)"
  by transfer (auto simp: upclosed_def downclosed_def)

lemma interval_unbounded_leq:
  assumes "j \<le> i" "k \<le> j"
  assumes "\<not> bounded I" (* [a, \<infinity>] *)
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" (* if j\<le>i is part of the interval, then so is k\<le>j\<le>i *)
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  have "\<tau> \<sigma> j \<ge> \<tau> \<sigma> k" using assms by auto
  then have "\<tau> \<sigma> i - \<tau> \<sigma> j \<le> \<tau> \<sigma> i - \<tau> \<sigma> k" by linarith
  then have "memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms
    by auto
  then show ?thesis using bounded_memR assms by auto
qed

lemma interval_unbounded_geq:
  assumes "i \<le> j" "j \<le> k"
  assumes "\<not> bounded I" (* [a, \<infinity>] *)
  assumes "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" (* if j\<le>i is part of the interval, then so is k\<le>j\<le>i *)
  shows "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" using assms by auto
  then have "\<tau> \<sigma> j - \<tau> \<sigma> i \<le> \<tau> \<sigma> k - \<tau> \<sigma> i" by linarith
  then have "memL I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using assms
    by auto
  then show ?thesis using bounded_memR assms by auto
qed

lemma interval_0_bounded_geq:
  assumes "j \<le> i" "j \<le> k"
  assumes "mem I 0" "bounded I" (* [0, a] *)
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" (* if j\<le>i is part of the interval, then so is j\<le>k\<le>i *)
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" using assms by auto
  then have ineq: "\<tau> \<sigma> i - \<tau> \<sigma> j \<ge> \<tau> \<sigma> i - \<tau> \<sigma> k" by linarith
  then have "memR I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms
    by (transfer' fixing: \<sigma>) (auto split: if_splits)
  moreover have "memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using ineq assms
    by (transfer' fixing: \<sigma>) (auto split: if_splits)
  ultimately show ?thesis by auto
qed

lemma flip_int_props:
  assumes "I' = flip_int I"
  shows "\<not>bounded I'"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_props:
  assumes "\<not>memL I 0" (* [a, b] *)
  assumes "I' = flip_int_less_lower I" (* [0, a] *)
  shows "mem I' 0 \<and> bounded I'"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_mem:
  assumes "\<not>bounded I" "\<not>mem I x" (* [a, \<infinity>], x < a *)
  shows "mem (flip_int_less_lower I) x" (* x \<in> [0, a] *)
  using assms
  by (transfer') (simp add: bounded_memR)

lemma int_flip_mem:
  assumes "bounded I" "mem I 0" "\<not>mem I x" (* [0, a], a<x *)
  shows "mem (flip_int I) x" (* [a, \<infinity>] *)
  using assms memL_mono
  by (transfer') (auto split: if_splits)

lemma historically_rewrite_0:
  fixes I1 I2 :: \<I>
  assumes "mem I1 0" "bounded I1"
  assumes "I2 = flip_int I1"
  shows "sat \<sigma> V v i (historically I1 \<phi>) = sat \<sigma> V v i (Or (Since \<phi> I2 TT) (Since \<phi> I1 (And first \<phi>)))"
proof (rule iffI)
  assume hist: "sat \<sigma> V v i (historically I1 \<phi>)"
  {
    define A where "A = {j. j\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
    define j where "j = Max A"
    assume "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using A_def by auto
    {
      fix k
      assume k_props: "j<k" "k\<le>i" 
      {
        assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        then have "False" using A_props k_props j_def A_def by auto
      }
      then have "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" by blast
      then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms
        by (transfer' fixing: \<sigma>) (auto split: if_splits)
    }
    then have "\<forall>k\<in>{j<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" by auto
    then have "\<forall>k\<in>{j<..i}. sat \<sigma> V v k \<phi>" using hist by auto
    then have "sat \<sigma> V v i (Since \<phi> I2 TT)" using j_props by auto
    then have "sat \<sigma> V v i (Or (Since \<phi> I2 TT) (Since \<phi> I1 (And first \<phi>)))"
      by simp
  }
  moreover {
    assume "\<forall>j\<le>i. \<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then have mem_leq_j: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms
      by (transfer' fixing: \<sigma>) (auto split: if_splits)
    then have sat_leq_j: "\<forall>j\<le>i. sat \<sigma> V v j \<phi>" using hist by auto
    then have "sat \<sigma> V v i (Since \<phi> I1 (And first \<phi>))"
      using mem_leq_j
      by auto
    then have "sat \<sigma> V v i (Or (Since \<phi> I2 TT) (Since \<phi> I1 (And first \<phi>)))"
      by simp
  }
  ultimately show "sat \<sigma> V v i (Or (Since \<phi> I2 TT) (Since \<phi> I1 (And first \<phi>)))"
    by blast
next
  assume "sat \<sigma> V v i (Or (Since \<phi> I2 TT) (Since \<phi> I1 (And first \<phi>)))"
  then have "sat \<sigma> V v i (Since \<phi> I2 TT) \<or> sat \<sigma> V v i (Since \<phi> I1 (And first \<phi>))" by auto
  moreover {
    assume since: "sat \<sigma> V v i (Since \<phi> I2 TT)"
    then have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))" by simp
    then obtain j where j_props: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)" by blast
    {
      fix k
      assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      {
        assume "k\<le>j"
        then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j" by simp
        then have "\<tau> \<sigma> i - \<tau> \<sigma> k \<ge> \<tau> \<sigma> i - \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using j_props assms
          by (transfer' fixing: \<sigma>) (auto split: if_splits dest: memR_antimono)
        then have "False" using assms k_props
          by (transfer' fixing: \<sigma>) (auto split: if_splits)
      }
      then have "\<not>(k\<le>j)" by blast
      then have "sat \<sigma> V v k \<phi>" using k_props j_props by auto
    }
    then have "sat \<sigma> V v i (historically I1 \<phi>)" by auto
  }
  moreover {
    assume "sat \<sigma> V v i (Since \<phi> I1 (And first \<phi>))"
    then have "sat \<sigma> V v i (historically I1 \<phi>)" by auto
  }
  ultimately show "sat \<sigma> V v i (historically I1 \<phi>)" by blast
qed

lemma historically_rewrite_unbounded:
  assumes "\<not> mem I1 0" "\<not> bounded I1" (* [a, \<infinity>] *)
  assumes "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  shows "sat \<sigma> V v i (And (once I1 \<phi>) (historically I1 \<phi>)) = sat \<sigma> V v i (And (once I2 (Prev all (Since \<phi> all (And \<phi> first)))) (once I1 \<phi>))"
proof (rule iffI)
  assume historically: "sat \<sigma> V v i (And (once I1 \<phi>) (historically I1 \<phi>))"
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>}"
  define j where "j = Max A"
  have "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>" using historically by auto
  then have A_props: "finite A" "A \<noteq> {}" using A_def by auto
  then have "j \<in> A" using j_def by auto
  then have j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j \<phi>" using A_def by auto
  {
    fix k
    assume k_props: "k\<le>j"
    then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      using assms(2) j_props(1-2) interval_unbounded_leq[of j i k I1 \<sigma>]
      by auto
    then have first_sat: "sat \<sigma> V v k \<phi>" 
      using j_props k_props historically assms(1-2) 
      by auto
  }
  then have leq_j: "\<forall>k\<le>j. sat \<sigma> V v k \<phi>" by auto
  define B where "B = {k. k\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)}"
  define k where "k = Min B"
  have "mem I2 0"
    using assms
    by (transfer') (auto split: if_splits)
  then have B_props: "B \<noteq> {}" "finite B" using B_def by auto
  then have k_in_B: "k \<in> B" using k_def by auto
  then have k_props: "k\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using B_def by auto
  {
    assume "k=0"
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
      using k_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of k i j I2 \<sigma>]
      by auto
    then have "False"
      using assms j_props
      by (transfer') (auto split: if_splits)
  }
  then have k_pos: "k>0" by blast
  {
    assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))"
    then have "(k-1) \<in> B" using B_def k_props by auto
    then have "(k-1) \<ge> k" using B_props k_def by auto
    then have "False" using k_pos by auto
  }
  then have "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))" by blast
  then have k_pre: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))"
    using assms flip_int_less_lower_mem by auto
  then have "sat \<sigma> V v (k-1) \<phi>" using historically k_props by auto
  then have "(k-1) \<in> A" using A_def k_pre k_props by auto
  then have "(k-1) \<le> j" using j_def A_props by auto
  then have "sat \<sigma> V v i (once I2 (Prev all (Since \<phi> all (And \<phi> first))))"
    using interval_all k_pos leq_j k_props
    by (auto split: nat.split)
  then have "sat \<sigma> V v i (once I2 (Prev all (Since \<phi> all (And \<phi> first)))) \<and> sat \<sigma> V v i (once I1 \<phi>)"
    using historically
    by auto
  then show "sat \<sigma> V v i (And (once I2 (Prev all (Since \<phi> all (And \<phi> first)))) (once I1 \<phi>))" by auto
next
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
  assume rewrite: "sat \<sigma> V v i (And (once I2 (Prev all (Since \<phi> all (And \<phi> first)))) (once I1 \<phi>))"
  then have "sat \<sigma> V v i (And (once I2 (Prev all (Since \<phi> all (And \<phi> first)))) (once I1 \<phi>))"
    by auto
  then have "sat \<sigma> V v i (once I2 (Prev all (Since \<phi> all (And \<phi> first))))" by auto
  then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j (Prev all (Since \<phi> all (And \<phi> first)))"
    by auto
  then obtain j where j_props:
    "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j (Prev all (Since \<phi> all (And \<phi> first)))"
    by blast
  {
    assume "j = 0"
    then have "\<not>sat \<sigma> V v j (Prev all (Since \<phi> all (And \<phi> first)))" by auto
    then have "False" using j_props by auto
  }
  then have j_pos: "j \<noteq> 0" by auto
  then have j_pred_sat: "sat \<sigma> V v (j-1) (Since \<phi> all (And \<phi> first))"
    using j_pos j_props
    by (simp add: Nitpick.case_nat_unfold)
  {
    fix x
    assume x_props: "x>j-1"
    then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" using x_props by auto
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using j_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of j i x I2]
      by auto
    then have "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using assms
      by (transfer') (auto split: if_splits)
  }
  then have x_greater: "\<forall>x>(j-1). \<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by blast
  {
    fix x
    assume x_props: "x\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
    {
      assume "x>(j-1)"
      then have "False" using x_props x_greater by auto
    }
    then have "\<not>(x>j-1)" by blast
    then have "x\<le>(j-1)" by auto
  }
  then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> x\<le>j-1" by blast
  then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> sat \<sigma> V v x \<phi>" using j_pred_sat by auto
  then show "sat \<sigma> V v i (And (once I1 \<phi>) (historically I1 \<phi>))" using rewrite by auto
qed

lemma historically_rewrite_bounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b], a>0 *)
  assumes "I2 = int_remove_lower_bound I1" (* [0, b] *) 
  (*
    [0, b-a] would be more efficient but this interval can
    (probably) not be constructed using the current
    implementation of intervals.
  *)
  shows "sat \<sigma> V v i (And (once I1 \<phi>) (historically I1 \<phi>)) = sat \<sigma> V v i (And (once I1 \<phi>) (Neg (once I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
proof (rule iffI)
  assume "sat \<sigma> V v i (And (once I1 \<phi>) (historically I1 \<phi>))"
  then show "sat \<sigma> V v i (And (once I1 \<phi>) (Neg (once I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
    by auto
next
  assume rewrite: "sat \<sigma> V v i (And (once I1 \<phi>) (Neg (once I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j \<phi>" by auto
  have j_leq_i_sat: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> (sat \<sigma> V v j (Neg (once I2 \<phi>)) \<and> sat \<sigma> V v j (Neg (sometimes I2 \<phi>))) \<or> sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    then have "(sat \<sigma> V v k (Neg (once I2 \<phi>)) \<and> sat \<sigma> V v k (Neg (sometimes I2 \<phi>))) \<or> sat \<sigma> V v k \<phi>"
      using j_leq_i_sat by auto
    moreover {
      assume assm: "(sat \<sigma> V v k (Neg (once I2 \<phi>)) \<and> sat \<sigma> V v k (Neg (sometimes I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>sat \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
          using j_props assms(1-2)
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
          using k_props assms(1-2)
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<phi>" by auto
  then show "sat \<sigma> V v i (And (once I1 \<phi>) (historically I1 \<phi>))" using rewrite by auto
qed

lemma sat_trigger_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "sat \<sigma> V v i (Trigger \<phi> I \<psi>)"
  assumes leq: "j\<le>i"
  assumes mem_j: "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
  shows "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> sat \<sigma> V v k (And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {j<..i}. sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {j<..i}. sat \<sigma> V v x \<phi>}"
  define k where "k = Max A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {j<..i}" "sat \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "\<forall>l>k. l \<notin> A"
    using Max_ge[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    using mem mem_j k_props interval_geq[of I 0 \<sigma> i j k]
    by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat_trigger_rewrite_0:
  assumes mem: "mem I 0"
shows "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = sat \<sigma> V v i (Or (Since \<psi> I (And \<phi> \<psi>)) (historically I \<psi>))"
proof (rule iffI)
  assume trigger: "sat \<sigma> V v i (Trigger \<phi> I \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<psi>"
    then have "sat \<sigma> V v i (Or (Since \<psi> I (And \<phi> \<psi>)) (historically I \<psi>))" by auto
  }
  moreover {
    define A where "A = {j. j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j (And \<phi> \<psi>)}"
    define j where "j = Max A"
    assume "\<not>(\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<psi>)"
    then obtain j' where "j' \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "\<not>sat \<sigma> V v j' \<psi>" by blast
    then have "\<exists>k \<in> {j'<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> sat \<sigma> V v k (And \<phi> \<psi>)"
      using mem trigger sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j (And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {j<..i}. sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {j<..i} \<and> \<not> sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        using mem j_props interval_geq[of I 0 \<sigma> i j k]
        by auto
      then have "\<exists>x \<in> {k<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> x) \<and> sat \<sigma> V v x (And \<phi> \<psi>)"
        using mem trigger k_props sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {k<..i}" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> x)" "sat \<sigma> V v x (And \<phi> \<psi>)"
        by blast
      then have "x \<le> Max A"
        using A_def A_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {j<..i}. sat \<sigma> V v k \<psi>" by blast
    then have "sat \<sigma> V v i (Or (Since \<psi> I (And \<phi> \<psi>)) (historically I \<psi>))"
      using j_props
      by auto
  }
  ultimately show "sat \<sigma> V v i (Or (Since \<psi> I (And \<phi> \<psi>)) (historically I \<psi>))" by blast
next
  assume "sat \<sigma> V v i (Or (Since \<psi> I (And \<phi> \<psi>)) (historically I \<psi>))"
  moreover {
    assume "sat \<sigma> V v i (historically I \<psi>)"
    then have "sat \<sigma> V v i (Trigger \<phi> I \<psi>)"
      by auto
  }
  moreover {
    fix j
    assume since_and_j_props: "sat \<sigma> V v i (Since \<psi> I (And \<phi> \<psi>))" "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then obtain "j'" where j'_props:
      "j'\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "sat \<sigma> V v j' (And \<phi> \<psi>)"
      "(\<forall>k \<in> {j' <.. i}. sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume le: "j' < j"
      then have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)"
        using j'_props since_and_j_props le
        by auto
    }
    moreover {
      assume geq: "\<not> j' < j"
      moreover {
        assume "j = j'"
        then have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)"
          using geq j'_props
          by auto
      }
      ultimately have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "sat \<sigma> V v i (Trigger \<phi> I \<psi>)" by auto
qed

lemma sat_trigger_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
  assumes "I2 = flip_int_less_lower I1" (* [0, a-1] *)
shows "sat \<sigma> V v i (Trigger \<phi> I1 \<psi>) = sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))"
proof (rule iffI)
  assume trigger: "sat \<sigma> V v i (Trigger \<phi> I1 \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<psi>"
    then have "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))" by auto
  }
  moreover {
    assume "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> \<not>sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "\<not>sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{j <.. i} \<and> sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Max A"
    have "(\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)" using j_props trigger by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{j <.. i}" "sat \<sigma> V v k \<phi>" using A_def by auto
    {
      fix x
      assume x_props: "x\<ge>j" "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      {
        assume k_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
        have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" using x_props by auto
        then have "\<tau> \<sigma> i - \<tau> \<sigma> x \<le> \<tau> \<sigma> i - \<tau> \<sigma> j" by auto
        moreover have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms j_props by auto 
        ultimately have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using memR_antimono by blast
        moreover have "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
          using x_props assms
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by auto
    }
    then have geq_j_mem: "\<forall>x\<ge>j. \<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      then have "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      then have k_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using geq_j_mem k_props by auto
      then have "sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {k <.. i}. sat \<sigma> V v k \<phi>)" using trigger k_props by auto
      moreover {
        assume "(\<exists>k \<in> {k <.. i}. sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {k <.. i}" "sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "sat \<sigma> V v k (And \<phi> \<psi>)" using k_props by auto
      then have k_since: "sat \<sigma> V v k (Since \<psi> all (And \<phi> \<psi>))" using interval_all by auto
      {
        assume "k=i"
        then have "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] assms k_mem
          by auto
      }
      moreover {
        assume "\<not>(k=i)"
        then have k_suc_leq_i: "k+1\<le>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
          then have "sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. sat \<sigma> V v k \<phi>)" using trigger by auto
          moreover {
            assume "\<exists>k \<in> {x <.. i}. sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {x <.. i}" "sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<le> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{k<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          moreover have "sat \<sigma> V v (k+1) (Prev all (Since \<psi> all (And \<phi> \<psi>)))"
            using k_suc_leq_i k_since interval_all
            by auto
          ultimately have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j (Prev all (Since \<psi> all (And \<phi> \<psi>))))"
            using k_suc_leq_i
            by blast
          then have "sat \<sigma> V v i (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{k<..i} \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<and> sat \<sigma> V v l \<psi>}"
          define c where "c = Max B"
          assume "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))" using geq_j_mem k_props by auto
          then have "sat \<sigma> V v (k+1) \<psi> \<or> (\<exists>x \<in> {k+1 <.. i}. sat \<sigma> V v x \<phi>)" using trigger k_suc_leq_i by auto
          moreover {
            assume "\<exists>x \<in> {k+1 <.. i}. sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {k+1 <.. i} \<and> sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<le> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "sat \<sigma> V v (k+1) \<psi>" by auto
          then have B_props: "B \<noteq> {}" "finite B" using B_def k_suc_leq_i k_suc_mem k_props by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> c)" "sat \<sigma> V v c \<psi>"
            using B_def
            by auto
          then have k_cond: "k\<le>c" "sat \<sigma> V v k (And \<phi> \<psi>)" using k_sat by auto
          {
            fix x
            assume x_props: "x\<in>{k<..c}"
            then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> c" by auto
            then have lower: "(\<tau> \<sigma> i - \<tau> \<sigma> x) \<ge> (\<tau> \<sigma> i - \<tau> \<sigma> c)" by linarith
            have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> k" using x_props by auto
            then have upper: "(\<tau> \<sigma> i - \<tau> \<sigma> x) \<le> (\<tau> \<sigma> i - \<tau> \<sigma> k)" by linarith
            then have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
              using k_mem memR_antimono by blast
            then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using assms c_props lower by auto
            then have "sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{k<..c}. sat \<sigma> V v x \<psi>" by auto
          then have c_sat: "sat \<sigma> V v c (Since \<psi> all (And \<phi> \<psi>))"
            using interval_all k_cond
            by auto
          {
            assume "(c+1) \<in> B"
            then have "c+1\<le>c" using c_def B_props by auto
            then have "False" by auto
          }
          then have "(c+1) \<notin> B" by blast
          then have disj: "(c+1)\<notin>{k<..i} \<or> \<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>sat \<sigma> V v (c+1) \<psi>" using B_def by blast
          {
            assume "(c+1)\<notin>{k<..i}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c+1)\<notin>{k<..i})"
            then have c_suc_leq_i: "(c+1)\<in>{k<..i}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>sat \<sigma> V v (c+1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
              then have "\<not>sat \<sigma> V v (c+1) \<psi>" using disj by blast
              then have "False"
                using k_greater_sat c_suc_leq_i c_suc_mem
                by auto
            }
            moreover {
              assume c_suc_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
              {
                assume not_mem2: "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                then have upper: "\<not>memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                  using c_suc_not_mem_1 assms geq_j_mem k_cond k_props
                  by auto
                have "\<tau> \<sigma> c \<le> \<tau> \<sigma> (c+1)" by auto
                then have "\<tau> \<sigma> i - \<tau> \<sigma> c \<ge> \<tau> \<sigma> i - \<tau> \<sigma> (c+1)" using diff_le_mono2 by blast
                moreover have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> c)" using c_props assms by auto
                ultimately have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                  using not_mem2 assms(3) memR_antimono
                  by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" by blast
              then have "(c+1)\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" "sat \<sigma> V v (c+1) (Prev all (Since \<psi> all (And \<phi> \<psi>)))"
                using c_suc_leq_i c_sat interval_all
                by auto
              then have "sat \<sigma> V v i (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>))))"
                using interval_all sat_once
                by blast
            }
            ultimately have "sat \<sigma> V v i (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>))))" by auto
          }
          ultimately have "sat \<sigma> V v i (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>))))" by blast
        }
        ultimately have "sat \<sigma> V v i (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>))))"
          by blast
        then have "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))" by blast
  }
  ultimately show "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))" by auto
next
  assume "sat \<sigma> V v i (Or (Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>)))))"
  then have "sat \<sigma> V v i (historically I1 \<psi>) \<or> sat \<sigma> V v i (once I2 \<phi>) \<or> sat \<sigma> V v i (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>))))"
    by auto
  moreover {
    assume "sat \<sigma> V v i (historically I1 \<psi>)"
    then have "sat \<sigma> V v i (Trigger \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "sat \<sigma> V v i (once I2 \<phi>)"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      {
        assume j_leq_x: "x\<ge>j"
        then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using j_leq_x j_props assms
          using flip_int_less_lower_props interval_0_bounded_geq memR_zero
          by blast
        then have "False"
          using x_props assms flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<ge>j)" by blast
      then have "x<j" by auto
    }
    then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> x<j" by auto
    then have "sat \<sigma> V v i (Trigger \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume since: "sat \<sigma> V v i (once I2 (Prev all (Since \<psi> all (And \<phi> \<psi>))))"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j (Prev all (Since \<psi> all (And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "sat \<sigma> V v j (Prev all (Since \<psi> all (And \<phi> \<psi>)))" by blast
    {
      assume "j = 0"
      then have "\<not>sat \<sigma> V v j (Prev all (Since \<psi> all (And \<phi> \<psi>)))" by auto
      then have "False" using j_props by auto
    }
    then have j_pos: "j>0" by auto
    then have j_pred_sat: "sat \<sigma> V v (j-1) (Since \<psi> all (And \<phi> \<psi>))"
      using j_pos j_props
      by (simp add: Nitpick.case_nat_unfold)
    then have "\<exists>x\<le>(j-1). sat \<sigma> V v x (And \<phi> \<psi>) \<and> (\<forall>k\<in>{x<..(j-1)}. sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<le>(j-1)" "sat \<sigma> V v x (And \<phi> \<psi>)" "\<forall>k\<in>{x<..(j-1)}. sat \<sigma> V v k \<psi>"
      by blast
    {
      fix l
      assume l_props: "l\<le>i"
      {
        assume "l<x"
        then have "\<exists>k \<in> {l <.. i}. sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l<x)" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
        then have l_props: "x\<le>l" "l\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)" using l_props by auto
        {
          assume "l\<le>(j-1)"
          then have "sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<le>(j-1)"
          then have l_geq: "l\<ge>(j-1)" by auto
          have j_pred_psi: "sat \<sigma> V v (j-1) \<psi>" using j_pred_sat by auto
          {
            assume l_greater: "l>(j-1)"
            then have "\<tau> \<sigma> l \<ge> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
              using assms j_props j_pos l_greater flip_int_less_lower_props interval_0_bounded_geq
              by (metis One_nat_def Suc_pred le_simps(3) memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
              using assms flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j-1)" using l_geq le_eq_less_or_eq by blast
          then have "sat \<sigma> V v l \<psi>" using j_pred_psi by blast
        }
        ultimately have "sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<longrightarrow> sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {l <.. i}. sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. sat \<sigma> V v k \<phi>)" by auto
    then have "sat \<sigma> V v i (Trigger \<phi> I1 \<psi>)" by auto
  }
  ultimately show "sat \<sigma> V v i (Trigger \<phi> I1 \<psi>)" by blast
qed

lemma always_rewrite_0:
  fixes I1 I2 :: \<I>
  assumes "mem I1 0" "bounded I1"
  assumes "I2 = flip_int I1"
  shows "sat \<sigma> V v i (always I1 \<phi>) = sat \<sigma> V v i (Until \<phi> I2 TT)"
proof (rule iffI)
  define A where "A = {j. j\<ge>i \<and> mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)}"
  define j where "j = Inf A"
  assume assm: "sat \<sigma> V v i (always I1 \<phi>)"
  have "\<forall>x. \<exists>j. x < \<tau> \<sigma> j" using Suc_le_lessD ex_le_\<tau> by blast
  then have exists_db: "\<forall>x. \<exists>j. x < \<tau> \<sigma> j - \<tau> \<sigma> i" by (simp add: less_diff_conv)
  obtain b where b_props: "\<not>memR I1 b" "b>0" using assms(1-2) using bounded_memR by blast
  then obtain t where t_props: "b < \<tau> \<sigma> t - \<tau> \<sigma> i" using exists_db by auto
  {
    assume "t<i"
    then have "\<tau> \<sigma> t - \<tau> \<sigma> i = 0" by auto
    then have "False" using b_props t_props by auto
  }
  then have t_geq_i: "\<not>(t<i)" by blast
  have "\<not>mem I1 (\<tau> \<sigma> t - \<tau> \<sigma> i)" using t_props b_props memR_antimono by auto
  then have "mem I2 (\<tau> \<sigma> t - \<tau> \<sigma> i)" using assms by (simp add: int_flip_mem)
  moreover have "t\<ge>i" using t_geq_i by auto
  ultimately have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" by auto
  then have A_props: "A \<noteq> {}" using A_def by auto
  then have "j \<in> A" using j_def Inf_nat_def1 by auto
  then have j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using A_def by auto
  {
    fix x
    assume x_props: "x\<in>{i..<j}"
    {
      assume "mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      then have "x \<in> A" using A_def x_props by auto
      then have "x \<ge> j" using A_props j_def by (simp add: cInf_lower)
      then have "False" using x_props by auto
    }
    then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      using assms
      by (transfer') (auto split: if_splits)
  }
  then have "\<forall>x\<in>{i..<j}. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
  then have "\<forall>x\<in>{i..<j}. sat \<sigma> V v x \<phi>" using assm by auto
  then show "sat \<sigma> V v i (Until \<phi> I2 TT)"
    using j_props
    by auto
next
  assume "sat \<sigma> V v i (Until \<phi> I2 TT)"
  then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. sat \<sigma> V v k \<phi>" by auto
  {
    fix k
    assume k_props: "k\<ge>i" "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
    {
      assume "k\<ge>j"
      then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using j_props assms flip_int_props interval_unbounded_geq[of i j k I2 \<sigma>]
        by auto
      then have "False"
        using k_props assms
        by (transfer) (auto)
    }
    then have "\<not>k\<ge>j" by blast
    then have "k<j" by auto
    then have "sat \<sigma> V v k \<phi>" using k_props(1) j_props(3) by auto
  }
  then have "\<forall>k\<ge>i. mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v k \<phi>" by auto
  then show "sat \<sigma> V v i (always I1 \<phi>)"
    by auto
qed

lemma always_rewrite_bounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b], a>0 *)
  assumes "I2 = int_remove_lower_bound I1" (* [0, b] *) 
  shows "sat \<sigma> V v i (And (sometimes I1 \<phi>) (always I1 \<phi>)) = sat \<sigma> V v i (And (sometimes I1 \<phi>) (Neg (sometimes I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
proof (rule iffI)
  assume "sat \<sigma> V v i (And (sometimes I1 \<phi>) (always I1 \<phi>))"
  then show "sat \<sigma> V v i (And (sometimes I1 \<phi>) (Neg (sometimes I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
    by auto
next
  assume rewrite: "sat \<sigma> V v i (And (sometimes I1 \<phi>) (Neg (sometimes I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
  then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat \<sigma> V v j \<phi>" by auto
  have j_geq_i_sat: "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> (sat \<sigma> V v j (Neg (once I2 \<phi>)) \<and> sat \<sigma> V v j (Neg (sometimes I2 \<phi>))) \<or> sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<ge>i" "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
    then have "(sat \<sigma> V v k (Neg (once I2 \<phi>)) \<and> sat \<sigma> V v k (Neg (sometimes I2 \<phi>))) \<or> sat \<sigma> V v k \<phi>"
      using j_geq_i_sat by auto
    moreover {
      assume assm: "(sat \<sigma> V v k (Neg (once I2 \<phi>)) \<and> sat \<sigma> V v k (Neg (sometimes I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>sat \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          using j_props assms(1-2)
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          using k_props assms(1-2)
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms interval_geq j_props(1)
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms j_props(1) k_props(1) interval_geq
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<phi>" by auto
  then show "sat \<sigma> V v i (And (sometimes I1 \<phi>) (always I1 \<phi>))"
    using rewrite
    by auto
qed

lemma sat_release_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "sat \<sigma> V v i (Release \<phi> I \<psi>)"
  assumes geq: "j\<ge>i"
  assumes mem_j: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  shows "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> sat \<sigma> V v k (And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {i..<j}. sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {i..<j}. sat \<sigma> V v x \<phi>}"
  define k where "k = Min A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {i..<j}" "sat \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "(\<forall>l<k. l \<notin> A)"
    using Min_le[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using mem mem_j k_props interval_leq[of I 0 \<sigma> j i k] by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat_release_rewrite_0_equiv:
  assumes mem: "mem I 0"
shows "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (Or (Until \<psi> I (And \<phi> \<psi>)) (always I \<psi>))"
proof (rule iffI)
  assume release: "sat \<sigma> V v i (Release \<phi> I \<psi>)"
  {
    assume "\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<psi>"
    then have "sat \<sigma> V v i (Or (Until \<psi> I (And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  moreover {
    assume "\<not>(\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<psi>)"
    then obtain j' where j'_props: "j' \<ge> i \<and> mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i) \<and> \<not>sat \<sigma> V v j' \<psi>" by blast
    define A where "A = {j. j\<in>{i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j (And \<phi> \<psi>)}"
    define j where "j = Min A"
    have A_nonempty: "A\<noteq>{}"
      using mem release j'_props A_def sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    moreover have A_finite: "finite A" using A_def by auto
    ultimately have j_in_A: "j \<in> A"
      using j_def Max_in[of "A"]
      by auto
    then have j_props: "j\<in>{i..<j'}" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat \<sigma> V v j (And \<phi> \<psi>)"
      using A_def
      by auto
    moreover {
      assume "\<forall>k \<in> {i..<j}. sat \<sigma> V v k \<psi>"
      then have "sat \<sigma> V v i (Or (Until \<psi> I (And \<phi> \<psi>)) (always I \<psi>))"
        using j_props
        by auto
    }
    moreover {
      assume "\<not>(\<forall>k \<in> {i..<j}. sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {i..<j} \<and> \<not> sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using mem j_props interval_leq[of I 0 \<sigma> j i k]
        by auto
      then have "\<exists>x \<in> {i..<k}. mem I (\<tau> \<sigma> x - \<tau> \<sigma> i) \<and> sat \<sigma> V v x (And \<phi> \<psi>)"
        using mem release k_props sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {i..<k}" "mem I (\<tau> \<sigma> x - \<tau> \<sigma> i)" "sat \<sigma> V v x (And \<phi> \<psi>)" by blast
      then have "x \<in> A" using A_def j_props k_props by auto
      then have "x \<ge> Min A" using A_nonempty A_finite by auto
      then have "x \<ge> j" "x < k" "k < j" using j_def k_props x_props by auto
      then have "False" by auto
    }
    ultimately have "sat \<sigma> V v i (Or (Until \<psi> I (And \<phi> \<psi>)) (always I \<psi>))" by blast
  }
  ultimately show "sat \<sigma> V v i (Or (Until \<psi> I (And \<phi> \<psi>)) (always I \<psi>))" by blast
next
  assume "sat \<sigma> V v i (Or (Until \<psi> I (And \<phi> \<psi>)) (always I \<psi>))"
  moreover {
    assume "sat \<sigma> V v i (always I \<psi>)"
    then have "sat \<sigma> V v i (Release \<phi> I \<psi>)" by auto
  }
  moreover {
    fix j
    assume until_and_j_props: "sat \<sigma> V v i (Until \<psi> I (And \<phi> \<psi>))" "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then obtain "j'" where j'_props: "j'\<ge>i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "sat \<sigma> V v j' (And \<phi> \<psi>)" "(\<forall>k \<in> {i ..< j'}. sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume ge: "j' > j"
      then have "\<forall>k \<in> {i ..< j'}. sat \<sigma> V v k \<psi>" using j'_props by auto
      then have "sat \<sigma> V v j \<psi>" using until_and_j_props ge by auto
      then have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)" by auto
    }
    moreover {
      assume leq: "\<not> j' > j"
      moreover {
        assume "j = j'"
        then have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)"
          using leq j'_props
          by auto
      }
      ultimately have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "sat \<sigma> V v i (Release \<phi> I \<psi>)" by auto
qed

lemma sat_release_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
  assumes "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assumes "a>0"
shows "sat \<sigma> V v i (Release \<phi> I1 \<psi>) = sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))"
proof (rule iffI)
  assume release: "sat \<sigma> V v i (Release \<phi> I1 \<psi>)"
  {
    assume "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<psi>"
    then have "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))" by auto
  }
  moreover {
    assume "\<exists>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> \<not>sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<not>sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{i ..< j} \<and> sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Min A"
    have "(\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)" using j_props release by auto
    then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{i ..< j}" "sat \<sigma> V v k \<phi>" using A_def by auto
    {
      fix x
      assume x_props: "x\<le>j" "\<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume k_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
        have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" using x_props by auto
        then have "\<tau> \<sigma> x - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by linarith
        moreover have "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using assms j_props by auto 
        ultimately have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using memR_antimono by blast
        moreover have "memL I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          using k_not_mem_1 x_props assms
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    }
    then have geq_j_mem: "\<forall>x\<le>j. \<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have k_mem: "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
      then have "sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {i ..< k}. sat \<sigma> V v k \<phi>)" using release k_props by auto
      moreover {
        assume "(\<exists>k \<in> {i ..< k}. sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {i ..< k}" "sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "sat \<sigma> V v k (And \<phi> \<psi>)" using k_props by auto
      then have k_until: "sat \<sigma> V v k (Until \<psi> all (And \<phi> \<psi>))" using interval_all by auto
      {
        assume "k=i"
        then have "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] using assms k_mem by auto
      }
      moreover {
        assume k_neq_i: "\<not>(k=i)"
        then have k_pred_geq_i: "k-1\<ge>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {i..<k}" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          then have "sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. sat \<sigma> V v k \<phi>)" using release by auto
          moreover {
            assume "\<exists>k \<in> {i ..< x}. sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {i ..< x}" "sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<ge> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{i..<k}. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          moreover have "sat \<sigma> V v (k-1) (Next all (Until \<psi> all (And \<phi> \<psi>)))"
            using k_pred_geq_i k_until interval_all k_neq_i
            by auto
          ultimately have "(\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j (Next all (Until \<psi> all (And \<phi> \<psi>))))"
            using k_pred_geq_i
            by blast
          then have "sat \<sigma> V v i (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{i..<k} \<and> mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<and> sat \<sigma> V v l \<psi>}"
          define c where "c = Min B"
          assume "\<not>mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
          then have "sat \<sigma> V v (k-1) \<psi> \<or> (\<exists>x \<in> {i ..< k-1}. sat \<sigma> V v x \<phi>)"
            using release k_pred_geq_i
            by auto
          moreover {
            assume "\<exists>x \<in> {i ..< k-1}. sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {i ..< k-1} \<and> sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<ge> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "sat \<sigma> V v (k-1) \<psi>" by auto
          then have B_props: "B \<noteq> {} \<and> finite B"
            using B_def k_pred_geq_i k_suc_mem k_props k_neq_i
            by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{i..<k}" "mem I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" "sat \<sigma> V v c \<psi>" using B_def by auto
          then have k_cond: "k\<ge>c" "sat \<sigma> V v k (And \<phi> \<psi>)" using k_sat by auto
          {
            assume "c=0"
            then have "False" using c_props assms by auto
          }
          then have c_pos: "c\<noteq>0" by auto
          {
            fix x
            assume x_props: "x\<in>{c..<k}"
            then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> c" by auto
            then have lower: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> c - \<tau> \<sigma> i)" by auto
            have "\<tau> \<sigma> x \<le> \<tau> \<sigma> k" using x_props by auto
            then have upper: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<le> (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
            then have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
              using k_mem memR_antimono by blast
            then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms c_props lower by auto
            then have "sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{c..<k}. sat \<sigma> V v x \<psi>" by auto
          then have c_sat: "sat \<sigma> V v c (Until \<psi> all (And \<phi> \<psi>))"
            using interval_all k_cond
            by auto
          {
            assume "(c-1) \<in> B"
            then have "c-1\<ge>c" using c_def B_props by auto
            moreover have "c-1 < c" using c_pos by auto
            ultimately have "False" by auto
          }
          then have "(c-1) \<notin> B" by blast
          then have disj: "(c-1)\<notin>{i..<k} \<or> \<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>sat \<sigma> V v (c-1) \<psi>" using B_def by blast
          {
            assume "(c-1)\<notin>{i..<k}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c-1)\<notin>{i..<k})"
            then have c_pred_geq_i: "(c-1)\<in>{i..<k}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>sat \<sigma> V v (c-1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              then have "\<not>sat \<sigma> V v (c-1) \<psi>" using disj by blast
              then have "False"
                using k_greater_sat c_pred_geq_i c_suc_mem
                by auto
            }
            moreover {
              assume c_pred_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              {
                assume "\<not>mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                then have upper: "\<not> memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                  using c_pred_not_mem_1 assms geq_j_mem k_cond k_props
                  by auto
                have "\<tau> \<sigma> c \<ge> \<tau> \<sigma> (c-1)" by auto
                then have "\<tau> \<sigma> c - \<tau> \<sigma> i \<ge> \<tau> \<sigma> (c-1) - \<tau> \<sigma> i" using diff_le_mono by blast
                moreover have "memR I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" using c_props assms by auto
                ultimately have "memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using memR_antimono by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
              then have "(c-1)\<ge>i \<and> mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<and> sat \<sigma> V v (c-1) (Next all (Until \<psi> all (And \<phi> \<psi>)))"
                using c_pred_geq_i c_sat interval_all c_pos
                by auto
              then have "sat \<sigma> V v i (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>))))"
                using interval_all sat_sometimes
                by blast
            }
            ultimately have "sat \<sigma> V v i (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>))))" by auto
          }
          ultimately have "sat \<sigma> V v i (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>))))" by blast
      }
        ultimately have "sat \<sigma> V v i (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>))))"
          by blast
        then have "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))" by blast
  }
  ultimately show "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))" by auto
next
  assume "sat \<sigma> V v i (Or (Or (always I1 \<psi>) (sometimes I2 \<phi>)) (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>)))))"
  then have "sat \<sigma> V v i (always I1 \<psi>) \<or> sat \<sigma> V v i (sometimes I2 \<phi>) \<or> sat \<sigma> V v i (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>))))"
    by auto
  moreover {
    assume "sat \<sigma> V v i (always I1 \<psi>)"
    then have "sat \<sigma> V v i (Release \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "sat \<sigma> V v i (sometimes I2 \<phi>)"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<ge>i" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume "x\<le>j"
        then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using j_props assms flip_int_less_lower_props
          by (meson diff_le_mono memL_mono memR_antimono memR_zero zero_le)
        then have "False" using x_props assms
          using flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<le>j)" by blast
      then have "x>j" by auto
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> x>j" by auto
    then have "sat \<sigma> V v i (Release \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume until: "sat \<sigma> V v i (sometimes I2 (Next all (Until \<psi> all (And \<phi> \<psi>))))"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j (Next all (Until \<psi> all (And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat \<sigma> V v j (Next all (Until \<psi> all (And \<phi> \<psi>)))" by blast
    then have j_pred_sat: "sat \<sigma> V v (j+1) (Until \<psi> all (And \<phi> \<psi>))" by auto
    then have "\<exists>x\<ge>(j+1). sat \<sigma> V v x (And \<phi> \<psi>) \<and> (\<forall>k\<in>{(j+1)..<x}. sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<ge>(j+1)" "sat \<sigma> V v x (And \<phi> \<psi>)" "\<forall>k\<in>{(j+1)..<x}. sat \<sigma> V v k \<psi>" by blast
    {
      fix l
      assume l_props: "l\<ge>i"
      {
        assume "l>x"
        then have "\<exists>k \<in> {i ..< l}. sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l>x)" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        then have l_props: "x\<ge>l" "l\<ge>i" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using l_props by auto
        {
          assume "l\<ge>(j+1)"
          then have "sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<ge>(j+1)"
          then have l_geq: "l\<le>(j+1)" by auto
          have j_suc_psi: "sat \<sigma> V v (j+1) \<psi>" using j_pred_sat by auto
          {
            assume "l<(j+1)"
            then have "\<tau> \<sigma> l \<le> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using assms j_props flip_int_less_lower_props
            by (meson diff_le_mono le0 memL_mono memR_antimono memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
              using assms flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j+1)" using l_geq le_eq_less_or_eq by blast
          then have "sat \<sigma> V v l \<psi>" using j_suc_psi by blast
        }
        ultimately have "sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {i ..< l}. sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. sat \<sigma> V v k \<phi>)" by auto
    then have "sat \<sigma> V v i (Release \<phi> I1 \<psi>)" by auto
  }
  ultimately show "sat \<sigma> V v i (Release \<phi> I1 \<psi>)" by blast
qed

subsection \<open>Past-only formulas\<close>

fun past_only :: "formula \<Rightarrow> bool" where
  "past_only (Pred _ _) = True"
| "past_only (Eq _ _) = True"
| "past_only (Less _ _) = True"
| "past_only (LessEq _ _) = True"
| "past_only (Let _ \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Neg \<psi>) = past_only \<psi>"
| "past_only (Or \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (And \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Ands l) = (\<forall>\<alpha>\<in>set l. past_only \<alpha>)"
| "past_only (Exists \<psi>) = past_only \<psi>"
| "past_only (Agg _ _ _ _ \<psi>) = past_only \<psi>"
| "past_only (Prev _ \<psi>) = past_only \<psi>"
| "past_only (Next _ _) = False"
| "past_only (Since \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Until \<alpha> _ \<beta>) = False"
| "past_only (Trigger \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Release \<alpha> _ \<beta>) = False"
| "past_only (MatchP _ r) = Regex.pred_regex past_only r"
| "past_only (MatchF _ _) = False"

lemma past_only_sat:
  assumes "prefix_of \<pi> \<sigma>" "prefix_of \<pi> \<sigma>'"
  shows "i < plen \<pi> \<Longrightarrow> dom V = dom V' \<Longrightarrow>
     (\<And>p i. p \<in> dom V \<Longrightarrow> i < plen \<pi> \<Longrightarrow> the (V p) i = the (V' p) i) \<Longrightarrow>
     past_only \<phi> \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma>' V' v i \<phi>"
proof (induction \<phi> arbitrary: V V' v i)
  case (Pred e ts)
  show ?case proof (cases "V e")
    case None
    then have "V' e = None" using \<open>dom V = dom V'\<close> by auto
    with None \<Gamma>_prefix_conv[OF assms(1,2) Pred(1)] show ?thesis by simp
  next
    case (Some a)
    moreover obtain a' where "V' e = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "the (V e) i = the (V' e) i"
      using Some Pred(1,3) by (fastforce intro: domI)
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?V = "\<lambda>V \<sigma>. (V(p \<mapsto> \<lambda>i. {v. length v = nfv \<phi> \<and> sat \<sigma> V v i \<phi>}))"
  show ?case unfolding sat.simps proof (rule Let.IH(2))
    show "i < plen \<pi>" by fact
    from Let.prems show "past_only \<psi>" by simp
    from Let.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by (simp del: fun_upd_apply)
  next
    fix p' i
    assume *: "p' \<in> dom (?V V \<sigma>)" "i < plen \<pi>"
    show "the (?V V \<sigma> p') i = the (?V V' \<sigma>' p') i" proof (cases "p' = p")
      case True
      with Let \<open>i < plen \<pi>\<close> show ?thesis by auto
    next
      case False
      with * show ?thesis by (auto intro!: Let.prems(3))
    qed
  qed
next
  case (Ands l)
  with \<Gamma>_prefix_conv[OF assms] show ?case by simp
next
  case (Prev I \<phi>)
  with \<tau>_prefix_conv[OF assms] show ?case by (simp split: nat.split)
next
  case (Since \<phi>1 I \<phi>2)
  with \<tau>_prefix_conv[OF assms] show ?case by auto
next
  case (Trigger \<phi> I \<psi>)
  with \<tau>_prefix_conv[OF assms] show ?case by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r a b = Regex.match (sat \<sigma>' V' v) r a b" if "b < plen \<pi>" for a b
    using that by (intro Regex.match_cong_strong) (auto simp: regex.pred_set)
  with \<tau>_prefix_conv[OF assms] MatchP(2) show ?case by auto
qed auto


subsection \<open>Safe formulas\<close>

fun remove_neg :: "formula \<Rightarrow> formula" where
  "remove_neg (Neg \<phi>) = \<phi>"
| "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "fvi b (remove_neg \<phi>) = fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

fun is_constraint :: "formula \<Rightarrow> bool" where
  "is_constraint (Eq t1 t2) = True"
| "is_constraint (Less t1 t2) = True"
| "is_constraint (LessEq t1 t2) = True"
| "is_constraint (Neg (Eq t1 t2)) = True"
| "is_constraint (Neg (Less t1 t2)) = True"
| "is_constraint (Neg (LessEq t1 t2)) = True"
| "is_constraint _ = False"

definition safe_assignment :: "nat set \<Rightarrow> formula \<Rightarrow> bool" where
  "safe_assignment X \<phi> = (case \<phi> of
       Eq (Var x) (Var y) \<Rightarrow> (x \<notin> X \<longleftrightarrow> y \<in> X)
     | Eq (Var x) t \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | Eq t (Var x) \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | _ \<Rightarrow> False)"

fun safe_formula :: "formula \<Rightarrow> bool" where
  "safe_formula (Eq t1 t2) = (is_Const t1 \<and> (is_Const t2 \<or> is_Var t2) \<or> is_Var t1 \<and> is_Const t2)"
| "safe_formula (Neg (Eq (Var x) (Var y))) = (x = y)"
| "safe_formula (Less t1 t2) = False"
| "safe_formula (LessEq t1 t2) = False"
| "safe_formula (Pred e ts) = (\<forall>t\<in>set ts. is_Var t \<or> is_Const t)"
| "safe_formula (Let p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Neg \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (Or \<phi> \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (And \<phi> \<psi>) = (safe_formula \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False))))"
| "safe_formula (Ands l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all safe_formula (map remove_neg neg) \<and> \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Agg y \<omega> b f \<phi>) = (safe_formula \<phi> \<and> y + b \<notin> fv \<phi> \<and> {0..<b} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
| "safe_formula (Until \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
| "safe_formula (Trigger \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    mem I 0)"
| "safe_formula (Release \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    mem I 0)"
| "safe_formula (MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "safe_formula (MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Futu Strict r"


(* verify that the derived rewrite formulas are safe *)

lemma TT_safe[simp]: "safe_formula TT"
  by (simp add: TT_def FF_def)

lemma first_fv[simp]: "fv first = {}"
  by (simp add: first_def)

lemma first_safe[simp]: "safe_formula first"
  by (simp add: first_def)

lemma once_safe[simp]: "safe_formula \<phi> \<Longrightarrow> safe_formula (once I \<phi>)"
  by (simp add: once_def)

lemma sometimes_safe[simp]: "safe_formula \<phi> \<Longrightarrow> safe_formula (sometimes I \<phi>)"
  by (simp add: sometimes_def)

(* historically *)

lemma historically_rewrite_0_safe:
  assumes "mem I1 0" "bounded I1"
  assumes "I2 = flip_int I1"
shows "sat \<sigma> V v i (historically I1 \<phi>) = sat \<sigma> V v i (Or (Since \<phi> I2 (sometimes all \<phi>)) (Since \<phi> I1 (And first \<phi>)))"
proof (rule iffI)
  assume hist: "sat \<sigma> V v i (historically I1 \<phi>)"
  then have "sat \<sigma> V v i (Or (Since \<phi> I2 TT) (Since \<phi> I1 (And first \<phi>)))"
    using assms historically_rewrite_0
    by auto
  moreover {
    assume "sat \<sigma> V v i (Since \<phi> I1 (And first \<phi>))"
    then have "sat \<sigma> V v i (Or (Since \<phi> I2 (sometimes all \<phi>)) (Since \<phi> I1 (And first \<phi>)))" by auto
  }
  moreover{
    assume since: "sat \<sigma> V v i (Since \<phi> I2 TT)"
    have "sat \<sigma> V v i \<phi>" using hist assms(1) by auto
    then have "sat \<sigma> V v i (Or (Since \<phi> I2 (sometimes all \<phi>)) (Since \<phi> I1 (And first \<phi>)))"
      using since interval_all
      by auto
  }
  ultimately show "sat \<sigma> V v i (Or (Since \<phi> I2 (sometimes all \<phi>)) (Since \<phi> I1 (And first \<phi>)))"
    by auto
next
  assume "sat \<sigma> V v i (Or (Since \<phi> I2 (sometimes all \<phi>)) (Since \<phi> I1 (And first \<phi>)))"
  then have "sat \<sigma> V v i (Or (Since \<phi> I2 TT) (Since \<phi> I1 (And first \<phi>)))" by auto
  then show "sat \<sigma> V v i (historically I1 \<phi>)"
    using assms historically_rewrite_0
    by auto
qed

(* [0, b] *)
lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (Or (Since \<phi> I2 (sometimes all \<phi>)) (Since \<phi> I1 (And first \<phi>)))"
  by (simp add: sometimes_def)

(* [b, \<infinity>) *)
lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (And (once I2 (Prev all (Since \<phi> all (And \<phi> first)))) (once I1 \<phi>))"
  by simp

(* [a, b] *)
lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (And (once I1 \<phi>) (Neg (once I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
  by (simp add: sometimes_def once_def)

(* always *)

lemma always_rewrite_0_safe:
  fixes I1 I2 :: \<I>
  assumes "mem I1 0" "bounded I1"
  assumes "I2 = flip_int I1"
  shows "sat \<sigma> V v i (always I1 \<phi>) = sat \<sigma> V v i (Until \<phi> I2 (once all \<phi>))"
proof (rule iffI)
  assume all: "sat \<sigma> V v i (always I1 \<phi>)"
  then have "sat \<sigma> V v i (Until \<phi> I2 TT)" using assms always_rewrite_0 by auto
  moreover have  "sat \<sigma> V v i \<phi>" using all assms(1) by auto
  ultimately show "sat \<sigma> V v i (Until \<phi> I2 (once all \<phi>))"
    using interval_all
    by auto
next
  assume "sat \<sigma> V v i (Until \<phi> I2 (once all \<phi>))"
  then have "sat \<sigma> V v i (Until \<phi> I2 TT)" by auto
  then show "sat \<sigma> V v i (always I1 \<phi>)" using assms always_rewrite_0 by auto
qed

(* [0, b] *)
lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (Until \<phi> I2 (once all \<phi>))"
  by (simp add: once_def)

(* [a, b] *)
lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (And (sometimes I1 \<phi>) (Neg (sometimes I1 (And (Or (once I2 \<phi>) (sometimes I2 \<phi>)) (Neg \<phi>)))))"
  by (simp add: sometimes_def once_def)

abbreviation "safe_regex \<equiv> Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "safe_regex m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi>)"
  by (cases g) (auto dest!: safe_regex_safe[rotated] split: formula.splits[where formula=\<phi>])

lemma safe_abbrevs[simp]: "safe_formula TT" "safe_formula FF"
  unfolding TT_def FF_def by auto

definition safe_neg :: "formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> (\<not> safe_formula \<phi> \<longrightarrow> safe_formula (remove_neg \<phi>))"

definition atms :: "formula Regex.regex \<Rightarrow> formula set" where
  "atms r = (\<Union>\<phi> \<in> Regex.atms r.
     if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"

lemma atms_simps[simp]:
  "atms (Regex.Skip n) = {}"
  "atms (Regex.Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
  "atms (Regex.Plus r s) = atms r \<union> atms s"
  "atms (Regex.Times r s) = atms r \<union> atms s"
  "atms (Regex.Star r) = atms r"
  unfolding atms_def by auto

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) (auto split: formula.splits)

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma safe_formula_induct[consumes 1, case_names Eq_Const Eq_Var1 Eq_Var2 neq_Var Pred Let
    And_assign And_safe And_constraint And_Not Ands Neg Or Exists Agg
    Prev Next Since Not_Since Until Not_Until MatchP MatchF]:
  assumes "safe_formula \<phi>"
    and Eq_Const: "\<And>c d. P (Eq (Const c) (Const d))"
    and Eq_Var1: "\<And>c x. P (Eq (Const c) (Var x))"
    and Eq_Var2: "\<And>c x. P (Eq (Var x) (Const c))"
    and neq_Var: "\<And>x. P (Neg (Eq (Var x) (Var x)))"
    and Pred: "\<And>e ts. \<forall>t\<in>set ts. is_Var t \<or> is_Const t \<Longrightarrow> P (Pred e ts)"
    and Let: "\<And>p \<phi> \<psi>. {0..<nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Let p \<phi> \<psi>)"
    and And_assign: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_safe: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow>
      P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_constraint: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> \<not> safe_formula \<psi> \<Longrightarrow>
      fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> is_constraint \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_Not: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) (Neg \<psi>) \<Longrightarrow> \<not> safe_formula (Neg \<psi>) \<Longrightarrow>
      fv (Neg \<psi>) \<subseteq> fv \<phi> \<Longrightarrow> \<not> is_constraint (Neg \<psi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> (Neg \<psi>))"
    and Ands: "\<And>l pos neg. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula pos \<Longrightarrow> list_all safe_formula (map remove_neg neg) \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all P (map remove_neg neg) \<Longrightarrow> P (Ands l)"
    and Neg: "\<And>\<phi>. fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and Or: "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and Exists: "\<And>\<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Exists \<phi>)"
    and Agg: "\<And>y \<omega> b f \<phi>. y + b \<notin> fv \<phi> \<Longrightarrow> {0..<b} \<subseteq> fv \<phi> \<Longrightarrow> fv_trm f \<subseteq> fv \<phi> \<Longrightarrow>
      safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Agg y \<omega> b f \<phi>)"
    and Prev: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Prev I \<phi>)"
    and Next: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Next I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since \<phi> I \<psi>)"
    and Not_Since: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since (Neg \<phi>) I \<psi> )"
    and Until: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until \<phi> I \<psi>)"
    and Not_Until: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until (Neg \<phi>) I \<psi>)"
    and MatchP: "\<And>I r. safe_regex Past Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchP I r)"
    and MatchF: "\<And>I r. safe_regex Futu Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchF I r)"
  shows "P \<phi>"
using assms(1) proof (induction \<phi> rule: safe_formula.induct)
  case (1 t1 t2)
  then show ?case using Eq_Const Eq_Var1 Eq_Var2 by (auto simp: trm.is_Const_def trm.is_Var_def)
next
  case (9 \<phi> \<psi>)
  from \<open>safe_formula (And \<phi> \<psi>)\<close> have "safe_formula \<phi>" by simp
  from \<open>safe_formula (And \<phi> \<psi>)\<close> consider
    (a) "safe_assignment (fv \<phi>) \<psi>"
    | (b) "\<not> safe_assignment (fv \<phi>) \<psi>" "safe_formula \<psi>"
    | (c) "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "is_constraint \<psi>"
    | (d) \<psi>' where "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "\<not> is_constraint \<psi>"
        "\<psi> = Neg \<psi>'" "safe_formula \<psi>'"
    by (cases \<psi>) auto
  then show ?case proof cases
    case a
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_assign)
  next
    case b
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_safe)
  next
    case c
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_constraint)
  next
    case d
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (blast intro!: And_Not)
  qed
next
  case (10 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "pos \<noteq> []" using "10.prems" posneg by simp
  moreover have "list_all safe_formula pos" using posneg by (simp add: list.pred_set)
  moreover have safe_remove_neg: "list_all safe_formula (map remove_neg neg)" using "10.prems" posneg by auto
  moreover have "list_all P pos"
    using posneg "10.IH"(1) by (simp add: list_all_iff)
  moreover have "list_all P (map remove_neg neg)"
    using "10.IH"(2)[OF posneg] safe_remove_neg by (simp add: list_all_iff)
  ultimately show ?case using "10.IH"(1) "10.prems" Ands posneg by simp
next
  case (15 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "15.IH"(1) "15.IH"(3) "15.prems" Since by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
next
  case (16 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "16.IH"(1) "16.IH"(3) "16.prems" Until by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
next
  case (19 I r)
  then show ?case
    by (intro MatchP) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
next
  case (20 I r)
  then show ?case
    by (intro MatchF) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
qed (auto simp: assms)

lemma safe_formula_NegD:
  "safe_formula (Formula.Neg \<phi>) \<Longrightarrow> fv \<phi> = {} \<or> (\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x))"
  by (induct "Formula.Neg \<phi>" rule: safe_formula_induct) auto


subsection \<open>Slicing traces\<close>

qualified fun matches ::
  "env \<Rightarrow> formula \<Rightarrow> name \<times> event_data list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (fst e = r \<and> map (eval_trm v) ts = snd e)"
| "matches v (Let p \<phi> \<psi>) e =
    ((\<exists>v'. matches v' \<phi> e \<and> matches v \<psi> (p, v')) \<or>
    fst e \<noteq> p \<and> matches v \<psi> e)"
| "matches v (Eq _ _) e = False"
| "matches v (Less _ _) e = False"
| "matches v (LessEq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (And \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Ands l) e = (\<exists>\<phi>\<in>set l. matches v \<phi> e)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Agg y \<omega> b f \<phi>) e = (\<exists>zs. length zs = b \<and> matches (zs @ v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (MatchP I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (MatchF I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v' e)
  case (Pred n ts)
  show ?case
    by (simp cong: map_cong eval_trm_fv_cong[OF Pred(1)[simplified, THEN bspec]])
next
  case (Let p b \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> (set l) \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  proof -
    fix \<phi> assume "\<phi> \<in> (set l)"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "matches v \<phi> e = matches v' \<phi> e" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "matches (zs @ v) \<phi> e = matches (zs @ v') \<phi> e" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  then show ?case by auto
qed (auto 9 0 simp add: nth_Cons' fv_regex_alt)

abbreviation relevant_events where "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

lemma sat_slice_strong:
  assumes "v \<in> S" "dom V = dom V'"
    "\<And>p v i. p \<in> dom V \<Longrightarrow> (p, v) \<in> relevant_events \<phi> S \<Longrightarrow> v \<in> the (V p) i \<longleftrightarrow> v \<in> the (V' p) i"
  shows "relevant_events \<phi> S - {e. fst e \<in> dom V} \<subseteq> E \<Longrightarrow>
    sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  using assms
proof (induction \<phi> arbitrary: V V' v S i)
  case (Pred r ts)
  show ?case proof (cases "V r")
    case None
    then have "V' r = None" using \<open>dom V = dom V'\<close> by auto
    with None Pred(1,2) show ?thesis by (auto simp: domIff dest!: subsetD)
  next
    case (Some a)
    moreover obtain a' where "V' r = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "(map (eval_trm v) ts \<in> the (V r) i) = (map (eval_trm v) ts \<in> the (V' r) i)"
      using Some Pred(2,4) by (fastforce intro: domI)
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  from Let.prems show ?case unfolding sat.simps
  proof (intro Let(2)[of S], goal_cases relevant v dom V)
    case (V p' v' i)
    then show ?case
    proof (cases "p' = p")
      case [simp]: True
      with V show ?thesis
        unfolding fun_upd_apply eqTrueI[OF True] if_True option.sel mem_Collect_eq
      proof (intro ex_cong conj_cong refl Let(1)[where
        S="{v'. (\<exists>v \<in> S. matches v \<psi> (p, v'))}" and V=V],
        goal_cases relevant' v' dom' V')
        case relevant'
        then show ?case
          by (elim subset_trans[rotated]) (auto simp: set_eq_iff)
      next
        case (V' p' v' i)
        then show ?case
          by (intro V(4)) (auto simp: set_eq_iff)
      qed auto
    next
      case False
      with V(2,3,5,6) show ?thesis
        unfolding fun_upd_apply eq_False[THEN iffD2, OF False] if_False
        by (intro V(4)) (auto simp: False)
    qed
  qed (auto simp: dom_def)
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S V v V'] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (And \<phi> \<psi>)
  show ?case using And.IH[of S V v V'] And.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Ands l)
  obtain "relevant_events (Ands l) S - {e. fst e \<in> dom V} \<subseteq> E" "v \<in> S" using Ands.prems(1) Ands.prems(2) by blast
  then have "{e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}} - {e. fst e \<in> dom V} \<subseteq> E" by simp
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    have "relevant_events \<phi> S = {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}" by simp
    have "{e. S \<inter> {v. matches v \<phi> e} \<noteq> {}} \<subseteq> {e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}}" (is "?A \<subseteq> ?B")
    proof (rule subsetI)
      fix e assume "e \<in> ?A"
      then have "S \<inter> {v. matches v \<phi> e} \<noteq> {}" by blast
      moreover have "S \<inter> {v. matches v (Ands l) e} \<noteq> {}"
      proof -
        obtain v where "v \<in> S" "matches v \<phi> e" using calculation by blast
        then show ?thesis using \<open>\<phi> \<in> set l\<close> by auto
      qed
      then show "e \<in> ?B" by blast
    qed
    then have "relevant_events \<phi> S - {e. fst e \<in> dom V} \<subseteq> E" using Ands.prems(1) by auto
    then show "sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
      using Ands.prems(2,3) \<open>\<phi> \<in> set l\<close>
      by (intro Ands.IH[of \<phi> S V v V' i] Ands.prems(4)) auto
  qed
  show ?case using \<open>\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>\<close> sat_Ands by blast
next
  case (Exists \<phi>)
  have "sat \<sigma> V (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (z # v) i \<phi>" for z
    using Exists.prems(1-3) by (intro Exists.IH[where S="{z # v | v. v \<in> S}"] Exists.prems(4)) auto
  then show ?case by simp
next
  case (Agg y \<omega> b f \<phi>)
  have "sat \<sigma> V (zs @ v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (zs @ v) i \<phi>" if "length zs = b" for zs
    using that Agg.prems(1-3) by (intro Agg.IH[where S="{zs @ v | v. v \<in> S}"] Agg.prems(4)) auto
  then show ?case by (simp cong: conj_cong)
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S V] Since.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S V] Until.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (MatchP I r)
  from MatchP.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchP(1)[of _ S V v] MatchP.prems(4)) auto
  then show ?case
    by auto
next
  case (MatchF I r)
  from MatchF.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchF(1)[of _ S V v] MatchF.prems(4)) auto
  then show ?case
    by auto
qed simp_all


subsection \<open>Translation to n-ary conjunction\<close>

fun get_and_list :: "formula \<Rightarrow> formula list" where
  "get_and_list (Ands l) = l"
| "get_and_list \<phi> = [\<phi>]"

lemma fv_get_and: "(\<Union>x\<in>(set (get_and_list \<phi>)). fvi b x) = fvi b \<phi>"
  by (induction \<phi> rule: get_and_list.induct) simp_all

lemma safe_get_and: "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: safe_neg_def list_all_iff)

lemma sat_get_and: "sat \<sigma> V v i \<phi> \<longleftrightarrow> list_all (sat \<sigma> V v i) (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: list_all_iff)

primrec convert_multiway :: "formula \<Rightarrow> formula" where
  "convert_multiway (Pred p ts) = (Pred p ts)"
| "convert_multiway (Eq t u) = (Eq t u)"
| "convert_multiway (Less t u) = (Less t u)"
| "convert_multiway (LessEq t u) = (LessEq t u)"
| "convert_multiway (Let p \<phi> \<psi>) = Let p (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (Neg \<phi>) = Neg (convert_multiway \<phi>)"
| "convert_multiway (Or \<phi> \<psi>) = Or (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      And (convert_multiway \<phi>) \<psi>
    else if safe_formula \<psi> then
      Ands (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway \<psi>))
    else if is_constraint \<psi> then
      And (convert_multiway \<phi>) \<psi>
    else Ands (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>)))"
| "convert_multiway (Ands \<phi>s) = Ands (map convert_multiway \<phi>s)"
| "convert_multiway (Exists \<phi>) = Exists (convert_multiway \<phi>)"
| "convert_multiway (Agg y \<omega> b f \<phi>) = Agg y \<omega> b f (convert_multiway \<phi>)"
| "convert_multiway (Prev I \<phi>) = Prev I (convert_multiway \<phi>)"
| "convert_multiway (Next I \<phi>) = Next I (convert_multiway \<phi>)"
| "convert_multiway (Since \<phi> I \<psi>) = Since (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Until \<phi> I \<psi>) = Until (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Trigger \<phi> I \<psi>) = Trigger (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Release \<phi> I \<psi>) = Release (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (MatchP I r) = MatchP I (Regex.map_regex convert_multiway r)"
| "convert_multiway (MatchF I r) = MatchF I (Regex.map_regex convert_multiway r)"

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex convert_multiway"

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "get_and_list (Ands l) = l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (Ands l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (Ands l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  have "get_and_list (Ands l) = l" by simp
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed simp_all

lemma case_NegE: "(case \<phi> of Neg \<phi>' \<Rightarrow> P \<phi>' | _ \<Rightarrow> False) \<Longrightarrow> (\<And>\<phi>'. \<phi> = Neg \<phi>' \<Longrightarrow> P \<phi>' \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (cases \<phi>) simp_all

lemma convert_multiway_remove_neg: "safe_formula (remove_neg \<phi>) \<Longrightarrow> convert_multiway (remove_neg \<phi>) = remove_neg (convert_multiway \<phi>)"
  by (cases \<phi>) (auto elim: case_NegE)

lemma fv_convert_multiway: "safe_formula \<phi> \<Longrightarrow> fvi b (convert_multiway \<phi>) = fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: safe_formula.induct)
  case (9 \<phi> \<psi>)
  then show ?case by (cases \<psi>) (auto simp: fv_get_and Un_commute)
next
  case (10 l)
  then show ?case using convert_multiway_remove_neg
    unfolding convert_multiway.simps fvi.simps list.set_map image_image Let_def
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (fastforce simp: list.pred_set)
next
  case (15 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 15 show ?thesis by simp
  next
    case False
    with "15.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 15 show ?thesis by simp
  qed
next
  case (16 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 16 show ?thesis by simp
  next
    case False
    with "16.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 16 show ?thesis by simp
  qed
next
  case (19 I r)
  then show ?case
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (auto dest!: safe_regex_safe_formula)
next
  case (20 I r)
  then show ?case
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (auto dest!: safe_regex_safe_formula)
qed (auto simp del: convert_multiway.simps(8))

lemma nfv_convert_multiway: "safe_formula \<phi> \<Longrightarrow> nfv (convert_multiway \<phi>) = nfv \<phi>"
  unfolding nfv_def by (auto simp: fv_convert_multiway)

lemma get_and_nonempty:
  assumes "safe_formula \<phi>"
  shows "get_and_list \<phi> \<noteq> []"
  using assms by (induction \<phi>) auto

lemma future_bounded_get_and:
  "list_all future_bounded (get_and_list \<phi>) = future_bounded \<phi>"
  by (induction \<phi>) simp_all

lemma safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  show ?case proof -
    let ?l = "get_and_list ?c\<phi> @ get_and_list ?c\<psi>"
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    have lsafe_neg: "list_all safe_neg ?l"
      using And_safe \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
      by (simp add: safe_get_and)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> set neg \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by auto
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis by (auto simp: list_all_iff)
    qed

    have pos_filter: "pos = filter safe_formula (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
      using posneg by simp
    have "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)"
    proof -
      have 1: "fv ?c\<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<phi>))). fv x)" (is "_ \<subseteq> ?fv\<phi>")
        using And_safe \<open>safe_formula \<phi>\<close> by (blast intro!: fv_safe_get_and)
      have 2: "fv ?c\<psi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<psi>))). fv x)" (is "_ \<subseteq> ?fv\<psi>")
        using And_safe \<open>safe_formula \<psi>\<close> by (blast intro!: fv_safe_get_and)
      have "(\<Union>x\<in>set neg. fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>" proof -
        have "\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` (set pos \<union> set neg))"
          by simp
        also have "... \<subseteq> fv (convert_multiway \<phi>) \<union> fv (convert_multiway \<psi>)"
          unfolding partition_set[OF posneg[symmetric], simplified]
          by (simp add: fv_get_and)
        finally show ?thesis .
      qed
      then have "(\<Union>x\<in>set neg. fv x) \<subseteq> ?fv\<phi> \<union> ?fv\<psi>" using 1 2 by blast
      then show ?thesis unfolding pos_filter by simp
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_safe \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  show ?case proof -
    let ?l = "Neg ?c\<psi> # get_and_list ?c\<phi>"
    note \<open>safe_formula ?c\<phi>\<close>
    then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
    moreover have "safe_neg (Neg ?c\<psi>)"
      using \<open>safe_formula ?c\<psi>\<close> by (simp add: safe_neg_def)
    then have lsafe_neg: "list_all safe_neg ?l" using calculation by simp
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> (set neg) \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by (auto simp del: filter.simps)
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis using Ball_set_list_all by force
    qed

    have pos_filter: "pos = filter safe_formula ?l"
      using posneg by simp
    have neg_filter: "neg = filter (Not \<circ> safe_formula) ?l"
      using posneg by simp
    have "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set pos). fv x)"
    proof -
      have fv_neg: "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set ?l). fv x)" using posneg by auto
      have "(\<Union>x\<in>(set ?l). fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
        by (simp add: fv_get_and fv_convert_multiway)
      also have "fv ?c\<phi> \<union> fv ?c\<psi> \<subseteq> fv ?c\<phi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close> \<open>fv (Neg \<psi>) \<subseteq> fv \<phi>\<close>
        by (simp add: fv_convert_multiway[symmetric])
      finally have "(\<Union>x\<in>(set neg). fv x) \<subseteq> fv ?c\<phi>"
        using fv_neg unfolding neg_filter by blast
      then show ?thesis
        unfolding pos_filter
        using fv_safe_get_and[OF And_Not.IH(1)]
        by auto
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_Not.IH \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (Ands l)
  then show ?case
    using convert_multiway_remove_neg fv_convert_multiway
    apply (auto simp: list.pred_set filter_map filter_empty_conv subset_eq)
    by (metis fvi_remove_neg)
next
  case (Neg \<phi>)
  have "safe_formula (Neg \<phi>') \<longleftrightarrow> safe_formula \<phi>'" if "fv \<phi>' = {}" for \<phi>'
    using that by (cases "Neg \<phi>'" rule: safe_formula.cases) simp_all
  with Neg show ?case by (simp add: fv_convert_multiway)
next
  case (MatchP I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
next
  case (MatchF I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
qed (auto simp add: fv_convert_multiway nfv_convert_multiway)

lemma future_bounded_remove_neg: "future_bounded (remove_neg \<phi>) = future_bounded \<phi>"
  by (cases \<phi>) auto

lemma future_bounded_convert_multiway: "safe_formula \<phi> \<Longrightarrow> future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
proof (induction \<phi> rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_safe by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?c\<psi> = list_all future_bounded (get_and_list ?c\<psi>)"
    using \<open>safe_formula \<psi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    unfolding b_def by simp
  ultimately show ?case by simp
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_Not by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    unfolding b_def by (simp add: list.pred_map o_def)
  ultimately show ?case by auto
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
qed (auto simp: list.pred_set convert_multiway_remove_neg future_bounded_remove_neg)

lemma sat_convert_multiway: "safe_formula \<phi> \<Longrightarrow> sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> V v i \<phi>"
proof (induction \<phi> arbitrary: V v i rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "get_and_list (convert_multiway \<psi>)"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (?la @ ?lb)" using And_safe by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_safe sat_get_and by blast
  moreover have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>" using And_safe sat_get_and by blast
  ultimately show ?case using And_safe by (auto simp: list.pred_set)
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "convert_multiway \<psi>"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (Neg ?lb # ?la)" using And_Not by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_Not sat_get_and by blast
  then show ?case using And_Not by (auto simp: list.pred_set)
next
  case (Agg y \<omega> b f \<phi>)
  then show ?case
    by (simp add: nfv_def fv_convert_multiway cong: conj_cong)
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (Ands l)
  have sat_remove_neg: "(sat \<sigma> V v i (remove_neg \<phi>) \<longleftrightarrow> sat \<sigma> V v i (remove_neg \<psi>)) \<longleftrightarrow>
        (sat \<sigma> V v i \<phi> \<longleftrightarrow> sat \<sigma> V v i \<psi>)" if "is_Neg \<phi> \<longleftrightarrow> is_Neg \<psi>" for V v i \<phi> \<psi>
    using that by (cases \<phi>; cases \<psi>) (auto simp add: is_Neg_def)
  have is_Neg_cm: "is_Neg (convert_multiway \<phi>) \<longleftrightarrow> is_Neg \<phi>" for \<phi>
    by (cases \<phi>) auto
  from Ands show ?case
    by (fastforce simp: list.pred_set convert_multiway_remove_neg sat_remove_neg[OF is_Neg_cm])
qed (auto cong: nat.case_cong)

end (*context*)

interpretation Formula_slicer: abstract_slicer "relevant_events \<phi>" for \<phi> .

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (Formula_slicer.slice \<phi> S \<sigma>) V v i \<phi>"
  by (rule sat_slice_strong[OF assms]) auto

lemma Neg_splits:
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | \<phi> \<Rightarrow> g \<phi>) =
   ((\<forall>\<psi>. \<phi> = formula.Neg \<psi> \<longrightarrow> P (f \<psi>)) \<and> ((\<not> Formula.is_Neg \<phi>) \<longrightarrow> P (g \<phi>)))"
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> g \<phi>) =
   (\<not> ((\<exists>\<psi>. \<phi> = formula.Neg \<psi> \<and> \<not> P (f \<psi>)) \<or> ((\<not> Formula.is_Neg \<phi>) \<and> \<not> P (g \<phi>))))"
  by (cases \<phi>; auto simp: Formula.is_Neg_def)+

(*<*)
end
(*>*)
