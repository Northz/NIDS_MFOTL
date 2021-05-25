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

lemma fvi_abbrevs[simp]: "\<forall>b. fvi b TT = {}" "\<forall>b. fvi b FF = {}"
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

lemma interval_all: "mem all i"
  by transfer auto

qualified definition "first = Neg (Prev all TT)"

lemma first_sat[simp] : "sat \<sigma> V v i first = (i=0)"
  using interval_all by (auto simp: first_def split: nat.split)

lemma first_fvi[simp]: "fvi b first = {}"
  by (auto simp: first_def TT_def FF_def split: nat.split)

lemma interval_bounds:
  fixes a:: nat
  fixes b:: enat
  fixes I::\<I>
  assumes "a \<le> b"
  assumes "I = interval a b"
  shows "memL I = (\<lambda>i. a \<le> i) \<and> memR I = (\<lambda>i. enat i \<le> b) \<and> (bounded I = (b \<noteq> \<infinity>))"
  using assms
  by transfer auto

(* [a, b] \<Rightarrow> [b+1, \<infinity>] *)
lift_definition flip_int :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if bounded I then ((\<lambda>i. \<not>memR I i), (\<lambda>i. True), False) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

(* [a, b] \<Rightarrow> [b+1, 2b]. nonempty if b+1\<le>2b \<Leftrightarrow> 1\<le>b *)
lift_definition flip_int_double_upper :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if (bounded I) then ((\<lambda>i. \<not>memR I i), (\<lambda>i. memR I ((div) i 2)), True) else ((\<lambda>i. True), (\<lambda>i. True), False)"
proof -
  define A where "A = {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
  {
    fix I :: \<I>
    assume I_props: "bounded I"
    define B where "B = {x. \<not> memR I x}"
    define b where "b = Inf B"
    define x where "x = 2 * b"
    have up: "upclosed (\<lambda>i. \<not> memR I i)"
      using memR_antimono upclosed_def
      by blast
    {
      fix r m
      assume assumptions: "(\<lambda>i. memR I ((div) i 2)) r" "m\<le>r"
      then have "(\<lambda>i. memR I ((div) i 2)) m" by auto
    }
    then have "\<forall>m r. (\<lambda>i. memR I ((div) i 2)) r \<longrightarrow> m \<le> r \<longrightarrow> (\<lambda>i. memR I ((div) i 2)) m" by auto
    then have down: "downclosed (\<lambda>i. memR I ((div) i 2))" using downclosed_def by auto
    have "\<exists>b. \<not>memR I b" using I_props bounded_memR by auto
    then have B_props: "B \<noteq> {}" using B_def by auto
    then have "b \<in> B" using b_def by (simp add: Inf_nat_def1)
    then have b_props: "\<not> memR I b" using B_def by auto
    then have "0 < b" using memR_nonzeroD by blast
    then have b_half_props: "(b div 2) < b" by auto
    {
      assume "\<not> memR I (b div 2)"
      then have "(b div 2) \<in> B" using B_def by blast
      then have "(b div 2) \<ge> b" using cInf_lower b_def by auto
      then have "False" using b_half_props by auto
    }
    then have "memR I (b div 2)" by blast
    moreover have "\<not>memR I (x div 2)" using x_def b_props by auto
    ultimately have "(\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) \<in> A"
      using b_props A_def up down
      by auto
  }
  then have "\<forall>I. bounded I \<longrightarrow> (\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) \<in> A" by auto
  moreover have "\<forall>I. \<not>bounded I \<longrightarrow> (\<lambda>i. True, \<lambda>i. True, False) \<in> A"
    using A_def
    by (metis Interval.all.rep_eq Rep_\<I>)
  ultimately have "\<forall>I. (if bounded I then (\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) else (\<lambda>i. True, \<lambda>i. True, False)) \<in> A"
    by (auto split: if_splits)
  then show "\<And>\<I>. (if bounded \<I> then (\<lambda>i. \<not> memR \<I> i, \<lambda>i. memR \<I> (i div 2), True) else (\<lambda>i. True, \<lambda>i. True, False))
         \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using A_def
    by auto
qed

(* [a, b] \<Rightarrow> [0, a-1] *)
lift_definition flip_int_less_lower :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if \<not>memL I 0 then ((\<lambda>i. True), (\<lambda>i. \<not>memL I i), True) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

(* [a, b] \<Rightarrow> [0, b] *)
lift_definition int_remove_lower_bound :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. ((\<lambda>i. True), (\<lambda>i. memR I i), bounded I)"
  by transfer (auto simp: upclosed_def downclosed_def)

lemma flip_int_props:
  assumes "bounded I"
  assumes "I' = flip_int I"
  shows "\<not>bounded I' \<and> \<not>mem I' 0"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_props:
  assumes "\<not>memL I 0" (* [a, b] *)
  assumes "I' = flip_int_less_lower I" (* [0, a-1] *)
  shows "mem I' 0 \<and> bounded I'"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_memL:
  assumes "\<not>memL I x" (* [a, b], x < a *)
  shows "memL (flip_int_less_lower I) x" (* x \<in> [0, a-1] *)
  using assms
  by (transfer') (simp)

lemma flip_int_less_lower_memR:
  assumes "\<not>memL I 0" (* I = [a, b], I' = [0, a-1]. x \<le> a-1 *)
  shows "(memR (flip_int_less_lower I) x) = (\<not>memL I x)" (* x \<notin> [a, b] *)
  using assms
  by (transfer') (simp)

lemma flip_int_less_lower_mem:
  assumes "\<not>bounded I" "\<not>mem I x" (* [a, \<infinity>], x < a *)
  shows "mem (flip_int_less_lower I) x" (* x \<in> [0, a-1] *)
  using assms
  by (transfer') (simp add: bounded_memR)

lemma int_flip_mem:
  assumes "bounded I" "mem I 0" "\<not>mem I x" (* [0, a], a<x *)
  shows "mem (flip_int I) x" (* [a, \<infinity>] *)
  using assms memL_mono
  by (transfer') (auto split: if_splits)

lemma flip_int_double_upper_leq:
  assumes "mem (flip_int_double_upper I) x" (* x \<in> [b+1, 2b] *)
  assumes "\<not> mem (flip_int_double_upper I) y" "y\<le>x" (* y \<notin> [b+1, 2b] and y \<le> x *)
  assumes "mem I 0"
  shows "mem I y"
proof -
  from assms(2) have "\<not>memL (flip_int_double_upper I) y \<or> \<not>memR (flip_int_double_upper I) y" by auto
  moreover have "\<forall>m. m \<le> x \<longrightarrow> memR (flip_int_double_upper I) m" using assms(1) by auto
  ultimately have "\<not>memL (flip_int_double_upper I) y" using assms(3) by auto
  then show "mem I y" using assms(4) by (transfer') (auto split: if_splits)
qed

lemma int_remove_lower_bound_bounded: "bounded I \<Longrightarrow> bounded (int_remove_lower_bound I)"
  by (transfer') (auto)

lemma int_remove_lower_bound_mem: "mem I x \<Longrightarrow> mem (int_remove_lower_bound I) x"
  by (transfer') (auto)

lemma "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Since (Neg \<phi>) I (Neg \<psi>)))"
  by auto

lemma "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Until (Neg \<phi>) I (Neg \<psi>)))"
  by auto

definition release :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "release \<phi> I \<psi> = Neg (Until (Neg \<phi>) I (Neg \<psi>))"

lemma sat_release[simp]:
  "sat \<sigma> V v i (release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
  unfolding release_def
  by auto

lemma sat_release_eq[simp]: "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (release \<phi> I \<psi>)"
  by auto

definition once :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "once I \<phi> = Since TT I \<phi>"

lemma sat_once[simp] : "sat \<sigma> V v i (once I \<phi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: once_def)

lemma once_fvi[simp] : "fvi b (once I \<phi>) = fvi b \<phi>"
  by (auto simp: once_def)

definition historically :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically I \<phi> = (Neg (once I (Neg \<phi>)))"

lemma sat_historically[simp]: "sat \<sigma> V v i (historically I \<phi>) = (\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding historically_def
  by auto

(*lemma sat_historically_eq[simp]: "sat \<sigma> V v i (Historically I \<phi>) = sat \<sigma> V v i (historically I \<phi>)"
  by auto*)

definition eventually :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "eventually I \<phi> = Until TT I \<phi>"

lemma eventually_fvi[simp]: "fvi b (eventually I \<phi>) = fvi b \<phi>"
  by (auto simp: eventually_def)

lemma sat_eventually[simp]: "sat \<sigma> V v i (eventually I \<phi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: eventually_def)

definition always :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "always I \<phi> = (Neg (eventually I (Neg \<phi>)))"

(*lemma "sat \<sigma> V v i (Always I \<phi>) = sat \<sigma> V v i (Neg (eventually I (Neg \<phi>)))"
  by auto*)

lemma sat_always[simp]: "sat \<sigma> V v i (always I \<phi>) = (\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding always_def
  by auto

(*lemma sat_always_eq[simp]: "sat \<sigma> V v i (Always I \<phi>) = sat \<sigma> V v i (always I \<phi>)"
  by auto*)

(* case distrinction since intervals aren't allowed to be empty and flip_int [0, \<infinity>] would be *)
definition historically_safe_0 :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically_safe_0 I \<phi> = (if (bounded I) then (Or (Since \<phi> (flip_int I) (Next all \<phi>)) (Since \<phi> I (And first \<phi>))) else (Since \<phi> I (And first \<phi>)))"
                                                                                                        
definition historically_safe_unbounded :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically_safe_unbounded I \<phi> = (And (once (flip_int_less_lower I) (Prev all (Since \<phi> all (And \<phi> first)))) (once I \<phi>))"

definition historically_safe_bounded :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "historically_safe_bounded I \<phi> = (And (once I \<phi>) (Neg (once I (And (Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>)) (Neg \<phi>)))))"

definition always_safe_0 :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "always_safe_0 I \<phi> = (Or (Until \<phi> (flip_int_double_upper I) (Prev all \<phi>)) (Until \<phi> I (And \<phi> (Next (flip_int I) TT))))"

definition always_safe_bounded :: "\<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "always_safe_bounded I \<phi> = (And (eventually I \<phi>) (Neg (eventually I (And (Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>)) (Neg \<phi>)))))"

definition trigger_safe_0 :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "trigger_safe_0 \<phi> I \<psi> = Or (Since \<psi> I (And \<psi> \<phi>)) (historically_safe_0 I \<psi>)"

definition trigger_safe_unbounded :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "trigger_safe_unbounded \<phi> I \<psi> = And (once I TT) (Or (Or (historically_safe_unbounded I \<psi>) (once (flip_int_less_lower I) \<phi>)) (once (flip_int_less_lower I) (Prev all (Since \<psi> (int_remove_lower_bound I) (And \<phi> \<psi>)))))"

definition trigger_safe_bounded :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "trigger_safe_bounded \<phi> I \<psi> = And (once I TT) (Or (Or (historically_safe_bounded I \<psi>) (once (flip_int_less_lower I) \<phi>)) (once (flip_int_less_lower I) (Prev all (Since \<psi> (int_remove_lower_bound I) (And \<phi> \<psi>)))))"

definition release_safe_0 :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "release_safe_0 \<phi> I \<psi> = Or (Until \<psi> I (And \<psi> \<phi>)) (always_safe_0 I \<psi>)"

definition release_safe_bounded :: "formula \<Rightarrow> \<I> \<Rightarrow> formula \<Rightarrow> formula" where
  "release_safe_bounded \<phi> I \<psi> = And (eventually I TT) (Or (Or (always_safe_bounded I \<psi>) (eventually (flip_int_less_lower I) \<phi>)) (eventually (flip_int_less_lower I) (Next all (Until \<psi> (int_remove_lower_bound I) (And \<psi> \<phi>)))))"

lemma since_true:
  assumes "\<not>mem I 0"
  shows "sat \<sigma> V v i (Since \<phi> I TT) = sat \<sigma> V v i (Since \<phi> I (Next all \<phi>))"
proof (rule iffI)
  assume "sat \<sigma> V v i (Since \<phi> I TT)"
  then obtain j where j_props: "j\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" "\<forall>k\<in>{j<..i}. sat \<sigma> V v k \<phi>" by auto
  {
    assume "j=i"
    then have "False" using j_props assms by auto
  }
  then have "j<i" using j_props(1) using le_eq_less_or_eq by blast
  then show "sat \<sigma> V v i (Since \<phi> I (Next all \<phi>))"
    using j_props interval_all
    by (auto intro!: exI[of _ j])
next
  assume "sat \<sigma> V v i (Since \<phi> I (Next all \<phi>))"
  then show "sat \<sigma> V v i (Since \<phi> I TT)" by auto
qed

lemma until_true:
  assumes "\<not>mem I 0"
  shows "sat \<sigma> V v i (Until \<phi> I TT) = sat \<sigma> V v i (Until \<phi> I (Prev all \<phi>))"
proof (rule iffI)
  assume "sat \<sigma> V v i (Until \<phi> I TT)"
  then obtain j where j_props: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. sat \<sigma> V v k \<phi>" by auto
  {
    assume "j=i"
    then have "False" using j_props assms by auto
  }
  then have "j>i" using j_props(1) using le_eq_less_or_eq by blast
  then show "sat \<sigma> V v i (Until \<phi> I (Prev all \<phi>))"
    using j_props interval_all
    by (auto split: nat.split intro!: exI[of _ j])
next
  assume "sat \<sigma> V v i (Until \<phi> I (Prev all \<phi>))"
  then show "sat \<sigma> V v i (Until \<phi> I TT)" by auto
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

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

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

definition safe_formula_dual where "
  safe_formula_dual b safe_formula \<phi> I \<psi> = (if (mem I 0) then
    (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> (
      safe_formula \<phi> \<comment> \<open>\<or> safe_assignment (fv \<psi>) \<phi> \<or> is_constraint \<phi>\<close> \<or>
      (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)
    ))
      else
    b \<and> (safe_formula \<phi> \<and> safe_formula \<psi> \<and> fv \<phi> = fv \<psi>))
"

lemma safe_formula_dual_impl:
  assumes "\<forall>x. P x \<longrightarrow> Q x"
  shows "safe_formula_dual b P \<phi> I \<psi> \<Longrightarrow> safe_formula_dual b Q \<phi> I \<psi>"
  using assms unfolding safe_formula_dual_def by (auto split: if_splits formula.splits)

lemma safe_formula_dual_size [fundef_cong]:
  assumes "\<And>f. size f \<le> size \<phi> + size \<psi> \<Longrightarrow> safe_formula f = safe_formula' f"
  shows "safe_formula_dual b safe_formula \<phi> I \<psi> = safe_formula_dual b safe_formula' \<phi> I \<psi>"
  using assms
  by (auto simp add: safe_formula_dual_def split: formula.splits)


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
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>'
      | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
      | _ \<Rightarrow> False
    ))))"
| "safe_formula (Ands l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg \<and>
    \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))
  )"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Agg y \<omega> b f \<phi>) = (safe_formula \<phi> \<and> y + b \<notin> fv \<phi> \<and> {0..<b} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
| "safe_formula (Until \<phi> I \<psi>) = (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
| "safe_formula (Trigger \<phi> I \<psi>) = safe_formula_dual False safe_formula \<phi> I \<psi>"
| "safe_formula (Release \<phi> I \<psi>) = safe_formula_dual False safe_formula \<phi> I \<psi>"
| "safe_formula (MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "safe_formula (MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Futu Strict r"


lemma safe_abbrevs[simp]: "safe_formula TT" "safe_formula FF"
  unfolding TT_def FF_def by auto

lemma TT_future_bounded[simp]: "future_bounded TT"
  by (simp add: TT_def FF_def)

lemma first_fv[simp]: "fv first = {}"
  by (simp add: first_def)

lemma first_safe[simp]: "safe_formula first"
  by (simp add: first_def)

lemma first_future_bounded[simp]: "future_bounded first"
  by (simp add: first_def)

lemma once_fv[simp]: "fv (once I \<phi>) = fv \<phi>"
  by (simp add: once_def)

lemma once_safe[simp]: "safe_formula (once I \<phi>) = safe_formula \<phi>"
  by (simp add: once_def)

lemma once_future_bounded[simp]: "future_bounded (once I \<phi>) = future_bounded \<phi>"
  by (simp add: once_def)

lemma eventually_fv[simp]: "fv (eventually I \<phi>) = fv \<phi>"
  by (simp add: eventually_def)

lemma eventually_safe[simp]: "safe_formula (eventually I \<phi>) = safe_formula \<phi>"
  by (simp add: eventually_def)

lemma eventually_future_bounded[simp]: "future_bounded (eventually I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (simp add: eventually_def)

(* historically *)

(* [0, b] *)
lemma historically_safe_0_safe[simp]: "safe_formula (historically_safe_0 I \<phi>) = safe_formula \<phi>"
  apply (auto simp add: historically_safe_0_def safe_assignment_def split: formula.splits)
  subgoal for \<phi>
    by (cases \<phi>) (auto simp add: is_Const_def)
  subgoal for \<phi>
    by (cases \<phi>) (auto simp add: is_Const_def)
  done

lemma historically_safe_0_fv[simp]: "fv (historically_safe_0 I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_0_def)

lemma historically_safe_0_future_bounded[simp]: "future_bounded (historically_safe_0 I \<phi>) = future_bounded \<phi>"
  by (simp add: historically_safe_0_def eventually_def)

(* [b, \<infinity>) *)

lemma historically_safe_unbounded_safe[simp]:"safe_formula (historically_safe_unbounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_unbounded_fv[simp]: "fv (historically_safe_unbounded I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_future_bounded[simp]:"future_bounded (historically_safe_unbounded I \<phi>) = future_bounded \<phi>"
  by (simp add: historically_safe_unbounded_def)

(* [a, b] *)

lemma historically_safe_bounded_safe[simp]: "safe_formula (historically_safe_bounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma historically_safe_bounded_fv[simp]: "fv (historically_safe_bounded I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma historically_safe_bounded_future_bounded[simp]: "future_bounded (historically_safe_bounded I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (auto simp add: historically_safe_bounded_def bounded.rep_eq int_remove_lower_bound.rep_eq)

(*lemma "mem I 0 \<Longrightarrow> safe_formula (historically I \<phi>) = safe_formula (historically_safe_0 I \<phi>)"
  unfolding historically_def once_def
  by auto

lemma "\<not>mem I 0 \<Longrightarrow> \<not>bounded I \<Longrightarrow> safe_formula (historically I \<phi>) = safe_formula (historically_safe_unbounded I \<phi>)"
  by auto

lemma "\<not>mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> safe_formula (historically I \<phi>) = safe_formula (historically_safe_bounded I \<phi>)"
  by auto*)

(* always *)

(* [0, b] *)

lemma always_safe_0_safe[simp]: "safe_formula (always_safe_0 I \<phi>) = safe_formula \<phi>"
  by (auto simp add: always_safe_0_def)

lemma always_safe_0_safe_fv[simp]: "fv (always_safe_0 I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_0_def)

lemma always_safe_0_future_bounded[simp]: "future_bounded (always_safe_0 I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (simp add: always_safe_0_def bounded.rep_eq flip_int_double_upper.rep_eq)

(* [a, b] *)

lemma always_safe_bounded_safe[simp]: "safe_formula (always_safe_bounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: always_safe_bounded_def)

lemma always_safe_bounded_fv[simp]: "fv (always_safe_bounded I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_bounded_def)

lemma always_safe_bounded_future_bounded[simp]: "future_bounded (always_safe_bounded I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (auto simp add: always_safe_bounded_def bounded.rep_eq int_remove_lower_bound.rep_eq)

(*lemma "mem I 0 \<Longrightarrow> safe_formula (always I \<phi>) = safe_formula (always_safe_0 I \<phi>)"
  by auto

lemma "\<not>mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> safe_formula (always I \<phi>) = safe_formula (always_safe_bounded I \<phi>)"
  by auto*)                        
  

abbreviation "safe_regex \<equiv> Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "safe_regex m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi>)"
  by (cases g) (auto dest!: safe_regex_safe[rotated] split: formula.splits[where formula=\<phi>])

definition safe_neg :: "formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> (\<not> safe_formula \<phi> \<longrightarrow> (case \<phi> of (Neg \<phi>') \<Rightarrow> safe_formula \<phi>' | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> False) )"

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
    And_assign And_safe And_constraint And_Not And_Trigger And_Not_Trigger
    Ands Neg Or Exists Agg
    Prev Next
    Since Not_Since Until Not_Until
    Trigger_0 Trigger
    Release_0 Release
    MatchP MatchF]:
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
    and And_Trigger: "\<And>\<phi> \<phi>' I \<psi>'. safe_formula \<phi> \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' \<Longrightarrow> fv (Trigger \<phi>' I \<psi>') \<subseteq> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<phi>' \<Longrightarrow> P \<psi>' \<Longrightarrow> P (And \<phi> (Trigger \<phi>' I \<psi>'))"
    and And_Not_Trigger: "\<And>\<phi> \<phi>' I \<psi>'. safe_formula \<phi> \<Longrightarrow> \<not>safe_formula (Neg \<phi>') \<Longrightarrow> safe_formula_dual True safe_formula (Neg \<phi>') I \<psi>' \<Longrightarrow> fv (Trigger \<phi>' I \<psi>') \<subseteq> fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<phi>' \<Longrightarrow> P \<psi>' \<Longrightarrow> P (And \<phi> (Trigger (Neg \<phi>') I \<psi>'))"
    and Ands: "\<And>l pos neg. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula pos \<Longrightarrow> list_all (\<lambda>\<phi>. (case \<phi> of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
          | _ \<Rightarrow> safe_formula \<phi>
        )
      ) neg \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all (\<lambda>\<phi>. (case \<phi> of
          Neg \<phi>' \<Rightarrow> P \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> P \<psi>' \<and> (if mem I 0 then
              P \<phi>' \<or> (case \<phi>' of
                (Neg \<phi>'') \<Rightarrow> P \<phi>''
                | _ \<Rightarrow> False
              )
            else
              P \<phi>'
          )
          | _ \<Rightarrow> P \<phi>
        )
      ) neg \<Longrightarrow> P (Ands l)"
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
    and Trigger_0: "\<And>\<phi> I \<psi>. mem I 0 \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> 
      ((safe_formula \<phi> \<and> P \<phi>) \<or> \<comment> \<open>(safe_assignment (fv \<psi>) \<phi>) \<or> is_constraint \<phi> \<or>\<close> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> P \<phi>' | _ \<Rightarrow> False)) \<Longrightarrow> P \<psi> \<Longrightarrow> P (Trigger \<phi> I \<psi>)"
    and Trigger: "\<And>\<phi> I \<psi>. False \<Longrightarrow> \<not>mem I 0 \<Longrightarrow> fv \<phi> = fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Trigger \<phi> I \<psi>)" (* TODO: remove False *)
    and Release_0: "\<And>\<phi> I \<psi>. mem I 0 \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> 
      ((safe_formula \<phi> \<and> P \<phi>) \<or> \<comment> \<open>(safe_assignment (fv \<psi>) \<phi>) \<or> is_constraint \<phi> \<or>\<close> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> P \<phi>' | _ \<Rightarrow> False)) \<Longrightarrow> P \<psi> \<Longrightarrow> P (Release \<phi> I \<psi>)"
    and Release: "\<And>\<phi> I \<psi>. False \<Longrightarrow> \<not>mem I 0 \<Longrightarrow> fv \<phi> = fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Release \<phi> I \<psi>)" (* TODO: remove False *)
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
    | (e) \<phi>' I \<psi>' where "\<psi> = Trigger \<phi>' I \<psi>'" "safe_formula_dual True safe_formula \<phi>' I \<psi>'" "fv \<psi> \<subseteq> fv \<phi>"
    by (cases \<psi>) (auto)
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
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (auto intro!: And_Not)
  next
    case e
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close>
    proof (cases "safe_formula \<phi>'")
      case False
      then obtain \<phi>'' where \<phi>'_def: "\<phi>' = Neg \<phi>''"
        using e
        by (auto simp add: safe_formula_dual_def split: if_splits formula.splits)
      show ?thesis
        using "9.IH" \<open>safe_formula \<phi>\<close> e False
        by (auto intro!: And_Not_Trigger simp add: safe_formula_dual_def \<phi>'_def split: if_splits formula.splits)
    qed (auto intro!: And_Trigger simp add: safe_formula_dual_def split: if_splits formula.splits)
  qed
next
  case (10 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "pos \<noteq> []" using "10.prems" posneg by simp
  moreover have "list_all safe_formula pos" using posneg by (simp add: list.pred_set)
  moreover have neg_props: "\<forall>\<phi> \<in> set neg. ((case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    )"
    using "10.prems" posneg
    by (simp add: list.pred_set)
  moreover have "list_all P pos"
    using posneg "10.IH"(1) by (simp add: list_all_iff)
  moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
          Neg \<phi>' \<Rightarrow> P \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> P \<psi>' \<and> (if mem I 0 then
              P \<phi>' \<or> (case \<phi>' of
                (Neg \<phi>'') \<Rightarrow> P \<phi>''
                | _ \<Rightarrow> False
              )
            else
              P \<phi>'
          )
          | _ \<Rightarrow> P \<phi>
        )
      ) neg"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set neg"
      then have \<phi>_props: "case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | Trigger \<phi>' I \<psi>' \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> safe_formula \<phi>"
        using neg_props
        by blast
      
      have "(case \<phi> of
          Neg \<phi>' \<Rightarrow> P \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> P \<psi>' \<and> (if mem I 0 then
              P \<phi>' \<or> (case \<phi>' of
                (Neg \<phi>'') \<Rightarrow> P \<phi>''
                | _ \<Rightarrow> False
              )
            else
              P \<phi>'
          )
          | _ \<Rightarrow> P \<phi>
        )"
      using "10.IH"(2-)[OF posneg _ assm] \<phi>_props
      proof (cases \<phi>)
        case (Trigger \<phi>' I \<psi>')
        then have safe_dual: "safe_formula_dual True safe_formula \<phi>' I \<psi>'"
          using \<phi>_props
          by auto
        then have "P \<psi>'"
          using "10.IH"(17)[OF posneg _ assm Trigger]
          unfolding safe_formula_dual_def
          by (auto split: if_splits formula.splits)
        moreover have "(if mem I 0 then P \<phi>' \<or> (case \<phi>' of (Neg \<phi>'') \<Rightarrow> P \<phi>'' | _ \<Rightarrow> False) else P \<phi>')"
        proof (cases "mem I 0")
          case True
          have "P \<phi>' \<or> (case \<phi>' of (Neg \<phi>'') \<Rightarrow> P \<phi>'' | _ \<Rightarrow> False)"
          proof (cases "safe_formula \<phi>'")
            case True
            then show ?thesis
              using "10.IH"(17)[OF posneg _ assm Trigger]
              by auto
          next
            case False
            then obtain \<phi>'' where \<phi>''_props: "\<phi>' = Neg \<phi>''" "safe_formula \<phi>''"
              using safe_dual True
              unfolding safe_formula_dual_def
              by (auto split: if_splits formula.splits)
            then have "P \<phi>''"
              using "10.IH"(17)[OF posneg _ assm Trigger]
              by auto
            then show ?thesis using \<phi>''_props by auto
          qed
            
          then show ?thesis using True by auto
        next
          case False
          then have "safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>'"
            using safe_dual
            unfolding safe_formula_dual_def
            by auto
          then have "P \<phi>'"
            using "10.IH"(17)[OF posneg _ assm Trigger]
            by auto
          then show ?thesis using False by auto
        qed
          
        ultimately show ?thesis using Trigger by (auto split: formula.splits)
      qed (auto split: formula.splits)
    }
    then show ?thesis
      by (metis (no_types, lifting) Ball_set_list_all)
  qed
  ultimately show ?case using "10.prems" Ands posneg by simp
next
  case (15 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "15.IH"(1-2) "15.prems" Since by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
next
  case (16 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "16.IH"(1-2)"16.prems" Until by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
next
  case (17 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    show ?thesis
    proof (cases "case \<phi> of Neg x \<Rightarrow> safe_formula x | _ \<Rightarrow> False")
      case True
      then obtain \<phi>' where "\<phi> = Neg \<phi>'"
        by (auto split: formula.splits)
      then show ?thesis using mem 17 Trigger_0 by (auto simp add: safe_formula_dual_def)
    next
      case False
      then show ?thesis using mem 17 Trigger_0 by (auto simp add: safe_formula_dual_def)
    qed
  next
    case False
    then show ?thesis using Trigger 17 by (auto simp add: safe_formula_dual_def)
  qed
next
  case (18 \<phi> I \<psi>)
  then show ?case
  proof (cases "mem I 0")
    case mem: True
    show ?thesis
    proof (cases "case \<phi> of Neg x \<Rightarrow> safe_formula x | _ \<Rightarrow> False")
      case True
      then obtain \<phi>' where "\<phi> = Neg \<phi>'"
        by (auto split: formula.splits)
      then show ?thesis using mem 18 Release_0 by (auto simp add: safe_formula_dual_def)
    next
      case False
      then show ?thesis using mem 18 Release_0 by (auto simp add: safe_formula_dual_def)
    qed
  next
    case False
    then show ?thesis using Release 18 by (auto simp add: safe_formula_dual_def)
  qed
next
  case (19 I r)
  then show ?case
    by (intro MatchP) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
next
  case (20 I r)
  then show ?case
    by (intro MatchF) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
qed (auto simp: assms)

lemma safe_formula_Neg: "safe_formula (Formula.Neg \<phi>) = ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>))"
  by (induct "Formula.Neg \<phi>" rule: safe_formula.induct) auto

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
| "matches v (Trigger \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Release \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
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
  case (Trigger \<phi> I \<psi>)
  show ?case using Trigger.IH[of S V] Trigger.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Release \<phi> I \<psi>)
  show ?case using Release.IH[of S V] Release.prems
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
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  then have "\<forall>\<phi> \<in> set l. \<not>safe_formula \<phi> \<longrightarrow> (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )"
    by (simp add: o_def list_all_iff)
  then have "\<forall>\<phi> \<in> set l. \<not>safe_formula \<phi> \<longrightarrow> (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> False
      )"
    by presburger
  then show ?case
    by (auto simp add: safe_neg_def list_all_iff)
qed (auto simp add: safe_neg_def list_all_iff )

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

lemma fv_convert_multiway: "fvi b (convert_multiway \<phi>) = fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: safe_formula.induct)
  case (9 \<phi> \<psi>)
  then show ?case by (cases \<psi>) (auto simp: fv_get_and Un_commute safe_formula_dual_def)
next
  case (10 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula (map convert_multiway l)" by simp
  {
    fix \<phi>
    assume assm: "\<phi> \<in> set l"
    then have "fvi b \<phi> = fvi b (convert_multiway \<phi>)"
      using 10(1)[OF assm]
      by auto
  }
  then show ?case by auto
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

lemma nfv_convert_multiway: "nfv (convert_multiway \<phi>) = nfv \<phi>"
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
    have list_all_neg: "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
    proof -
      have "\<And>x. x \<in> set neg \<Longrightarrow> (case x of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula x
      )"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by auto
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "(case x of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
          | _ \<Rightarrow> safe_formula x
        )" unfolding safe_neg_def
          by presburger
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
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> list_all_neg \<open>list_all safe_formula pos\<close> posneg
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
    
    have list_all_neg: "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
    proof -
      have "\<And>x. x \<in> (set neg) \<Longrightarrow> (case x of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula x
      )"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by (auto simp del: filter.simps)
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "(case x of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
          | _ \<Rightarrow> safe_formula x
        )" unfolding safe_neg_def
          by presburger
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
        by (auto simp add: fv_convert_multiway)
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
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> list_all_neg \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger \<phi>' I \<psi>'"
  define f where "f = And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have "\<exists>f \<in> set (get_and_list (convert_multiway \<phi>)). safe_formula f"
  proof -
    {
      assume assm: "\<forall>f \<in> set (get_and_list (convert_multiway \<phi>)). \<not>safe_formula f"
      then have "False"
      proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
        case True
        then obtain l where "convert_multiway \<phi> = Ands l"
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Trigger(5)
          by auto
      next
        case False
        then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
          using assm
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Trigger(5)
          by auto
      qed
    }
    then show ?thesis by auto
  qed
  then have filter_pos: "filter safe_formula (get_and_list (convert_multiway \<phi>)) \<noteq> []"
    by (simp add: filter_empty_conv)

  have \<phi>_fvs: "\<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>)))))) \<subseteq> \<Union>(set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
    using And_Trigger
    by (cases "(convert_multiway \<phi>)") (auto)

  show ?case
  proof (cases "safe_formula t")
    define l where "l = get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t)"
    define pos where "pos = fst (partition safe_formula l)"
    define neg where "neg = snd (partition safe_formula l)"

    case True
    then have convert_f: "convert_multiway f = Ands l"
      unfolding f_def l_def
      using t_not_safe_assign
      by auto

    have "safe_formula (convert_multiway t)"
      using And_Trigger True
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def fv_convert_multiway)
    then have neg_fv: "\<Union>(set (map fv neg)) = \<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      unfolding neg_def l_def t_def
      by auto

    have mem:
      "mem I 0"
      "safe_formula \<psi>'"
      "fv \<phi>' \<subseteq> fv \<psi>'"
      "safe_formula \<phi>'"
      using True And_Trigger
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def)

    have "filter safe_formula pos \<noteq> []"
      using filter_pos
      unfolding pos_def l_def
      by auto
    moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
      using And_Trigger mem
      unfolding l_def neg_def t_def
      by (cases "(convert_multiway \<phi>)") (auto simp add: safe_formula_dual_def fv_convert_multiway)
    moreover have "\<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))"
      using \<phi>_fvs neg_fv
      unfolding l_def pos_def
      by (auto simp add: fv_convert_multiway)
    ultimately have "safe_formula (Ands l)"
      unfolding pos_def neg_def
      by auto
    then show ?thesis
      using convert_f
      unfolding f_def t_def
      by auto
  next
    define l where "l = convert_multiway t # get_and_list (convert_multiway \<phi>)"
    define pos where "pos = fst (partition safe_formula l)"
    define neg where "neg = snd (partition safe_formula l)"

    case False
    then have convert_f: "convert_multiway f = Ands l"
      unfolding f_def l_def
      using t_not_safe_assign t_not_constraint
      by auto

    have unsafe: "\<not>safe_formula (convert_multiway t)"
      using And_Trigger False
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def fv_convert_multiway)
    then have pos_fv: "\<Union>(set (map fv pos)) = \<Union>(set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      unfolding pos_def l_def t_def
      by auto

    have neg_eq: "neg = convert_multiway t # snd (partition safe_formula (get_and_list (convert_multiway \<phi>)))"
      using unsafe
      unfolding neg_def l_def
      by auto

    have "\<Union> (set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>)))))) = fv \<phi>"
    proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
      case True
      then obtain l where l_props: "(convert_multiway \<phi>) = Ands l"
        by (auto split: formula.splits)
      then have "get_and_list (convert_multiway \<phi>) = l"
        by auto
      then have "fv \<phi> = fv (Ands l)"
        using l_props fv_convert_multiway[of 0 \<phi>]
        by auto
      then show ?thesis
        using l_props And_Trigger(5) l_props
        by auto
    next
      case False
      then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
        by (auto split: formula.splits)
      then show ?thesis
        using And_Trigger(5)
        by (auto simp add: fv_convert_multiway)
    qed
    then have t_fvs: "fv (convert_multiway t) \<subseteq> \<Union> (set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      using And_Trigger(4)
      unfolding t_def
      by (auto simp add: fv_convert_multiway)

    then have mem: "\<not>mem I 0 \<or> (case \<phi>' of Formula.Neg \<phi>'' \<Rightarrow> \<not> safe_formula \<phi>'' | _ \<Rightarrow> True)"
      using False And_Trigger
      unfolding t_def safe_formula_dual_def
      by (auto simp add: safe_formula_dual_def)

    have unsafe_convert_t: "\<not> safe_formula (convert_multiway t)"
      using False And_Trigger
      unfolding t_def
      by (auto simp add: safe_formula_dual_def)
    then have unsafe_convert_t_rem_neg: "\<not>safe_formula (convert_multiway t)"
      unfolding t_def
      by auto

    have filter_pos: "filter safe_formula pos \<noteq> []"
      using filter_pos
      unfolding pos_def l_def
      by auto
    moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
    proof -
      {
        fix \<alpha>
        assume assm: "\<alpha> \<in> set neg"

        have "(case \<alpha> of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
          | _ \<Rightarrow> safe_formula \<alpha>
        )"
        proof (cases "\<alpha> \<in> set (snd (partition safe_formula (get_and_list (convert_multiway \<phi>))))")
          case True
          then have \<alpha>_props:
            "\<not>safe_formula \<alpha>"
            "\<alpha> \<in> set (get_and_list (convert_multiway \<phi>))"
            by auto
          then show ?thesis
          proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
            case True
            then obtain l where l_props: "(convert_multiway \<phi>) = Ands l"
              by (auto split: formula.splits)
            then have "safe_formula (Ands l)"
              using And_Trigger(5)
              by auto
            then have "list_all (\<lambda>\<phi>. case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | Trigger \<phi>' I \<psi>' \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> safe_formula \<phi>)
              (filter (\<lambda>f. \<not> safe_formula f) l)"
              by (auto simp add: o_def)
            then have "\<forall>\<phi> \<in> set (filter (\<lambda>f. \<not> safe_formula f) l). case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | Trigger \<phi>' I \<psi>' \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> safe_formula \<phi>"
              by (simp add: list.pred_set)
            moreover have "\<alpha> \<in> set (filter (\<lambda>f. \<not> safe_formula f) l)"
              using \<alpha>_props l_props
              by auto
            ultimately show ?thesis
              by auto
          next
            case False
            then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
              by (auto split: formula.splits)
            then have "False"
              using \<alpha>_props And_Trigger(5)
              by auto
            then show ?thesis by auto
          qed
        next
          case False
          then have "\<alpha> = convert_multiway t"
            using assm neg_eq
            by auto
          then show ?thesis
            using And_Trigger
            unfolding t_def safe_formula_dual_def
            by (auto simp add: fv_convert_multiway split: if_splits)
        qed
      }
      then show ?thesis by (auto simp: list_all_iff)
    qed
    moreover have "\<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))"
      using pos_fv \<phi>_fvs t_fvs
      unfolding neg_def l_def t_def
      by (auto simp add: fv_convert_multiway)
    ultimately have "safe_formula (Ands l)"
      unfolding pos_def neg_def
      by auto
    then show ?thesis
      using convert_f
      unfolding f_def t_def
      by auto
  qed
next
  case (And_Not_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = (Trigger (Neg \<phi>') I \<psi>')"
  define f where "f = And \<phi> t"

  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    unfolding t_def
    by auto

  have "\<exists>f \<in> set (get_and_list (convert_multiway \<phi>)). safe_formula f"
  proof -
    {
      assume assm: "\<forall>f \<in> set (get_and_list (convert_multiway \<phi>)). \<not>safe_formula f"
      then have "False"
      proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
        case True
        then obtain l where "convert_multiway \<phi> = Ands l"
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Not_Trigger(5)
          by auto
      next
        case False
        then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
          using assm
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Not_Trigger(5)
          by auto
      qed
    }
    then show ?thesis by auto
  qed
  then have filter_pos: "filter safe_formula (get_and_list (convert_multiway \<phi>)) \<noteq> []"
    by (simp add: filter_empty_conv)

  have \<phi>_fvs: "\<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>)))))) \<subseteq> \<Union>(set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
    using And_Not_Trigger
    by (cases "(convert_multiway \<phi>)") (auto)

  then show ?case
  proof (cases "safe_formula t")
    define l where "l = get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t)"
    define pos where "pos = fst (partition safe_formula l)"
    define neg where "neg = snd (partition safe_formula l)"

    case True
    then have convert_f: "convert_multiway f = Ands l"
      unfolding f_def l_def
      using t_not_safe_assign
      by auto

    have "safe_formula (convert_multiway t)"
      using And_Not_Trigger True
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def fv_convert_multiway)
    then have neg_fv: "\<Union>(set (map fv neg)) = \<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      unfolding neg_def l_def t_def
      by auto

    have mem:
      "mem I 0"
      "safe_formula \<psi>'"
      "fv \<phi>' \<subseteq> fv \<psi>'"
      "safe_formula \<phi>'"
      using True And_Not_Trigger
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def)

    have "filter safe_formula pos \<noteq> []"
      using filter_pos
      unfolding pos_def l_def
      by auto
    moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
      using And_Not_Trigger mem
      unfolding l_def neg_def t_def
      by (cases "(convert_multiway \<phi>)") (auto simp add: safe_formula_dual_def fv_convert_multiway)
    moreover have "\<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))"
      using \<phi>_fvs neg_fv
      unfolding l_def pos_def
      by (auto simp add: fv_convert_multiway)
    ultimately have "safe_formula (Ands l)"
      unfolding pos_def neg_def
      by auto
    then show ?thesis
      using convert_f
      unfolding f_def t_def
      by auto
  next
    define l where "l = convert_multiway t # get_and_list (convert_multiway \<phi>)"
    define pos where "pos = fst (partition safe_formula l)"
    define neg where "neg = snd (partition safe_formula l)"

    case False
    then have convert_f: "convert_multiway f = Ands l"
      unfolding f_def l_def
      using t_not_safe_assign t_not_constraint
      by auto

    have unsafe: "\<not>safe_formula (convert_multiway t)"
      using And_Not_Trigger False
      unfolding t_def
      by (auto split: if_splits simp add: safe_formula_dual_def fv_convert_multiway)
    then have pos_fv: "\<Union>(set (map fv pos)) = \<Union>(set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      unfolding pos_def l_def t_def
      by auto

    have neg_eq: "neg = convert_multiway t # snd (partition safe_formula (get_and_list (convert_multiway \<phi>)))"
      using unsafe
      unfolding neg_def l_def
      by auto

    have "\<Union> (set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>)))))) = fv \<phi>"
    proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
      case True
      then obtain l where l_props: "(convert_multiway \<phi>) = Ands l"
        by (auto split: formula.splits)
      then have "get_and_list (convert_multiway \<phi>) = l"
        by auto
      then have "fv \<phi> = fv (Ands l)"
        using l_props fv_convert_multiway[of 0 \<phi>]
        by auto
      then show ?thesis
        using l_props And_Not_Trigger(5) l_props
        by auto
    next
      case False
      then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
        by (auto split: formula.splits)
      then show ?thesis
        using And_Not_Trigger(5)
        by (auto simp add: fv_convert_multiway)
    qed
    then have t_fvs: "fv (convert_multiway t) \<subseteq> \<Union> (set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      using And_Not_Trigger(4)
      unfolding t_def
      by (auto simp add: fv_convert_multiway)

    then have mem: "\<not>mem I 0 \<or> (case \<phi>' of Formula.Neg \<phi>'' \<Rightarrow> \<not> safe_formula \<phi>'' | _ \<Rightarrow> True)"
      using False And_Not_Trigger
      unfolding t_def safe_formula_dual_def
      by (auto simp add: safe_formula_dual_def)

    have unsafe_convert_t: "\<not> safe_formula (convert_multiway t)"
      using False And_Not_Trigger
      unfolding t_def
      by (auto simp add: safe_formula_dual_def)
    then have unsafe_convert_t_rem_neg: "\<not>safe_formula (convert_multiway t)"
      unfolding t_def
      by auto

    have filter_pos: "filter safe_formula pos \<noteq> []"
      using filter_pos
      unfolding pos_def l_def
      by auto
    moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg"
    proof -
      {
        fix \<alpha>
        assume assm: "\<alpha> \<in> set neg"

        have "(case \<alpha> of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
          | _ \<Rightarrow> safe_formula \<alpha>
        )"
        proof (cases "\<alpha> \<in> set (snd (partition safe_formula (get_and_list (convert_multiway \<phi>))))")
          case True
          then have \<alpha>_props:
            "\<not>safe_formula \<alpha>"
            "\<alpha> \<in> set (get_and_list (convert_multiway \<phi>))"
            by auto
          then show ?thesis
          proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
            case True
            then obtain l where l_props: "(convert_multiway \<phi>) = Ands l"
              by (auto split: formula.splits)
            then have "safe_formula (Ands l)"
              using And_Not_Trigger(5)
              by auto
            then have "list_all (\<lambda>\<phi>. case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | Trigger \<phi>' I \<psi>' \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> safe_formula \<phi>)
              (filter (\<lambda>f. \<not> safe_formula f) l)"
              by (auto simp add: o_def)
            then have "\<forall>\<phi> \<in> set (filter (\<lambda>f. \<not> safe_formula f) l). case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | Trigger \<phi>' I \<psi>' \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> safe_formula \<phi>"
              by (simp add: list.pred_set)
            moreover have "\<alpha> \<in> set (filter (\<lambda>f. \<not> safe_formula f) l)"
              using \<alpha>_props l_props
              by auto
            ultimately show ?thesis
              by auto
          next
            case False
            then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
              by (auto split: formula.splits)
            then have "False"
              using \<alpha>_props And_Not_Trigger(5)
              by auto
            then show ?thesis by auto
          qed
        next
          case False
          then have "\<alpha> = convert_multiway t"
            using assm neg_eq
            by auto
          then show ?thesis
            using And_Not_Trigger
            unfolding t_def safe_formula_dual_def
            by (auto simp add: fv_convert_multiway split: if_splits)
        qed
      }
      then show ?thesis by (auto simp: list_all_iff)
    qed
    moreover have "\<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))"
      using pos_fv \<phi>_fvs t_fvs
      unfolding neg_def l_def t_def
      by (auto simp add: fv_convert_multiway)
    ultimately have "safe_formula (Ands l)"
      unfolding pos_def neg_def
      by auto
    then show ?thesis
      using convert_f
      unfolding f_def t_def
      by auto
  qed
next
  (*

  let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg \<and>
    \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))
  *)
  case (Ands l pos neg)
  define pos' where "pos' = fst (partition safe_formula (map convert_multiway l))"
  define neg' where "neg' = snd (partition safe_formula (map convert_multiway l))"

  have pos_fv: "\<Union>(set (map fv pos)) \<subseteq> \<Union>(set (map fv pos'))"
    using Ands(1,6)
    unfolding pos'_def
    by (auto simp add: list_all_iff fv_convert_multiway)

  have neg_mem: "\<forall>\<alpha> \<in> set neg'. \<exists>\<alpha>' \<in> set neg. \<alpha> = convert_multiway \<alpha>'"
  proof -
    {
      fix \<alpha>
      assume "\<alpha> \<in> set neg'"
      then have \<alpha>_props: "\<alpha> \<in> set neg'" "\<not>safe_formula \<alpha>"
        unfolding neg'_def
        by auto

      then obtain \<alpha>' where \<alpha>'_props: "\<alpha> = convert_multiway \<alpha>'" "\<alpha>' \<in> set l"
        unfolding neg'_def
        by auto
      {
        assume "safe_formula \<alpha>'"
        then have "safe_formula \<alpha>"
          using \<alpha>'_props Ands(1,6)
          by (auto simp add: list_all_iff)
        then have "False" using \<alpha>_props(2) by auto
      }
      then have "\<not>safe_formula \<alpha>'" by auto
      then have "\<alpha>' \<in> set neg" "\<alpha> = convert_multiway \<alpha>'"
        using Ands(1) \<alpha>'_props
        by auto
      then have "\<exists>\<alpha>' \<in> set neg. \<alpha> = convert_multiway \<alpha>'"
        by auto
    }
    then show ?thesis by auto
  qed

  have neg_fv: "\<Union>(set (map fv neg')) \<subseteq> \<Union>(set (map fv neg))"
  proof -
    {
      fix x
      assume "x \<in> \<Union>(set (map fv neg'))"
      then obtain \<alpha> where \<alpha>_props: "x \<in> fv \<alpha>" "\<alpha> \<in> set neg'" "\<not>safe_formula \<alpha>"
        unfolding neg'_def
        by auto

      then obtain \<alpha>' where "\<alpha>'\<in> set neg" "\<alpha> = convert_multiway \<alpha>'"
        using neg_mem
        by auto
      
      then have "x \<in> \<Union>(set (map fv neg))"
        using \<alpha>_props(1)
        by (auto simp add: fv_convert_multiway)
    }
    then show ?thesis by auto
  qed

  obtain \<alpha> where "\<alpha> \<in> set pos"
    using Ands(2)
    using hd_in_set
    by blast
  then have
    "\<alpha> \<in> set l"
    "safe_formula (convert_multiway \<alpha>)"
    using Ands(1,6)
    by (auto simp add: list_all_iff)
  then have "convert_multiway \<alpha> \<in> set pos'"
    unfolding pos'_def
    by auto
  then have "pos' \<noteq> []"
    by auto
  moreover have "list_all (\<lambda>\<phi>. (case \<phi> of
        Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
        | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
        | _ \<Rightarrow> safe_formula \<phi>
      )
    ) neg'"
  proof -
    {
      fix \<phi>
      assume "\<phi> \<in> set neg'"
      then obtain \<phi>' where \<phi>'_props: "\<phi>'\<in>set neg" "\<phi> = convert_multiway \<phi>'"
        using neg_mem
        by auto
      then have \<phi>'_cases: "case \<phi>' of
           Neg \<phi>' \<Rightarrow> safe_formula (convert_multiway \<phi>')
           | Trigger \<phi>' I \<psi>' \<Rightarrow>
               safe_formula (convert_multiway \<psi>') \<and>
               (if mem I 0 then safe_formula (convert_multiway \<phi>') \<or> (case \<phi>' of Neg \<phi>'' \<Rightarrow> safe_formula (convert_multiway \<phi>'') | _ \<Rightarrow> False)
                else safe_formula (convert_multiway \<phi>'))
           | _ \<Rightarrow> safe_formula \<phi>"
        "case \<phi>' of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | Trigger \<phi>' I \<psi>' \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>' | _ \<Rightarrow> safe_formula \<phi>'"
        using Ands(4,7)
        by (auto simp add: list_all_iff)

      then have "(case \<phi> of
          Neg \<phi>' \<Rightarrow> safe_formula \<phi>'
          | (Trigger \<phi>' I \<psi>') \<Rightarrow> safe_formula_dual True safe_formula \<phi>' I \<psi>'
          | _ \<Rightarrow> safe_formula \<phi>
        )"
        using \<phi>'_props
      proof (cases "\<phi>'")
        case (And \<alpha> \<beta>)
        then show ?thesis using \<phi>'_cases(1) \<phi>'_props
          by (auto split: if_splits)
      next
        case (Trigger \<alpha> I \<beta>)
        then have IH:
          "safe_formula (convert_multiway \<beta>)"
          "if mem I 0 then
              safe_formula (convert_multiway \<alpha>) \<or> (case \<alpha> of Neg \<phi>'' \<Rightarrow> safe_formula (convert_multiway \<phi>'') | _ \<Rightarrow> False)
           else
              safe_formula (convert_multiway \<alpha>)"
          using \<phi>'_cases
          by auto
        have safe_dual: "safe_formula_dual True safe_formula \<alpha> I \<beta>"
          using Trigger \<phi>'_cases(2)
          by auto
        
        have "safe_formula_dual True safe_formula (convert_multiway \<alpha>) I (convert_multiway \<beta>)"
        proof (cases "mem I 0")
          case True
          then show ?thesis
          proof (cases "safe_formula (convert_multiway \<alpha>)")
            case True
            then show ?thesis
              using IH safe_dual
              unfolding safe_formula_dual_def
              by (auto simp add: fv_convert_multiway)
          next
            case False
            then obtain \<phi>'' where "\<alpha> = Neg \<phi>''" "safe_formula (convert_multiway \<phi>'')"
              using True False IH
              by (auto split: formula.splits)
            then show ?thesis
              using IH safe_dual
              unfolding safe_formula_dual_def
              by (auto simp add: fv_convert_multiway split: formula.splits)
          qed
        next
          case False
          then show ?thesis
            using IH safe_dual
            unfolding safe_formula_dual_def
            by (auto simp add: fv_convert_multiway)
        qed
        then show ?thesis
          using \<phi>'_props(2) Trigger
          by auto
      qed (auto)
    }
    then show ?thesis by (auto simp add: list_all_iff)
  qed
  moreover have "\<Union>(set (map fv neg')) \<subseteq> \<Union>(set (map fv pos'))"
    using Ands(5) pos_fv neg_fv
    by auto
  ultimately show ?case
    unfolding neg'_def pos'_def
    by auto
next
  case (Neg \<phi>)
  have "safe_formula (Neg \<phi>') \<longleftrightarrow> safe_formula \<phi>'" if "fv \<phi>' = {}" for \<phi>'
    using that by (cases "Neg \<phi>'" rule: safe_formula.cases) simp_all
  with Neg show ?case by (simp add: fv_convert_multiway)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  moreover {
    assume "safe_formula \<phi> \<and> safe_formula (convert_multiway \<phi>)"
    then have ?case using assms by (simp add: fv_convert_multiway safe_formula_dual_def)
  }
  (*moreover {
    assume assm: "safe_assignment (fv \<psi>) \<phi>"
    
    then have "safe_assignment (fv (convert_multiway \<psi>)) (convert_multiway \<phi>)"
      using assm assms(2-3)
      by (cases \<phi>) (auto simp add: safe_assignment_def fv_convert_multiway)

    moreover have "fv (convert_multiway \<phi>) \<subseteq> fv (convert_multiway \<psi>)"
      using assm assms(2-3)
      by (cases \<phi>) (auto simp add: safe_assignment_def fv_convert_multiway)

    ultimately have ?case
      using assms
      by (auto simp add: fv_convert_multiway)
  }
  moreover {
    assume assm: "is_constraint \<phi>"
    then have "is_constraint (convert_multiway \<phi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    moreover have "fv (convert_multiway \<phi>) \<subseteq> fv (convert_multiway \<psi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assms(2-3) assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    ultimately have ?case
      using assms
      by (auto simp add: fv_convert_multiway)
  }*)
  moreover {
    assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> safe_formula (convert_multiway \<phi>') | _ \<Rightarrow> False)"
    then obtain \<phi>' where \<phi>_def: "\<phi> = Neg \<phi>'" "safe_formula \<phi>'" "safe_formula (convert_multiway \<phi>')"
      by (auto split: formula.splits)
    then have ?case
      using assms
      by (auto simp add: fv_convert_multiway safe_formula_dual_def)
  }
  ultimately show ?case by blast
next
case assms: (Release_0 \<phi> I \<psi>)
  moreover {       
    assume "safe_formula \<phi> \<and> safe_formula (convert_multiway \<phi>)"
    then have ?case using assms by (simp add: fv_convert_multiway safe_formula_dual_def)
  }
  moreover {
    assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> safe_formula (convert_multiway \<phi>') | _ \<Rightarrow> False)"
    then obtain \<phi>' where \<phi>_def: "\<phi> = Neg \<phi>'" "safe_formula \<phi>'" "safe_formula (convert_multiway \<phi>')"
      by (auto split: formula.splits)
    then have ?case
      using assms
      by (auto simp add: fv_convert_multiway safe_formula_dual_def)
  }
  (*moreover {
    assume assm: "safe_assignment (fv \<psi>) \<phi>"
    
    then have "safe_assignment (fv (convert_multiway \<psi>)) (convert_multiway \<phi>)"
      using assm assms(2-3)
      by (cases \<phi>) (auto simp add: safe_assignment_def fv_convert_multiway)

    moreover have "fv (convert_multiway \<phi>) \<subseteq> fv (convert_multiway \<psi>)"
      using assm assms(2-3)
      by (cases \<phi>) (auto simp add: safe_assignment_def fv_convert_multiway)

    ultimately have ?case
      using assms
      by (auto simp add: fv_convert_multiway)
  }
  moreover {
    assume assm: "is_constraint \<phi>"
    then have "is_constraint (convert_multiway \<phi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    moreover have "fv (convert_multiway \<phi>) \<subseteq> fv (convert_multiway \<psi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assms(2-3) assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    ultimately have ?case
      using assms
      by (auto simp add: fv_convert_multiway)
  }*)
  ultimately show ?case by blast
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
qed (auto simp add: fv_convert_multiway nfv_convert_multiway split: if_splits)

lemma future_bounded_multiway_Ands: "future_bounded (convert_multiway \<phi>) = future_bounded \<phi> \<Longrightarrow> future_bounded (Ands (get_and_list (convert_multiway \<phi>))) = future_bounded \<phi>"
  by (cases "case (convert_multiway \<phi>) of Ands l \<Rightarrow> True | _ \<Rightarrow> False") (auto split: formula.splits)


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
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger \<phi>' I \<psi>'"
  define f where "f = And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  then show ?case proof (cases "safe_formula t")
    define l where "l = (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t))"
    case True
    then have f_convert: "convert_multiway f = Ands l"
      using t_not_safe_assign
      unfolding l_def f_def
      by auto
    have t_multiway: "future_bounded (convert_multiway t) = future_bounded t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
    have "list_all future_bounded l = (future_bounded \<phi> \<and> future_bounded (Trigger \<phi>' I \<psi>'))"
      using future_bounded_multiway_Ands[OF t_multiway] future_bounded_multiway_Ands[OF And_Trigger(5)]
      unfolding l_def t_def
      by auto
    then show ?thesis
      using f_convert
      unfolding f_def t_def
      by auto
  next
    define l where "l = (convert_multiway t) # get_and_list (convert_multiway \<phi>)"
    case False
    then have f_convert: "convert_multiway f = Ands l"
      using t_not_safe_assign t_not_constraint
      unfolding l_def f_def
      by auto
    have t_multiway: "future_bounded (convert_multiway t) = future_bounded t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
    have "list_all future_bounded l = (future_bounded \<phi> \<and> future_bounded (Trigger \<phi>' I \<psi>'))"
      using future_bounded_multiway_Ands[OF t_multiway] future_bounded_multiway_Ands[OF And_Trigger(5)]
      unfolding l_def t_def
      by auto
    then show ?thesis
      using f_convert
      unfolding f_def t_def
      by auto
  qed
next
  case (And_Not_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger (Neg \<phi>') I \<psi>'"
  define f where "f = And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  then show ?case proof (cases "safe_formula t")
    define l where "l = (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t))"
    case True
    then have f_convert: "convert_multiway f = Ands l"
      using t_not_safe_assign
      unfolding l_def f_def
      by auto
    have t_multiway: "future_bounded (convert_multiway t) = future_bounded t"
      using And_Not_Trigger(6-7)
      unfolding t_def
      by auto
    have "list_all future_bounded l = (future_bounded \<phi> \<and> future_bounded (Trigger (Neg \<phi>') I \<psi>'))"
      using future_bounded_multiway_Ands[OF t_multiway] future_bounded_multiway_Ands[OF And_Not_Trigger(5)]
      unfolding l_def t_def
      by auto
    then show ?thesis
      using f_convert
      unfolding f_def t_def
      by auto
  next
    define l where "l = (convert_multiway t) # get_and_list (convert_multiway \<phi>)"
    case False
    then have f_convert: "convert_multiway f = Ands l"
      using t_not_safe_assign t_not_constraint
      unfolding l_def f_def
      by auto
    have t_multiway: "future_bounded (convert_multiway t) = future_bounded t"
      using And_Not_Trigger(6-7)
      unfolding t_def
      by auto
    have "list_all future_bounded l = (future_bounded \<phi> \<and> future_bounded (Trigger (Neg \<phi>') I \<psi>'))"
      using future_bounded_multiway_Ands[OF t_multiway] future_bounded_multiway_Ands[OF And_Not_Trigger(5)]
      unfolding l_def t_def
      by auto
    then show ?thesis
      using f_convert
      unfolding f_def t_def
      by auto
  qed
next
  case (Ands l pos neg)
  then have l_future_bounded: "list_all (\<lambda>a. future_bounded (convert_multiway a) = future_bounded a) l"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set l"
      then have "future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
      proof (cases "\<phi> \<in> set pos")
        case True
        then show ?thesis using Ands(6) by (auto simp add: list_all_iff)
      next
        case False
        then have \<phi>'_props: "case \<phi> of Neg \<phi>' \<Rightarrow> future_bounded (convert_multiway \<phi>') = future_bounded \<phi>'
           | Trigger \<phi>' I \<psi>' \<Rightarrow>
               future_bounded (convert_multiway \<psi>') = future_bounded \<psi>' \<and>
               (if mem I 0
                then future_bounded (convert_multiway \<phi>') = future_bounded \<phi>' \<or>
                     (case \<phi>' of Neg \<phi>'' \<Rightarrow> future_bounded (convert_multiway \<phi>'') = future_bounded \<phi>'' | _ \<Rightarrow> False)
                else future_bounded (convert_multiway \<phi>') = future_bounded \<phi>')
           | _ \<Rightarrow> future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
          using Ands(1,7) assm
          by (auto simp add: list_all_iff)
        then show ?thesis
          by (cases \<phi>) (auto split: if_splits formula.splits)
      qed
    }
    then show ?thesis by (auto simp add: list_all_iff)
  qed
  then show ?case by (auto simp add: list_all_iff)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  then have "future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
  proof -
    {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis by (cases \<phi>) (auto simp add: safe_assignment_def)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> future_bounded (convert_multiway \<phi>') = future_bounded \<phi>' | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms by auto
next
  case assms: (Release_0 \<phi> I \<psi>)
  then have "future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
  proof -
    {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis by (cases \<phi>) (auto simp add: safe_assignment_def)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> future_bounded (convert_multiway \<phi>') = future_bounded \<phi>' | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms by auto
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
qed (auto simp: list.pred_set)

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
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger \<phi>' I \<psi>'"

  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  moreover have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  moreover have "get_and_list (convert_multiway t) = [convert_multiway t]"
    unfolding t_def
    by auto

  ultimately obtain l where l_props:
    "convert_multiway (And \<phi> t) = Ands l"
    "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
    by (metis Un_insert_right convert_multiway.simps(8) empty_set list.simps(15) set_append sup_bot.right_neutral)

  have t_sat: "sat \<sigma> V v i (convert_multiway t) = sat \<sigma> V v i t"
    using And_Trigger(6-7)
    unfolding t_def
    by auto

  have "(\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>) = sat \<sigma> V v i (And \<phi> (Trigger \<phi>' I \<psi>'))"
  proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
    case True
    then obtain l' where l'_props: "convert_multiway \<phi> = Ands l'" by (auto split: formula.splits)
    then have "get_and_list (convert_multiway \<phi>) = l'"
      by auto
    moreover have "(\<forall>\<phi> \<in> set l'. sat \<sigma> V v i \<phi>) = sat \<sigma> V v i \<phi>"
      using And_Trigger(5) l'_props
      by auto
    ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
  next
    case False
    then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
      by (auto split: formula.splits)
    moreover have "sat \<sigma> V v i (convert_multiway \<phi>) = sat \<sigma> V v i \<phi>"
      using And_Trigger(5)
      by auto
    ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
  qed

  then show ?case
    using l_props(1)
    unfolding t_def
    by auto
next
  case (And_Not_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Trigger (Neg \<phi>') I \<psi>'"

  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  moreover have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  moreover have "get_and_list (convert_multiway t) = [convert_multiway t]"
    unfolding t_def
    by auto

  ultimately obtain l where l_props:
    "convert_multiway (And \<phi> t) = Ands l"
    "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
    by (metis Un_insert_right convert_multiway.simps(8) empty_set list.simps(15) set_append sup_bot.right_neutral)

  have t_sat: "sat \<sigma> V v i (convert_multiway t) = sat \<sigma> V v i t"
    using And_Not_Trigger(6-7)
    unfolding t_def
    by auto

  have "(\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>) = sat \<sigma> V v i (And \<phi> (Trigger (Neg \<phi>') I \<psi>'))"
  proof (cases "case (convert_multiway \<phi>) of (Ands l) \<Rightarrow> True | _ \<Rightarrow> False")
    case True
    then obtain l' where l'_props: "convert_multiway \<phi> = Ands l'" by (auto split: formula.splits)
    then have "get_and_list (convert_multiway \<phi>) = l'"
      by auto
    moreover have "(\<forall>\<phi> \<in> set l'. sat \<sigma> V v i \<phi>) = sat \<sigma> V v i \<phi>"
      using And_Not_Trigger(5) l'_props
      by auto
    ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
  next
    case False
    then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
      by (auto split: formula.splits)
    moreover have "sat \<sigma> V v i (convert_multiway \<phi>) = sat \<sigma> V v i \<phi>"
      using And_Not_Trigger(5)
      by auto
    ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
  qed

  then show ?case
    using l_props(1)
    unfolding t_def
    by auto
next
  case (Agg y \<omega> b f \<phi>)
  then show ?case
    by (simp add: nfv_def fv_convert_multiway cong: conj_cong)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  then have "\<forall>V v i. sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> V v i \<phi>"
  proof -
    {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis by (cases \<phi>) (auto simp add: safe_assignment_def)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> (\<forall>V v i. sat \<sigma> V v i (convert_multiway \<phi>') = sat \<sigma> V v i \<phi>') | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms(5) by auto
next
  case assms: (Release_0 \<phi> I \<psi>)
  then have "\<forall>V v i. sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> V v i \<phi>"
  proof -
    {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis by (cases \<phi>) (auto simp add: safe_assignment_def)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> (\<forall>V v i. sat \<sigma> V v i (convert_multiway \<phi>') = sat \<sigma> V v i \<phi>') | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms by auto
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
  case (Ands l pos neg)
  then have l_future_bounded: "list_all (\<lambda>a. sat \<sigma> V v i (convert_multiway a) = sat \<sigma> V v i a) l"
  proof -
    {
      fix \<phi>
      assume assm: "\<phi> \<in> set l"
      then have "sat \<sigma> V v i (convert_multiway \<phi>) = sat \<sigma> V v i \<phi>"
      proof (cases "\<phi> \<in> set pos")
        case True
        then show ?thesis using Ands(6) by (auto simp add: list_all_iff)
      next
        case False
        then have \<phi>'_props: "case \<phi> of Neg \<phi>' \<Rightarrow> \<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<phi>') = sat \<sigma> x xa xaa \<phi>'
           | Trigger \<phi>' I \<psi>' \<Rightarrow>
               (\<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<psi>') = sat \<sigma> x xa xaa \<psi>') \<and>
               (if mem I 0
                then (\<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<phi>') = sat \<sigma> x xa xaa \<phi>') \<or>
                     (case \<phi>' of Neg \<phi>'' \<Rightarrow> \<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<phi>'') = sat \<sigma> x xa xaa \<phi>'' | _ \<Rightarrow> False)
                else \<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<phi>') = sat \<sigma> x xa xaa \<phi>')
           | _ \<Rightarrow> \<forall>x xa xaa. sat \<sigma> x xa xaa (convert_multiway \<phi>) = sat \<sigma> x xa xaa \<phi>"
          using Ands(1,7) assm
          by (auto simp add: list_all_iff)
        then show ?thesis
          by (cases \<phi>) (auto split: if_splits formula.splits)
      qed
    }
    then show ?thesis by (auto simp add: list_all_iff)
  qed
  then show ?case by (auto simp add: list_all_iff)
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
