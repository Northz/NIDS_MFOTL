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


subsection \<open> Instantiations \<close>

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

instantiation enat :: card_UNIV begin
definition "finite_UNIV = Phantom(enat) False"
definition "card_UNIV = Phantom(enat) 0"
instance by intro_classes (simp_all add: finite_UNIV_enat_def card_UNIV_enat_def infinite_UNIV_char_0)
end

datatype rec_safety = Unused | PastRec | NonFutuRec | AnyRec

instantiation rec_safety :: "{finite, bounded_semilattice_sup_bot, monoid_mult, mult_zero}"
begin

fun less_eq_rec_safety where
  "Unused \<le> _ = True"
| "PastRec \<le> PastRec = True"
| "PastRec \<le> NonFutuRec = True"
| "PastRec \<le> AnyRec = True"
| "NonFutuRec \<le> NonFutuRec = True"
| "NonFutuRec \<le> AnyRec = True"
| "AnyRec \<le> AnyRec = True"
| "(_::rec_safety) \<le> _ = False"

definition "(x::rec_safety) < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

definition [code_unfold]: "\<bottom> = Unused"

fun sup_rec_safety where
  "AnyRec \<squnion> _ = AnyRec"
| "_ \<squnion> AnyRec = AnyRec"
| "NonFutuRec \<squnion> _ = NonFutuRec"
| "_ \<squnion> NonFutuRec = NonFutuRec"
| "PastRec \<squnion> _ = PastRec"
| "_ \<squnion> PastRec = PastRec"
| "Unused \<squnion> Unused = Unused"

definition [code_unfold]: "0 = Unused"
definition [code_unfold]: "1 = NonFutuRec"

fun times_rec_safety where
  "Unused * _ = Unused"
| "_ * Unused = Unused"
| "AnyRec * _ = AnyRec"
| "_ * AnyRec = AnyRec"
| "PastRec * _ = PastRec"
| "_ * PastRec = PastRec"
| "NonFutuRec * NonFutuRec = NonFutuRec"

instance proof
  fix x y z :: rec_safety
  have "x \<in> {Unused, PastRec, NonFutuRec, AnyRec}" for x
    by (cases x) simp_all
  then have UNIV_alt: "UNIV = \<dots>" by blast
  show "finite (UNIV :: rec_safety set)"
    unfolding UNIV_alt by blast
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_rec_safety_def
    by (cases x; cases y) simp_all
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "\<bottom> \<le> x"
    unfolding bot_rec_safety_def
    by (cases x) simp_all
  show "(x * y) * z = x * (y * z)"
    by (cases x; cases y; cases z) simp_all
  show "1 * x = x"
    unfolding one_rec_safety_def
    by (cases x) simp_all
  show "x * 1 = x"
    unfolding one_rec_safety_def
    by (cases x) simp_all
  show "0 * x = 0"
    unfolding zero_rec_safety_def by simp
  show "x * 0 = 0"
    unfolding zero_rec_safety_def
    by (cases x) simp_all
qed

end

instantiation rec_safety :: Sup
begin

definition "\<Squnion> A = Finite_Set.fold (\<squnion>) Unused A"

instance ..

end

lemma mult_commute: "(x::rec_safety) * y = y * x"
  by (cases x; cases y; clarsimp)

lemma mult_assoc: "(x::rec_safety) * y * z = x * (y * z)"
  by (simp add: mult.assoc)

lemma mult_sup_distrib: "(x::rec_safety) * (a \<squnion> b) = x * a \<squnion> x * b"
  by (cases x; cases a; cases b; clarsimp)

lemma (in semilattice_sup) comp_fun_idem_on_sup: "comp_fun_idem_on UNIV sup"
  using comp_fun_idem_sup by (simp add: comp_fun_idem_def')

lemma Sup_rec_safety_empty[simp]: "\<Squnion> {} = Unused"
  by (simp add: Sup_rec_safety_def)

lemma Sup_rec_safety_insert[simp]: "\<Squnion>(insert (x::rec_safety) A) = x \<squnion> \<Squnion>A"
  by (simp add: Sup_rec_safety_def comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_on_sup])

lemma Sup_rec_safety_union: "\<Squnion>((A::rec_safety set) \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
  unfolding Sup_rec_safety_def
  using finite[of A]
  by (induction A rule: finite_induct) (simp_all flip: bot_rec_safety_def
      add: comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_on_sup] sup_assoc)


context begin

subsection \<open>Syntax and semantics\<close>

qualified type_synonym name = string8
qualified type_synonym event = "(name \<times> event_data list)"
qualified type_synonym database = "event set"
qualified type_synonym prefix = "database prefix"
qualified type_synonym trace = "database trace"

qualified type_synonym env = "event_data list"

subsubsection \<open>Terms\<close>

qualified datatype trm = is_Var: Var nat | is_Const: Const event_data
  | Plus trm trm | Minus trm trm | UMinus trm | Mult trm trm | Div trm trm | Mod trm trm
  | F2i trm | I2f trm

lemma trm_exhaust: "(\<And>x. t = Var x \<Longrightarrow> P (Var x)) 
  \<Longrightarrow> (\<And>a. t = Const a \<Longrightarrow> P (Const a))
  \<Longrightarrow> (\<And>t1 t2. t = Plus t1 t2 \<Longrightarrow> P (Plus t1 t2))
  \<Longrightarrow> (\<And>t1 t2. t = Minus t1 t2 \<Longrightarrow> P (Minus t1 t2))
  \<Longrightarrow> (\<And>t1. t = UMinus t1 \<Longrightarrow> P (UMinus t1))
  \<Longrightarrow> (\<And>t1 t2. t = Mult t1 t2 \<Longrightarrow> P (Mult t1 t2))
  \<Longrightarrow> (\<And>t1 t2. t = Div t1 t2 \<Longrightarrow> P (Div t1 t2))
  \<Longrightarrow> (\<And>t1 t2. t = Mod t1 t2 \<Longrightarrow> P (Mod t1 t2))
  \<Longrightarrow> (\<And>t1. t = F2i t1 \<Longrightarrow> P (F2i t1))
  \<Longrightarrow> (\<And>t1. t = I2f t1 \<Longrightarrow> P (I2f t1))
  \<Longrightarrow> P t"
  by (cases t, simp_all)

text \<open> In this implementation of MFODL, to use De Bruijn indices, binding operators increase the
value of the bounding number @{term b} (that starts at $0$) and this number is subtracted from
all free variables (type @{typ nat}) greater than @{term b}. For instance, the free variable of
$\exists.\ P\, (Var 0) \land Q\, (Var 1)$ is @{term "Var 0"} because the existential makes $b=1$
and this value is subtracted from $Q$s argument while that of $P$ is not even taken into account. \<close>


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


subsubsection \<open>Formulas\<close>

text \<open> Aggregation operators @{text "Agg nat ('t agg_op) ('t list) trm ('t formula)"} 
are special formulas with five parameters:
\begin{itemize}
\item A variable @{term "y::nat"} that saves the value of the aggregation operation.
\item A type of aggregation (sum, avg, min, max, ...).
\item A list @{term "ts::'t list"} binding (with its length) the variables in the next arguments.
\item A term @{term "t::trm"} that represents an operation to be aggregated.
\item A formula @{term "\<phi>"} that restricts the domain where the aggregation takes place.
\end{itemize} \<close>

datatype ty = TInt | TFloat | TString

qualified datatype agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
qualified type_synonym 't agg_op = "agg_type \<times> 't"

definition flatten_multiset :: "(event_data \<times> enat) set \<Rightarrow> event_data list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x) (csorted_list_of_set M))"

definition finite_multiset :: "(event_data \<times> enat) set \<Rightarrow> bool" where
"finite_multiset M = (finite M \<and> \<not>(\<exists>s. (s,\<infinity>) \<in> M ))"

definition aggreg_default_value :: "agg_type \<Rightarrow> ty \<Rightarrow> event_data" where
  "aggreg_default_value op t = (case (op, t) of
    (Agg_Min, TFloat) \<Rightarrow> EFloat Code_Double.infinity |
    (Agg_Max, TFloat) \<Rightarrow> EFloat (-Code_Double.infinity) |
    (_, TFloat) \<Rightarrow> EFloat 0 |
    (_, TInt) \<Rightarrow> EInt 0 |
    (_, TString) \<Rightarrow> EString empty_string)"

fun eval_agg_op :: "ty agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op (Agg_Cnt, ty) M = (let y0 = aggreg_default_value Agg_Cnt ty in
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EInt (integer_of_int (length xs)))"
| "eval_agg_op (Agg_Min, ty) M = (let y0 = aggreg_default_value Agg_Min ty in
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl min x xs)"
| "eval_agg_op (Agg_Max, ty) M = (let y0 = aggreg_default_value Agg_Max ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl max x xs)"
| "eval_agg_op (agg_type.Agg_Sum, ty) M = (let y0 = aggreg_default_value Agg_Sum ty in
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x # xs,_) \<Rightarrow> foldl (+) x xs)"
| "eval_agg_op (Agg_Avg, ty) M =(let y0 = aggreg_default_value Agg_Avg ty in 
    case  (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (x#xs,_) \<Rightarrow> EFloat ( double_of_event_data_agg (foldl plus x xs) / double_of_int (length (x#xs))))"
| "eval_agg_op (Agg_Med, ty) M =(let y0 = aggreg_default_value Agg_Med ty in
    case (flatten_multiset M, finite_multiset M) of
    (_, False) \<Rightarrow> y0
    |    ([],_) \<Rightarrow> y0
    | (xs,_) \<Rightarrow> EFloat (let u = length xs;  u' = u div 2 in
          if even u then
            (double_of_event_data_agg (xs ! (u'-1)) + double_of_event_data_agg (xs ! u')) / double_of_int 2
          else double_of_event_data_agg (xs ! u')))"

qualified datatype (discs_sels) 't formula = Pred name "trm list"
  | Let name "'t formula" "'t formula"
  | LetPast name "'t formula" "'t formula"
  | Eq trm trm | Less trm trm | LessEq trm trm
  | Neg "'t formula" | Or "'t formula" "'t formula" | And "'t formula" "'t formula" 
  | Ands "'t formula list" | Exists 't "'t formula"
  | Agg nat "'t agg_op" "'t list" trm "'t formula"
  | Prev \<I> "'t formula" | Next \<I> "'t formula"
  | Since "'t formula" \<I> "'t formula" | Until "'t formula" \<I> "'t formula"
  | Trigger "'t formula" \<I> "'t formula" | Release "'t formula" \<I> "'t formula"
  | MatchF \<I> "'t formula Regex.regex" | MatchP \<I> "'t formula Regex.regex"
  | TP trm | TS trm

lemma Neg_splits:
  "P (case \<phi> of Formula.formula.Neg \<psi> \<Rightarrow> f \<psi> | \<phi> \<Rightarrow> g \<phi>) =
   ((\<forall>\<psi>. \<phi> = Formula.formula.Neg \<psi> \<longrightarrow> P (f \<psi>)) \<and> ((\<not> Formula.is_Neg \<phi>) \<longrightarrow> P (g \<phi>)))"
  "P (case \<phi> of Formula.formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> g \<phi>) =
   (\<not> ((\<exists>\<psi>. \<phi> = Formula.formula.Neg \<psi> \<and> \<not> P (f \<psi>)) \<or> ((\<not> Formula.is_Neg \<phi>) \<and> \<not> P (g \<phi>))))"
  by (cases \<phi>; auto simp: Formula.is_Neg_def)+

lemma case_Neg_iff: "(case \<gamma> of Neg x \<Rightarrow> P x | _ \<Rightarrow> False) 
    \<longleftrightarrow> (\<exists>\<gamma>'. \<gamma> = Neg \<gamma>' \<and> P \<gamma>')" 
  by (cases \<gamma>) auto

lemma case_NegE: "(case \<phi> of Neg \<phi>' \<Rightarrow> P \<phi>' | _ \<Rightarrow> False) 
  \<Longrightarrow> (\<And>\<phi>'. \<phi> = Neg \<phi>' \<Longrightarrow> P \<phi>' \<Longrightarrow> Q) \<Longrightarrow> Q"
  using case_Neg_iff
  by auto

lemma case_release_iff: 
  "(case \<phi> of Release \<phi>' I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<longleftrightarrow> (\<exists>\<phi>' I \<psi>'. \<phi> = Release \<phi>' I \<psi>')"
  by (auto split: formula.splits)

lemma case_trigger_iff: 
  "(case \<phi> of Trigger \<phi>' I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<longleftrightarrow> (\<exists>\<phi>' I \<psi>'. \<phi> = Trigger \<phi>' I \<psi>')"
  by (auto split: formula.splits)

qualified definition "FF = Eq (Const (EInt 0)) (Const (EInt 1))"
qualified definition "TT \<equiv> Eq (Const (EInt 0)) (Const (EInt 0))"

qualified fun fvi :: "nat \<Rightarrow> 't formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Let p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (LetPast p \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Less t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (LessEq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi b (Exists t \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> tys f \<phi>) = fvi (b + length tys) \<phi> \<union> fvi_trm (b + length tys) f \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Trigger \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Release \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"
| "fvi b (TP t) = fvi_trm b t"
| "fvi b (TS t) = fvi_trm b t"

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

lemma fvi_trm_minus: "x \<in> fvi_trm b t \<and> x \<ge> c \<longrightarrow> x-c \<in> fvi_trm (b+c) t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b' = "length tys"
  have *: "b + c + ?b' = b + ?b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_minus: "x \<in> fvi b \<phi> \<and> x \<ge> c \<longrightarrow> x - c \<in> fvi (b+c) \<phi>"
  by (simp add: fvi_plus)

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

qualified definition nfv :: "'t formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "'t formula \<Rightarrow> env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Let p \<phi> \<psi>) = nfv \<psi>"
  "nfv (LetPast p \<phi> \<psi>) = nfv \<psi>"
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

fun contains_pred :: "name \<times> nat \<Rightarrow> 't formula \<Rightarrow> bool" where
   "contains_pred p (Eq t1 t2) = False"
|  "contains_pred p (Less t1 t2) = False"
|  "contains_pred p (LessEq t1 t2) = False"
|  "contains_pred p (Pred e ts) = (p = (e, length ts))"
|  "contains_pred p (Let e \<phi> \<psi>) = ((contains_pred p \<phi> \<and> contains_pred (e, nfv \<phi>) \<psi>) \<or> (p \<noteq> (e, nfv \<phi>) \<and> contains_pred p \<psi>))"
|  "contains_pred p (LetPast e \<phi> \<psi>) =  (p \<noteq> (e, nfv \<phi>) \<and> ((contains_pred p \<phi> \<and> contains_pred (e, nfv \<phi>) \<psi>) \<or> contains_pred p \<psi>))"
|  "contains_pred p (Neg \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Or \<phi> \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (And \<phi> \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Ands l) = (\<exists>\<phi>\<in>set l. contains_pred p \<phi>)"
|  "contains_pred p (Exists t \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Agg y \<omega> tys f \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Prev I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Next I \<phi>) = contains_pred p \<phi>"
|  "contains_pred p (Since \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Until \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Trigger \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (Release \<phi> I \<psi>) = (contains_pred p \<phi> \<or> contains_pred p \<psi>)"
|  "contains_pred p (MatchP I r) = (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"
|  "contains_pred p (MatchF I r) =  (\<exists>\<phi>\<in>Regex.atms r. contains_pred p \<phi>)"
|  "contains_pred p (TP t) = False"
|  "contains_pred p (TS t) = False"

lemma TT_no_pred [simp]: 
  "\<not> contains_pred p Formula.TT"
  by (simp add: Formula.TT_def)

subsubsection \<open>Semantics\<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

declare conj_cong[fundef_cong]
fun letpast_sat where
  "letpast_sat sat v (i::nat) = sat (\<lambda>w j. j < i \<and> letpast_sat sat w j) v i"
declare letpast_sat.simps[simp del]

lemma V_subst_letpast_sat:
  "(\<And>X v j. j \<le> i \<Longrightarrow> f X v j = g X v j) \<Longrightarrow>
  Formula.letpast_sat f v i = Formula.letpast_sat g v i"
  by (induct f v i rule: letpast_sat.induct) (subst (1 2) letpast_sat.simps, auto cong: conj_cong)

qualified fun sat :: "trace \<Rightarrow> (name \<times> nat \<rightharpoonup> env \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> ty formula \<Rightarrow> bool" where
  "sat \<sigma> V v i (Pred r ts) = (case V (r, length ts) of
       None \<Rightarrow> (r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> X (map (eval_trm v) ts) i)"
| "sat \<sigma> V v i (Let p \<phi> \<psi>) = sat \<sigma> (V((p, nfv \<phi>) \<mapsto> \<lambda>w j. sat \<sigma> V w j \<phi>)) v i \<psi>"
| "sat \<sigma> V v i (LetPast p \<phi> \<psi>) =
    (let pn = (p, nfv \<phi>) in
    sat \<sigma> (V(pn \<mapsto> letpast_sat (\<lambda>X u k. sat \<sigma> (V(pn \<mapsto> X)) u k \<phi>))) v i \<psi>)"
| "sat \<sigma> V v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> V v i (Less t1 t2) = (eval_trm v t1 < eval_trm v t2)"
| "sat \<sigma> V v i (LessEq t1 t2) = (eval_trm v t1 \<le> eval_trm v t2)"
| "sat \<sigma> V v i (Neg \<phi>) = (\<not> sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Or \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<or> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (And \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Exists t \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
| "sat \<sigma> V v i (Agg y \<omega> tys f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<length tys}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
| "sat \<sigma> V v i (Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> V v (Suc i) \<phi>)"
| "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = (\<forall>j\<le>i. (mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (Release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
| "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> V v) r j i)"
| "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> V v) r i j)"
| "sat \<sigma> V v i (TP t) = (eval_trm v t = EInt (integer_of_nat i))"
| "sat \<sigma> V v i (TS t) = (eval_trm v t = EInt (integer_of_nat (\<tau> \<sigma> i)))"

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
  case (Let p \<phi> \<psi>)
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
  case (Exists t \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b = "length tys"
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> V (zs @ v) i \<phi> = sat \<sigma> V (zs @ v') i \<phi>" if "length zs = ?b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b= ?b])
  moreover have "eval_trm (zs @ v) f = eval_trm (zs @ v') f" if "length zs = ?b" for zs
    using that Agg.prems by (auto intro!: eval_trm_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        simp: nth_append fvi_iff_fv(1)[where b= ?b] fvi_trm_iff_fv_trm[where b= ?b])
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
next
  case (TP t)
  then show ?case unfolding fvi.simps sat.simps by (metis eval_trm_fv_cong)
next
  case (TS t)
  then show ?case unfolding fvi.simps sat.simps by (metis eval_trm_fv_cong)
qed (auto 10 0 simp: Let_def split: nat.splits intro!: iff_exI)

lemma sat_the_restrict: "fv \<phi> \<subseteq> A \<Longrightarrow> Formula.sat \<sigma> V (map the (restrict A v)) i \<phi> = Formula.sat \<sigma> V (map the v) i \<phi>"
  by (rule sat_fv_cong) (auto intro!: map_the_restrict)

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

lemma first_fv[simp]: "fv first = {}"
  by (simp add: first_def)

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

lemma flip_int_double_upper_bounded[simp]: "bounded (flip_int_double_upper I) = bounded I"
  by (transfer') (auto)

lemma int_remove_lower_bound_bounded[simp]: "bounded (int_remove_lower_bound I) = bounded I"
  by (transfer') (auto)

lemma int_remove_lower_bound_mem: "mem I x \<Longrightarrow> mem (int_remove_lower_bound I) x"
  by (transfer') (auto)

lemma "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Since (Neg \<phi>) I (Neg \<psi>)))"
  by auto

lemma "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (Neg (Until (Neg \<phi>) I (Neg \<psi>)))"
  by auto

definition release :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "release \<phi> I \<psi> = Neg (Until (Neg \<phi>) I (Neg \<psi>))"

lemma sat_release[simp]:
  "sat \<sigma> V v i (release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
  unfolding release_def
  by auto

lemma sat_release_eq[simp]: "sat \<sigma> V v i (Release \<phi> I \<psi>) = sat \<sigma> V v i (release \<phi> I \<psi>)"
  by auto

definition once :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "once I \<phi> = Since TT I \<phi>"

lemma syntax_once_simps [simp]:
  "once I \<psi> \<noteq> (Formula.Eq t1 t2)"
  "once I \<psi> \<noteq> (Formula.Less t1 t2)"
  "once I \<psi> \<noteq> (Formula.LessEq t1 t2)"
  "once I \<psi> \<noteq> (Formula.Neg \<phi>)"
  unfolding once_def
  by auto

lemma once_fv[simp]: "fv (once I \<phi>) = fv \<phi>"
  by (simp add: once_def)

lemma sat_once[simp] : "sat \<sigma> V v i (once I \<phi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: once_def)

lemma once_fvi[simp] : "fvi b (once I \<phi>) = fvi b \<phi>"
  by (auto simp: once_def)

definition historically :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "historically I \<phi> = (Neg (once I (Neg \<phi>)))"

lemma sat_historically[simp]: "sat \<sigma> V v i (historically I \<phi>) = (\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding historically_def
  by auto

definition eventually :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "eventually I \<phi> = Until TT I \<phi>"

lemma syntax_eventually_simps [simp]:
  "Formula.eventually I \<psi> \<noteq> (Formula.Eq t1 t2)"
  "Formula.eventually I \<psi> \<noteq> (Formula.Less t1 t2)"
  "Formula.eventually I \<psi> \<noteq> (Formula.LessEq t1 t2)"
  "Formula.eventually I \<psi> \<noteq> (Formula.Neg \<phi>)"
  unfolding Formula.eventually_def
  by auto

lemma eventually_fv[simp]: "fv (eventually I \<phi>) = fv \<phi>"
  by (simp add: eventually_def)

lemma eventually_fvi[simp]: "fvi b (eventually I \<phi>) = fvi b \<phi>"
  by (auto simp: eventually_def)

lemma sat_eventually[simp]: "sat \<sigma> V v i (eventually I \<phi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<phi>)"
  by (auto simp: eventually_def)

lemma contains_pred_eventually [simp]: 
  "contains_pred p (Formula.eventually I \<psi>') \<longleftrightarrow> contains_pred p \<psi>'"
  unfolding Formula.eventually_def
  by simp

lemma contains_pred_once [simp]: 
  "contains_pred p (once I \<psi>') \<longleftrightarrow> contains_pred p \<psi>'"
  unfolding once_def
  by simp

definition always :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "always I \<phi> = (Neg (eventually I (Neg \<phi>)))"

lemma sat_always[simp]: "sat \<sigma> V v i (always I \<phi>) = (\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  unfolding always_def
  by auto

(* case distrinction since intervals aren't allowed to be empty and flip_int [0, \<infinity>] would be *)
definition historically_safe_0 :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "historically_safe_0 I \<phi> = (if (bounded I) then (Or (Since \<phi> (flip_int I) (Next all \<phi>)) (Since \<phi> I (And first \<phi>))) else (Since \<phi> I (And first \<phi>)))"
                                                                                                        
definition historically_safe_unbounded :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "historically_safe_unbounded I \<phi> = (And (once (flip_int_less_lower I) (Prev all (Since \<phi> all (And \<phi> first)))) (once I \<phi>))"

definition historically_safe_bounded :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "historically_safe_bounded I \<phi> = (And (once I \<phi>) (Neg (once I (And (Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>)) (Neg \<phi>)))))"

definition always_safe_0 :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "always_safe_0 I \<phi> = (Or (Until \<phi> (flip_int_double_upper I) (Prev all \<phi>)) (Until \<phi> I (And \<phi> (Next (flip_int I) TT))))"

definition always_safe_bounded :: "\<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "always_safe_bounded I \<phi> = (And (eventually I \<phi>) (Neg (eventually I (And (Or (once (int_remove_lower_bound I) \<phi>) (eventually (int_remove_lower_bound I) \<phi>)) (Neg \<phi>)))))"

definition trigger_safe_0 :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "trigger_safe_0 \<phi> I \<psi> = Or (Since \<psi> I (And \<psi> \<phi>)) (historically_safe_0 I \<psi>)"

definition trigger_safe_unbounded :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "trigger_safe_unbounded \<phi> I \<psi> = And (once I TT) (Or (Or (historically_safe_unbounded I \<psi>) (once (flip_int_less_lower I) \<phi>)) (once (flip_int_less_lower I) (Prev all (Since \<psi> (int_remove_lower_bound I) (And \<phi> \<psi>)))))"

definition trigger_safe_bounded :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "trigger_safe_bounded \<phi> I \<psi> = And (once I TT) (Or (Or (historically_safe_bounded I \<psi>) (once (flip_int_less_lower I) \<phi>)) (once (flip_int_less_lower I) (Prev all (Since \<psi> (int_remove_lower_bound I) (And \<phi> \<psi>)))))"

definition and_trigger_safe_bounded :: "'t formula \<Rightarrow> 't formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "and_trigger_safe_bounded \<phi> \<phi>' I \<psi>' = (Or (And \<phi> (Neg (once I TT))) (And \<phi> (trigger_safe_bounded \<phi>' I \<psi>')))"

definition and_trigger_safe_unbounded :: "'t formula \<Rightarrow> 't formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "and_trigger_safe_unbounded \<phi> \<phi>' I \<psi>' = (Or (And \<phi> (Neg (once I TT))) (And \<phi> (trigger_safe_unbounded \<phi>' I \<psi>')))"

definition release_safe_0 :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "release_safe_0 \<phi> I \<psi> = Or (Until \<psi> I (And \<psi> \<phi>)) (always_safe_0 I \<psi>)"

definition release_safe_bounded :: "'t formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "release_safe_bounded \<phi> I \<psi> = And (eventually I TT) (Or (Or (always_safe_bounded I \<psi>) (eventually (flip_int_less_lower I) \<phi>)) (eventually (flip_int_less_lower I) (Next all (Until \<psi> (int_remove_lower_bound I) (And \<psi> \<phi>)))))"

definition and_release_safe_bounded :: "'t formula \<Rightarrow> 't formula \<Rightarrow> \<I> \<Rightarrow> 't formula \<Rightarrow> 't formula" where
  "and_release_safe_bounded \<phi> \<phi>' I \<psi>' = (Or (And \<phi> (Neg (eventually I TT))) (And \<phi> (release_safe_bounded \<phi>' I \<psi>')))"

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

lemma contains_pred_always_safe_bounded [simp]:
  "contains_pred p (always_safe_bounded I \<psi>') \<longleftrightarrow> contains_pred p \<psi>'"
  unfolding always_safe_bounded_def
  by simp

lemma contains_pred_release_safe_bounded [simp]: "contains_pred p (release_safe_bounded \<phi>' I \<psi>') 
  \<longleftrightarrow> contains_pred p \<phi>' \<or> contains_pred p \<psi>'"
  unfolding release_safe_bounded_def
  by auto


subsection \<open>Past-only formulas\<close>

fun past_only :: "'t formula \<Rightarrow> bool" where
  "past_only (Pred _ _) = True"
| "past_only (Eq _ _) = True"
| "past_only (Less _ _) = True"
| "past_only (LessEq _ _) = True"
| "past_only (Let _ \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (LetPast _ \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Neg \<psi>) = past_only \<psi>"
| "past_only (Or \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (And \<alpha> \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Ands l) = (\<forall>\<alpha>\<in>set l. past_only \<alpha>)"
| "past_only (Exists _ \<psi>) = past_only \<psi>"
| "past_only (Agg _ _ _ _ \<psi>) = past_only \<psi>"
| "past_only (Prev _ \<psi>) = past_only \<psi>"
| "past_only (Next _ _) = False"
| "past_only (Since \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Until \<alpha> _ \<beta>) = False"
| "past_only (Trigger \<alpha> _ \<beta>) = (past_only \<alpha> \<and> past_only \<beta>)"
| "past_only (Release \<alpha> _ \<beta>) = False"
| "past_only (MatchP _ r) = Regex.pred_regex past_only r"
| "past_only (MatchF _ _) = False"
| "past_only (TP _) = True"
| "past_only (TS _) = True"

lemma past_only_sat:
  assumes "prefix_of \<pi> \<sigma>" "prefix_of \<pi> \<sigma>'"
  shows "i < plen \<pi> \<Longrightarrow> dom V = dom V' \<Longrightarrow>
     (\<And>p v i. p \<in> dom V \<Longrightarrow> i < plen \<pi> \<Longrightarrow> the (V p) v i = the (V' p) v i) \<Longrightarrow>
     past_only \<phi> \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma>' V' v i \<phi>"
proof (induction \<phi> arbitrary: V V' v i)
  case (Pred e ts)
  let ?en = "(e, length ts)"
  show ?case proof (cases "V ?en")
    case None
    then have "V' (e, length ts) = None" using \<open>dom V = dom V'\<close> by auto
    with None \<Gamma>_prefix_conv[OF assms(1,2) Pred(1)] show ?thesis by simp
  next
    case (Some a)
    moreover obtain a' where "V' ?en = Some a'"
      using Some \<open>dom V = dom V'\<close> by auto
    moreover have "the (V ?en) w i = the (V' ?en) w i" for w
      using Some Pred(1,3) by (fastforce intro: domI)
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  let ?pn = "(p, nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. (V(?pn \<mapsto> \<lambda>w j. sat \<sigma> V w j \<phi>))"
  show ?case unfolding sat.simps proof (rule Let.IH(2))
    show "i < plen \<pi>" by fact
    from Let.prems show "past_only \<psi>" by simp
    from Let.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by (simp del: fun_upd_apply)
  next
    fix p' v i
    assume *: "p' \<in> dom (?V V \<sigma>)" "i < plen \<pi>"
    show "the (?V V \<sigma> p') v i = the (?V V' \<sigma>' p') v i" proof (cases "p' = ?pn")
      case True
      with Let \<open>i < plen \<pi>\<close> show ?thesis by auto
    next
      case False
      with * show ?thesis by (auto intro!: Let.prems(3))
    qed
  qed
next
  case (LetPast p \<phi> \<psi>)
  let ?pn = "(p, nfv \<phi>)"
  let ?V = "\<lambda>V \<sigma>. V(?pn \<mapsto> letpast_sat (\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>))"
  show ?case unfolding sat.simps Let_def proof (rule LetPast.IH(2))
    show "i < plen \<pi>" by fact
    from LetPast.prems show "past_only \<psi>" by simp
    from LetPast.prems show "dom (?V V \<sigma>) = dom (?V V' \<sigma>')"
      by (simp del: fun_upd_apply)
  next
    fix p' v i'
    assume *: "p' \<in> dom (?V V \<sigma>)" "i' < plen \<pi>"
    show "the (?V V \<sigma> p') v i' = the (?V V' \<sigma>' p') v i'"
    proof (cases "p' = ?pn")
      case True
      then have "?pn \<in> dom (?V V \<sigma>)" by simp
      then have "letpast_sat (\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) v j =
            letpast_sat (\<lambda>X u k. sat \<sigma>' (V'(?pn \<mapsto> X)) u k \<phi>) v j"
        if "j < plen \<pi>" for j
        using that
      proof (induct "\<lambda>X u k. sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>" v j rule: letpast_sat.induct)
        case (1 v j)
        show ?case
        proof (subst (1 2) letpast_sat.simps, rule LetPast.IH(1), goal_cases plen dom eq past_only)
          case plen
          from "1" show ?case by simp
        next
          case dom
          from LetPast.prems show ?case by (auto simp add: dom_def)
        next
          case (eq p'' v' j')
          with "1" LetPast.prems(3)[of p'' j' v'] show ?case
            by (cases "p'' = ?pn") fastforce+
        next
          case past_only
          from LetPast.prems show ?case by simp
        qed
      qed
      with True \<open>i' < plen \<pi>\<close>
      show ?thesis by simp
    next
      case False
      with * show ?thesis by (auto intro!: LetPast.prems(3))
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
next
  case (TP t)
  with \<tau>_prefix_conv[OF assms] show ?case by simp
next
  case (TS t)
  with \<tau>_prefix_conv[OF assms] show ?case by simp
qed auto


subsection \<open>Well-formed formulas\<close>

fun wf_formula :: "'t formula \<Rightarrow> bool" 
  where "wf_formula (Let p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (LetPast p \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Neg \<phi>) =  wf_formula \<phi>"
| "wf_formula (Or \<phi> \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (And \<phi> \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi> )"
| "wf_formula (Ands l) = (list_all wf_formula l)"
| "wf_formula (Exists x \<phi>) = (wf_formula \<phi> \<and> 0 \<in> fv \<phi>)"
| "wf_formula (Agg y \<omega> tys f \<phi>) = (wf_formula \<phi> \<and> y + length tys \<notin> fv \<phi> \<and> {0..< length tys} \<subseteq> fv \<phi> )"
| "wf_formula (Prev I \<phi>) = (wf_formula \<phi>)"
| "wf_formula (Next I \<phi>) = (wf_formula \<phi>)"
| "wf_formula (Since \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Until \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Trigger \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (Release \<phi> I \<psi>) = (wf_formula \<phi> \<and> wf_formula \<psi>)"
| "wf_formula (MatchP I r) = Regex.pred_regex wf_formula r"
| "wf_formula (MatchF I r) = Regex.pred_regex wf_formula r"
| "wf_formula _ = True"

end (* context *)


subsection \<open> Notation \<close>

context
begin

abbreviation "eval_trm_option v t \<equiv> Formula.eval_trm (map the v) t"

abbreviation "sat_the \<sigma> V v i \<equiv> Formula.sat \<sigma> V (map the v) i"

end

bundle MFODL_no_notation
begin

no_notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

no_notation formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq (infixl "=\<^sub>F" 75)
     and formula.LessEq ("(_/ \<le>\<^sub>F _)" [76,76] 75)
     and formula.Less ("(_/ <\<^sub>F _)" [76,76] 75)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Exists ("\<exists>\<^sub>F:_. _" [70,70] 70)
     and formula.Ands ("\<And>\<^sub>F _" [70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)
     and formula.Trigger ("_ \<^bold>T _ _" [60,55,60] 60)
     and formula.Release ("_ \<^bold>R _ _" [60,55,60] 60)

no_notation Formula.fv_trm ("FV\<^sub>t")
     and Formula.fv ("FV")
     and eval_trm_option ("_\<lbrakk>_\<rbrakk>\<^sub>M" [51,89] 89)
     and sat_the ("\<langle>_, _, _, _\<rangle> \<Turnstile>\<^sub>M _" [56, 56, 56, 56, 56] 55)
     and Formula.sat ("\<langle>_, _, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56, 56] 55)
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end

bundle MFODL_notation
begin

notation trm.Var ("\<^bold>v")
     and trm.Const ("\<^bold>c")

notation formula.Pred ("_ \<dagger> _" [85, 85] 85)
     and formula.Eq (infixl "=\<^sub>F" 75)
     and formula.LessEq ("(_/ \<le>\<^sub>F _)" [76,76] 75)
     and formula.Less ("(_/ <\<^sub>F _)" [76,76] 75)
     and formula.Neg ("\<not>\<^sub>F _" [82] 82)
     and formula.And (infixr "\<and>\<^sub>F" 80)
     and formula.Or (infixr "\<or>\<^sub>F" 80)
     and formula.Exists ("\<exists>\<^sub>F:_. _" [70,70] 70)
     and formula.Ands ("\<And>\<^sub>F _" [70] 70)
     and formula.Prev ("\<^bold>Y _ _" [55, 65] 65)
     and formula.Next ("\<^bold>X _ _" [55, 65] 65)
     and formula.Since ("_ \<^bold>S _ _" [60,55,60] 60)
     and formula.Until ("_ \<^bold>U _ _" [60,55,60] 60)
     and formula.Trigger ("_ \<^bold>T _ _" [60,55,60] 60)
     and formula.Release ("_ \<^bold>R _ _" [60,55,60] 60)

notation Formula.fv_trm ("FV\<^sub>t")
     and Formula.fv ("FV")
     and eval_trm_option ("_\<lbrakk>_\<rbrakk>\<^sub>M" [51,89] 89)
     and sat_the ("\<langle>_, _, _, _\<rangle> \<Turnstile>\<^sub>M _" [56, 56, 56, 56, 56] 55)
     and Formula.sat ("\<langle>_, _, _, _\<rangle> \<Turnstile> _" [56, 56, 56, 56, 56] 55)
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end

unbundle MFODL_notation \<comment> \<open> enable notation \<close>

term "\<^bold>c (EInt 0) =\<^sub>F \<^bold>c (EInt 0)"
term "v\<lbrakk>\<^bold>c t\<rbrakk>\<^sub>M"
term "\<And>\<^sub>F [\<exists>\<^sub>F:t. (trm =\<^sub>F \<^bold>v x) \<and>\<^sub>F (a \<le>\<^sub>F \<^bold>c z), \<phi> \<^bold>U I \<psi>]"

term "\<langle>\<sigma>, V, v, i + length v\<rangle> \<Turnstile>\<^sub>M \<^bold>Y I (\<not>\<^sub>F (P \<dagger> [\<^bold>c a, \<^bold>v 0]) 
  \<and>\<^sub>F (Q \<dagger> [\<^bold>v y])) \<^bold>S (point n) ((\<^bold>X \<^bold>[2,3\<^bold>] (P \<dagger> [\<^bold>c b, \<^bold>v 0])) \<or>\<^sub>F Q \<dagger> [\<^bold>v y])"

definition "down_cl_ivl \<sigma> I i \<equiv> {j |j. j \<le> i \<and> mem I ((\<tau> \<sigma> i - \<tau> \<sigma> j))}"

lemma down_cl_ivl_nmem0I: "down_cl_ivl \<sigma> I i = {} \<Longrightarrow> \<not> mem I 0"
  unfolding down_cl_ivl_def
  by (transfer, clarsimp simp: downclosed_def upclosed_def)
    (metis bot_nat_0.extremum diff_self_eq_0 le_refl)

definition "up_cl_ivl \<sigma> I i \<equiv> {j |j. i \<le> j \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i))}"

lemma up_cl_ivl_nmem0I: "up_cl_ivl \<sigma> I i = {} \<Longrightarrow> \<not> mem I 0"
  unfolding up_cl_ivl_def
  by (transfer, clarsimp simp: downclosed_def upclosed_def)
    (metis bot_nat_0.extremum diff_self_eq_0 le_refl)

lemma release_fvi:
  "Formula.fvi b (\<phi> \<^bold>R I \<psi>) = Formula.fvi b (release_safe_0 \<phi> I \<psi>)"
  "Formula.fvi b (\<phi> \<^bold>R I \<psi>) = Formula.fvi b (release_safe_bounded \<phi> I \<psi>)"
  "Formula.fvi b (\<phi>' \<and>\<^sub>F (\<phi> \<^bold>R I \<psi>)) = Formula.fvi b (and_release_safe_bounded \<phi>' \<phi> I \<psi>)"
  by (auto simp add: release_safe_0_def always_safe_0_def Formula.TT_def Formula.FF_def 
      and_release_safe_bounded_def release_safe_bounded_def always_safe_bounded_def)

unbundle MFODL_no_notation \<comment> \<open> disable notation \<close>


subsection \<open> Rewriting formulas \<close>

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

lemma historically_rewrite_0:
  fixes I1 :: \<I>
  assumes "mem I1 0"
  shows "Formula.sat \<sigma> V v i (historically I1 \<phi>) = Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int I1"
  assume hist: "Formula.sat \<sigma> V v i (historically I1 \<phi>)"
  {
    define A where "A = {j. j\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
    define j where "j = Max A"
    assume int_bound: "bounded I1" "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
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
      then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms I2_def
        by (transfer' fixing: \<sigma>) (auto split: if_splits)
    }
    then have "\<forall>k\<in>{j<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" by auto
    then have "\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<phi>" using hist by auto
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 Formula.TT)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>))"
      using since_true int_bound I2_def flip_int_props
      by simp
  }
  moreover {
    assume unbounded: "\<not>bounded I1"
    then have mem_leq_j: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms
      using bounded_memR memL_mono
      by blast
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using mem_leq_j hist
      by auto
  }
  moreover {
    assume "\<forall>j\<le>i. \<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then have mem_leq_j: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms I2_def
      by (transfer' fixing: \<sigma>) (auto split: if_splits)
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using mem_leq_j hist
      by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
    using I2_def historically_safe_0_def
    by (metis sat.simps(8))
next
  define I2 where "I2 = flip_int I1"
  assume hist: "Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
  {
    assume int_bounded: "bounded I1"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<phi> I2 (Formula.Next all \<phi>)) (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>)))"
      using I2_def historically_safe_0_def hist
      by metis
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>)) \<or> Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))" by auto
    moreover {
      assume since: "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>))"
      then have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>))" by auto
      then obtain j where j_props: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
      {
        fix k
        assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        {
          assume "k\<le>j"
          then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j" by simp
          then have "\<tau> \<sigma> i - \<tau> \<sigma> k \<ge> \<tau> \<sigma> i - \<tau> \<sigma> j" by auto
          then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using j_props I2_def
            by (transfer' fixing: \<sigma>) (auto split: if_splits dest: memR_antimono)
          then have "False" using int_bounded k_props I2_def
            by (transfer' fixing: \<sigma>) (auto split: if_splits)
        }
        then have "\<not>(k\<le>j)" by blast
        then have "Formula.sat \<sigma> V v k \<phi>" using k_props j_props by auto
      }
      then have "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by auto
    }
    moreover {
      assume "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      then have "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (historically I1 \<phi>)" by blast
  }
  moreover {
    assume "\<not>bounded I1"
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using historically_safe_0_def hist
      by metis
    then have "Formula.sat \<sigma> V v i (historically I1 \<phi>)"
      by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (historically I1 \<phi>)" 
    by blast
qed

lemma historically_rewrite_unbounded:
  assumes "\<not> mem I1 0" "\<not> bounded I1" (* [a, \<infinity>] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>)) = Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1"
  assume historically: "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))"
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>}"
  define j where "j = Max A"
  have "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>" using historically by auto
  then have A_props: "finite A" "A \<noteq> {}" using A_def by auto
  then have "j \<in> A" using j_def by auto
  then have j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" using A_def by auto
  {
    fix k
    assume k_props: "k\<le>j"
    then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      using assms(2) j_props(1-2) interval_unbounded_leq[of j i k I1 \<sigma>]
      by auto
    then have first_sat: "Formula.sat \<sigma> V v k \<phi>" 
      using j_props k_props historically assms(1-2) 
      by auto
  }
  then have leq_j: "\<forall>k\<le>j. Formula.sat \<sigma> V v k \<phi>" by auto
  define B where "B = {k. k\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)}"
  define k where "k = Min B"
  have "mem I2 0"
    using assms I2_def
    by (transfer') (auto split: if_splits)
  then have B_props: "B \<noteq> {}" "finite B" using B_def by auto
  then have k_in_B: "k \<in> B" using k_def by auto
  then have k_props: "k\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using B_def by auto
  {
    assume "k=0"
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
      using k_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of k i j I2 \<sigma>] I2_def
      by auto
    then have "False"
      using assms j_props I2_def
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
    using assms flip_int_less_lower_mem I2_def
    by auto
  then have "Formula.sat \<sigma> V v (k-1) \<phi>" using historically k_props by auto
  then have "(k-1) \<in> A" using A_def k_pre k_props by auto
  then have "(k-1) \<le> j" using j_def A_props by auto
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))))"
    using interval_all k_pos leq_j k_props
    by (auto split: nat.split)
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) \<and> Formula.sat \<sigma> V v i (once I1 \<phi>)"
    using historically
    by auto
  then show "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
    using assms historically_safe_unbounded_def I2_def
    by (metis sat.simps(9))
next
  define I2 where "I2 = flip_int_less_lower I1"
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
  assume "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) (once I1 \<phi>))"
    using assms historically_safe_unbounded_def I2_def
    by metis
  then have "Formula.sat \<sigma> V v i (Formula.And (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) (once I1 \<phi>))"
    by auto
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))))" by auto
  then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))"
    by auto
  then obtain j where j_props:
    "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))"
    by blast
  {
    assume "j = 0"
    then have "\<not>Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))" by auto
    then have "False" using j_props by auto
  }
  then have j_pos: "j \<noteq> 0" by auto
  then have j_pred_sat: "Formula.sat \<sigma> V v (j-1) (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))"
    using j_pos j_props
    by (simp add: Nitpick.case_nat_unfold)
  {
    fix x
    assume x_props: "x>j-1"
    then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" using x_props by auto
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using j_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of j i x I2] I2_def
      by auto
    then have "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using assms I2_def
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
  then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<phi>" using j_pred_sat by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))" using rewrite by auto
qed

lemma historically_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b], a>0 *)
  (*
    [0, b-a] would be more efficient but this interval can
    (probably) not be constructed using the current
    implementation of intervals.
  *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>)) = Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))"
  then show "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
    using assms
    by (simp add: historically_safe_bounded_def)
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Neg (once I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def
    by (simp add: historically_safe_bounded_def)
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" by auto
  have j_leq_i_sat: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> (Formula.sat \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    then have "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v k \<phi>"
      using j_leq_i_sat by auto
    moreover {
      assume assm: "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
          using j_props assms(1-2)
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
          using k_props assms(1-2)
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms I2_def
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "Formula.sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<phi>" by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (historically I1 \<phi>))" using rewrite by auto
qed

lemma sat_trigger_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
  assumes leq: "j\<le>i"
  assumes mem_j: "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
  shows "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {j<..i}. Formula.sat \<sigma> V v x \<phi>}"
  define k where "k = Max A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {j<..i}" "Formula.sat \<sigma> V v k \<phi>" by (auto simp: A_def)
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
  assumes "mem I 0"
shows "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>) = Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  moreover {
    define A where "A = {j. j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Max A"
    assume "\<not>(\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "\<not>Formula.sat \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    then have "\<not>Formula.sat \<sigma> V v j' \<psi> \<or> Formula.sat \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>Formula.sat \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {j'<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms trigger sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {j<..i} \<and> \<not> Formula.sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        using assms j_props interval_geq[of I 0 \<sigma> i j k]
        by auto
      then have "\<exists>x \<in> {k<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> x) \<and> Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms trigger k_props sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {k<..i}" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> x)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<le> Max A"
        using A_def A_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<psi>" by blast
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>}"
      define k where "k = Max B"
      assume "Formula.sat \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)" "Formula.sat \<sigma> V v k \<phi>" using B_def by auto
      have "\<forall>l>k. l \<notin> B"
        using Max_ge[OF B_props(2)]
        by (fastforce simp: k_def)
      {
        fix l
        assume l_props: "l \<in> {k<..i}"
        then have l_mem: "mem I (\<tau> \<sigma> i - \<tau> \<sigma> l)"
          using assms k_props interval_geq[of I 0 \<sigma> i k l]
          by auto
        {
          assume "Formula.sat \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem by auto
          then have "l\<le>k" "l>k"
            using k_def l_props B_props(2) Max_ge[of B l]
            by auto
        }
        then have "\<not>Formula.sat \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{k<..i}. \<not>Formula.sat \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "Formula.sat \<sigma> V v k \<psi>" using k_props trigger B_def by auto
      {
        fix l
        assume l_props: "l\<in>{k<..i}"
        then have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> l)"
          using k_props assms interval_geq[of I 0 \<sigma> i k l]
          by auto
        then have "Formula.sat \<sigma> V v l \<psi>"
          using l_props trigger not_phi
          by auto
      }
      then have "\<forall>l\<in>{k<..i}. Formula.sat \<sigma> V v l \<psi>"
        using not_phi assms trigger
        by auto
      then have "Formula.sat \<sigma> V v i (Formula.Since \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by blast
  then show "Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
    using assms historically_rewrite_0[of I \<sigma> V v i "\<psi>"] trigger_safe_0_def
    by (simp add: trigger_safe_0_def) blast
next
  assume "Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (historically I \<psi>))"
    using trigger_safe_0_def assms historically_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by (simp add: trigger_safe_0_def) blast
  moreover {
    assume "Formula.sat \<sigma> V v i (historically I (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
      by auto
  }
  moreover {
    fix j
    assume since_and_j_props: "Formula.sat \<sigma> V v i (Formula.Since \<psi> I (Formula.And \<phi> \<psi>))" "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then obtain "j'" where j'_props:
      "j'\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "Formula.sat \<sigma> V v j' (Formula.And \<phi> \<psi>)"
      "(\<forall>k \<in> {j' <.. i}. Formula.sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume le: "j' < j"
      then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
        using j'_props since_and_j_props le
        by auto
    }
    moreover {
      assume geq: "\<not> j' < j"
      moreover {
        assume "j = j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
          using geq j'_props
          by auto
      }
      ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)" by auto
qed

lemma sat_trigger_rewrite:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" (* [a, b] *)
  assumes "I2 = flip_int_less_lower I1" (* [0, a-1] *)
shows "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>) = Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
proof (rule iffI)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> all (Formula.And \<phi> \<psi>)))))" by auto
  }
  moreover {
    assume "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> \<not>Formula.sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "\<not>Formula.sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{j <.. i} \<and> Formula.sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Max A"
    have "(\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" using j_props trigger by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{j <.. i}" "Formula.sat \<sigma> V v k \<phi>" using A_def by auto
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
      then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      then have k_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using geq_j_mem k_props by auto
      then have "Formula.sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {k <.. i}. Formula.sat \<sigma> V v k \<phi>)" using trigger k_props by auto
      moreover {
        assume "(\<exists>k \<in> {k <.. i}. Formula.sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {k <.. i}" "Formula.sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "Formula.sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_since: "Formula.sat \<sigma> V v k (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using int_remove_lower_bound.rep_eq memL.rep_eq by auto
      {
        assume "k=i"
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] assms k_mem
          by auto
      }
      moreover {
        assume "\<not>(k=i)"
        then have k_suc_leq_i: "k+1\<le>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
          then have "Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>)" using trigger by auto
          moreover {
            assume "\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {x <.. i}" "Formula.sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<le> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{k<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          moreover have "Formula.sat \<sigma> V v (k+1) (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_suc_leq_i k_since interval_all
            by auto
          ultimately have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_suc_leq_i
            by blast
          then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{k<..i} \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<and> Formula.sat \<sigma> V v l \<psi>}"
          define c where "c = Max B"
          assume "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))" using geq_j_mem k_props by auto
          then have "Formula.sat \<sigma> V v (k+1) \<psi> \<or> (\<exists>x \<in> {k+1 <.. i}. Formula.sat \<sigma> V v x \<phi>)" using trigger k_suc_leq_i by auto
          moreover {
            assume "\<exists>x \<in> {k+1 <.. i}. Formula.sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {k+1 <.. i} \<and> Formula.sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<le> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v (k+1) \<psi>" by auto
          then have B_props: "B \<noteq> {}" "finite B" using B_def k_suc_leq_i k_suc_mem k_props by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> c)" "Formula.sat \<sigma> V v c \<psi>"
            using B_def
            by auto
          then have k_cond: "k\<le>c" "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
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
            then have "Formula.sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{k<..c}. Formula.sat \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> c - \<tau> \<sigma> k)"
            using k_mem c_props
          by (metis diff_is_0_eq diff_self_eq_0 greaterThanAtMost_iff int_remove_lower_bound.rep_eq interval_leq memL.rep_eq memR.rep_eq prod.sel(1-2))
          ultimately have c_sat: "Formula.sat \<sigma> V v c (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using k_cond
            by auto
          {
            assume "(c+1) \<in> B"
            then have "c+1\<le>c" using c_def B_props by auto
            then have "False" by auto
          }
          then have "(c+1) \<notin> B" by blast
          then have disj: "(c+1)\<notin>{k<..i} \<or> \<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>Formula.sat \<sigma> V v (c+1) \<psi>" using B_def by blast
          {
            assume "(c+1)\<notin>{k<..i}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c+1)\<notin>{k<..i})"
            then have c_suc_leq_i: "(c+1)\<in>{k<..i}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>Formula.sat \<sigma> V v (c+1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
              then have "\<not>Formula.sat \<sigma> V v (c+1) \<psi>" using disj by blast
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
                  using not_mem2 memR_antimono
                  by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" by blast
              then have "(c+1)\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" "Formula.sat \<sigma> V v (c+1) (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_suc_leq_i c_sat interval_all
                by auto
              then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat_once
                by blast
            }
            ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by auto
next
  assume "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
  then have "Formula.sat \<sigma> V v i (historically I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (historically I1 \<psi>)"
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (once I2 \<phi>)"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" by blast
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
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume since: "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    {
      assume "j = 0"
      then have "\<not>Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
      then have "False" using j_props by auto
    }
    then have j_pos: "j>0" by auto
    then have j_pred_sat: "Formula.sat \<sigma> V v (j-1) (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
      using j_pos j_props
      by (simp add: Nitpick.case_nat_unfold)
    then have "\<exists>x\<le>(j-1). Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{x<..(j-1)}. Formula.sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<le>(j-1)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{x<..(j-1)}. Formula.sat \<sigma> V v k \<psi>"
      by blast
    {
      fix l
      assume l_props: "l\<le>i"
      {
        assume "l<x"
        then have "\<exists>k \<in> {l <.. i}. Formula.sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l<x)" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
        then have l_props: "x\<le>l" "l\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)" using l_props by auto
        {
          assume "l\<le>(j-1)"
          then have "Formula.sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<le>(j-1)"
          then have l_geq: "l\<ge>(j-1)" by auto
          have j_pred_psi: "Formula.sat \<sigma> V v (j-1) \<psi>" using j_pred_sat by auto
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
          then have "Formula.sat \<sigma> V v l \<psi>" using j_pred_psi by blast
        }
        ultimately have "Formula.sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<longrightarrow> Formula.sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {l <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by blast
qed

lemma sat_trigger_rewrite_unbounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "\<not>bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
  have disj: "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using trigger assms I2_def sat_trigger_rewrite
      by auto
  {
    assume "Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (once I1 \<psi>)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      using disj assms historically_rewrite_unbounded[of I1 \<sigma> V v i \<psi>]
    by simp
  }
  moreover {
    assume "\<not>Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (once I2 \<phi>) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using disj j_props
      by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      by simp
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_unbounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using trigger
    by auto
  then show "Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
    using trigger_safe_unbounded_def[of \<phi> I1 \<psi>] assms I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_unbounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def trigger_safe_unbounded_def
    by metis
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
    using assms historically_rewrite_unbounded[of I1 \<sigma> V v i \<psi>]
    by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
    using assms I2_def sat_trigger_rewrite assm
    by auto
qed

lemma sat_trigger_rewrite_bounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
  have disj: "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using trigger assms I2_def sat_trigger_rewrite
      by auto
  {
    assume "Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (once I1 \<psi>)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      using disj assms historically_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
    by simp
  }
  moreover {
    assume "\<not>Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (once I2 \<phi>) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using disj j_props
      by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      by simp
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_bounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using trigger
    by auto
  then show "Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
    using trigger_safe_bounded_def[of \<phi> I1 \<psi>] assms I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_bounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def trigger_safe_bounded_def
    by metis
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
    using assms historically_rewrite_bounded[of I1 \<sigma> V v i]
    by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
    using assms I2_def sat_trigger_rewrite assm
    by auto
qed

lemma sat_and_trigger_bounded_rewrite:
  assumes "bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) = Formula.sat \<sigma> V v i (and_trigger_safe_bounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)")
  case True
  then have once: "Formula.sat \<sigma> V v i (once I Formula.TT)"
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi>' I \<psi>') = Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi>' I \<psi>')"
    using sat_trigger_rewrite_bounded[OF assms(2,1), of \<sigma> V v i]
    by auto
  moreover have "
    Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<phi> (Formula.Neg (once I Formula.TT))) (Formula.And \<phi> (trigger_safe_bounded \<phi>' I \<psi>'))) =
    Formula.sat \<sigma> V v i (Formula.And \<phi> (trigger_safe_bounded \<phi>' I \<psi>'))"
    using once
    by auto
  ultimately show ?thesis
    unfolding and_trigger_safe_bounded_def
    by auto
qed (auto simp add: and_trigger_safe_bounded_def)

lemma sat_and_trigger_unbounded_rewrite:
  assumes "\<not>bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And \<phi> (Formula.Trigger \<phi>' I \<psi>')) = Formula.sat \<sigma> V v i (and_trigger_safe_unbounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)")
  case True
  then have once: "Formula.sat \<sigma> V v i (once I Formula.TT)"
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi>' I \<psi>') = Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi>' I \<psi>')"
    using sat_trigger_rewrite_unbounded[OF assms(2,1), of \<sigma> V v i]
    by auto
  moreover have "
    Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<phi> (Formula.Neg (once I Formula.TT))) (Formula.And \<phi> (trigger_safe_unbounded \<phi>' I \<psi>'))) =
    Formula.sat \<sigma> V v i (Formula.And \<phi> (trigger_safe_unbounded \<phi>' I \<psi>'))"
    using once
    by auto
  ultimately show ?thesis
    unfolding and_trigger_safe_unbounded_def
    by auto
qed (auto simp add: and_trigger_safe_unbounded_def)

lemma always_rewrite_0:
  fixes I :: \<I>
  assumes "mem I 0" "bounded I"
  shows "Formula.sat \<sigma> V v i (always I \<phi>) = Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)"
proof (rule iffI)
  assume all: "Formula.sat \<sigma> V v i (always I \<phi>)"
  {
    define A where "A = {j. j\<ge>i \<and> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)}"
    define j where "j = Inf A"
    assume "\<exists>j\<ge>i. mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then have "A \<noteq> {}" using A_def by auto
    then have "j \<in> A" using j_def by (simp add: Inf_nat_def1)
    then have j_props: "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" using A_def by auto
    {
      fix k
      assume k_props: "k \<in> {i..<j}"
      then have ineq: "\<tau> \<sigma> k - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by (simp add: diff_le_mono)
      {
        assume "mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        then have "k \<in> A" using A_def k_props by auto
        then have "k \<ge> j" using j_def cInf_lower by auto
        then have "False" using k_props by auto
      }
      then have "\<not>mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using j_props ineq assms(1) flip_int_double_upper_leq[of I "(\<tau> \<sigma> j - \<tau> \<sigma> i)" "(\<tau> \<sigma> k - \<tau> \<sigma> i)"]
        by auto 
      then have "Formula.sat \<sigma> V v k \<phi>" using k_props all by auto
    }
    then have until_j: "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>" by blast
    have "\<not> mem (flip_int_double_upper I) 0"
      using assms
      by (simp add: flip_int_double_upper.rep_eq memL.rep_eq)
    then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>))"
      using j_props until_j until_true[of "(flip_int_double_upper I)" \<sigma> V v i \<phi>]
      by auto
  }
  moreover {
    define B where "B = {b. \<not>memR I b}"
    define b where "b = Inf B"
    define C where "C = {k. k\<ge>i \<and> b \<le> \<tau> \<sigma> k - \<tau> \<sigma> i}"
    define c where "c = Inf C"
    assume empty_int: "\<forall>j\<ge>i. \<not> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" (* [b+1, 2b] *)
    from assms(2) have "B \<noteq> {}" using B_def bounded_memR by auto
    then have "b \<in> B" using b_def by (simp add: Inf_nat_def1)
    then have b_props: "\<not>memR I b" using B_def by auto
   
    have exists_db: "\<And>x. \<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
    proof -
      fix x
      show "\<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
        using ex_le_\<tau>[of i "x + \<tau> \<sigma> i" \<sigma>]
        by auto
    qed
    then have "C \<noteq> {}" using C_def by auto
    then have "c \<in> C" using c_def by (simp add: Inf_nat_def1)
    then have c_props: "c\<ge>i" "b \<le> \<tau> \<sigma> c - \<tau> \<sigma> i" using C_def by auto
    {
      assume "b = 0"
      then have "False" using b_props by auto
    }
    then have b_pos: "b>0" by blast
    {
      assume "c = i"
      then have "False" using c_props b_pos by auto
    }
    then have c_ge_i: "c>i" using c_props using le_less by blast
    {
      assume "\<not>mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
      then have "\<not>memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using assms(1) memL_mono by blast
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<in> B" using B_def by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<ge> b" using b_def cInf_lower by auto
      then have "(c-1) \<in> C" using C_def c_ge_i by auto
      then have "c-1 \<ge> c" using c_def cInf_lower by auto
      then have "False" using c_ge_i by auto
    }
    then have c_pred_mem: "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
    then have c_pred_sat: "Formula.sat \<sigma> V v (c-1) \<phi>" using all c_ge_i by auto
    {
      assume "\<not>mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" (* [b+1, \<infinity>] but attention, here 'b' = b+1 *)
      then have "memR I (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" using assms(1) bounded_memR int_flip_mem by blast
      then have c_dist: "(\<tau> \<sigma> c - \<tau> \<sigma> (c-1)) < b" using b_props memR_antimono not_le by blast
      from c_pred_mem have "memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) < b" using b_props memR_antimono not_le by blast
      then have b_ineq: "b \<le> (\<tau> \<sigma> c - \<tau> \<sigma> i)" "(\<tau> \<sigma> c - \<tau> \<sigma> i) \<le> 2 * (b-1)"
        using c_props c_dist
        by auto
      {
        assume "\<not>memR I (b-1)"
        then have "(b-1) \<in> B" using B_def by auto
        then have "(b-1) \<ge> b" using b_def cInf_lower by auto
        then have "False" using b_pos by linarith
      }
      then have "memR I (b-1)" by blast
      then have "(\<lambda>i. memR I ((div) i 2)) (2*(b-1))" by auto
      then have "(\<lambda>i. memR I ((div) i 2)) (\<tau> \<sigma> c - \<tau> \<sigma> i)" using b_ineq by auto
      then have "memR (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        by (simp add: flip_int_double_upper.rep_eq memR.rep_eq)
      moreover have "memL (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        using b_ineq b_props flip_int_double_upper.rep_eq memL.rep_eq memR_antimono
        by auto
      ultimately have "False" using empty_int c_props by auto
    }
    then have "mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" by blast
    then have c_pred_sat: "Formula.sat \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      using c_pred_sat c_ge_i
      by auto
    have "\<forall>j\<in>{i..<(c-1)}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
      by (meson \<tau>_mono assms(1) atLeastLessThan_iff c_pred_mem diff_le_mono le_eq_less_or_eq memL_mono memR_antimono zero_le)
    then have "\<forall>j\<in>{i..<(c-1)}. Formula.sat \<sigma> V v j \<phi>" using all by auto
    then have
        "(c-1)\<ge>i"
        "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
        "Formula.sat \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
        "(\<forall>k \<in> {i ..< (c-1)}. Formula.sat \<sigma> V v k \<phi>)"
      using c_ge_i c_pred_mem c_pred_sat
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
      by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    by auto
  then show "Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)" using always_safe_0_def by metis
next
  assume "Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    using always_safe_0_def
    by metis
  then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT) \<or> Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))" by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT)"
    then obtain j where j_props:
      "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>"
      by auto
    then have "\<forall>k\<ge>i. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<longrightarrow> k<j"
      by (metis (no_types, lifting) assms flip_int_double_upper.rep_eq forall_finite(1) interval_leq leI memL.rep_eq prod.sel(1))
    then have "Formula.sat \<sigma> V v i (always I \<phi>)" using j_props by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
    then obtain j where j_props:
      "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>"
      by auto
    then have phi_sat: "\<forall>k\<in>{i..j}. Formula.sat \<sigma> V v k \<phi>" by auto
    {
      fix k
      assume k_props: "k>j" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have t_geq: "(\<tau> \<sigma> k - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using diff_le_mono by auto
      from j_props have "mem (flip_int I) (\<tau> \<sigma> (j+1) - \<tau> \<sigma> j)" by auto
      then have "\<not>mem I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)"
        by (metis \<tau>_mono assms(2) diff_le_mono2 flip_int.rep_eq j_props(1) memL.rep_eq memL_mono prod.sel(1))
      then have "\<not>memR I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using assms memL_mono by blast
      then have "\<not>memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using t_geq memR_antimono by blast
      then have "False" using k_props by auto
    }
    then have "\<forall>k>j. \<not>mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
    then have "Formula.sat \<sigma> V v i (always I \<phi>)" using phi_sat by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (always I \<phi>)" by blast
qed

lemma always_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>)) = Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
  then show "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
    using assms always_safe_bounded_def
    by (simp add: always_safe_bounded_def)
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Neg (eventually I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def always_safe_bounded_def
    by (simp add: always_safe_bounded_def)
  then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<phi>" by auto
  have j_geq_i_sat: "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> (Formula.sat \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<ge>i" "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
    then have "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v k \<phi>"
      using j_geq_i_sat by auto
    moreover {
      assume assm: "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          using j_props assms
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          using k_props assms
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def interval_geq j_props(1)
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms I2_def j_props(1) k_props(1) interval_geq
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "Formula.sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<phi>" by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
    using rewrite
    by auto
qed

lemma sat_release_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  assumes geq: "j\<ge>i"
  assumes mem_j: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  shows "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {i..<j}. Formula.sat \<sigma> V v x \<phi>}"
  define k where "k = Min A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {i..<j}" "Formula.sat \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "(\<forall>l<k. l \<notin> A)"
    using Min_le[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using mem mem_j k_props interval_leq[of I 0 \<sigma> j i k] by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat_release_rewrite_0:
  assumes mem: "mem I 0" "bounded I"
shows "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume release: "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  {
    assume "\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  moreover {
    assume "\<not>(\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<ge> i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "\<not>Formula.sat \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    define A where "A = {j. j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Min A"
    from j'_props have "\<not>Formula.sat \<sigma> V v j' \<psi> \<or> Formula.sat \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>Formula.sat \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {i..<j'}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms release sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {i..<j} \<and> \<not> Formula.sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using assms j_props interval_leq[of I 0 \<sigma> j i k]
        by auto
      then have "\<exists>x \<in> {i..<k}. mem I (\<tau> \<sigma> x - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms release k_props sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {i..<k}" "mem I (\<tau> \<sigma> x - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<ge> Min A"
        using A_def A_props k_props j_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<psi>" by blast
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<in>{i..j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j \<phi>}"
      define k where "k = Min B"
      assume "Formula.sat \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<in>{i..j'}" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v k \<phi>" using B_def by auto
      have "\<forall>l<k. l \<notin> B"
        using Min_le[OF B_props(2)]
        by (fastforce simp: k_def)
      {
        fix l
        assume l_props: "l \<in> {i..<k}"
        then have l_mem: "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using assms k_props interval_leq[of I 0 \<sigma> k i l]
          by auto
        {
          assume "Formula.sat \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem k_props by auto
          then have "l\<ge>k" "l<k"
            using k_def l_props B_props(2) Min_le[of B l]
            by auto
        }
        then have "\<not>Formula.sat \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{i..<k}. \<not>Formula.sat \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "Formula.sat \<sigma> V v k \<psi>" using k_props release B_def by auto
      {
        fix l
        assume l_props: "l\<in>{i..<k}"
        then have "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using k_props assms interval_leq[of I 0 \<sigma> k i l]
          by auto
        then have "Formula.sat \<sigma> V v l \<psi>"
          using l_props release not_phi
          by auto
      }
      then have "\<forall>l\<in>{i..<k}. Formula.sat \<sigma> V v l \<psi>"
        using not_phi assms release
        by auto
      then have "Formula.sat \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by blast
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  then show "Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
next
  assume "Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
    using assms always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (always I \<psi>)"
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
  }
  moreover {
    fix j
    assume until_and_j_props: "Formula.sat \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))" "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then obtain "j'" where j'_props: "j'\<ge>i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j' (Formula.And \<phi> \<psi>)" "(\<forall>k \<in> {i ..< j'}. Formula.sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume ge: "j' > j"
      then have "\<forall>k \<in> {i ..< j'}. Formula.sat \<sigma> V v k \<psi>" using j'_props by auto
      then have "Formula.sat \<sigma> V v j \<psi>" using until_and_j_props ge by auto
      then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by auto
    }
    moreover {
      assume leq: "\<not> j' > j"
      moreover {
        assume "j = j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using leq j'_props
          by auto
      }
      ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
qed

lemma sat_release_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
shows "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume release: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
  {
    assume "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<psi>"
    then have all: "Formula.sat \<sigma> V v i (always I1 \<psi>)" by auto
    obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using release by auto
    then have "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>)"
      using assms always_rewrite_bounded[of I1 \<sigma> V v i \<psi>] all
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      by auto
  }
  moreover {
    assume "\<exists>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> \<not>Formula.sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<not>Formula.sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{i ..< j} \<and> Formula.sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Min A"
    have "(\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" using j_props release by auto
    then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{i ..< j}" "Formula.sat \<sigma> V v k \<phi>" using A_def by auto
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
          using k_not_mem_1 x_props assms I2_def
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    }
    then have geq_j_mem: "\<forall>x\<le>j. \<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have k_mem: "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
      then have "Formula.sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {i ..< k}. Formula.sat \<sigma> V v k \<phi>)" using release k_props by auto
      moreover {
        assume "(\<exists>k \<in> {i ..< k}. Formula.sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {i ..< k}" "Formula.sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "Formula.sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_until: "Formula.sat \<sigma> V v k (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using assms int_remove_lower_bound.rep_eq memL.rep_eq prod.sel(1)
        by auto
      {
        assume "k=i"
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] using assms k_mem by auto
      }
      moreover {
        assume k_neq_i: "\<not>(k=i)"
        then have k_pred_geq_i: "k-1\<ge>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {i..<k}" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          then have "Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>)" using release by auto
          moreover {
            assume "\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {i ..< x}" "Formula.sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<ge> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{i..<k}. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          moreover have "Formula.sat \<sigma> V v (k-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_pred_geq_i k_until interval_all k_neq_i
            by auto
          ultimately have "(\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_pred_geq_i
            by blast
          then have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{i..<k} \<and> mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v l \<psi>}"
          define c where "c = Min B"
          assume "\<not>mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
          then have "Formula.sat \<sigma> V v (k-1) \<psi> \<or> (\<exists>x \<in> {i ..< k-1}. Formula.sat \<sigma> V v x \<phi>)"
            using release k_pred_geq_i
            by auto
          moreover {
            assume "\<exists>x \<in> {i ..< k-1}. Formula.sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {i ..< k-1} \<and> Formula.sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<ge> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v (k-1) \<psi>" by auto
          then have B_props: "B \<noteq> {} \<and> finite B"
            using B_def k_pred_geq_i k_suc_mem k_props k_neq_i
            by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{i..<k}" "mem I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v c \<psi>" using B_def by auto
          then have k_cond: "k\<ge>c" "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
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
            then have "Formula.sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{c..<k}. Formula.sat \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> k - \<tau> \<sigma> c)"
            using k_mem c_props
            by (metis atLeastLessThan_iff int_remove_lower_bound.rep_eq interval_geq less_or_eq_imp_le memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
          ultimately have c_sat: "Formula.sat \<sigma> V v c (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using assms k_cond
            by auto
          {
            assume "(c-1) \<in> B"
            then have "c-1\<ge>c" using c_def B_props by auto
            moreover have "c-1 < c" using c_pos by auto
            ultimately have "False" by auto
          }
          then have "(c-1) \<notin> B" by blast
          then have disj: "(c-1)\<notin>{i..<k} \<or> \<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>Formula.sat \<sigma> V v (c-1) \<psi>" using B_def by blast
          {
            assume "(c-1)\<notin>{i..<k}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c-1)\<notin>{i..<k})"
            then have c_pred_geq_i: "(c-1)\<in>{i..<k}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>Formula.sat \<sigma> V v (c-1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              then have "\<not>Formula.sat \<sigma> V v (c-1) \<psi>" using disj by blast
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
              then have "(c-1)\<ge>i" "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v (c-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_pred_geq_i c_sat interval_all c_pos
                by auto
              then have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat_eventually
                by blast
            }
            ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using release
    by auto
  then show "Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
    using assms I2_def
    by (simp add: release_safe_bounded_def) blast
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def
    by (auto simp: release_safe_bounded_def)
  then have eventually: "Formula.sat \<sigma> V v i (eventually I1 Formula.TT)" by auto
  then have "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (eventually I2 \<phi>) \<or> Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    using assm
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>)"
    then have "Formula.sat \<sigma> V v i (always I1 \<psi>)"
      using assms always_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (eventually I2 \<phi>)"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<ge>i" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume "x\<le>j"
        then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using j_props assms I2_def flip_int_less_lower_props
          by (meson diff_le_mono memL_mono memR_antimono memR_zero zero_le)
        then have "False" using x_props assms I2_def
          using flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<le>j)" by blast
      then have "x>j" by auto
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> x>j" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume until: "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    then have j_pred_sat: "Formula.sat \<sigma> V v (j+1) (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))" by auto
    then have "\<exists>x\<ge>(j+1). Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{(j+1)..<x}. Formula.sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<ge>(j+1)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{(j+1)..<x}. Formula.sat \<sigma> V v k \<psi>" by blast
    {
      fix l
      assume l_props: "l\<ge>i"
      {
        assume "l>x"
        then have "\<exists>k \<in> {i ..< l}. Formula.sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l>x)" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        then have l_props: "x\<ge>l" "l\<ge>i" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using l_props by auto
        {
          assume "l\<ge>(j+1)"
          then have "Formula.sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<ge>(j+1)"
          then have l_geq: "l\<le>(j+1)" by auto
          have j_suc_psi: "Formula.sat \<sigma> V v (j+1) \<psi>" using j_pred_sat by auto
          {
            assume "l<(j+1)"
            then have "\<tau> \<sigma> l \<le> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using assms I2_def j_props flip_int_less_lower_props
            by (meson diff_le_mono le0 memL_mono memR_antimono memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
              using assms I2_def flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j+1)" using l_geq le_eq_less_or_eq by blast
          then have "Formula.sat \<sigma> V v l \<psi>" using j_suc_psi by blast
        }
        ultimately have "Formula.sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {i ..< l}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>)" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by blast
  then show "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
    using assm
    by auto
qed

lemma sat_and_release_rewrite:
  assumes "bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>')) = Formula.sat \<sigma> V v i (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
  case True
  then have eventually: "Formula.sat \<sigma> V v i (eventually I Formula.TT)"
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Release \<phi>' I \<psi>') = Formula.sat \<sigma> V v i (release_safe_bounded \<phi>' I \<psi>')"
    using sat_release_rewrite[OF assms, of \<sigma> V v i \<phi>' \<psi>']
    by auto
  moreover have "
    Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<phi> (Formula.Neg (eventually I Formula.TT))) (Formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>'))) =
    Formula.sat \<sigma> V v i (Formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>'))"
    using eventually
    by auto
  ultimately show ?thesis
    unfolding and_release_safe_bounded_def
    by auto
qed (auto simp add: and_release_safe_bounded_def)

(* end rewrite formulas *)

fun map_formula :: "('t Formula.formula \<Rightarrow> 't Formula.formula) 
  \<Rightarrow> 't Formula.formula \<Rightarrow> 't Formula.formula" 
  where "map_formula f (Formula.Pred r ts) = f (Formula.Pred r ts)"
  | "map_formula f (Formula.Let p \<phi> \<psi>) = f (
      Formula.Let p (map_formula f \<phi>) (map_formula f \<psi>)
    )"
  | "map_formula f (Formula.LetPast p \<phi> \<psi>) = f (
      Formula.LetPast p (map_formula f \<phi>) (map_formula f \<psi>)
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
  | "map_formula f (Formula.Exists t \<phi>) = f (Formula.Exists t (map_formula f \<phi>))"
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
  | "map_formula f (formula.TP t) = f (formula.TP t)"
  | "map_formula f (formula.TS t) = f (formula.TS t)"

lemma map_formula_fvi:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  shows "Formula.fvi b (map_formula f \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi> arbitrary: b) 
qed (auto simp add: assms release_safe_0_def always_safe_0_def)

lemma map_formula_sat:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  assumes "\<And>\<sigma> V v i \<phi>. Formula.sat \<sigma> V v i (f \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  shows "\<And>\<sigma> V v i. Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (map_formula f \<phi>)"
  using assms 
proof (induction \<phi>)
  case assm: (Let p \<phi>' \<psi>')
  from assms have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
    using Formula.nfv_def map_formula_fvi
    by (simp add: Formula.nfv_def map_formula_fvi)
  {
    fix \<sigma> V v i
    let ?V' = "V((p, Formula.nfv \<phi>') \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>')"
    have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> ?V' v i \<psi>'"
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> ?V' v i (map_formula f \<psi>')"
      using assm
      by blast
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Let p \<phi>' \<psi>'))"
      using assm nfv_eq assms
      by auto
  }
  then show ?case by blast
next
  case assm: (LetPast p \<phi>' \<psi>')
  from assms have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
    using Formula.nfv_def map_formula_fvi
    by (simp add: Formula.nfv_def map_formula_fvi)
  {
    fix \<sigma> V v i
    let ?V' = "V((p, Formula.nfv \<phi>') \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>') \<mapsto> X)) u k \<phi>'))"
    have "Formula.sat \<sigma> V v i (formula.LetPast p \<phi>' \<psi>') = Formula.sat \<sigma> ?V' v i \<psi>'"
      by (auto simp: Let_def)
    then have "Formula.sat \<sigma> V v i (formula.LetPast p \<phi>' \<psi>') = Formula.sat \<sigma> ?V' v i (map_formula f \<psi>')"
      using assm
      by blast
    then have "Formula.sat \<sigma> V v i (formula.LetPast p \<phi>' \<psi>') 
      = Formula.sat \<sigma> V v i (map_formula f (formula.LetPast p \<phi>' \<psi>'))"
      using assm nfv_eq assms
      by auto
  }
  then show ?case by blast
next
  case assm: (Agg y \<omega> tys f' \<phi>')
  {
    fix \<sigma> V v i
    define M where "M = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = length tys \<and>
        Formula.sat \<sigma> V (zs @ v) i \<phi>' \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    define M' where "M' = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = length tys \<and>
        Formula.sat \<sigma> V (zs @ v) i (map_formula f \<phi>') \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    have M_eq: "M = M'" using M_def M'_def assm by auto
    have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
      using assms
      by (simp add: Formula.nfv_def map_formula_fvi)

    have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> tys f' \<phi>') = (
      (M = {} \<longrightarrow> fv \<phi>' \<subseteq> {0..<(length tys)}) \<and> v ! y = eval_agg_op \<omega> M
    )"
      using M_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> tys f' \<phi>') = (
      (M' = {} \<longrightarrow> fv (map_formula f \<phi>') \<subseteq> {0..<(length tys)}) \<and> v ! y = eval_agg_op \<omega> M')"
      using assms assm
      by (auto simp: M_eq nfv_eq map_formula_fvi)
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> tys f' \<phi>') 
    = Formula.sat \<sigma> V v i (formula.Agg y \<omega> tys f' (map_formula f \<phi>'))"
      using M'_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> tys f' \<phi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Agg y \<omega> tys f' \<phi>'))"
      using assms by auto
  }
  then show ?case by blast
qed (auto split: nat.split)


fun rewrite_trigger :: "'t Formula.formula \<Rightarrow> 't Formula.formula" where
  "rewrite_trigger (Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)) = (
    if (mem I 0) then
      \<comment> \<open>the rewrite function already was applied recursively, hence the trigger should already be rewritten\<close>
      Formula.And \<phi> ( trigger_safe_0 \<alpha> I \<beta>)
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
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> ( trigger_safe_0 \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And
        using Trigger
        by simp
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have obs: "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          by (simp add: obs and_trigger_safe_bounded_def)
      next
        case False
        then have obs: "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          unfolding And Trigger
          by (simp add: obs and_trigger_safe_unbounded_def)
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
      by simp
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
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (trigger_safe_0 \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And Trigger
        using sat_trigger_rewrite_0[OF True]
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


(*<*)
end
(*>*)
