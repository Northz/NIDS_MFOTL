(*<*)
theory Safety
  imports Formula
begin
(*>*)


section \<open> Safety \<close>


subsection \<open> Safety definition \<close>


subsubsection \<open> Constraints \<close>

unbundle MFODL_notation \<comment> \<open> enable notation \<close>

fun is_constraint :: "'t Formula.formula \<Rightarrow> bool" 
  where "is_constraint (t1 =\<^sub>F t2) = True"
  | "is_constraint (t1 <\<^sub>F t2) = True"
  | "is_constraint (t1 \<le>\<^sub>F t2) = True"
  | "is_constraint (\<not>\<^sub>F (t1 =\<^sub>F t2)) = True"
  | "is_constraint (\<not>\<^sub>F (t1 <\<^sub>F t2)) = True"
  | "is_constraint (\<not>\<^sub>F (t1 \<le>\<^sub>F t2)) = True"
  | "is_constraint _ = False"

lemma is_constraint_Neg_iff: "is_constraint (\<not>\<^sub>F \<alpha>) \<longleftrightarrow> 
  (\<exists>t1 t2. \<alpha> = t1 =\<^sub>F t2 \<or> \<alpha> = t1 <\<^sub>F t2 \<or> \<alpha> = t1 \<le>\<^sub>F t2)"
  by (cases \<alpha>, simp_all)

lemma is_constraint_iff: "is_constraint \<alpha> \<longleftrightarrow> (\<exists>t1 t2. \<alpha> = t1 =\<^sub>F t2 \<or> \<alpha> = t1 <\<^sub>F t2 
  \<or> \<alpha> = t1 \<le>\<^sub>F t2 \<or> \<alpha> = \<not>\<^sub>F (t1 =\<^sub>F t2) \<or> \<alpha> = \<not>\<^sub>F (t1 <\<^sub>F t2) \<or> \<alpha> = \<not>\<^sub>F (t1 \<le>\<^sub>F t2))"
  by (cases \<alpha>, simp_all add: is_constraint_Neg_iff)

lemma no_constr_neventually: "\<not> is_constraint (formula.Neg (Formula.eventually I \<phi>))"
  unfolding eventually_def
  by auto

lemma no_constr_release_safe_bounded [simp]: 
  "\<not> is_constraint (release_safe_bounded \<phi>'' I \<psi>')"
  unfolding is_constraint_iff release_safe_bounded_def 
  by simp


subsubsection \<open> Equalities for conjunctions \<close>

definition safe_assignment :: "nat set \<Rightarrow> 'a Formula.formula \<Rightarrow> bool" where
  "safe_assignment X \<alpha> = (case \<alpha> of
       \<^bold>v x =\<^sub>F \<^bold>v y \<Rightarrow> (x \<notin> X \<longleftrightarrow> y \<in> X)
     | \<^bold>v x =\<^sub>F t \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | t =\<^sub>F \<^bold>v x \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | _ \<Rightarrow> False)"

lemma safe_assignment_Eq_iff: "safe_assignment X (t1 =\<^sub>F t2) 
  \<longleftrightarrow> (\<exists>x y. t1 = \<^bold>v x \<and> t2 = \<^bold>v y \<and> (x \<notin> X \<longleftrightarrow> y \<in> X)) 
    \<or> (\<exists>x. t1 = \<^bold>v x \<and> (x \<notin> X \<and> FV\<^sub>t t2 \<subseteq> X)) 
    \<or> (\<exists>x. t2 = \<^bold>v x \<and> (x \<notin> X \<and> FV\<^sub>t t1 \<subseteq> X))"
  by (cases t1; cases t2, auto simp: safe_assignment_def)

lemmas safe_assignment_EqD = iffD1[OF safe_assignment_Eq_iff]
   and safe_assignment_EqI = iffD2[OF safe_assignment_Eq_iff]

lemma safe_assignment_iff: "safe_assignment X \<beta> 
  \<longleftrightarrow> (\<exists>x y. \<beta> = (\<^bold>v x =\<^sub>F \<^bold>v y) \<and> (x \<notin> X \<longleftrightarrow> y \<in> X)) 
    \<or> (\<exists>x t. \<beta> = (\<^bold>v x =\<^sub>F t) \<and> (x \<notin> X \<and> FV\<^sub>t t \<subseteq> X)) 
    \<or> (\<exists>x t. \<beta> = (t =\<^sub>F \<^bold>v x) \<and> (x \<notin> X \<and> FV\<^sub>t t \<subseteq> X))"
  by (cases \<beta>; simp add: safe_assignment_Eq_iff) 
    (simp_all add: safe_assignment_def)

lemma safe_assignment_iff2: 
  "safe_assignment X \<beta> \<longleftrightarrow> (\<exists>x t. (x \<notin> X \<and> FV\<^sub>t t \<subseteq> X) \<and> (\<beta> = (\<^bold>v x =\<^sub>F t) \<or> \<beta> = (t =\<^sub>F \<^bold>v x)))
  \<or> (\<exists>x y. (x \<notin> X \<longleftrightarrow> y \<in> X) \<and> \<beta> = (\<^bold>v x =\<^sub>F \<^bold>v y))"
  unfolding safe_assignment_iff
  by (intro conjI impI allI iffI; (clarsimp, blast))

lemmas safe_assignmentD = iffD1[OF safe_assignment_iff]
   and safe_assignmentI = iffD2[OF safe_assignment_iff]

lemma safe_assignment_Neg_iff[simp]: "safe_assignment X (\<not>\<^sub>F \<beta>) \<longleftrightarrow> False"
  unfolding safe_assignment_iff by auto

lemma no_safe_assign_next: "\<not> safe_assignment X (formula.Next I \<phi>)"
  unfolding safe_assignment_def
  by auto

lemma no_safe_assign_release_safe_bounded [simp]: 
  "\<not> safe_assignment X (release_safe_bounded \<phi>'' I \<psi>')"
  unfolding safe_assignment_iff release_safe_bounded_def 
  by simp

lemma no_safe_assign_trigger: "\<not> safe_assignment (fv \<phi>) (formula.Trigger \<alpha> I \<beta>)"
  unfolding safe_assignment_def
  by auto


subsubsection \<open> Let past \<close>

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

lemma sup_Unused[simp]: "x \<squnion> Unused = x" "Unused \<squnion> x = x"
  by (simp_all flip: bot_rec_safety_def)

lemma sup_eq_Unused_iff: "(x::rec_safety) \<squnion> y = Unused \<longleftrightarrow> x = Unused \<and> y = Unused"
  by (cases x; cases y) simp_all

lemma sup_eq_NonFutuRec_iff: "x \<squnion> y = NonFutuRec \<longleftrightarrow>
    (x = NonFutuRec \<and> y \<le> NonFutuRec) \<or> (x \<le> NonFutuRec \<and> y = NonFutuRec)"
  by (cases x; cases y) simp_all

lemma Sup_rec_safety_le_iff: "\<Squnion> A \<le> (x::rec_safety) \<longleftrightarrow> (\<forall>y\<in>A. y \<le> x)"
  unfolding Sup_rec_safety_def using finite[of A]
  by (induction A rule: finite_induct)
    (simp_all add: comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_on_sup])

lemma le_Sup_rec_safety_iff: "(x::rec_safety) \<le> \<Squnion> A \<longleftrightarrow> (\<exists>y\<in>insert Unused A. x \<le> y)"
  unfolding Sup_rec_safety_def using finite[of A]
  apply (induction A rule: finite_induct)
   apply (auto simp add: comp_fun_idem_on.fold_insert_idem[OF comp_fun_idem_on_sup]
        bot.extremum_unique
      simp flip: bot_rec_safety_def
      intro: sup.coboundedI1 sup.coboundedI2)
  by (smt (z3) sup_rec_safety.elims)

lemma Sup_eq_Unused_iff: "\<Squnion> A = Unused \<longleftrightarrow> A \<subseteq> {Unused}"
proof -
  have "\<Squnion> A = Unused \<longleftrightarrow> \<Squnion> A \<le> Unused"
    by (simp flip: bot_rec_safety_def add: bot_unique)
  also have "\<dots> \<longleftrightarrow> (\<forall>y\<in>A. y \<le> Unused)"
    unfolding Sup_rec_safety_le_iff ..
  finally show ?thesis
    by (auto simp flip: bot_rec_safety_def simp add: bot_unique)
qed

lemma mult_Unused[simp]: "x * Unused = Unused"
  by (simp flip: zero_rec_safety_def)

lemma mult_eq_Unused_iff: "(x::rec_safety) * y = Unused \<longleftrightarrow> x = Unused \<or> y = Unused"
  by (cases x; cases y) simp_all

lemma mult_le_NonFutuRec_iff:
  "x * y \<le> NonFutuRec \<longleftrightarrow> x = Unused \<or> y = Unused \<or> x \<le> NonFutuRec \<and> y \<le> NonFutuRec"
  by (cases x; cases y) simp_all

lemma mult_le_NonFutuRec_cases:
  assumes "x * y \<le> NonFutuRec"
  obtains (unused1) "x = Unused" | (unused2) "y = Unused"
  | (NonFutuRec) "x \<le> NonFutuRec" and "y \<le> NonFutuRec"
  using assms by (auto simp add: mult_le_NonFutuRec_iff)

lemma mult_eq_NonFutuRec_iff: "x * y = NonFutuRec \<longleftrightarrow> x = NonFutuRec \<and> y = NonFutuRec"
  by (cases x; cases y) simp_all

context begin

fun safe_letpast :: "Formula.name \<times> nat \<Rightarrow> 't Formula.formula \<Rightarrow> rec_safety" 
  where "safe_letpast p (t1 =\<^sub>F t2) = Unused"
  | "safe_letpast p (t1 <\<^sub>F t2) = Unused"
  | "safe_letpast p (t1 \<le>\<^sub>F t2) = Unused"
  | "safe_letpast p (e \<dagger> ts) = (if p = (e, length ts) then NonFutuRec else Unused)"
  | "safe_letpast p (Formula.Let e \<phi> \<psi>) =
        (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion>
        (if p = (e, Formula.nfv \<phi>) then Unused else safe_letpast p \<psi>)"
  | "safe_letpast p (Formula.LetPast e \<phi> \<psi>) =
        (if p = (e, Formula.nfv \<phi>) then Unused else
          (safe_letpast (e, Formula.nfv \<phi>) \<psi> * safe_letpast p \<phi>) \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (\<not>\<^sub>F \<phi>) = safe_letpast p \<phi>"
  | "safe_letpast p (\<phi> \<or>\<^sub>F \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (\<phi> \<and>\<^sub>F \<psi>) = (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (\<And>\<^sub>F l) = \<Squnion>(safe_letpast p ` set l)"
  | "safe_letpast p (\<exists>\<^sub>F:t. \<phi>) = safe_letpast p \<phi>"
  | "safe_letpast p (Formula.Agg y \<omega> tys f \<phi>) = safe_letpast p \<phi>"
  | "safe_letpast p (\<^bold>Y I \<phi>) = PastRec * safe_letpast p \<phi>"
  | "safe_letpast p (\<^bold>X I \<phi>) = AnyRec * safe_letpast p \<phi>"
  | "safe_letpast p (\<phi> \<^bold>S I \<psi>) = safe_letpast p \<phi> \<squnion>
        ((if memL I 0 then NonFutuRec else PastRec) * safe_letpast p \<psi>)"
  | "safe_letpast p (\<phi> \<^bold>U I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (\<phi> \<^bold>T I \<psi>) = safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>"
  | "safe_letpast p (\<phi> \<^bold>R I \<psi>) = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
  | "safe_letpast p (Formula.MatchP I r) = \<Squnion>(safe_letpast p ` Regex.atms r)"
  | "safe_letpast p (Formula.MatchF I r) =  AnyRec * \<Squnion>(safe_letpast p ` Regex.atms r)"
  | "safe_letpast p (Formula.TP t) = Unused"
  | "safe_letpast p (Formula.TS t) = Unused"

lemma safe_letpast_simps2[simp]: 
  "safe_letpast p Formula.TT = Unused"
  "safe_letpast p (eventually I \<phi>) = AnyRec * safe_letpast p \<phi>"
  "safe_letpast p (once I \<phi>) = (if mem I 0 then NonFutuRec * safe_letpast p \<phi> else PastRec * safe_letpast p \<phi>)"
  by (simp_all add: Formula.TT_def eventually_def once_def bot_rec_safety_def[symmetric])

lemma safe_letpast_Unused: "safe_letpast p \<phi> = Unused \<Longrightarrow> \<not> contains_pred p \<phi>"
  by (induction \<phi> arbitrary: p) (auto simp add: sup_eq_Unused_iff Sup_eq_Unused_iff
      mult_eq_Unused_iff split: if_splits)

lemma V_subst_letpast_gen:
  "safe_letpast p \<phi> \<le> NonFutuRec \<Longrightarrow>
  (safe_letpast p \<phi> = NonFutuRec \<Longrightarrow> (\<And>v j. j \<le> i \<Longrightarrow> f v j = g v j)) \<Longrightarrow>
  (\<And>v j. j < i \<Longrightarrow> f v j = g v j) \<Longrightarrow>
  Formula.sat \<sigma> (V(p \<mapsto> f)) v i \<phi> = Formula.sat \<sigma> (V(p \<mapsto> g)) v i \<phi>"
proof (induction \<phi> arbitrary: p V v i f g)
  case (Pred e tms)
  then show ?case by (auto split: if_splits)
next
  case (Let e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  let ?s\<phi> = "\<lambda>V v i. Formula.sat \<sigma> V v i \<phi>"
  let ?s\<psi> = "\<lambda>V. Formula.sat \<sigma> V v i \<psi>"
  from Let.prems(1) have "safe_letpast ?en \<psi> * safe_letpast p \<phi> \<le> NonFutuRec" by simp
  then have "?s\<psi> (V(p \<mapsto> f, ?en \<mapsto> ?s\<phi> (V(p \<mapsto> f)))) = ?s\<psi> (V(p \<mapsto> f, ?en \<mapsto> ?s\<phi> (V(p \<mapsto> g))))"
  proof (cases rule: mult_le_NonFutuRec_cases)
    case unused1
    then show ?thesis by (simp add: safe_letpast_Unused)
  next
    case unused2
    then show ?thesis by (simp add: safe_letpast_Unused)
  next
    case NonFutuRec
    have "\<And>v j. j \<le> i \<Longrightarrow> ?s\<phi> (V(p \<mapsto> f)) v j = ?s\<phi> (V(p \<mapsto> g)) v j"
      if "safe_letpast ?en \<psi> = NonFutuRec"
      using NonFutuRec(2)
      apply (rule Let.IH(1))
       apply (rule Let.prems(2))
      using Let.prems(1) that apply (simp add: sup.absorb_iff1 split: if_splits)
       apply simp
      apply (rule Let.prems(3))
      apply simp
      done
    moreover have "\<And>v j. j < i \<Longrightarrow> ?s\<phi> (V(p \<mapsto> f)) v j = ?s\<phi> (V(p \<mapsto> g)) v j"
      using NonFutuRec(2)
      apply (rule Let.IH(1))
      using Let.prems(3) by auto
    ultimately show ?thesis
      using NonFutuRec(1)
      by (intro Let.IH(2)) simp_all
  qed
  also have "\<dots> = ?s\<psi> (V(p \<mapsto> g, ?en \<mapsto> ?s\<phi> (V(p \<mapsto> g))))"
  proof (cases "p = ?en")
    case True
    then show ?thesis by simp
  next
    case False
    have "?s\<psi> (V(?en \<mapsto> ?s\<phi> (V(p \<mapsto> g)), p \<mapsto> f)) = ?s\<psi> (V(?en \<mapsto> ?s\<phi> (V(p \<mapsto> g)), p \<mapsto> g))"
      apply (rule Let.IH(2))
      using Let.prems(1) False apply simp
       apply (rule Let.prems(2))
      using Let.prems(1) False apply (simp add: sup.absorb2)
      apply assumption
      by (rule Let.prems(3))
    then show ?thesis
      using False by (simp add: fun_upd_twist[of p])
  qed
  finally show ?case by (simp del: fun_upd_apply)
next
  case (LetPast e \<phi> \<psi>)
  let ?en = "(e, Formula.nfv \<phi>)"
  let ?s\<phi>1 = "\<lambda>V v i. Formula.sat \<sigma> V v i \<phi>"
  let ?s\<phi> = "\<lambda>V. letpast_sat (\<lambda>X. ?s\<phi>1 (V(?en \<mapsto> X)))"
  let ?s\<psi> = "\<lambda>V. Formula.sat \<sigma> V v i \<psi>"
  show ?case
  proof (cases "p = ?en")
    case True
    then show ?thesis by (simp add: Let_def del: fun_upd_apply)
  next
    case False
    with LetPast.prems(1) have "safe_letpast ?en \<psi> * safe_letpast p \<phi> \<le> NonFutuRec"
      by simp
    then have "?s\<psi> (V(p \<mapsto> f, ?en \<mapsto> ?s\<phi> (V(p \<mapsto> f)))) = ?s\<psi> (V(p \<mapsto> f, ?en \<mapsto> ?s\<phi> (V(p \<mapsto> g))))"
    proof (cases rule: mult_le_NonFutuRec_cases)
      case unused1
      then show ?thesis by (simp add: safe_letpast_Unused)
    next
      case unused2
      with False show ?thesis by (simp add: safe_letpast_Unused fun_upd_twist[of p])
    next
      case NonFutuRec
      have "\<And>v j. j \<le> i \<Longrightarrow> ?s\<phi>1 (W(p \<mapsto> f)) v j = ?s\<phi>1 (W(p \<mapsto> g)) v j"
        if "safe_letpast ?en \<psi> = NonFutuRec" for W
        using NonFutuRec(2)
        apply (rule LetPast.IH(1))
         apply (rule LetPast.prems(2))
        using LetPast.prems(1) that False apply simp
          apply (metis sup.orderE)
         apply simp
        apply (rule LetPast.prems(3))
        apply simp
        done
      moreover have "\<And>v j. j < i \<Longrightarrow> ?s\<phi>1 (W(p \<mapsto> f)) v j = ?s\<phi>1 (W(p \<mapsto> g)) v j" for W
        using NonFutuRec(2)
        apply (rule LetPast.IH(1))
        using LetPast.prems(3) by auto
      ultimately show ?thesis
        using NonFutuRec(1)
        apply (intro LetPast.IH(2))
          apply assumption
         apply (intro V_subst_letpast_sat)
         apply (simp add: fun_upd_twist[of p, OF False])
        apply (intro V_subst_letpast_sat)
        apply (simp add: fun_upd_twist[of p, OF False])
        done
    qed
    moreover have "?s\<psi> (V(?en \<mapsto> ?s\<phi> (V(p \<mapsto> g)), p \<mapsto> f)) = ?s\<psi> (V(?en \<mapsto> ?s\<phi> (V(p \<mapsto> g)), p \<mapsto> g))"
      apply (rule LetPast.IH(2))
      using LetPast.prems(1) False apply simp
       apply (rule LetPast.prems(2))
      using LetPast.prems(1) False apply (simp add: sup.absorb2)
       apply assumption
      by (rule LetPast.prems(3))
    ultimately show ?thesis
      by (simp add: Let_def fun_upd_twist[of p, OF False] del: fun_upd_apply)
  qed
next
  case (Neg \<phi>)
  show ?case
    using Neg.IH[of p i f g V v] Neg.prems
    by simp
next
  case (Or \<phi> \<psi>)
  show ?case
    using Or.IH[of p i f g V v] Or.prems
    by (simp add: sup.absorb1 sup.absorb2 del: fun_upd_apply)
next
  case (And \<phi> \<psi>)
  show ?case
    using And.IH[of p i f g V v] And.prems
    by (simp add: sup.absorb1 sup.absorb2 del: fun_upd_apply)
next
  case (Ands l)
  show ?case
    using Ands.IH[of _ p i f g V v] Ands.prems
    by (fastforce simp add: Sup_rec_safety_le_iff le_Sup_rec_safety_iff eq_iff[of _ NonFutuRec]
        simp del: fun_upd_apply)
next
  case (Exists \<phi>)
  show ?case
    using Exists.IH[of p i f g V] Exists.prems
    by simp
next
  case (Agg y \<omega> b h \<phi>)
  show ?case
    using Agg.IH[of p i f g V] Agg.prems
    by simp
next
  case (Prev I \<phi>)
  show ?case
    using Prev.IH[of p "i-1" f g V] Prev.prems
    by (auto simp add: mult_le_NonFutuRec_iff split: nat.split)
next
  case (Next I \<phi>)
  show ?case
    using Next.IH[of p "i+1" f g V] Next.prems
    by (simp add: mult_le_NonFutuRec_iff safe_letpast_Unused del: fun_upd_apply)
next
  case (Since \<phi> I \<psi>)
  have "k \<le> i \<Longrightarrow> Formula.sat \<sigma> (V(p \<mapsto> f)) v k \<phi> = Formula.sat \<sigma> (V(p \<mapsto> g)) v k \<phi>" for k
    using Since.prems
    by (intro Since.IH(1)) (auto simp add: sup_eq_NonFutuRec_iff)
  moreover have "j \<le> i \<Longrightarrow> memL I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow>
      Formula.sat \<sigma> (V(p \<mapsto> f)) v j \<psi> = Formula.sat \<sigma> (V(p \<mapsto> g)) v j \<psi>" for j
    using Since.prems
    by (intro Since.IH(2)) (auto simp add: sup_eq_NonFutuRec_iff mult_le_NonFutuRec_iff split: if_splits,
        (metis diff_self_eq_0 le_neq_implies_less order.strict_trans1)+)
  ultimately show ?case
    by (auto intro!: ex_cong ball_cong simp del: fun_upd_apply)
next
  case (Until \<phi> I \<psi>)
  show ?case
    using Until.IH[of p _ f g V] Until.prems
    by (simp add: mult_le_NonFutuRec_iff safe_letpast_Unused sup_eq_Unused_iff del: fun_upd_apply)
next
  case (Trigger \<phi> I \<psi>)
  have "k \<le> i \<Longrightarrow> Formula.sat \<sigma> (V(p \<mapsto> f)) v k \<phi> = Formula.sat \<sigma> (V(p \<mapsto> g)) v k \<phi>" for k
    using Trigger.prems
    by (intro Trigger.IH(1)) (auto simp add: sup_eq_NonFutuRec_iff)
  moreover have "j \<le> i \<Longrightarrow> memL I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<Longrightarrow>
      Formula.sat \<sigma> (V(p \<mapsto> f)) v j \<psi> = Formula.sat \<sigma> (V(p \<mapsto> g)) v j \<psi>" for j
    using Trigger.prems
    by (intro Trigger.IH(2)) 
      (auto simp add: sup_eq_NonFutuRec_iff mult_le_NonFutuRec_iff split: if_splits)
  ultimately show ?case
    by (auto intro!: ex_cong ball_cong simp del: fun_upd_apply)
next
  case (Release \<phi> I \<psi>)
  show ?case
    using Release.IH[of p _ f g V] Release.prems
    by (simp add: mult_le_NonFutuRec_iff safe_letpast_Unused sup_eq_Unused_iff del: fun_upd_apply)
next
  case (MatchF I r)
  show ?case
    using MatchF.IH[of _ p _ f g V] MatchF.prems
    apply (simp add: mult_le_NonFutuRec_iff Sup_eq_Unused_iff del: fun_upd_apply)
    apply (intro ex_cong conj_cong[OF refl] match_cong_strong)
    by (metis image_eqD insertCI not_contains_pred_sat safe_letpast_Unused singletonD singleton_insert_inj_eq')
next
  case (MatchP I r)
  show ?case
    using MatchP.IH[of _ p _ f g V v] MatchP.prems
    apply (simp add: Sup_rec_safety_le_iff le_Sup_rec_safety_iff eq_iff[of _ NonFutuRec] del: fun_upd_apply)
    apply (intro ex_cong conj_cong[OF refl] match_cong_strong)
    subgoal for j k \<phi>
      apply (drule meta_spec2[of _ \<phi> k])
      apply (drule (1) meta_mp)
      apply (drule meta_mp)
       apply (metis atLeastLessThan_iff discrete less_le_trans not_less)
      apply (erule meta_mp)
      by simp
    done
qed simp_all

lemma V_subst_letpast:
  "safe_letpast p \<phi> \<le> PastRec \<Longrightarrow>
  (\<And>v j. j < i \<Longrightarrow> f v j = g v j) \<Longrightarrow>
  Formula.sat \<sigma> (V(p \<mapsto> f)) v i \<phi> = Formula.sat \<sigma> (V(p \<mapsto> g)) v i \<phi>"
  by (intro V_subst_letpast_gen) (auto intro: order_trans)


subsubsection \<open> Dual operators \<close>

fun remove_neg :: "'t Formula.formula \<Rightarrow> 't Formula.formula" 
  where "remove_neg (\<not>\<^sub>F \<phi>) = \<phi>"
  | "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "Formula.fvi b (remove_neg \<phi>) = Formula.fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma fv_remove_neg: "fv \<phi> = fv (remove_neg \<phi>)"
  by simp

definition safe_dual where "
  safe_dual conjoined safety_pred \<phi> I \<psi> = (if mem I 0 then
    (safety_pred \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> 
        \<and> (safety_pred \<phi> 
        \<comment> \<open> \<or> is_constraint \<phi> \<close>
        \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safety_pred \<phi>' | _ \<Rightarrow> False)
        ))
    else (conjoined \<and> safety_pred \<phi> \<and> safety_pred \<psi> \<and> fv \<phi> = fv \<psi>))"

lemma safe_dual_impl:
  assumes "\<forall>x. P x \<longrightarrow> Q x"
  shows "safe_dual b P \<phi> I \<psi> \<Longrightarrow> safe_dual b Q \<phi> I \<psi>"
  using assms unfolding safe_dual_def 
  by (auto split: if_splits formula.splits)

subsubsection \<open> Termination lemmas \<close>

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_regex_cong [fundef_cong]:
  assumes "\<And>f. size f < Regex.size_regex size r \<Longrightarrow> size' f = size'' f"
  shows "Regex.size_regex size' r = Regex.size_regex size'' r"
  using assms
  by (induction r) (auto)

lemma safe_dual_size [fundef_cong]:
  assumes "\<And>f. size f \<le> size \<phi> + size \<psi> \<Longrightarrow> safety_pred f = safety_pred' f"
  shows "safe_dual b safety_pred \<phi> I \<psi> = safe_dual b safety_pred' \<phi> I \<psi>"
  using assms
  by (auto simp add: safe_dual_def split: formula.splits)

fun size' :: "'t Formula.formula \<Rightarrow> nat" 
  where "size' (r \<dagger> ts) = 0"
  | "size' (Formula.Let p \<phi> \<psi>) = size' \<psi> + size' \<phi> + 1"
  | "size' (Formula.LetPast p \<phi> \<psi>) = size' \<psi> + size' \<phi> + 1"
  | "size' (t1 =\<^sub>F t2) = 0"
  | "size' (t1 <\<^sub>F t2) = 0"
  | "size' (t1 \<le>\<^sub>F t2) = 0"
  | "size' (\<not>\<^sub>F \<phi>) = size' \<phi> + 1"
  | "size' (\<phi> \<or>\<^sub>F \<psi>) = size' \<phi> + size' \<psi> + 1"
  | "size' (\<phi> \<and>\<^sub>F \<psi>) = (case \<psi> of
      (\<phi>' \<^bold>R I \<psi>') \<Rightarrow> 2 * size' \<phi> + 2 * size' \<psi> + 1
      | _ \<Rightarrow> size' \<phi> + size' \<psi> + 1
    )"
  | "size' (\<And>\<^sub>F \<phi>s) = sum_list (map (size') \<phi>s) + 1"
  | "size' (\<exists>\<^sub>F:t. \<phi>) = size' \<phi> + 1"
  | "size' (Formula.Agg y \<omega> tys f \<phi>) = size' \<phi> + 1"
  | "size' (\<^bold>Y I \<phi>) = size' \<phi> + 1"
  | "size' (\<^bold>X I \<phi>) = size' \<phi> + 1"
  | "size' (\<phi> \<^bold>S I \<psi>) = size' \<phi> + size' \<psi> + 1"
  | "size' (\<phi> \<^bold>U I \<psi>) = size' \<phi> + size' \<psi> + 1"
  | "size' (\<phi> \<^bold>T I \<psi>) = size' \<phi> + size' \<psi> + 1"
  | "size' (\<phi> \<^bold>R I \<psi>) = 6 * size' \<phi> + 24 * size' \<psi> + 110"
  | "size' (Formula.MatchF I r) = Suc (Regex.size_regex (size') r)"
  | "size' (Formula.MatchP I r) = Suc (Regex.size_regex (size') r)"
  | "size' (formula.TP t) = 0"
  | "size' (formula.TS t) = 0"

lemma size'_Or:
  "size' \<phi> < size' (\<phi> \<and>\<^sub>F \<psi>)"
  "size' \<psi> < size' (\<phi> \<and>\<^sub>F \<psi>)"
  by (auto split: formula.splits)

lemma size'_remove_neg[termination_simp]: "size' (remove_neg \<phi>) \<le> size' \<phi>"
  by (induct \<phi>) auto

lemma size'_regex_cong [fundef_cong]:
  assumes "\<And>f. size' f < Regex.size_regex size' r \<Longrightarrow> size1 f = size2 f"
  shows "Regex.size_regex size1 r = Regex.size_regex size2 r"
  using assms
  by (induction r) (auto)

lemma sum_list_mem_leq:
  fixes f::"'a \<Rightarrow> nat"
  shows "x \<in> set l \<Longrightarrow> f x \<le> sum_list (map f l)"
  by (induction l) (auto)

lemma regex_atms_size': "x \<in> regex.atms r \<Longrightarrow> size' x < regex.size_regex size' r"
  by (induction r) (auto)

lemma safe_dual_size' [fundef_cong]:
  assumes "\<And>f. size' f \<le> size' \<phi> + size' \<psi> \<Longrightarrow> safety_pred f = safety_pred' f"
  shows "safe_dual b safety_pred \<phi> I \<psi> = safe_dual b safety_pred' \<phi> I \<psi>"
  using assms
  by (auto simp add: safe_dual_def split: formula.splits)

lemma size'_and_release: "size' (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>')) \<ge> size' (and_release_safe_bounded \<phi> \<phi>' I \<psi>') + 1"
  by (clarsimp simp add: and_release_safe_bounded_def eventually_def once_def
      release_safe_bounded_def always_safe_bounded_def Formula.TT_def Formula.FF_def
      split: formula.splits)

lemma size'_Release: "size' (\<phi> \<^bold>R I \<psi>) \<ge> size' (release_safe_0 \<phi> I \<psi>) + size' (release_safe_bounded \<phi> I \<psi>) + 1"
  by (clarsimp simp add: release_safe_0_def eventually_def once_def always_safe_0_def
      release_safe_bounded_def always_safe_bounded_def Formula.TT_def Formula.FF_def
      split: formula.splits)

lemma size'_release_aux:
  "size' (and_release_safe_bounded \<phi> \<phi>' I \<psi>') < 221 + (2 * size' \<phi> + (12 * size' \<phi>' + 48 * size' \<psi>'))"
  "(case \<phi> of \<phi>' \<^bold>R I \<psi>' \<Rightarrow> 2 * size' \<psi> + 2 * size' \<phi> + 1 | _ \<Rightarrow> size' \<psi> + size' \<phi> + 1) + size' (always_safe_0 I \<psi>) < 23 * size' \<psi> + (108 + 6 * size' \<phi>)"
  "size' (release_safe_bounded \<phi> I \<psi>) < 6 * size' \<phi> + 24 * size' \<psi> + 110"
  "size' (release_safe_0 \<phi> I \<psi>) < 6 * size' \<phi> + 24 * size' \<psi> + 110"
  unfolding and_release_safe_bounded_def release_safe_0_def release_safe_bounded_def 
    always_safe_bounded_def always_safe_0_def eventually_def once_def 
    Formula.TT_def Formula.FF_def 
  by (auto split: formula.split)


subsubsection \<open> Safe formula predicate \<close>

function (sequential) safe_formula :: "'t Formula.formula \<Rightarrow> bool" 
  where "safe_formula (t1 =\<^sub>F t2) = (Formula.is_Const t1 
      \<and> (Formula.is_Const t2 \<or> Formula.is_Var t2) \<or> Formula.is_Var t1 \<and> Formula.is_Const t2)"
  | "safe_formula (t1 <\<^sub>F t2) = False"
  | "safe_formula (t1 \<le>\<^sub>F t2) = False"
  | "safe_formula (e \<dagger> ts) = (\<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t)"
  | "safe_formula (Formula.Let p \<phi> \<psi>) = ({0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
  | "safe_formula (Formula.LetPast p \<phi> \<psi>) = (safe_letpast (p, Formula.nfv \<phi>) \<phi> \<le> PastRec \<and> {0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
  | "safe_formula (\<not>\<^sub>F \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
  | "safe_formula (\<phi> \<or>\<^sub>F \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
  | "safe_formula (\<phi> \<and>\<^sub>F \<psi>) = (safe_formula \<phi> \<and>
      (safe_assignment (fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or>
        fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> 
        \<or> (case \<psi> of 
          \<not>\<^sub>F \<psi>' \<Rightarrow> safe_formula \<psi>'
        | (\<phi>' \<^bold>T I \<psi>') \<Rightarrow> safe_dual True safe_formula \<phi>' I \<psi>'
        | (\<phi>' \<^bold>R I \<psi>') \<Rightarrow> (bounded I \<and> \<not> mem I 0 \<and>
            safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>' \<and>
            safe_formula (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
          )
        | _ \<Rightarrow> False))))"
  | "safe_formula (\<And>\<^sub>F l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
      list_all safe_formula (map remove_neg neg) \<and> \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
  | "safe_formula (\<exists>\<^sub>F:t. \<phi>) = (safe_formula \<phi> \<and> 0 \<in> fv \<phi>)"
  | "safe_formula (Formula.Agg y \<omega> tys f \<phi>) = (safe_formula \<phi> \<and> y + length tys \<notin> fv \<phi> \<and> {0..<length tys} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
  | "safe_formula (\<^bold>Y I \<phi>) = (safe_formula \<phi>)"
  | "safe_formula (\<^bold>X I \<phi>) = (safe_formula \<phi>)"
  | "safe_formula (\<phi> \<^bold>S I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
      (safe_formula \<phi> \<or> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
  | "safe_formula (\<phi> \<^bold>U I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
      (safe_formula \<phi> \<or> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
  | "safe_formula (\<phi> \<^bold>T I \<psi>) = safe_dual False safe_formula \<phi> I \<psi>"
  | "safe_formula (\<phi> \<^bold>R I \<psi>) = (mem I 0 \<and> bounded I \<and> safe_formula \<psi> 
        \<and> fv \<phi> \<subseteq> fv \<psi> \<and> safe_formula (release_safe_0 \<phi> I \<psi>))"
  | "safe_formula (Formula.MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
       (g = Lax \<and> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Strict r"
  | "safe_formula (Formula.MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
       (g = Lax \<and> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Futu Strict r"
  | "safe_formula (Formula.TP t) = (Formula.is_Var t \<or> Formula.is_Const t)"
  | "safe_formula (Formula.TS t) = (Formula.is_Var t \<or> Formula.is_Const t)"
  by pat_completeness auto

termination safe_formula
proof ((relation "measure size'"; simp split: formula.splits), 
    goal_cases R_self_bdd Ands1 Ands2 R_safe0 rgx1 rgx2 rgx3 rgx4)
  case (R_self_bdd \<phi> \<psi> \<psi>\<^sub>L I \<psi>\<^sub>R)
  then show ?case
    by (clarsimp simp add: and_release_safe_bounded_def release_safe_bounded_def 
        Formula.eventually_def Formula.once_def always_safe_bounded_def Formula.TT_def 
        split: formula.splits)
next
  case (Ands1 l \<phi>)
  then show ?case 
    by (force dest!: sum_list_mem_leq[of _ _ size'])
next
  case (Ands2 l pair safes \<phi>)
  then show ?case 
    by (auto simp add: Nat.less_Suc_eq_le dest!: sum_list_mem_leq[of _ _ size'])
      (smt (z3) order.trans size'_remove_neg)
next
  case (R_safe0 \<phi> I \<psi>)
  then show ?case 
    by (clarsimp simp add: release_safe_0_def always_safe_0_def 
        release_safe_bounded_def Formula.TT_def split: formula.splits)
qed (auto dest!: regex_atms_size')

lemma safe_abbrevs[simp]: "safe_formula Formula.TT" "safe_formula Formula.FF"
  unfolding Formula.TT_def Formula.FF_def by auto

lemma first_safe[simp]: "safe_formula Formula.first"
  by (simp add: Formula.first_def)

lemma once_safe[simp]: "safe_formula (once I \<phi>) = safe_formula \<phi>"
  by (simp add: once_def)

lemma eventually_safe[simp]: "safe_formula (eventually I \<phi>) = safe_formula \<phi>"
  by (simp add: eventually_def)

lemma safe_eventually_TT [simp]: "safe_formula (\<not>\<^sub>F Formula.eventually I Formula.TT)"
  by (simp add: eventually_def)

(* historically *)

(* [0, b] *)
lemma historically_safe_0_safe[simp]: 
  "safe_formula (historically_safe_0 I \<phi>) = safe_formula \<phi>"
  by (auto simp: historically_safe_0_def safe_assignment_def 
      split: formula.splits)

lemma historically_safe_0_fv[simp]: "fv (historically_safe_0 I \<phi>) = fv \<phi>"
  by (auto simp: historically_safe_0_def)

(* [b, \<infinity>) *)

lemma historically_safe_unbounded_safe[simp]:
  "safe_formula (historically_safe_unbounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_unbounded_fv[simp]: "fv (historically_safe_unbounded I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

(* [a, b] *)

lemma historically_safe_bounded_safe[simp]: 
  "safe_formula (historically_safe_bounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma historically_safe_bounded_fv[simp]: "fv (historically_safe_bounded I \<phi>) = fv \<phi>"
  by (auto simp add: historically_safe_bounded_def)

(* always *)

(* [0, b] *)

lemma always_safe_0_safe[simp]: "safe_formula (always_safe_0 I \<phi>) = safe_formula \<phi>"
  by (auto simp add: always_safe_0_def)

lemma always_safe_0_safe_fv[simp]: "fv (always_safe_0 I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_0_def)

(* [a, b] *)

lemma always_safe_bounded_safe[simp]: "safe_formula (always_safe_bounded I \<phi>) = safe_formula \<phi>"
  by (auto simp add: always_safe_bounded_def)

lemma always_safe_bounded_fv[simp]: "fv (always_safe_bounded I \<phi>) = fv \<phi>"
  by (auto simp add: always_safe_bounded_def)

lemma release_safe_unbounded: "safe_formula (release_safe_bounded \<phi>' I \<psi>') 
  \<Longrightarrow> safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>'"
  unfolding release_safe_bounded_def always_safe_bounded_def once_def eventually_def 
    Formula.TT_def Formula.FF_def
  by (auto simp add: safe_assignment_def)

lemma safe_release_bdd_iff: "safe_formula (release_safe_bounded \<phi>' I \<psi>') \<longleftrightarrow> 
  safe_formula \<phi>' \<and> safe_formula \<psi>' \<and> fv \<phi>' = fv \<psi>'"
  by (auto simp add: release_safe_bounded_def once_def 
      historically_safe_unbounded_def safe_dual_def
      safe_assignment_iff)

lemma safe_formula_release_bounded:
  assumes "safe_formula \<phi> \<and> safe_formula \<psi> \<and> fv \<phi> = fv \<psi>"
  shows "safe_formula (release_safe_bounded \<phi> I \<psi>)"
  using assms safe_release_bdd_iff
  by blast

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
      then have rewrite: "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (trigger_safe_0 \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      have "safe_dual False safe_formula \<alpha> I \<beta>"
        using safe True
        unfolding And Trigger
        by (auto simp add: safe_assignment_def safe_dual_def split: if_splits)
      then have "safe_formula (trigger_safe_0 \<alpha> I \<beta>)"
        using True
        unfolding safe_dual_def trigger_safe_0_def
        by (auto) (auto split: formula.splits)
      then show ?thesis
        using safe
        unfolding And rewrite
        by auto
    next
      case not_mem: False
      show ?thesis
      proof (cases "bounded I")
        case True
        then have obs: "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_bounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        show ?thesis
          using Trigger not_mem
          unfolding And obs and_trigger_safe_bounded_def trigger_safe_bounded_def 
          apply (simp add: Un_absorb Un_left_absorb Un_left_commute 
              Un_commute safe_dual_def)
          by (smt (z3) And Un_absorb Un_commute formula.simps(501) fvi.simps(17) 
              is_constraint.simps(38) safe safe_formula.simps(17) safe_formula.simps(9) 
              safe_dual_def sup.orderE no_safe_assign_trigger)
      next
        case False
        then have obs: "(rewrite_trigger (formula.And \<phi> \<psi>)) = and_trigger_safe_unbounded \<phi> \<alpha> I \<beta>"
          using not_mem
          unfolding Trigger
          by auto
        then show ?thesis
          using Trigger not_mem
          unfolding And obs and_trigger_safe_unbounded_def trigger_safe_unbounded_def
          apply (simp add: Un_absorb Un_left_absorb Un_left_commute 
              Un_commute safe_dual_def)
          by (smt (z3) And formula.simps(501) fvi.simps(17) is_constraint.simps(38) 
              safe safe_formula.simps(17) safe_formula.simps(9) safe_dual_def 
              sup.absorb_iff2 sup_assoc no_safe_assign_trigger)
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
      by (auto simp add: safe_dual_def split: if_splits) 
        (auto split: formula.splits)
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


subsubsection \<open> Regular expressions \<close>

definition safe_neg :: "'t Formula.formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> safe_formula (remove_neg \<phi>)"

abbreviation "rgx_safe_pred \<equiv> (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Lax \<and> (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "Regex.safe_regex fv rgx_safe_pred m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = \<not>\<^sub>F \<psi> \<and> safe_formula \<psi>)"
  by (cases g) 
    (auto dest!: safe_regex_safe[rotated] 
      split: Formula.formula.splits[where formula=\<phi>])

definition safe_atms :: "'t Formula.formula Regex.regex \<Rightarrow> 't Formula.formula set" 
  where "safe_atms r = (\<Union>\<phi> \<in> Regex.atms r.
     if safe_formula \<phi> then {\<phi>} else case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"

lemma safe_atms_simps[simp]:
  "safe_atms (Regex.Skip n) = {}"
  "safe_atms (Regex.Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
  "safe_atms (Regex.Plus r s) = safe_atms r \<union> safe_atms s"
  "safe_atms (Regex.Times r s) = safe_atms r \<union> safe_atms s"
  "safe_atms (Regex.Star r) = safe_atms r"
  unfolding safe_atms_def by auto

lemma regex_atms_to_atms:
  assumes "Regex.safe_regex fv rgx_safe_pred m s r"
  assumes "\<phi> \<in> regex.atms r"
  shows "\<phi> \<in> safe_atms r \<or> (\<exists>\<psi>. \<phi> = \<not>\<^sub>F \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> safe_atms r)"
proof (cases "safe_formula \<phi>")
  case True
  then show ?thesis
    using assms(2)
    unfolding safe_atms_def
    by auto
next
  case False
  then obtain \<psi> where \<psi>_props: "\<phi> = \<not>\<^sub>F \<psi>" "safe_formula \<psi>"
    using safe_regex_safe_formula[OF assms(1-2)]
    by auto
  have "(if safe_formula \<phi> then {\<phi>} else case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) = {\<psi>}"
    using False \<psi>_props(1)
    by auto
  then have "\<psi> \<in> safe_atms r"
    using assms(2)
    unfolding safe_atms_def
    by blast
  then have "\<phi> = \<not>\<^sub>F \<psi> \<and> safe_formula \<psi> \<and> \<psi> \<in> safe_atms r"
    using \<psi>_props
    by auto
  then show ?thesis
    by auto
qed

lemma finite_safe_atms[simp]: "finite (safe_atms r)"
  by (induct r) (auto split: Formula.formula.splits)


subsubsection \<open> Induction principle for safety \<close>

lemma safe_formula_induct[consumes 1, case_names Eq_Const Eq_Var1 Eq_Var2 Pred Let LetPast
    And_assign And_safe And_constraint And_Not And_Trigger And_Release
    Ands Neg Or Exists Agg
    Prev Next Since Not_Since Until Not_Until
    Trigger_0 Trigger
    Release_0 Release
    MatchP MatchF TP TS]:
  assumes "safe_formula \<phi>"
    and Eq_Const: "\<And>c d. P (\<^bold>c c =\<^sub>F \<^bold>c d)"
    and Eq_Var1: "\<And>c x. P (\<^bold>c c =\<^sub>F \<^bold>v x)"
    and Eq_Var2: "\<And>c x. P (\<^bold>v x =\<^sub>F (\<^bold>c c))"
    and Pred: "\<And>e ts. \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow> P (e \<dagger> ts)"
    and Let: "\<And>p \<phi> \<psi>. {0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Formula.Let p \<phi> \<psi>)"
    and LetPast: "\<And>p \<phi> \<psi>. safe_letpast (p, Formula.nfv \<phi>) \<phi> \<le> PastRec 
      \<Longrightarrow> {0..<Formula.nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Formula.LetPast p \<phi> \<psi>)"
    and And_assign: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F \<psi>)"
    and And_safe: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F \<psi>)"
    and And_constraint: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> 
      \<Longrightarrow> \<not> safe_formula \<psi> \<Longrightarrow> fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> is_constraint \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F \<psi>)"
    and And_Not: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) (\<not>\<^sub>F \<psi>) 
      \<Longrightarrow> \<not> safe_formula (\<not>\<^sub>F \<psi>) \<Longrightarrow> fv (\<not>\<^sub>F \<psi>) \<subseteq> fv \<phi> \<Longrightarrow> \<not> is_constraint (\<not>\<^sub>F \<psi>) 
      \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>))"
    and And_Trigger: "\<And>\<phi> \<phi>' I \<psi>'. safe_formula \<phi> \<Longrightarrow> safe_formula \<phi>' 
      \<Longrightarrow> safe_dual True safe_formula \<phi>' I \<psi>' \<Longrightarrow> fv (\<phi>' \<^bold>T I \<psi>') \<subseteq> fv \<phi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<phi>' \<Longrightarrow> P \<psi>' \<Longrightarrow> P (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>'))"
    and And_Release: "\<And>\<phi> \<phi>' I \<psi>'. safe_formula \<phi> \<Longrightarrow> safe_formula \<phi>' 
      \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> fv \<phi>' = fv \<psi>' \<Longrightarrow> bounded I \<Longrightarrow> \<not> mem I 0 
      \<Longrightarrow> fv (\<phi>' \<^bold>R I \<psi>') \<subseteq> fv \<phi>  \<Longrightarrow> P (and_release_safe_bounded \<phi> \<phi>' I \<psi>') 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<phi>' \<Longrightarrow> P \<psi>' \<Longrightarrow> P (\<phi> \<and>\<^sub>F (\<phi>' \<^bold>R I \<psi>'))"
    and Ands: "\<And>l pos neg. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula pos \<Longrightarrow> list_all safe_formula (map remove_neg neg) \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all P (map remove_neg neg) \<Longrightarrow> P (\<And>\<^sub>F l)"
    and Neg: "\<And>\<phi>. fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<not>\<^sub>F \<phi>)"
    and Or: "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<or>\<^sub>F \<psi>)"
    and Exists: "\<And>t \<phi>. safe_formula \<phi> \<Longrightarrow> 0 \<in> fv \<phi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<exists>\<^sub>F:t. \<phi>)" (* any t?*)
    and Agg: "\<And>y \<omega> tys f \<phi>. y + length tys \<notin> fv \<phi> \<Longrightarrow> {0..<length tys} \<subseteq> fv \<phi> 
      \<Longrightarrow> fv_trm f \<subseteq> fv \<phi> \<Longrightarrow> safe_formula \<phi> 
      \<Longrightarrow> (\<And>\<phi>'. size' \<phi>' \<le> size' \<phi> \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> P \<phi>') \<Longrightarrow> P (Formula.Agg y \<omega> tys f \<phi>)"
    and Prev: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<^bold>Y I \<phi>)"
    and Next: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (\<^bold>X I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<^bold>S I \<psi>)"
    and Not_Since: "\<And>\<phi> I \<psi>. fv (\<not>\<^sub>F \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> 
      \<Longrightarrow> \<not> safe_formula (\<not>\<^sub>F \<phi>) \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P ((\<not>\<^sub>F \<phi>) \<^bold>S I \<psi> )"
    and Until: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<^bold>U I \<psi>)"
    and Not_Until: "\<And>\<phi> I \<psi>. fv (\<not>\<^sub>F \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> \<not> safe_formula (\<not>\<^sub>F \<phi>) 
      \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P ((\<not>\<^sub>F \<phi>) \<^bold>U I \<psi>)"
    and Trigger_0: "\<And>\<phi> I \<psi>. mem I 0 \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> fv \<phi> \<subseteq> fv \<psi>  
      \<Longrightarrow> ((safe_formula \<phi> \<and> P \<phi>) 
        \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> P \<phi>' | _ \<Rightarrow> False))
      \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<^bold>T I \<psi>)"
    and Trigger: "\<And>\<phi> I \<psi>. False \<Longrightarrow> \<not> mem I 0 \<Longrightarrow> fv \<phi> = fv \<psi>
      \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> 
      \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<^bold>T I \<psi>)"
    and Release_0: "\<And>\<phi> I \<psi>. mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> fv \<phi> \<subseteq> fv \<psi> 
      \<Longrightarrow> P (release_safe_0 \<phi> I \<psi>) \<Longrightarrow> P (\<phi> \<^bold>R I \<psi>)"
    and Release: "\<And>\<phi> I \<psi>. False \<Longrightarrow> \<not>mem I 0 \<Longrightarrow> fv \<phi> = fv \<psi> \<Longrightarrow> safe_formula \<phi> 
      \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (\<phi> \<^bold>R I \<psi>)"
    and MatchP: "\<And>I r. Regex.safe_regex fv rgx_safe_pred Past Strict r \<Longrightarrow> \<forall>\<phi> \<in> safe_atms r. P \<phi> \<Longrightarrow> P (Formula.MatchP I r)"
    and MatchF: "\<And>I r. Regex.safe_regex fv rgx_safe_pred Futu Strict r \<Longrightarrow> \<forall>\<phi> \<in> safe_atms r. P \<phi> \<Longrightarrow> P (Formula.MatchF I r)"
    and TP: "\<And>t. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow> P (Formula.TP t)"
    and TS: "\<And>t. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow> P (Formula.TS t)"
  shows "P \<phi>"
  using assms(1) 
proof (induction "size' \<phi>" arbitrary: \<phi> rule: nat_less_induct)
  case 1
  then have IH: "size' \<psi> < size' \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<psi>" "safe_formula \<phi>" for \<psi>
    by auto
  then show ?case
  proof (cases \<phi> rule: safe_formula.cases)
    case (1 t1 t2)
    then show ?thesis 
      using Eq_Const Eq_Var1 Eq_Var2 IH 
      by (auto simp: trm.is_Const_def trm.is_Var_def)
  next
    case (9 \<phi>' \<psi>')
    from IH(2)[unfolded 9]
    consider (a) "safe_assignment (fv \<phi>') \<psi>'"
      | (b) "\<not> safe_assignment (fv \<phi>') \<psi>'" "safe_formula \<psi>'"
      | (c) "fv \<psi>' \<subseteq> fv \<phi>'" "\<not> safe_assignment (fv \<phi>') \<psi>'" "\<not> safe_formula \<psi>'" "is_constraint \<psi>'"
      | (d) \<psi>'' where "fv \<psi>' \<subseteq> fv \<phi>'" "\<not> safe_assignment (fv \<phi>') \<psi>'" "\<not> safe_formula \<psi>'"
        "\<not> is_constraint \<psi>'" "\<psi>' = \<not>\<^sub>F \<psi>''" "safe_formula \<psi>''"
            | (e) \<phi>'' I \<psi>'' where "\<psi>' = \<phi>'' \<^bold>T I \<psi>''" "safe_dual True safe_formula \<phi>'' I \<psi>''" 
          "fv \<psi>' \<subseteq> fv \<phi>'" "safe_formula \<phi>'"
      | (f) \<phi>'' I \<psi>'' where "\<psi>' = \<phi>'' \<^bold>R I \<psi>''" "\<not>mem I 0" "bounded I"
          "safe_formula (and_release_safe_bounded \<phi>' \<phi>'' I \<psi>'')" "safe_formula \<phi>'" 
          "safe_formula \<phi>''" "safe_formula \<psi>''" "fv \<phi>'' = fv \<psi>''" "fv \<psi>' \<subseteq> fv \<phi>'"
      by (cases \<psi>')
        (auto split: if_splits)
    then show ?thesis 
    proof cases
      case a
      thus ?thesis 
        using IH by (auto simp: 9 intro: And_assign split: formula.splits)
    next
      case b
      thus ?thesis 
        using IH by (auto simp: 9 intro: And_safe split: formula.splits)
    next
      case c
      thus ?thesis 
        using IH by (auto simp: 9 is_constraint_iff intro: And_constraint split: formula.splits)
    next
      case d
      thus ?thesis 
        using IH by (auto simp: 9 intro!: And_Not)
    next
      case e
      thus ?thesis 
        using IH \<open>safe_formula \<phi>'\<close>
      proof (cases "safe_formula \<phi>''")
        case False
        hence mem: "mem I 0"
          using e False
          by (auto simp add: safe_dual_def split: if_splits)
        hence safe_dual'_mem_0: "safe_dual False safe_formula \<phi>'' I \<psi>''"
          using e
          unfolding safe_dual_def
          by auto
        hence \<psi>_props:
          "\<not> safe_assignment (fv \<phi>') \<psi>'"
          "safe_formula \<psi>'"
          using e(1) safe_dual'_mem_0
          unfolding safe_assignment_def
          by auto
        thus ?thesis
          using IH \<open>safe_formula \<phi>'\<close>
          by (auto simp: 9 intro!: And_safe split: formula.splits)
      next
        case True
        have "P \<phi>'" "safe_formula \<phi>'' \<Longrightarrow> P \<phi>''" "safe_formula \<psi>'' \<Longrightarrow> P \<psi>''"
          using \<open>safe_formula \<phi>'\<close> 
          by (auto simp: 9 e(1) intro!: IH)
        thus ?thesis
          using e True no_safe_assign_trigger[of \<phi>' \<phi>'' I]
           apply (simp add: 9 safe_dual_def split: if_splits)
          subgoal by (rule And_safe; clarsimp simp: safe_dual_def)
              (rule IH; clarsimp simp: 9 safe_dual_def)
          by (rule And_Trigger; clarsimp simp: 9 safe_dual_def)
      qed
    next
      case f
      hence p: "P \<phi>'" "P \<phi>''" "P \<psi>''"
        using f
        by (auto simp: 9 intro!: IH)
      have subs: "FV (\<phi>'' \<^bold>R I \<psi>'') \<subseteq> FV \<phi>'"
        using f(9)[unfolded f(1)] .
      show ?thesis
        unfolding 9
        using IH(2)
        by (auto simp: 9 f intro!: And_Release[OF \<open>safe_formula \<phi>'\<close> f(6,7,8,3,2) subs _ p]
            IH size'_and_release size'_release_aux split: formula.splits)
    qed
  next
    case (10 l)
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
    have "pos \<noteq> []" using IH(2) posneg by (simp add: 10)
    moreover have "list_all safe_formula pos" 
      using posneg 
      by (simp add: list.pred_set)
    moreover have safe_remove_neg: "list_all safe_formula (map remove_neg neg)"
      using IH(2) posneg 
      by (auto simp: 10)
    moreover have "list_all P pos"
      using posneg IH(1)
      by (auto simp add: 10 list_all_iff le_imp_less_Suc size_list_estimation') 
        (meson le_imp_less_Suc sum_list_mem_leq)
    moreover have "list_all P (map remove_neg neg)"
      using IH(1) posneg safe_remove_neg
      by (auto simp add: 10 list_all_iff le_imp_less_Suc size_list_estimation' size_remove_neg)
        (meson le_imp_less_Suc order.trans size'_remove_neg sum_list_mem_leq)
    ultimately show ?thesis 
      using IH Ands posneg 
      by (simp add: 10)
  next
    case (15 \<phi>' I \<psi>')
    with IH show ?thesis
    proof (cases \<phi>')
      case (Ands l)
      then show ?thesis using IH Since
        by (auto simp: 15)
    qed (auto 0 3 simp: 15 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
  next
    case (16 \<phi>' I \<psi>')
    with IH show ?thesis
    proof (cases \<phi>')
      case (Ands l)
      then show ?thesis using IH Until by (auto simp: 16)
    qed (auto 0 3 simp: 16 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
  next
    case (17 \<phi>' I \<psi>')
    show ?thesis
    proof (cases "mem I 0")
      case mem0: True
      show ?thesis
      proof (cases "case \<phi>' of \<not>\<^sub>F \<gamma> \<Rightarrow> safe_formula \<gamma> | _ \<Rightarrow> False")
        case True
        then obtain \<phi>'' where "\<phi>' = \<not>\<^sub>F \<phi>''" 
          and "safe_formula \<phi>''"
          by (auto split: formula.splits)
        hence "P \<phi>''" "safe_formula \<psi>' \<Longrightarrow> P \<psi>'"
          by (auto simp: 17 intro!: IH)
        then show ?thesis 
          using mem0 17 \<open>\<phi>' = \<not>\<^sub>F \<phi>''\<close> \<open>safe_formula \<phi>\<close>
          by (auto simp add: safe_dual_def intro!: Trigger_0)
      next
        case False
        hence "safe_formula \<phi>' \<Longrightarrow> P \<phi>'" "safe_formula \<psi>' \<Longrightarrow> P \<psi>'"
          by (auto simp: 17 intro!: IH)
        then show ?thesis 
          using False mem0 17 \<open>safe_formula \<phi>\<close>
          by (auto simp add: safe_dual_def intro!: Trigger_0)
      qed
    next
      case False
      then show ?thesis 
        using \<open>safe_formula \<phi>\<close> IH Trigger[OF _ False]
        by (simp add: 17 safe_dual_def)
    qed
  next
    case (18 \<phi>' I \<psi>')
    then show ?thesis
    proof (cases "mem I 0")
      case mem: True
      show ?thesis 
        using 18 \<open>safe_formula \<phi>\<close>
        by (auto intro!: Release_0)
          (auto intro!: IH size'_release_aux(4))
    next
      case False
      then show ?thesis 
        using \<open>safe_formula \<phi>\<close>
        by (simp add: 18 safe_dual_def)
    qed
  next
    case (19 I r)
    have case_Neg: "\<phi> \<in> (case x of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<longleftrightarrow> x = \<not>\<^sub>F \<phi>" 
      for \<phi> :: "'t Formula.formula" and x
      by (auto split: Formula.formula.splits)
    {
      fix \<psi>
      assume atms: "\<psi> \<in> safe_atms r"
      then have "safe_formula \<psi>"
        using safe_regex_safe_formula IH(2)
        by (fastforce simp: 19 safe_atms_def)
      moreover have obs: "size' \<psi> \<le> regex.size_regex size' r"
        using atms
        by (auto simp: safe_atms_def size_regex_estimation' case_Neg)
      ultimately have "P \<psi>"
        using IH(1)
        by (auto simp: 19)
    }
    then show ?thesis
      using IH(2)
      by (auto simp: 19 intro!: MatchP)
  next
    case (20 I r)
    have case_Neg: "\<phi> \<in> (case x of \<not>\<^sub>F \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {}) \<longleftrightarrow> x = \<not>\<^sub>F \<phi>" 
      for \<phi> :: "'t Formula.formula" and x
      by (auto split: Formula.formula.splits)
    {
      fix \<psi>
      assume atms: "\<psi> \<in> safe_atms r"
      then have "safe_formula \<psi>"
        using safe_regex_safe_formula IH(2)
        by (fastforce simp: 20 safe_atms_def)
      moreover have "size' \<psi> \<le> regex.size_regex size' r"
        using atms
        by (auto simp: safe_atms_def size_regex_estimation' case_Neg)
      ultimately have "P \<psi>"
        using IH(1)
        by (auto simp: 20)
    }
    then show ?thesis
      using IH(2)
      by (auto simp: 20 intro!: MatchF)
  qed (auto simp: assms)
qed


subsection \<open>Future reach definition \<close>

qualified fun future_bounded :: "'t Formula.formula \<Rightarrow> bool" where
  "future_bounded (Formula.Pred _ _) = True"
| "future_bounded (Formula.Let p \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Formula.LetPast p \<phi> \<psi>) = (safe_letpast (p, Formula.nfv \<phi>) \<phi> \<le> PastRec \<and> future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Formula.Eq _ _) = True"
| "future_bounded (Formula.Less _ _) = True"
| "future_bounded (Formula.LessEq _ _) = True"
| "future_bounded (\<not>\<^sub>F \<phi>) = future_bounded \<phi>"
| "future_bounded (\<phi> \<or>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<and>\<^sub>F \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<And>\<^sub>F l) = list_all future_bounded l"
| "future_bounded (\<exists>\<^sub>F:t. \<phi>) = future_bounded \<phi>"
| "future_bounded (Formula.Agg y \<omega> tys f \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>Y I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<^bold>X I \<phi>) = future_bounded \<phi>"
| "future_bounded (\<phi> \<^bold>S I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (\<phi> \<^bold>U I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (Formula.Trigger \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Formula.Release \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> bounded I)"
| "future_bounded (Formula.MatchP I r) = Regex.pred_regex future_bounded r"
| "future_bounded (Formula.MatchF I r) = (Regex.pred_regex future_bounded r \<and> bounded I)"
| "future_bounded (Formula.TP _) = True"
| "future_bounded (Formula.TS _) = True"

lemma TT_future_bounded[simp]: "future_bounded Formula.TT"
  by (simp add: Formula.TT_def Formula.FF_def)

lemma first_future_bounded[simp]: "future_bounded Formula.first"
  by (simp add: Formula.first_def)

lemma once_future_bounded[simp]: "future_bounded (once I \<phi>) = future_bounded \<phi>"
  by (simp add: once_def)

lemma eventually_future_bounded[simp]: 
  "future_bounded (eventually I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (simp add: eventually_def)

lemma historically_safe_0_future_bounded[simp]: 
  "future_bounded (historically_safe_0 I \<phi>) = future_bounded \<phi>"
  by (simp add: historically_safe_0_def eventually_def)

lemma historically_safe_future_bounded[simp]:
  "future_bounded (historically_safe_unbounded I \<phi>) = future_bounded \<phi>"
  by (simp add: historically_safe_unbounded_def)

lemma historically_safe_bounded_future_bounded[simp]: 
  "future_bounded (historically_safe_bounded I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (auto simp add: historically_safe_bounded_def bounded.rep_eq int_remove_lower_bound.rep_eq)

lemma always_safe_0_future_bounded[simp]: 
  "future_bounded (always_safe_0 I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (simp add: always_safe_0_def bounded.rep_eq flip_int_double_upper.rep_eq)

lemma always_safe_bounded_future_bounded[simp]: 
  "future_bounded (always_safe_bounded I \<phi>) = (future_bounded \<phi> \<and> bounded I)"
  by (auto simp add: always_safe_bounded_def bounded.rep_eq int_remove_lower_bound.rep_eq)

lemma release_bounded_future_bounded: "future_bounded (release_safe_bounded \<phi> I \<psi>) 
  \<longleftrightarrow> (bounded I \<and> \<not>mem I 0 \<and> future_bounded \<psi> \<and> future_bounded \<phi>)"
proof (rule iffI)
  assume "future_bounded (release_safe_bounded \<phi> I \<psi>)"
  then show "bounded I \<and> \<not>mem I 0 \<and> future_bounded \<psi> \<and> future_bounded \<phi>"
    by (auto simp add: release_safe_bounded_def eventually_def bounded.rep_eq flip_int_less_lower.rep_eq)
next
  assume "bounded I \<and> \<not>mem I 0 \<and> future_bounded \<psi> \<and> future_bounded \<phi>"
  then show "future_bounded (release_safe_bounded \<phi> I \<psi>)"
    using flip_int_less_lower_props[of I "flip_int_less_lower I"] int_remove_lower_bound_bounded
  by (auto simp add: release_safe_bounded_def eventually_def)
qed

lemma release_safe_0_future_bounded[simp]:
  "future_bounded (release_safe_0 \<phi> I \<psi>) = (bounded I \<and> future_bounded \<psi> \<and> future_bounded \<phi>)"
  by (auto simp add: release_safe_0_def)

lemma future_bounded_remove_neg: "future_bounded (remove_neg \<phi>) = future_bounded \<phi>"
  by (cases \<phi>) auto


subsection \<open>Translation to n-ary conjunction\<close>

fun get_and_list :: "'t Formula.formula \<Rightarrow> 't Formula.formula list" where
  "get_and_list (\<And>\<^sub>F l) = (if l = [] then [\<And>\<^sub>F l] else l)"
| "get_and_list \<phi> = [\<phi>]"

lemma get_and_list_eventually [simp]: 
  "get_and_list (Formula.eventually I \<phi>) = [Formula.eventually I \<phi>]"
  unfolding Formula.eventually_def
  by simp

lemma get_and_list_once [simp]: 
  "get_and_list (once I \<phi>) = [once I \<phi>]"
  unfolding once_def
  by simp

lemma fv_get_and: "(\<Union>x\<in>(set (get_and_list \<phi>)). Formula.fvi b x) = Formula.fvi b \<phi>"
  by (induction \<phi> rule: get_and_list.induct) simp_all

lemma safe_remove_negI: "safe_formula \<phi> \<Longrightarrow> safe_formula (remove_neg \<phi>)"
  by (cases \<phi>) auto

lemma safe_get_and: "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) 
    (auto simp: safe_neg_def list_all_iff intro: safe_remove_negI)

lemma sat_get_and: "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> list_all (Formula.sat \<sigma> V v i) (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: list_all_iff)

lemma safe_letpast_get_and: "\<Squnion>(safe_letpast p ` set (get_and_list \<phi>)) = safe_letpast p \<phi>"
  by (induction \<phi> rule: get_and_list.induct) (simp_all flip: bot_rec_safety_def)

lemma not_contains_pred_get_and: "\<And>x.\<not> contains_pred p \<phi> \<Longrightarrow> x \<in> set (get_and_list \<phi>) 
  \<Longrightarrow> \<not> contains_pred p x"
  by (induction \<phi> rule: get_and_list.induct) (auto split: if_splits)

lemma get_and_nonempty[simp]: "get_and_list \<phi> \<noteq> []"
  by (induction \<phi>) auto

lemma future_bounded_get_and:
  "list_all future_bounded (get_and_list \<phi>) = future_bounded \<phi>"
  by (induction \<phi>) simp_all

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed simp_all

function (sequential) convert_multiway :: "'t Formula.formula \<Rightarrow> 't Formula.formula" 
  where "convert_multiway (Formula.Pred p ts) = (Formula.Pred p ts)"
  | "convert_multiway (Formula.Eq t u) = (Formula.Eq t u)"
  | "convert_multiway (Formula.Less t u) = (Formula.Less t u)"
  | "convert_multiway (Formula.LessEq t u) = (Formula.LessEq t u)"
  | "convert_multiway (Formula.Let p \<phi> \<psi>) = Formula.Let p (convert_multiway \<phi>) (convert_multiway \<psi>)"
  | "convert_multiway (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (convert_multiway \<phi>) (convert_multiway \<psi>)"
  | "convert_multiway (\<not>\<^sub>F \<phi>) = \<not>\<^sub>F (convert_multiway \<phi>)"
  | "convert_multiway (\<phi> \<or>\<^sub>F \<psi>) = (convert_multiway \<phi>) \<or>\<^sub>F (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<and>\<^sub>F \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
        (convert_multiway \<phi>) \<and>\<^sub>F \<psi>
      else if safe_formula \<psi> then
         \<And>\<^sub>F (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway \<psi>))
      else if is_constraint \<psi> then
         (convert_multiway \<phi>) \<and>\<^sub>F \<psi>
      else if (case \<psi> of (\<phi>' \<^bold>T I \<psi>') \<Rightarrow> True | _ \<Rightarrow> False) then
         (convert_multiway \<phi>) \<and>\<^sub>F (convert_multiway \<psi>)
      else if (case \<psi> of (\<phi>' \<^bold>R I \<psi>') \<Rightarrow> True | _ \<Rightarrow> False) then (
         case \<psi> of (\<phi>' \<^bold>R I \<psi>') \<Rightarrow>
           if mem I 0 then
             (convert_multiway \<phi>) \<and>\<^sub>F (convert_multiway \<psi>)
           else
             convert_multiway (and_release_safe_bounded \<phi> \<phi>' I \<psi>')
      )
      else \<And>\<^sub>F (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>)))"
  | "convert_multiway (\<And>\<^sub>F \<phi>s) = \<And>\<^sub>F (map convert_multiway \<phi>s)"
  | "convert_multiway (\<exists>\<^sub>F:t. \<phi>) = \<exists>\<^sub>F:t. (convert_multiway \<phi>)"
  | "convert_multiway (Formula.Agg y \<omega> b f \<phi>) = Formula.Agg y \<omega> b f (convert_multiway \<phi>)"
  | "convert_multiway (\<^bold>Y I \<phi>) = \<^bold>Y I (convert_multiway \<phi>)"
  | "convert_multiway (\<^bold>X I \<phi>) = \<^bold>X I (convert_multiway \<phi>)"
  | "convert_multiway (\<phi> \<^bold>S I \<psi>) = (convert_multiway \<phi>) \<^bold>S I (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<^bold>U I \<psi>) = (convert_multiway \<phi>) \<^bold>U I (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<^bold>T I \<psi>) = (convert_multiway \<phi>) \<^bold>T I (convert_multiway \<psi>)"
  | "convert_multiway (\<phi> \<^bold>R I \<psi>) = (
      if mem I 0 then
        convert_multiway (release_safe_0 \<phi> I \<psi>)
      else (
        convert_multiway (release_safe_bounded \<phi> I \<psi>)
      )
    )"
  | "convert_multiway (Formula.MatchP I r) = Formula.MatchP I (Regex.map_regex convert_multiway r)"
  | "convert_multiway (Formula.MatchF I r) = Formula.MatchF I (Regex.map_regex convert_multiway r)"
  | "convert_multiway (Formula.TP t) = Formula.TP t"
  | "convert_multiway (Formula.TS t) = Formula.TS t"
  by pat_completeness auto
termination
  using size'_and_release size'_Release size'_Or size'_release_aux
  apply (relation "measure size'")
  by (auto simp add: Nat.less_Suc_eq_le dest!: sum_list_mem_leq[of _ _ size'] regex_atms_size')

lemma convert_multiway_TT [simp]: 
  "convert_multiway Formula.TT = Formula.TT"
  by (simp add: Formula.TT_def)

lemma convert_multiway_once [simp]: 
  "convert_multiway (once I \<psi>') = once I (convert_multiway \<psi>')"
  unfolding once_def
  by simp

lemma convert_multiway_eventually [simp]: 
  "convert_multiway (Formula.eventually I \<psi>') = Formula.eventually I (convert_multiway \<psi>')"
  unfolding Formula.eventually_def
  by simp

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex convert_multiway"


subsection \<open>Slicing traces\<close>

qualified fun matches ::
  "Formula.env \<Rightarrow> 't Formula.formula \<Rightarrow> Formula.name \<times> event_data list \<Rightarrow> bool" where
  "matches v (Formula.Pred r ts) e = (fst e = r \<and> map (Formula.eval_trm v) ts = snd e)"
| "matches v (Formula.Let p \<phi> \<psi>) e =
    ((\<exists>v'. length v' = Formula.nfv \<phi> \<and> matches v' \<phi> e \<and> matches v \<psi> (p, v')) \<or>
    (fst e \<noteq> p \<or> length (snd e) \<noteq> Formula.nfv \<phi>) \<and> matches v \<psi> e)"
| "matches v (Formula.LetPast p \<phi> \<psi>) e =
    ((fst e \<noteq> p \<or> length (snd e) \<noteq> Formula.nfv \<phi>) \<and>
      (\<exists>e'. (\<lambda>e' e. matches (snd e') \<phi> e \<and> fst e' = p \<and> length (snd e') = Formula.nfv \<phi>)\<^sup>*\<^sup>* e' e \<and> matches v \<psi> e'))"
| "matches v (Formula.Eq _ _) e = False"
| "matches v (Formula.Less _ _) e = False"
| "matches v (Formula.LessEq _ _) e = False"
| "matches v (\<not>\<^sub>F \<phi>) e = matches v \<phi> e"
| "matches v (\<phi> \<or>\<^sub>F \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (\<phi> \<and>\<^sub>F \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (\<And>\<^sub>F l) e = (\<exists>\<phi>\<in>set l. matches v \<phi> e)"
| "matches v (\<exists>\<^sub>F:t. \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Formula.Agg y \<omega> tys f \<phi>) e = (\<exists>zs. length zs = length tys \<and> matches (zs @ v) \<phi> e)"
| "matches v (\<^bold>Y I \<phi>) e = matches v \<phi> e"
| "matches v (\<^bold>X I \<phi>) e = matches v \<phi> e"
| "matches v (\<phi> \<^bold>S I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (\<phi> \<^bold>U I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Formula.Trigger \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Formula.Release \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Formula.MatchP I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (Formula.MatchF I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (Formula.TP _) e = False"
| "matches v (Formula.TS _) e = False"

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v' e)
  case (Pred n ts)
  show ?case
    by (simp cong: map_cong eval_trm_fv_cong[OF Pred(1)[simplified, THEN bspec]])
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> (set l) \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  proof -
    fix \<phi> assume "\<phi> \<in> (set l)"
    then have "fv \<phi> \<subseteq> fv (\<And>\<^sub>F l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "matches v \<phi> e = matches v' \<phi> e" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b = "length tys"
  have "matches (zs @ v) \<phi> e = matches (zs @ v') \<phi> e" if "length zs = ?b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b= ?b])
  then show ?case by auto
qed (auto 9 0 simp add: nth_Cons' fv_regex_alt)

abbreviation relevant_events where "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

lemma sat_slice_strong:
  assumes "v \<in> S" "dom V = dom V'"
    "\<And>p n v i. (p, n) \<in> dom V \<Longrightarrow> (p, v) \<in> relevant_events \<phi> S \<Longrightarrow> n = length v \<Longrightarrow>
      the (V (p, n)) v i = the (V' (p, n)) v i"
  shows "relevant_events \<phi> S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E \<Longrightarrow>
    Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  using assms
proof (induction \<phi> arbitrary: V V' v S i)
  case (Pred r ts)
  let ?rn = "(r, length ts)"
  show ?case proof (cases "V ?rn")
    case None
    then have "V' ?rn = None" using \<open>dom V = dom V'\<close> by auto
    with None Pred(1,2) show ?thesis by (auto simp: domIff dest!: subsetD)
  next
    case (Some a)
    moreover obtain a' where "V' ?rn = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "the (V ?rn) (map (Formula.eval_trm v) ts) i = the (V' ?rn) (map (Formula.eval_trm v) ts) i"
      using Some Pred(2,4) by fastforce
    ultimately show ?thesis by simp
  qed
next
  case (Let p \<phi> \<psi>)
  from Let.prems show ?case unfolding sat.simps
  proof (intro Let(2)[of S], goal_cases relevant v dom V)
    case (V p' n v' i)
    then show ?case
    proof (cases "(p', n) = (p, Formula.nfv \<phi>)")
      case True
      with V show ?thesis
        unfolding fun_upd_apply eqTrueI[OF True] if_True option.sel mem_Collect_eq
      proof (intro conj_cong refl Let(1)[where
        S="{v'. (p, v') \<in> relevant_events \<psi> S \<and> length v' = Formula.nfv \<phi>}" and V=V],
        goal_cases relevant' v' dom' V')
        case relevant'
        then show ?case
          by (elim subset_trans[rotated]) auto
      next
        case v'
        with True show ?case by simp
      next
        case (V' p' v' i)
        then show ?case
          by (intro V(4)) auto
      qed auto
    next
      case False
      from V(3,5,6,7) show ?thesis
        unfolding fun_upd_apply eq_False[THEN iffD2, OF False] if_False
        using False by (intro V(4)) (auto simp add: dom_def)
    qed
  qed (auto simp: dom_def)
next
  case (LetPast p \<phi> \<psi>)
  show ?case unfolding sat.simps Let_def
  proof (intro LetPast.IH(2)[of "S"], goal_cases relevant v dom V)
    case (V p' n v' i')
    show ?case
    proof (cases "(p', n) = (p, Formula.nfv \<phi>)")
      case True
      let ?pn = "(p, Formula.nfv \<phi>)"
      let ?R = "(\<lambda>e' e. matches (snd e') \<phi> e \<and> fst e' = p \<and> length (snd e') = Formula.nfv \<phi>)\<^sup>*\<^sup>*"
      have inter_matches_imp_R: "?R (p, v') (p, w) \<Longrightarrow> matches w \<phi> (p'', u) \<Longrightarrow> length w = Formula.nfv \<phi> \<Longrightarrow>
        ?R (p, v') (p'', u)" for w p'' u
        by (auto intro: rtranclp.rtrancl_into_rtrancl)

      have "letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j =
          letpast_sat (\<lambda>X u k. Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (V'(?pn \<mapsto> X)) u k \<phi>) w j"
        if "?R (p, v') (p, w)" "length w = Formula.nfv \<phi>" "j \<le> i'" for w j
        using that
      proof (induct "\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>" w j rule: letpast_sat.induct)
        case (1 w j)
        show ?case
        proof (subst (1 2) letpast_sat.simps,
            rule LetPast.IH(1)[where S="{w. ?R (p, v') (p, w) \<and> length w = Formula.nfv \<phi>}"],
            goal_cases relevant R dom eq)
          case relevant
          have "relevant_events \<phi> {w. ?R (p, v') (p, w) \<and> length w = Formula.nfv \<phi>} - {e. (fst e, length (snd e)) \<in> insert ?pn (dom V)}
          \<subseteq> relevant_events (Formula.LetPast p \<phi> \<psi>) S - {e. (fst e, length (snd e)) \<in> dom V}"
            using V(2) True
            by (auto dest!: inter_matches_imp_R)
          also have "insert ?pn (dom V) = dom (V(?pn \<mapsto> \<lambda>w j'. j' < j \<and> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w j'))"
            by simp
          finally show ?case
            using LetPast.prems(1) by (rule subset_trans)
        next
          case R
          with 1 show ?case by simp
        next
          case dom
          then show ?case
            using LetPast.prems(3) by (auto simp add: dom_def)
        next
          case (eq p'' n' w' j')
          show ?case proof (cases "(p'', n') = ?pn")
            case True
            moreover have "letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>) w' j' =
            letpast_sat (\<lambda>X u k. Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (V'(?pn \<mapsto> X)) u k \<phi>) w' j'"
              if "j' < j"
              using that eq "1" True
              by (auto split: if_splits dest: inter_matches_imp_R)
            ultimately show ?thesis
              by (simp cong: conj_cong)
          next
            case False
            then show ?thesis
              using eq V(2) LetPast.prems(4)[of p'' n' w' j'] True
              by (fastforce simp add: dom_def dest: inter_matches_imp_R)
          qed
        qed
      qed
      then show ?thesis
        using V(3) True by auto
    next
      case False
      then show ?thesis
        using V LetPast.prems(4)[of p' n v' i']
        by (fastforce simp: dom_def)
    qed
  qed (use LetPast.prems in \<open>auto simp: dom_def\<close>)
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
  obtain "relevant_events (\<And>\<^sub>F l) S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E" "v \<in> S"
    using Ands.prems(1) Ands.prems(2) by blast
  then have "{e. S \<inter> {v. matches v (\<And>\<^sub>F l) e} \<noteq> {}} - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E" by simp
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    have "relevant_events \<phi> S = {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}" by simp
    have "{e. S \<inter> {v. matches v \<phi> e} \<noteq> {}} \<subseteq> {e. S \<inter> {v. matches v (\<And>\<^sub>F l) e} \<noteq> {}}" (is "?A \<subseteq> ?B")
    proof (rule subsetI)
      fix e assume "e \<in> ?A"
      then have "S \<inter> {v. matches v \<phi> e} \<noteq> {}" by blast
      moreover have "S \<inter> {v. matches v (\<And>\<^sub>F l) e} \<noteq> {}"
      proof -
        obtain v where "v \<in> S" "matches v \<phi> e" using calculation by blast
        then show ?thesis using \<open>\<phi> \<in> set l\<close> by auto
      qed
      then show "e \<in> ?B" by blast
    qed
    then have "relevant_events \<phi> S - {e. (fst e, length (snd e)) \<in> dom V} \<subseteq> E"
      using Ands.prems(1) by auto
    then show "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
      using Ands.prems(2,3) \<open>\<phi> \<in> set l\<close>
      by (intro Ands.IH[of \<phi> S V v V' i] Ands.prems(4)) auto
  qed
  show ?case using \<open>\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> Formula.sat \<sigma> V v i \<phi> = Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>\<close> sat_Ands by blast
next
  case (Exists t \<phi>)
  have "Formula.sat \<sigma> V (z # v) i \<phi> = Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (z # v) i \<phi>" for z
    using Exists.prems(1-3) by (intro Exists.IH[where S="{z # v | v. v \<in> S}"] Exists.prems(4)) auto
  then show ?case by simp
next
  case (Agg y \<omega> tys f \<phi>)
  have "Formula.sat \<sigma> V (zs @ v) i \<phi> = Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (zs @ v) i \<phi>" if "length zs = length tys" for zs
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
  from MatchP.prems(1-3) have "Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchP(1)[of _ S V v] MatchP.prems(4)) auto
  then show ?case
    by auto
next
  case (MatchF I r)
  from MatchF.prems(1-3) have "Regex.match (Formula.sat \<sigma> V v) r = Regex.match (Formula.sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchF(1)[of _ S V v] MatchF.prems(4)) auto
  then show ?case
    by auto
qed simp_all

end (*context*)

locale traces_downward_closed =
  fixes traces :: "Formula.trace set"
  assumes closed: "\<sigma> \<in> traces \<Longrightarrow> (\<And>i. \<Gamma> \<sigma>' i \<subseteq> \<Gamma> \<sigma> i) \<Longrightarrow> \<sigma>' \<in> traces"
begin

lemma map_\<Gamma>_subset_traces: "\<sigma> \<in> traces \<Longrightarrow> (\<And>D. f D \<subseteq> D) \<Longrightarrow> map_\<Gamma> f \<sigma> \<in> traces"
  by (simp add: closed)

sublocale formula_slicer: sliceable_fo_spec "Formula.nfv \<phi>" "Formula.fv \<phi>" traces
  "relevant_events \<phi>" "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" for \<phi>
  by unfold_locales
    (auto simp add: fvi_less_nfv sat_fv_cong closed iff: sat_slice_strong)

end

unbundle MFODL_no_notation \<comment> \<open> disable notation \<close>


(*<*)
end
(*>*)