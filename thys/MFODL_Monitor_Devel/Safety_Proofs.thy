(*<*)
theory Safety_Proofs
  imports Progress
begin
(*>*)

unbundle MFODL_notation \<comment> \<open> enable notation \<close>


subsection \<open> convert multiway and fv \<close>

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (\<And>\<^sub>F l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (\<And>\<^sub>F l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma fv_convert_multiway_TT[simp]: "Formula.fvi b (convert_multiway Formula.TT) = {}"
  unfolding Formula.TT_def Formula.FF_def
  by auto

lemma fv_convert_multiway: "Formula.fvi b (convert_multiway \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: convert_multiway.induct)
next
  case (9 \<phi> \<psi>)
  note IH_safe_assign = 9(1)
  note IH_not_safe_assign = 9(2-6)
  note IH_psi_eq_release = 9(7,8,9)
  note IH_not_anything = 9(10,11)
  have "(case \<psi> of \<phi>' \<^bold>T I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (\<exists>\<phi>' I \<psi>'. \<psi> = \<phi>' \<^bold>T I \<psi>')"
    "(case \<psi> of \<phi>' \<^bold>R I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (\<exists>\<phi>' I \<psi>'. \<psi> = \<phi>' \<^bold>R I \<psi>')"
    by (simp split: formula.splits)+
  thus "Formula.fvi b (convert_multiway (\<phi> \<and>\<^sub>F \<psi>)) = Formula.fvi b (\<phi> \<and>\<^sub>F \<psi>)"
    apply (simp only: Formula.fvi.simps convert_multiway.simps split: if_splits)
  proof ((intro conjI impI allI iffI; clarsimp simp add: is_constraint_iff 
        safe_assignment_iff fv_get_and sup.commute), goal_cases)
    case (1 \<phi>' I \<psi>')
    then show ?case 
      using IH_not_safe_assign
      by (clarsimp simp add: safe_assignment_iff)
  next
    case (2 \<phi>' I \<psi>')
    then show ?case 
      using IH_psi_eq_release[of \<phi>' I \<psi>' b]
      by (clarsimp simp add: safe_assignment_iff)
  next
    case (3 \<phi>' I \<psi>')
    then show ?case 
      using IH_not_safe_assign
      by (clarsimp simp add: safe_assignment_iff)
  next
    case (4 \<phi>' I \<psi>')
    then show ?case 
      using IH_not_safe_assign
      by (clarsimp simp add: safe_assignment_iff)
  next
    case (5 t1 t2)
    then show ?case 
      using IH_safe_assign
      by (clarsimp simp add: safe_assignment_iff sup.commute)
  next
    case (6 t1 t2)
    then show ?case 
      using IH_not_safe_assign
      by (clarsimp simp add: safe_assignment_iff)
  next
    case (7 t1 t2)
    then show ?case 
      using IH_safe_assign
      by (clarsimp simp add: safe_assignment_iff sup.commute)
  next
    case (8 t1 t2)
    then show ?case
      using IH_not_safe_assign[of b]
      by (auto simp add: safe_assignment_iff)
  next
    case 9
    then show ?case 
      using IH_not_safe_assign
      by (clarsimp simp add: safe_assignment_iff)
  next
    case 10
    then show ?case 
      using IH_not_anything
      by (clarsimp simp add: is_constraint_iff safe_assignment_iff)
  qed
qed (simp_all add: fv_regex_alt regex.set_map)

lemma nfv_convert_multiway: "Formula.nfv (convert_multiway \<phi>) = Formula.nfv \<phi>"
  unfolding Formula.nfv_def by (auto simp: fv_convert_multiway)


subsection \<open> convert multiway and safety \<close>

lemma pred_cmultiway_conjD: "contains_pred p (convert_multiway (\<phi> \<and>\<^sub>F \<psi>)) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway \<psi>)
  \<Longrightarrow> contains_pred p (convert_multiway \<phi>)"
 apply (cases \<psi>; clarsimp simp: safe_assignment_iff split: if_splits)
  using not_contains_pred_get_and apply blast+
  apply (clarsimp simp: is_constraint_iff; elim disjE; clarsimp)
  using not_contains_pred_get_and apply blast+
  subgoal for \<phi>' I \<psi>'
    apply (clarsimp simp: and_release_safe_bounded_def split: if_splits)
    using not_contains_pred_get_and apply blast
    using not_contains_pred_get_and apply blast
    apply (clarsimp simp: release_safe_bounded_def)
    using not_contains_pred_get_and by blast
  using not_contains_pred_get_and[of p "convert_multiway \<phi>"] by blast+

lemma no_pred_cmultiway_always_safe_0I: "\<not> contains_pred p (convert_multiway \<psi>) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway (always_safe_0 I \<psi>))"
  by (auto simp: always_safe_0_def simp del: convert_multiway.simps(9,10) 
      dest!: pred_cmultiway_conjD)

lemma no_pred_cmultiway_release_safe_0I: "\<not> contains_pred p (convert_multiway \<phi>) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway \<psi>) 
  \<Longrightarrow> \<not> contains_pred p (convert_multiway (release_safe_0 \<phi> I \<psi>))"
  by (auto simp: release_safe_0_def simp del: convert_multiway.simps(9,10) 
      intro!: no_pred_cmultiway_always_safe_0I
      dest!: pred_cmultiway_conjD)

lemma convert_multiway_remove_neg: "safe_formula (remove_neg \<phi>) 
  \<Longrightarrow> convert_multiway (remove_neg \<phi>) = remove_neg (convert_multiway \<phi>)"
  by (cases \<phi>) (auto simp: and_release_safe_bounded_def release_safe_0_def 
      elim: case_NegE split: formula.splits)

lemma contains_pred_convert_multiway_always_safe_bounded [simp]: 
  "contains_pred p (convert_multiway (always_safe_bounded I \<psi>')) = contains_pred p (convert_multiway \<psi>')"
  unfolding always_safe_bounded_def
  by (auto simp: is_constraint_iff)

lemma no_pred_cmultiway_release_safe_boundedI: "\<not> contains_pred p (convert_multiway \<phi>) 
    \<Longrightarrow> \<not> contains_pred p (convert_multiway \<psi>) 
    \<Longrightarrow> \<not> contains_pred p (convert_multiway (release_safe_bounded \<phi> I \<psi>))"
  unfolding always_safe_0_def
  by (auto simp: release_safe_bounded_def simp del: convert_multiway.simps(9,10) 
      dest!: pred_cmultiway_conjD)

lemma contains_pred_convert_multiway: "\<not> contains_pred p \<phi> \<Longrightarrow> \<not> contains_pred p (convert_multiway \<phi>)"
proof (induction p \<phi> rule: contains_pred.induct)
  case(9 p \<phi> \<psi>)
  have "(case \<psi> of \<phi>' \<^bold>R I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (\<exists>\<phi>' I \<psi>'. \<psi> = \<phi>' \<^bold>R I \<psi>')"
    and "(case \<psi> of \<phi>' \<^bold>T I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (\<exists>\<phi>' I \<psi>'. \<psi> = \<phi>' \<^bold>T I \<psi>')"
    by (auto split: formula.splits)
  then show ?case
    apply (simp only: convert_multiway.simps split: if_splits)
    apply (intro conjI impI allI iffI; clarsimp simp add: is_constraint_iff 
        safe_assignment_iff fv_get_and sup.commute)
    using 9 apply (simp_all add: not_contains_pred_get_and split: if_splits)
        apply (metis convert_multiway.simps(18) memR_zero not_contains_pred_get_and)
       prefer 4 subgoal by (auto simp add: not_contains_pred_get_and)
       prefer 3 subgoal by (auto simp add: not_contains_pred_get_and)
     prefer 2 subgoal by (auto simp add: not_contains_pred_get_and)
    unfolding and_release_safe_bounded_def 
    apply (simp only: convert_multiway.simps(8) contains_pred.simps)
    apply (erule disjE)
    by (drule pred_cmultiway_conjD; simp)+
next
  case(18 p \<phi> I \<psi>)
  have "(case \<psi> of \<phi>' \<^bold>R I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (\<exists>\<phi>' I \<psi>'. \<psi> = \<phi>' \<^bold>R I \<psi>')"
    and "(case \<psi> of \<phi>' \<^bold>T I \<psi>' \<Rightarrow> True | _ \<Rightarrow> False) \<Longrightarrow> (\<exists>\<phi>' I \<psi>'. \<psi> = \<phi>' \<^bold>T I \<psi>')"
    by (auto split: formula.splits)
  then show ?case 
    using 18
    apply (simp only: convert_multiway.simps split: if_splits)
    apply (intro conjI impI allI iffI; clarsimp)
    using no_pred_cmultiway_release_safe_0I apply blast
    using no_pred_cmultiway_release_safe_boundedI by blast
next
  case(19 p I r)
  then show ?case by (auto simp add: regex.set_map)
next
  case(20 p I r)
  then show ?case by (auto simp add: regex.set_map)
qed (auto simp: nfv_convert_multiway)

lemma sf_letpast_cmultiway_subst1:
  "safe_letpast p (convert_multiway (\<phi> \<and>\<^sub>F \<not>\<^sub>F Formula.eventually I Formula.TT))
  = safe_letpast p (convert_multiway \<phi>) \<squnion> Unused"
  by (simp add: safe_letpast_get_and sup_commute)

lemma sf_letpast_cmultiway_subst2:
  "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi> 
  \<Longrightarrow> safe_letpast p (convert_multiway (\<phi> \<and>\<^sub>F release_safe_bounded \<phi>' I \<psi>')) 
  = (safe_letpast p \<phi>) \<squnion> safe_letpast p (convert_multiway (release_safe_bounded \<phi>' I \<psi>'))"
  by (auto simp: is_constraint_iff safe_assignment_iff
      Sup_rec_safety_union image_Un safe_letpast_get_and sup_commute) 
    (clarsimp simp: release_safe_bounded_def)

lemma sf_letpast_cmultiway_conj: "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi>
 \<Longrightarrow> safe_letpast p (convert_multiway \<psi>) = safe_letpast p \<psi>
  \<Longrightarrow> safe_letpast p (convert_multiway (\<phi> \<and>\<^sub>F \<psi>)) = safe_letpast p (\<phi> \<and>\<^sub>F \<psi>)"
  by (auto simp add: image_Un Sup_rec_safety_union safe_letpast_get_and sup_commute
        sf_letpast_cmultiway_subst1 split: formula.splits) 
      (simp add: and_release_safe_bounded_def bot_rec_safety_def[symmetric] 
        sf_letpast_cmultiway_subst1 sf_letpast_cmultiway_subst2 
        del: convert_multiway.simps(9))

lemma sf_letpast_cmultiway_subst3: "safe_letpast p (convert_multiway (always_safe_0 I \<psi>)) 
  = AnyRec * (safe_letpast p (convert_multiway \<psi>))"
  by (simp add: always_safe_0_def safe_assignment_iff safe_letpast_get_and)
    (rule_tac y="safe_letpast p (convert_multiway \<psi>)" in rec_safety.exhaust; clarsimp)

lemma sf_letpast_cmultiway_subst4:
  "safe_letpast p (convert_multiway (\<psi> \<and>\<^sub>F (\<^bold>X I Formula.TT))) 
  = safe_letpast p (convert_multiway \<psi>)"
  by (clarsimp simp: safe_assignment_iff Sup_rec_safety_union image_Un safe_letpast_get_and)

lemma sf_letpast_cmultiway_subst5:
  "safe_letpast p (convert_multiway (always_safe_bounded I \<psi>))
  = AnyRec * (safe_letpast p (convert_multiway \<psi>))"
  by (simp add: always_safe_bounded_def safe_assignment_iff is_constraint_iff)
    (rule_tac y="safe_letpast p (convert_multiway \<psi>)" in rec_safety.exhaust; force)

lemma sf_letpast_cmultiway_subst6:
  "safe_letpast p (convert_multiway (and_release_safe_bounded (Formula.eventually J Formula.TT) \<phi>' I \<psi>')) =
    Unused \<squnion> safe_letpast p (convert_multiway (release_safe_bounded \<phi>' I \<psi>'))"
  by (clarsimp simp: and_release_safe_bounded_def sup_commute
          Sup_rec_safety_union image_Un safe_letpast_get_and split: if_splits) 
        (clarsimp simp: release_safe_bounded_def)

lemma sf_letpast_cmultiway_subst7:
  "safe_letpast p (convert_multiway ((Formula.eventually I Formula.TT) \<and>\<^sub>F \<gamma>)) 
  = Unused \<squnion> (safe_letpast p (convert_multiway \<gamma>))"
    by (auto simp: safe_assignment_iff is_constraint_iff case_release_iff case_trigger_iff
        Sup_rec_safety_union image_Un safe_letpast_get_and sup_commute
        sf_letpast_cmultiway_subst6)

lemma safe_letpast_convert_multiway: "safe_letpast p (convert_multiway \<phi>) = safe_letpast p \<phi>"
proof (induction p \<phi> rule: safe_letpast.induct)
  case (5 p e \<phi> \<psi>)
  then show?case 
    by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case (6 p e \<phi> \<psi>)
  then show?case 
    by (auto simp add: contains_pred_convert_multiway nfv_convert_multiway)
next
  case(9 p \<phi> \<psi>)
  then show ?case
    by (intro sf_letpast_cmultiway_conj)
next
  case (18 p \<phi> I \<psi>)
  hence "memL I 0 \<Longrightarrow> safe_letpast p (convert_multiway (release_safe_0 \<phi> I \<psi>)) 
    = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
    by (clarsimp simp: release_safe_0_def always_safe_0_def mult_sup_distrib mult_assoc[symmetric]
        sf_letpast_cmultiway_subst4 sf_letpast_cmultiway_subst7 sf_letpast_cmultiway_conj 
        simp del: convert_multiway.simps(9))
      (metis sup_commute sup_left_idem)
  moreover have "\<not> memL I 0 \<Longrightarrow> safe_letpast p (convert_multiway (release_safe_bounded \<phi> I \<psi>)) 
    = AnyRec * (safe_letpast p \<phi> \<squnion> safe_letpast p \<psi>)"
    using 18 by (clarsimp simp: release_safe_bounded_def mult_sup_distrib mult_assoc[symmetric]
         sf_letpast_cmultiway_subst5 sf_letpast_cmultiway_subst7 sf_letpast_cmultiway_conj 
         bot_rec_safety_def[symmetric] simp del: convert_multiway.simps(9))
      (simp add: sup.commute)
  ultimately show ?case
    by simp
next
  case(19 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
next
  case(20 p I r)
  then show ?case
    by (simp add: regex.set_map image_image cong: image_cong)
qed (auto simp add: image_image)

lemma safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway fv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
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
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  show ?case proof -
    let ?l = "\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>"
    note \<open>safe_formula ?c\<phi>\<close>
    then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
    moreover have "safe_neg (\<not>\<^sub>F ?c\<psi>)"
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
        using \<open>fv (\<not>\<^sub>F \<psi>) \<subseteq> fv \<phi>\<close>
        by (simp add: fv_convert_multiway)
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
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = \<phi>' \<^bold>T I \<psi>'"
  define f where "f = \<phi> \<and>\<^sub>F t"
  have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not> is_constraint t"
    by (auto simp add: t_def)

  have "\<exists>f \<in> set (get_and_list (convert_multiway \<phi>)). safe_formula f"
  proof -
    {
      assume assm: "\<forall>f \<in> set (get_and_list (convert_multiway \<phi>)). \<not> safe_formula f"
      then have "False"
      proof (cases "case (convert_multiway \<phi>) of (\<And>\<^sub>F l) \<Rightarrow> True | _ \<Rightarrow> False")
        case True
        then obtain l where "convert_multiway \<phi> = \<And>\<^sub>F l"
          by (auto split: formula.splits)
        then show ?thesis
          using assm And_Trigger(5)
          by (auto simp: list_all_iff split: if_splits)
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

  have \<phi>_fvs: "\<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>)))))) 
    \<subseteq> \<Union>(set (map fv (fst (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
    using And_Trigger
    by (cases "(convert_multiway \<phi>)") (auto)

  show ?case
  proof (cases "safe_formula t")
    define l where "l = get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t)"
    define pos where "pos = fst (partition safe_formula l)"
    define neg where "neg = snd (partition safe_formula l)"

    case True
    then have convert_f: "convert_multiway f = \<And>\<^sub>F l"
      unfolding f_def l_def
      using t_not_safe_assign
      by auto

    have "safe_formula (convert_multiway t)"
      using And_Trigger True
      unfolding t_def
      by (auto split: if_splits simp add: safe_dual_def fv_convert_multiway)
    then have neg_fv: "\<Union>(set (map fv neg)) 
      = \<Union>(set (map fv (snd (partition safe_formula (get_and_list (convert_multiway \<phi>))))))"
      unfolding neg_def l_def t_def
      by auto

    have mem:
      "mem I 0"
      "safe_formula \<psi>'"
      "fv \<phi>' \<subseteq> fv \<psi>'"
      "safe_formula \<phi>'"
      using True And_Trigger
      unfolding t_def
      by (auto split: if_splits simp add: safe_dual_def)
    have case_neg_to_fol: "(case \<gamma> of \<not>\<^sub>F x \<Rightarrow> safe_formula x | _ \<Rightarrow> safe_formula \<gamma>) \<longleftrightarrow> 
      (\<not> ((\<exists>x. \<gamma> = \<not>\<^sub>F x \<and> safe_formula x) \<longleftrightarrow> (\<forall>x. \<gamma> \<noteq> \<not>\<^sub>F x \<and> safe_formula \<gamma>)))"
      for \<gamma>:: "'a Formula.formula"
      by (cases \<gamma>, auto simp: trm.is_Var_def trm.is_Const_def simp del: safe_formula.simps)

    have "filter safe_formula pos \<noteq> []"
      using filter_pos
      unfolding pos_def l_def
      by auto
    moreover have "list_all (\<lambda>\<phi>. (case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> safe_formula \<phi>)) neg"
      using And_Trigger mem
      unfolding l_def neg_def t_def
      apply (cases "convert_multiway \<phi>")
      apply (auto simp add: safe_dual_def fv_convert_multiway
          list_all_iff)
      subgoal for \<phi>s \<gamma>
        by (erule_tac x=\<gamma> in allE; cases \<gamma>; clarsimp simp del: safe_formula.simps)
      done
    moreover have "\<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos))"
      using \<phi>_fvs neg_fv
      unfolding l_def pos_def
      by (auto simp add: fv_convert_multiway)
    ultimately have "safe_formula (\<And>\<^sub>F l)"
      unfolding pos_def neg_def
      by (auto simp: case_neg_to_fol list_all_iff split: if_splits)
    then show ?thesis
      using convert_f
      unfolding f_def t_def
      by auto
  next

    case False
    then have convert_f: "convert_multiway f 
      = (convert_multiway \<phi>) \<and>\<^sub>F ((convert_multiway \<phi>') \<^bold>T I (convert_multiway \<psi>'))"
      using t_not_safe_assign t_not_constraint
      unfolding f_def t_def convert_multiway.simps
      by auto

    then show ?thesis
      using And_Trigger
      unfolding f_def t_def
      by (auto simp add: safe_assignment_iff
          fv_convert_multiway safe_dual_def split: if_splits)
  qed
next
  case (Ands l)
  then show ?case
    using convert_multiway_remove_neg fv_convert_multiway
    apply (auto simp: list.pred_set filter_map filter_empty_conv subset_eq)
     apply (smt (verit, del_insts) convert_multiway_remove_neg)(*metis fvi_remove_neg*)
    by (smt (verit, del_insts) convert_multiway_remove_neg fv_convert_multiway fvi_remove_neg)
next
  case (Neg \<phi>)
  with Neg show ?case 
    by (simp add: fv_convert_multiway)
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  moreover {
    assume "safe_formula \<phi> \<and> safe_formula (convert_multiway \<phi>)"
    then have ?case 
      using assms 
      by (auto simp add: fv_convert_multiway safe_dual_def safe_assignment_iff)
  }
  moreover {
    assume assm: "is_constraint \<phi>"
    then have "is_constraint (convert_multiway \<phi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    moreover have "FV (convert_multiway \<phi>) \<subseteq> FV (convert_multiway \<psi>)"
      using assm assms(2-3)
    proof (cases \<phi>)
      case (Neg \<phi>')
      then show ?thesis using assms(2-3) assm by (cases \<phi>') (auto simp add: fv_convert_multiway)
    qed (auto simp add: fv_convert_multiway)

    ultimately have ?case
      using assms case_NegE
      by (auto simp add: fv_convert_multiway safe_dual_def
          \<open>FV (convert_multiway \<phi>) \<subseteq> FV (convert_multiway \<psi>)\<close>)
        fastforce
  }
  moreover {
    assume "(case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' \<and> safe_formula (convert_multiway \<phi>') | _ \<Rightarrow> False)"
    then obtain \<phi>' where \<phi>_def: "\<phi> = \<not>\<^sub>F \<phi>'" "safe_formula \<phi>'" "safe_formula (convert_multiway \<phi>')"
      by (auto split: formula.splits)
    then have ?case
      using assms
      by (auto simp add: fv_convert_multiway safe_dual_def)
  }
  ultimately show ?case by blast
next
  case (MatchP I r)
  then show ?case
    by (auto 0 3 simp: safe_atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest:  split: if_splits)
next
  case (MatchF I r)
  then show ?case
    by (auto 0 3 simp: safe_atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: split: if_splits)
qed (auto simp add: fv_convert_multiway nfv_convert_multiway 
    safe_assignment_iff is_constraint_iff
    safe_dual_def case_Neg_iff)


subsection \<open> convert multiway and future bounded \<close>

lemma future_bounded_multiway_Ands: "Safety.future_bounded (convert_multiway \<phi>) = Safety.future_bounded \<phi> 
  \<Longrightarrow> Safety.future_bounded (\<And>\<^sub>F (get_and_list (convert_multiway \<phi>))) = Safety.future_bounded \<phi>"
  by (cases "case (convert_multiway \<phi>) of \<And>\<^sub>F l \<Rightarrow> True | _ \<Rightarrow> False") 
    (auto split: formula.splits)

lemma future_bounded_convert_multiway: 
  "safe_formula \<phi> \<Longrightarrow> Safety.future_bounded (convert_multiway \<phi>) = Safety.future_bounded \<phi>"
proof (induction \<phi> rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case by (auto simp: safe_letpast_convert_multiway nfv_convert_multiway)
next
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  have "Safety.future_bounded ?a = (Safety.future_bounded ?c\<phi> \<and> Safety.future_bounded ?c\<psi>)"
    using And_safe by simp
  moreover have "Safety.future_bounded ?c\<phi> = list_all Safety.future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "Safety.future_bounded ?c\<psi> = list_all Safety.future_bounded (get_and_list ?c\<psi>)"
    using \<open>safe_formula \<psi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "Safety.future_bounded ?b = list_all Safety.future_bounded (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    unfolding b_def by simp
  ultimately show ?case by simp
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = \<phi>' \<^bold>T I \<psi>'"
  define f where "f = \<phi> \<and>\<^sub>F t"
  have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not> is_constraint t"
    by (auto simp add: t_def)

  then show ?case proof (cases "safe_formula t")
    define l where "l = (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway t))"
    case True
    then have f_convert: "convert_multiway f = \<And>\<^sub>F l"
      using t_not_safe_assign
      unfolding l_def f_def
      by auto
    have t_multiway: "Safety.future_bounded (convert_multiway t) = Safety.future_bounded t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
    have "list_all Safety.future_bounded l = (Safety.future_bounded \<phi> \<and> Safety.future_bounded (\<phi>' \<^bold>T I \<psi>'))"
      using future_bounded_multiway_Ands[OF t_multiway] future_bounded_multiway_Ands[OF And_Trigger(5)]
      unfolding l_def t_def
      by auto
    then show ?thesis
      using f_convert
      unfolding f_def t_def
      by auto
  next
    case False
    then have convert_f: "convert_multiway f 
      = (convert_multiway \<phi>) \<and>\<^sub>F ((convert_multiway \<phi>') \<^bold>T I (convert_multiway \<psi>'))"
      using t_not_safe_assign t_not_constraint
      unfolding f_def t_def convert_multiway.simps
      by auto
    then show ?thesis
      using And_Trigger
      unfolding f_def t_def
      by (auto simp add: fv_convert_multiway safe_dual_def split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  then show ?case 
    by (auto simp add: and_release_safe_bounded_def 
        release_bounded_future_bounded safe_assignment_iff)
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  have "Safety.future_bounded ?a = (Safety.future_bounded ?c\<phi> \<and> Safety.future_bounded ?c\<psi>)"
    using And_Not by simp
  moreover have "Safety.future_bounded ?c\<phi> = list_all Safety.future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "Safety.future_bounded ?b = list_all Safety.future_bounded (\<not>\<^sub>F ?c\<psi> # get_and_list ?c\<phi>)"
    unfolding b_def by (simp add: list.pred_map o_def)
  ultimately show ?case by auto
next
  case assms: (Trigger_0 \<phi> I \<psi>)
  then have "Safety.future_bounded (convert_multiway \<phi>) = Safety.future_bounded \<phi>"
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
      assume "(case \<phi> of \<not>\<^sub>F \<phi>' \<Rightarrow> safe_formula \<phi>' 
      \<and> Safety.future_bounded (convert_multiway \<phi>') = Safety.future_bounded \<phi>' | _ \<Rightarrow> False)"
      then have ?thesis by (cases \<phi>) (auto)
    }
    ultimately show ?thesis using assms by auto
  qed
  then show ?case using assms by auto
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp: safe_atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp: safe_atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
qed (auto simp: list.pred_set convert_multiway_remove_neg is_constraint_iff
    future_bounded_remove_neg case_Neg_iff safe_assignment_iff)

lemma sat_convert_multiway: 
  "safe_formula \<phi> \<Longrightarrow> Formula.sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> Formula.sat \<sigma> V v i \<phi>"
proof (induction \<phi> arbitrary: V v i rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F \<psi>"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "get_and_list (convert_multiway \<psi>)"
  let ?sat = "Formula.sat \<sigma> V v i"
  have b_def: "?b = \<And>\<^sub>F (?la @ ?lb)" using And_safe by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_safe sat_get_and by blast
  moreover have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>" using And_safe sat_get_and by blast
  ultimately show ?case using And_safe by (auto simp: list.pred_set)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = \<phi>' \<^bold>T I \<psi>'"

  have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not> is_constraint t"
    by (auto simp add: t_def)

  have get_and_list: "get_and_list (convert_multiway t) = [convert_multiway t]"
    unfolding t_def
    by auto

  show ?case
  proof (cases "safe_formula t")
    case True
    then obtain l where l_props:
      "convert_multiway (\<phi> \<and>\<^sub>F t) = \<And>\<^sub>F l"
      "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
      using t_not_safe_assign t_not_constraint get_and_list
      by simp
  
    have t_sat: "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> convert_multiway t = \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> t"
      using And_Trigger(6-7)
      unfolding t_def
      by auto
  
    have "(\<forall>\<phi>\<in>set l. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>) \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi> \<and>\<^sub>F (\<phi>' \<^bold>T I \<psi>')"
    proof (cases "case (convert_multiway \<phi>) of (\<And>\<^sub>F l) \<Rightarrow> True | _ \<Rightarrow> False")
      case True
      then obtain l' where l'_props: "convert_multiway \<phi> = \<And>\<^sub>F l'" 
        by (auto split: formula.splits)
      then have "get_and_list (convert_multiway \<phi>) = (if l' = [] then [\<And>\<^sub>F l'] else l')"
        by (simp add: l'_props)
      moreover have "(\<forall>\<phi>\<in>set l'. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>) = \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
        using And_Trigger(5) l'_props
        by auto
      ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
    next
      case False
      then have "get_and_list (convert_multiway \<phi>) = [convert_multiway \<phi>]"
        by (auto split: formula.splits)
      moreover have "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> convert_multiway \<phi> = \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
        using And_Trigger(5)
        by auto
      ultimately show ?thesis using t_sat l_props(2) unfolding t_def by auto
    qed
  
    then show ?thesis
      using l_props(1)
      unfolding t_def
      by auto
  next
    case False
    then show ?thesis
      using And_Trigger t_not_safe_assign t_not_constraint
      unfolding t_def
      by auto
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  then show ?case 
    using sat_and_release_rewrite[OF And_Release(5)] 
    by auto
next
  case (And_Not \<phi> \<psi>)
  let ?a = "\<phi> \<and>\<^sub>F (\<not>\<^sub>F \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "convert_multiway \<psi>"
  let ?sat = "Formula.sat \<sigma> V v i"
  have b_def: "?b = \<And>\<^sub>F (\<not>\<^sub>F ?lb # ?la)" using And_Not by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_Not sat_get_and by blast
  then show ?case using And_Not by (auto simp: list.pred_set)
next
  case (Agg y \<omega> tys f \<phi>)
  then show ?case
    by (simp add: Formula.nfv_def fv_convert_multiway cong: conj_cong)
next
  case (MatchP I r)
  then have "Regex.match (Formula.sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (Formula.sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: safe_atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (MatchF I r)
  then have "Regex.match (Formula.sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (Formula.sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 5 simp: safe_atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (Let p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp add: nfv_convert_multiway fun_upd_def)
next
  case (Ands l pos neg)
  have sat_remove_neg: "(\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> (remove_neg \<phi>) \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>(remove_neg \<psi>)) 
    \<longleftrightarrow> (\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi> \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<psi>)" 
    if "Formula.is_Neg \<phi> \<longleftrightarrow> Formula.is_Neg \<psi>" for V v i \<phi> \<psi>
    using that 
    by (cases \<phi>; cases \<psi>) 
      (auto simp add: Formula.is_Neg_def)
  have "formula.is_Neg (convert_multiway (\<phi>1 \<and>\<^sub>F \<phi>2)) \<longleftrightarrow> False" 
    for \<phi>1 \<phi>2 :: "'t Formula.formula"
    by (clarsimp, cases \<phi>2; clarsimp simp: and_release_safe_bounded_def split: if_splits)
  hence is_Neg_cm: "Formula.is_Neg (convert_multiway \<phi>) \<longleftrightarrow> Formula.is_Neg \<phi>" 
    for \<phi> :: "'t Formula.formula"
    by (cases \<phi>; clarsimp simp: release_safe_0_def release_safe_bounded_def eventually_def 
        simp del: convert_multiway.simps(9)) blast+
  from Ands show ?case
    by (fastforce simp: list.pred_set convert_multiway_remove_neg sat_remove_neg[OF is_Neg_cm])
next
  case (Trigger_0 \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>; auto)
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case
    using sat_release_rewrite_0 
    by auto
qed (auto cong: nat.case_cong)

subsection \<open> Finite @{term safe_formula} \<close>

lemma inj_eval: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. map (Formula.eval_trm (map the v)) ts) {v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  apply(intro inj_onI)
      apply(rule nth_equalityI)
       apply(auto simp add: wf_tuple_def)[]
      subgoal for x y i
        apply(cases "i \<in> (\<Union> (fv_trm ` set ts))")
         apply(subgoal_tac "\<^bold>v i \<in> set ts")
          apply(simp)
        apply(rotate_tac)
          apply(drule(1) bspec)
          apply(simp add: wf_tuple_def)
          apply (meson option.expand)
         apply(auto simp add: Formula.is_Var_def Formula.is_Const_def)[]
          apply(simp add: wf_tuple_def)
        by metis
      done

lemma inj_eval2: " \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t \<Longrightarrow>
    inj_on (\<lambda>v. (e, map (Formula.eval_trm (map the v)) ts)) {v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}"
  apply(intro inj_onI)
      apply(rule nth_equalityI)
       apply(auto simp add: wf_tuple_def)[]
      subgoal for x y i
        apply(cases "i \<in> (\<Union> (fv_trm ` set ts))")
         apply(subgoal_tac "\<^bold>v i \<in> set ts")
          apply(simp)
        apply(rotate_tac)
          apply(drule(1) bspec)
          apply(simp add: wf_tuple_def)
          apply (meson option.expand)
         apply(auto simp add: Formula.is_Var_def Formula.is_Const_def)[]
          apply(simp add: wf_tuple_def)
        by metis
      done

lemma finite_listset: "(\<And>A. A \<in> set xs \<Longrightarrow> finite A) \<Longrightarrow> finite (listset xs)"
  by (induct xs) (simp_all add: set_Cons_def finite_image_set2)

fun joinN :: "'a tuple list \<Rightarrow> 'a tuple option" where
"joinN [] = Some []"
|"joinN (a#b#cs) =  (case (join1 (a, b)) of None \<Rightarrow> None| Some x \<Rightarrow> joinN (x#cs))"
|"joinN (a#[]) = Some a"

lemma in_listset_conv_list_all2: "xs \<in> listset ys \<longleftrightarrow> list_all2 (\<in>) xs ys"
  by (induct ys arbitrary: xs) (auto simp: set_Cons_def list_all2_Cons2)

lemma joinN_Some_restrict:
  fixes as :: "'a tuple list"
  fixes bs :: "nat set list"
  assumes "list_all2 (wf_tuple n) bs as"
  assumes "as\<noteq>[]"
  shows "joinN (as) = Some z \<longleftrightarrow> wf_tuple n (\<Union> (set bs)) z \<and> list_all2 (\<lambda>b a. restrict b z = a) bs as"
  using assms
proof (induct "as" arbitrary: n bs z rule: joinN.induct)
  case 1
  then show ?case
    by(auto)
next
  case (2 a b cs)
  then show ?case
    apply(simp)
    apply(cases "join1 (a, b)")
     apply(simp_all)
     apply(auto simp add: list_all2_Cons2)[]
    subgoal for A B Cs
      using join1_Some_restrict[of n A a B b "(restrict (A\<union>B) z)"] apply(auto simp add: restrict_restrict intro: wf_tuple_restrict_simple)
      done
    subgoal for c
      apply(erule thin_rl)
      apply(clarsimp simp add: list_all2_Cons2)[]
      subgoal for A B Cs
      using join1_Some_restrict[of n A a B b c] 2(1)[of c n "(A\<union>B)#Cs" z] apply(auto simp add: Un_assoc restrict_restrict intro: wf_tuple_restrict_simple)
      apply(subgoal_tac "restrict (A\<union>B) z = restrict (A\<union>B) c")
       apply(simp add: restrict_idle)
      apply(simp add: list_eq_iff_nth_eq nth_restrict')
      apply(simp split: if_splits)
      by (metis nth_restrict)
    done
    done
next
  case (3 a)
  then show ?case
    apply(auto)
      apply(simp add: wf_tuple_def)
      apply (smt (verit, best) in_set_simps(2) list_all2_Cons2 list_all2_Nil2)
      apply(simp add: wf_tuple_def)
     apply (smt (z3) "3.prems" list_all2_Cons2 list_all2_Nil2 restrict_idle)
    apply(simp add: wf_tuple_def)
    apply(auto)
    by (smt (z3) in_set_simps(2) list.inject list_all2_Cons2 list_all2_Nil2 nth_equalityI nth_restrict)
qed

lemma finite_letpast:
  assumes fv: "{0..<Formula.nfv \<phi>} \<subseteq> fv \<phi>"
  assumes V: "\<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i}"
  assumes IH: "\<And>V i.
    \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
    finite {v. wf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  shows "finite {v. length v = Formula.nfv \<phi> \<and>
    letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) v i}"
proof (induction i rule: less_induct)
  case (less i)
  note fun_upd_apply[simp del]
  show ?case
    apply (rule finite_surj[where f="map the"])
     apply (rule IH[where i=i and V="(V((p, Formula.nfv \<phi>) \<mapsto>
          \<lambda>w j. j < i \<and> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) u k \<phi>) w j))"])
     apply (intro ballI)
     apply clarsimp
    subgoal for p' n k
      apply (cases "(p', n) = (p, Formula.nfv \<phi>)")
       apply (clarsimp simp add: fun_upd_apply)
       apply (cases "k < i")
        apply simp
        apply (rule less[of k])
        apply simp
       apply clarsimp
      apply (subst fun_upd_apply)
      apply (simp only: if_False)
      apply (rule V[rule_format, of "(p', n)", simplified])
      by auto
    apply (intro subsetI)
    subgoal for v
      apply (rule image_eqI[where x="map Some v"])
       apply simp
      apply (subst (asm) letpast_sat.simps)
      using fv by (auto simp: wf_tuple_def)
    done
qed

lemma safe_regex_Past_finite: "Regex.safe_regex fv rgx_safe_pred Past Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> safe_atms r \<Longrightarrow> finite {v. wf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"
  apply (induct Past Strict r arbitrary: i rule: safe_regex.induct)
      apply (auto simp flip: in_unit_table simp add: unit_table_def
        conj_disj_distribL ex_disj_distrib relcompp_apply Un_absorb2)
  subgoal for r s i
  apply (rule finite_subset[rotated])
     apply (rule finite_UN_I[where B="\<lambda>i. {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<le>i. Regex.match (test v) r j i)}"])
      apply (rule finite_atLeastAtMost[of 0 i])
     apply assumption
    apply (auto simp: Bex_def)
    apply (meson match_le)
    done
  done

lemma safe_regex_Future_finite: "Regex.safe_regex fv rgx_safe_pred Futu Strict r \<Longrightarrow>
  (\<And>i \<phi>. \<phi> \<in> safe_atms r \<Longrightarrow> finite {v. wf_tuple n (fv \<phi>) v \<and> test v i \<phi>}) \<Longrightarrow>
  finite {v. wf_tuple n (fv_regex r) v \<and> (\<exists>j\<in>{i..thr}. Regex.match (test v) r i j)}"
  apply (induct Futu Strict r arbitrary: i rule: safe_regex.induct)
      apply (auto simp flip: in_unit_table simp add: unit_table_def Bex_def
        conj_disj_distribL ex_disj_distrib relcompp_apply Un_absorb1 intro: rev_finite_subset)
  subgoal for r s i
  apply (rule finite_subset[rotated])
     apply (rule finite_UN_I[where B="\<lambda>i. {v. wf_tuple n (fv_regex s) v \<and> (\<exists>j\<ge>i. j \<le> thr \<and> Regex.match (test v) s i j)}"])
      apply (rule finite_atLeastAtMost[of i thr])
     apply assumption
    apply (auto simp: Bex_def)
    apply (meson match_le order_trans)
    done
  done

lemma Collect_singleton_tuple_eq_image: "i < n \<Longrightarrow> {v. wf_tuple n {i} v \<and> P (map the v ! i)} =
  (\<lambda>x. (replicate n None)[i := Some x]) ` Collect P"
  unfolding wf_tuple_def
  by (auto simp add: list_eq_iff_nth_eq nth_list_update intro: rev_image_eqI)
  
lemma safe_formula_finite: "safe_formula \<phi> \<Longrightarrow> Safety.future_bounded \<phi> \<Longrightarrow> n\<ge> (Formula.nfv \<phi>) \<Longrightarrow> \<forall> i. finite (\<Gamma> \<sigma> i) \<Longrightarrow>
  \<forall>pn\<in>dom V. \<forall>i. finite {v. length v = snd pn \<and> the (V pn) v i} \<Longrightarrow>
  finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
proof(induct \<phi> arbitrary: i n V rule: safe_formula_induct)
  case (Eq_Const c d)
  then show ?case
    by(simp flip: in_unit_table add: unit_table_def)
next
  case (Eq_Var1 c x)
  then have "finite (singleton_table n x c)"
    unfolding singleton_table_def by(simp)
  then show ?case using Eq_Var1
    apply(elim finite_subset[rotated])
    apply(auto intro: nth_equalityI simp add: singleton_table_def wf_tuple_def 
        tabulate_alt Formula.nfv_def Suc_le_eq)
    done
next
  case (Eq_Var2 c x)
  then have "finite (singleton_table n x c)"
    unfolding singleton_table_def by(simp)
  then show ?case
    apply(simp)
    apply(elim finite_subset[rotated])
    apply(auto intro: nth_equalityI simp add: singleton_table_def wf_tuple_def 
        tabulate_alt Formula.nfv_def Suc_le_eq)
    done
next
case (Pred e ts)
  then show ?case
    apply(simp)
    apply(cases "V (e, length ts)")
     apply(simp)
    subgoal
      apply(rule finite_vimage_IntI[of "\<Gamma> \<sigma> i" "\<lambda> v. (e, map (Formula.eval_trm (map the v)) ts)" "{v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}", THEN finite_subset[rotated]])
        apply simp
       apply(auto simp add: inj_eval2)
      done
    apply(simp)
    subgoal for a
      apply(rule finite_vimage_IntI[of "{v. length v = length ts \<and> a v i}" "\<lambda> v. map (Formula.eval_trm (map the v)) ts" "{v. wf_tuple n (\<Union> (fv_trm ` set ts)) v}", THEN finite_subset[rotated]])
        apply (drule (1) bspec[OF _ domI])
        apply(auto simp add: inj_eval)
      done
    done
next
  case (Let p \<phi> \<psi>)
  then have IH: " finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    apply(simp)
    done
  then have IH2: "\<forall>i.  finite (map the ` {v. wf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>})" using Let
    by(auto)
  then have "\<forall> i. {v. length v = Formula.nfv \<phi> \<and> Formula.sat \<sigma> V v i \<phi>} = map the ` {v. wf_tuple (Formula.nfv \<phi>) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    using Let
    apply(simp)
    by(auto simp add: wf_tuple_def intro!: image_eqI[where x="map Some _"])
   then have " finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>)) (map the v) i \<psi>}"
     using Let IH2
    by(auto)
  then show ?case using Let
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (LetPast p \<phi> \<psi>)
  show ?case
    unfolding sat.simps fvi.simps Let_def
    apply (rule LetPast.hyps(6))
    using LetPast apply auto[3]
    apply (intro ballI allI)
    subgoal for pn i
      apply (cases "pn = (p, Formula.nfv \<phi>)")
       apply (simp add: dom_def)
       apply (rule finite_letpast)
      using LetPast apply auto[2]
      apply (rule LetPast.hyps(5))
      using LetPast by auto
    done
next
  case (And_assign \<phi> \<psi>)
  then have IH: " finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    apply(simp)
    done
  consider x y where "\<psi> = \<^bold>v x =\<^sub>F (\<^bold>v y)" and  "(x \<notin> fv \<phi> \<longleftrightarrow> y \<in> fv \<phi>)"
    |x t where "\<psi> = \<^bold>v x =\<^sub>F t" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    |x t where "\<psi> = t =\<^sub>F (\<^bold>v x)" and "\<not> Formula.is_Var t" and "(x \<notin> fv \<phi> \<and> fv_trm t \<subseteq> fv \<phi>)"
    using And_assign(2)
    by(simp add: safe_assignment_def Formula.is_Var_def split: Formula.formula.splits trm.splits)
      then show ?case proof cases
        case 1
        then show ?thesis
          apply(simp)
          apply(cases "(x \<notin> fv \<phi>)")
           apply(simp add: insert_commute insert_absorb)
           apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=v!y]"])
           apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update nth_list_update_neq)
            apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            apply(simp add: wf_tuple_def)
            apply(subst nth_list_update_neq)
             apply blast
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            by (metis Suc_le_lessD option.expand nth_map)
          apply(simp add: insert_absorb)
           apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [y:=v!x]"])
           apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [y:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update nth_list_update_neq)
            apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            apply(simp add: wf_tuple_def)
            apply(subst nth_list_update_neq)
             apply blast
            using And_assign(5) apply(simp add: wf_tuple_def Formula.nfv_def)
            by (metis Suc_le_eq nth_map option.expand)
          done
      next
        case 2
        then show ?thesis
          apply(simp add: Un_absorb2)
          apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=Some (Formula.eval_trm (map the v) t)]"])
          apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update_eq nth_list_update_neq)
             apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp_all add: wf_tuple_def Formula.nfv_def)
            apply(subst eval_trm_fv_cong[of _ _ "map the v"] )
             apply (metis in_mono map_update nth_list_update_neq)
            by (metis Suc_le_eq option.collapse)
          done
      next
        case 3
        then show ?thesis
          apply(simp add: Un_absorb2)
          apply(rule finite_surj[OF IH, of _ "\<lambda> v. v [x:=Some (Formula.eval_trm (map the v) t)]"])
          apply(auto)[]
          subgoal for v
            apply(rule rev_image_eqI[of "v [x:=None]"])
             apply(auto)
              apply(simp add: wf_tuple_def)
              apply (metis nth_list_update_eq nth_list_update_neq)
             apply (smt (verit, best) map_update nth_list_update_neq sat_fv_cong)
            apply(rule sym)
            apply(subst list_update_same_conv)
            using And_assign(5) apply(simp_all add: wf_tuple_def Formula.nfv_def)
            apply(subst eval_trm_fv_cong[of _ _ "map the v"] )
             apply (metis in_mono map_update nth_list_update_neq)
            by (metis Suc_le_eq option.collapse)
          done
      qed
next
  case (And_safe \<phi> \<psi>)
  let ?A = "\<lambda>\<phi>. {v | v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (restrict (fv \<phi>) v, restrict (fv \<psi>) v)"
  let ?test = "(?A \<phi> \<times> ?A \<psi>)"
  have "finite (?A \<phi>)" and "finite (?A \<psi>)" using And_safe by auto
  then have "finite (?A \<phi> \<times> ?A \<psi>)" ..
  then have "finite (Option.these (join1 ` (?A \<phi> \<times> ?A \<psi>)))"
    by (auto simp: Option.these_def)
  moreover have "{v. wf_tuple n (fv \<phi> \<union> fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi> \<and> Formula.sat \<sigma> V (map the v) i \<psi>}
      \<subseteq> Option.these (join1 ` (?A \<phi> \<times> ?A \<psi>))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have "(restrict (fv \<phi>) v, restrict (fv \<psi>) v) \<in> ?A \<phi> \<times> ?A \<psi>"
      by (auto simp: wf_tuple_restrict_simple sat_the_restrict)
    moreover have "join1 (restrict (fv \<phi>) v, restrict (fv \<psi>) v) = Some v"
      using \<open>v \<in> ?B\<close>
      apply (subst join1_Some_restrict)
      by(auto simp: wf_tuple_restrict_simple)
    ultimately show "v \<in> ?B'"
      apply(simp)
      by (force simp: Option.these_def)
  qed
  ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (And_constraint \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  then show ?case using And_constraint
    apply(elim finite_subset[rotated])
    apply(auto)
    by (metis sup.order_iff)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  hence obs: "finite {v. wf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by simp
  thus ?case
    using And_Trigger
    by (auto simp del: fvi.simps(17)) 
      (smt (verit, best) Collect_mono_iff 
        Diff_partition Un_Diff_cancel2 
        Un_commute obs finite_subset)
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  hence obs: "finite {v. wf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>}"
    by simp
  thus ?case
    using And_Release
    by (auto simp del: fvi.simps(18)) 
      (smt (verit, best) Collect_mono_iff 
        Diff_partition Un_Diff_cancel2 
        Un_commute obs finite_subset)
next
  case (And_Not \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  then show ?case using And_Not
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb2)
next
  case (Ands l pos neg)
  let ?A = "\<lambda>\<phi>. {v | v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
  let ?p = "\<lambda>v. (map (\<lambda> \<phi>.(restrict (fv \<phi>) v)) pos)"
  let ?A_list = "listset (map (\<lambda> \<phi>. ?A \<phi>) pos)"
  have "finite (?A_list)" using Ands
    apply(intro finite_listset)
    by(auto simp add:list_all_def)
  then have "finite (Option.these (joinN ` (?A_list)))"
    by(auto simp: Option.these_def)
  moreover have "{v. wf_tuple n (\<Union> (fv ` set l)) v \<and> (\<forall>x\<in>set l. Formula.sat \<sigma> V (map the v) i x)}
      \<subseteq> (Option.these (joinN ` (?A_list)))" (is "?B \<subseteq> ?B'")
  proof
    fix v
    assume "v \<in> ?B"
    then have "?p v \<in> ?A_list"
      using Ands(1)
      by (auto simp: sat_the_restrict in_listset_conv_list_all2 list.rel_map intro!: list.rel_refl_strong wf_tuple_restrict_simple)
    moreover have "joinN (?p v) = Some v"
      using \<open>v \<in> ?B\<close> using Ands(1, 5) Ands.hyps(2)
      apply(subst joinN_Some_restrict[of n "map fv pos" "map (\<lambda>\<phi>. restrict (fv \<phi>) v) pos" v])
       apply(auto simp: wf_tuple_restrict_simple list.rel_map intro!: list.rel_refl_strong wf_tuple_restrict_simple)
      apply(subgoal_tac "\<Union> (fv ` {x \<in> set l. safe_formula x}) = \<Union> (fv ` set l)")
      by(auto)
    ultimately show "v \<in> ?B'"
      apply(simp)
      by (force simp: Option.these_def)
  qed
   ultimately show ?case
    by (auto elim!: finite_subset)
next
  case (Neg \<phi>)
  then show ?case
   by(simp flip: in_unit_table add: unit_table_def)
next
  case (Or \<phi> \<psi>)
  then have "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp)
  moreover from Or have "finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>}"
    by(simp)
  ultimately have "finite ({v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>} \<union> {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) i \<psi>})"
    by(simp)
  then show ?case using Or
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Exists t \<phi>)
 then have "finite (Formula.fvi (Suc 0) \<phi>)"
   by(simp)
  moreover from Exists have IH: "finite {v. wf_tuple (Suc n) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(simp add: Formula.nfv_def fvi_Suc_bound Suc_le_eq)
  ultimately show ?case using Exists
    apply(simp)
    apply(rule finite_surj[OF IH, of _ "tl"])
    apply(auto)
    subgoal for v z
      apply(rule image_eqI[of _ _ "(if 0 \<in> fv \<phi> then Some z else None)#v"])
       apply(auto simp add: wf_tuple_def)
      apply (metis fvi_Suc length_nth_simps(3) length_nth_simps(4) less_Suc_eq_0_disj option.discI)
      apply (metis fvi_Suc length_nth_simps(4) less_Suc_eq_0_disj)
      done
    done
next
  case (Agg y \<omega> tys f \<phi>)
  define b where [simp]: "b= length tys"
  from Agg have IH: "finite {v. wf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>}"
    by(auto 0 4 simp add: Suc_le_eq ball_Un Formula.nfv_def intro!: Agg(5)[where ?n="n+(length tys)"] dest!: fvi_plus_bound[where b=0 and c=b, simplified])
  then have IH_alt: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) i \<phi>})"
    by(auto)
  have drop_b: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}})"
    apply(rule finite_subset[of _ "{replicate n None}"])
     apply(auto simp add: wf_tuple_def list_eq_iff_nth_eq[where ?ys="replicate n None"])
    done
  have final_subset: "finite (drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"
    using drop_b IH_alt
    apply(auto)
    by (smt (z3) Collect_cong b_def drop_b)
  have sat_eq: "Formula.sat \<sigma> V (zs @ map the (x[y := None])) i \<phi> = Formula.sat \<sigma> V (zs @ map the (x)) i \<phi>" if "length zs = b" and "y<length x" for x zs
    using Agg(1, 7) that
    apply -
    apply(rule sat_fv_cong)
    apply(simp add: nth_append)
    apply(auto simp add: Formula.nfv_def Suc_le_eq)
    by (metis add.commute add_diff_inverse_nat map_update nth_list_update_neq)
  have eval_trm_eq: "Formula.eval_trm (zs @ map the (x[y := None])) f = Formula.eval_trm (zs @ map the (x)) f" if "length zs = b" and "y<length x" for x zs
using Agg(1, 7) that
    apply -
    apply(rule eval_trm_fv_cong)
    apply(simp add: nth_append)
  apply(auto simp add: Formula.nfv_def Suc_le_eq)
  by (metis Agg.hyps(3) add.commute add_diff_inverse_nat map_update nth_list_update_neq subset_iff)
  then show ?case using Agg IH
    apply(simp)
    apply(rule finite_surj[ of "{v. wf_tuple n (Formula.fvi b \<phi> \<union> Formula.fvi_trm b f) v \<and>
         ((\<forall>a x. length x = b \<longrightarrow> Formula.sat \<sigma> V (x @ map the v) i \<phi> \<longrightarrow> Formula.eval_trm (x @ map the v) f \<noteq> a) \<longrightarrow>
          fv \<phi> = {0..<b})}" _ "\<lambda> v. v [y:= (Some (eval_agg_op \<omega>
         {(x, ecard
               {zs.
                length zs = b \<and>
                Formula.sat \<sigma> V (zs @ map the v) i \<phi> \<and> Formula.eval_trm (zs @ map the v) f = x}) |
          x. \<exists>xa. Formula.sat \<sigma> V (xa @ map the v) i \<phi> \<and>
                  length xa = b \<and> Formula.eval_trm (xa @ map the v) f = x}))]"])
     defer
     apply(intro subsetI)
     apply(clarify)
    subgoal for x
      apply(frule wf_tuple_length)
    apply(rule image_eqI[where x="x[y:=None]"])
       apply(rule sym)
      apply(simp add: ac_simps sat_eq eval_trm_eq Formula.nfv_def Suc_le_eq cong: conj_cong Collect_cong)
     apply(subst list_update_same_conv)
      apply(simp add: Formula.nfv_def Suc_le_eq wf_tuple_def)
       apply(simp add: Formula.nfv_def Suc_le_eq wf_tuple_def)
       apply (metis option.exhaust_sel)
      apply(auto)
      apply(auto simp add: sat_eq eval_trm_eq wf_tuple_def nth_list_update Formula.nfv_def Suc_le_eq  fvi_trm_iff_fv_trm[where b="length _"] fvi_iff_fv[where b="length _"])
      done
    apply(rule finite_subset[of _ "(drop b`{v. wf_tuple (n+b) (fv \<phi>) v \<and> (Formula.sat \<sigma> V (map the v) i \<phi> \<or> fv \<phi> = {0..<b})})"])
     apply(intro subsetI)
    apply(clarify)
    subgoal for x
      apply(erule impCE)
       apply(simp)
       apply(elim exE conjE)
      subgoal for zs
        apply(rule image_eqI[where x="map2 (\<lambda> i z. if i \<in> fv \<phi> then Some z else None) [0..<b] zs @ x"])
         apply(simp)
        apply(intro conjI[rotated] CollectI)
        apply(subgoal_tac "Formula.sat \<sigma> V (map the (map2 (\<lambda>x y. if x \<in> fv \<phi> then Some y else None) [0..<b] zs @ x)) i \<phi>")
        apply(simp)
         apply(erule sat_fv_cong[THEN iffD1, rotated])
         apply(simp add: Formula.nfv_def nth_append)
         apply(auto simp add: wf_tuple_def nth_append Formula.nfv_def)
           apply (metis add_diff_inverse_nat fvi_iff_fv le_add1 le_add_diff_inverse2)
        apply (metis bot_nat_0.not_eq_extremum diff_is_0_eq fvi_iff_fv le_add_diff_inverse2 zero_less_diff)
        subgoal for i
          apply(subgoal_tac "i\<in>fv_trm f")
           apply(auto)[]
          by (metis bot_nat_0.not_eq_extremum diff_is_0_eq fvi_trm_iff_fv_trm le_add_diff_inverse2 zero_less_diff)
        done
      apply(subgoal_tac "wf_tuple n {} x")
      subgoal
        apply(subgoal_tac "x \<in> drop b ` {v. wf_tuple (n + b) (fv \<phi>) v \<and> fv \<phi> = {0..<b}}")
          apply blast
        apply(subgoal_tac "x\<in>{v. wf_tuple n {} v}")
        subgoal
          apply(subgoal_tac "{v. wf_tuple n {} v} \<subseteq> drop b ` {v. wf_tuple (n + b) (fv \<phi>) v}")
           apply(auto )[]
          by (auto simp: in_unit_table[symmetric] unit_table_def image_iff nth_append
    intro!: exI[of _ "replicate b (Some undefined) @ replicate n None"] wf_tuple_def[THEN iffD2])
        apply(auto)
        done
      apply(auto simp add: wf_tuple_def fvi_iff_fv[of _ "length tys"] fvi_trm_iff_fv_trm[of _ "length tys"])
      done
      using final_subset apply(auto)
      done
next
  case (Prev I \<phi>)
  then have "finite
            {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (i-1) \<phi>}"
    apply(simp)
    done
  then show ?case
    apply(simp)
    apply(cases "i")
     apply(simp)
    apply(simp)
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Next I \<phi>)
  then have "finite
     {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) (Suc i) \<phi>}"
    apply(simp)
    done
  then show ?case using Next
    apply(elim finite_subset[rotated])
    by(auto)
next
  case (Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have "finite (\<Union> j\<le>i. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  then show ?case using Since
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb1)
next
  case (Not_Since \<phi> I \<psi>)
  then have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  then have "finite (\<Union> j\<le>i. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>})"
    by(auto)
  then show ?case using Not_Since
    apply(elim finite_subset[rotated])
    by(auto simp add: Un_absorb1)
next
  case (Until \<phi> I \<psi>)
  then obtain m j where m: "\<not> memR I m" and "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  moreover from Until have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  moreover from Until have "finite (\<Union> j'\<le>j. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  ultimately show ?case using Until
    apply(elim finite_subset[rotated])
    apply(simp add: Un_absorb1)
    apply(auto)
    subgoal for v j2
      apply(cases "(\<tau> \<sigma> j2 - \<tau> \<sigma> i)\<le>m")
      subgoal
        apply(auto)
        apply(subgoal_tac "j2\<le>j")
         apply blast
        by (metis \<tau>_mono diff_le_mono le_antisym nat_le_linear)
      subgoal
        apply(subgoal_tac "\<not> memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)")
         apply blast
        apply(auto)
        by (meson memR_antimono nat_le_linear)
      done
    done
next
  case (Not_Until \<phi> I \<psi>)
  obtain m j where m: "\<not> memR I m" and "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    using \<open>Safety.future_bounded (\<not>\<^sub>F \<phi> \<^bold>U I \<psi>)\<close>
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  moreover from Not_Until have "\<forall> j. finite {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j \<psi>}"
    by(simp)
  moreover from Not_Until have "finite (\<Union> j'\<le>j. {v. wf_tuple n (fv \<psi>) v \<and> Formula.sat \<sigma> V (map the v) j' \<psi>})"
    by(auto)
  ultimately show ?case using Not_Until
    apply(elim finite_subset[rotated])
    apply(simp add: Un_absorb1)
    apply(auto)
    subgoal for v j2
      apply(cases "(\<tau> \<sigma> j2 - \<tau> \<sigma> i)\<le>m")
      subgoal
        apply(auto)
        apply(subgoal_tac "j2\<le>j")
         apply blast
        by (metis \<tau>_mono diff_le_mono le_antisym nat_le_linear)
      subgoal
        apply(subgoal_tac "\<not> memR I (\<tau> \<sigma> j2 - \<tau> \<sigma> i)")
         apply blast
        apply(auto)
        by (meson memR_antimono nat_le_linear)
      done
    done
next
  case (Trigger \<phi> I \<psi>) (* notice the False at the end *)
  let ?sats = "{v. wf_tuple n (FV (\<phi> \<^bold>T I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>T I \<psi>}"
  have "finite (unit_table n)"
    by (auto simp: unit_table_def)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Trigger.prems
    by (auto simp: Formula.nfv_def)
  have phi_prptys: "Safety.future_bounded \<phi>" "Formula.nfv \<phi> \<le> n"
    using Trigger.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. wf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" 
    and "finite {v. wf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}" 
    for j
    using Trigger.hyps(6)[OF phi_prptys Trigger.prems(3,4)]
    Trigger.hyps(7)[OF psi_prptys Trigger.prems(3,4)]
    by auto
  hence "finite ((\<Union>j\<le>i. {v. wf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}) \<union> 
    (\<Union>j\<le>i. {v. wf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}))" (is "finite ?bigU")
    by auto
  have False
    using Trigger(1) .
  thus ?case
    by blast
next
  case (Trigger_0 \<phi> I \<psi>)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Trigger_0.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. wf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" for j
    using Trigger_0.hyps(5)[OF psi_prptys Trigger_0.prems(3,4)]
    by force
  hence "finite (\<Union>j\<le>i. {v. wf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>})"
    by auto
  moreover have "{v. wf_tuple n (FV (\<phi> \<^bold>T I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>T I \<psi>}
    \<subseteq> (\<Union>j\<le>i. {v. wf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>})"
    using Trigger_0.hyps
    by (auto simp add: Un_absorb1)
  ultimately show ?case 
    by (elim finite_subset[rotated])
next
  case (Release \<phi> I \<psi>) (* notice the False at the end *)
  let ?sats = "{v. wf_tuple n (FV (\<phi> \<^bold>R I \<psi>)) v \<and> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi> \<^bold>R I \<psi>}"
  have "finite (unit_table n)"
    by (auto simp: unit_table_def)
  have psi_prptys: "Safety.future_bounded \<psi>" "Formula.nfv \<psi> \<le> n"
    using Release.prems
    by (auto simp: Formula.nfv_def)
  have phi_prptys: "Safety.future_bounded \<phi>" "Formula.nfv \<phi> \<le> n"
    using Release.prems
    by (auto simp: Formula.nfv_def)
  hence "finite {v. wf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}" 
    and "finite {v. wf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}" 
    for j
    using Release.hyps(6)[OF phi_prptys Release.prems(3,4)]
    Release.hyps(7)[OF psi_prptys Release.prems(3,4)]
    by auto
  hence "finite ((\<Union>j\<le>i. {v. wf_tuple n (FV \<psi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<psi>}) \<union> 
    (\<Union>j\<le>i. {v. wf_tuple n (FV \<phi>) v \<and> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile>\<^sub>M \<phi>}))" (is "finite ?bigU")
    by auto
  have False
    using Release(1) .
  thus ?case
    by blast
next
  case (Release_0 \<phi> I \<psi>)
  thus ?case
    using release_fvi
    by (auto simp: Formula.nfv_def sat_release_rewrite_0[OF Release_0(1,2), symmetric])
next
  case (MatchP I r)
  from MatchP(1,3-) have IH: "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> safe_atms r" for k \<phi> using that
    apply (intro MatchP(2)[rule_format, OF that])
       apply (auto simp: regex.pred_set safe_atms_def Regex.nfv_regex_def fv_regex_alt Formula.nfv_def)
     apply (auto split: Formula.formula.splits)
    done
  from MatchP(3-) show ?case
    by (intro finite_subset[OF _ safe_regex_Past_finite[OF MatchP(1) IH, of i]]) auto
next
  case (MatchF I r)
  then obtain m j where m: "\<not> memR I m" "m = (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    apply(auto)
    apply(atomize_elim)
    apply(simp add: bounded_memR)
    by (metis (no_types, opaque_lifting) add_diff_cancel_right' diff_le_mono ex_le_\<tau> memR_antimono)
  from MatchF(1,3-) have IH: "finite {v. wf_tuple n (fv \<phi>) v \<and> Formula.sat \<sigma> V (map the v) k \<phi>}"
    if "\<phi> \<in> safe_atms r" for k \<phi> using that
    apply (intro MatchF(2)[rule_format, OF that])
       apply (auto simp: regex.pred_set safe_atms_def Regex.nfv_regex_def fv_regex_alt Formula.nfv_def)
     apply (auto split: Formula.formula.splits)
    done
  from MatchF(3-) m show ?case
    apply (intro finite_subset[OF _ safe_regex_Future_finite[OF MatchF(1) IH, of i j]])
     apply clarsimp
     apply (erule bexI[where A = "{i .. j}"])
     apply auto
    apply (meson \<tau>_mono diff_le_mono le_cases memR_antimono)
    done
next
  case (TP t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def 
    by (auto simp add: wf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
next
  case (TS t)
  then show ?case
    unfolding Formula.is_Var_def Formula.is_Const_def Formula.nfv_def
    by (auto simp add: wf_tuple_empty_iff Collect_singleton_tuple_eq_image[where P="\<lambda>x. x = _"])
qed


subsection \<open> Progress and safety \<close>

lemma safe_progress_get_and: "safe_formula \<phi> \<Longrightarrow>
  Min ((\<lambda>\<phi>. progress \<sigma> P \<phi> j) ` set (get_and_list \<phi>)) = progress \<sigma> P \<phi> j"
  by (induction \<phi> rule: get_and_list.induct) auto

lemma progress_convert_multiway: "safe_formula \<phi> 
  \<Longrightarrow> progress \<sigma> P (convert_multiway \<phi>) j = progress \<sigma> P \<phi> j"
proof (induction \<phi> arbitrary: P rule: safe_formula_induct)
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp add: letpast_progress_def Let_def nfv_convert_multiway simp del: fun_upd_apply)
next
  case (And_safe \<phi> \<psi>)
  let ?c = "convert_multiway (Formula.And \<phi> \<psi>)"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have c_eq: "?c = Formula.Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  from \<open>safe_formula \<phi>\<close> have "safe_formula ?c\<phi>" by (rule safe_convert_multiway)
  moreover from \<open>safe_formula \<psi>\<close> have "safe_formula ?c\<psi>" by (rule safe_convert_multiway)
  ultimately show ?case
    unfolding c_eq
    using And_safe.IH
    by (auto simp: Min.union safe_progress_get_and)
next
  case (And_Not \<phi> \<psi>)
  let ?c = "convert_multiway (Formula.And \<phi> (Formula.Neg \<psi>))"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have c_eq: "?c = Formula.Ands (Formula.Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  from \<open>safe_formula \<phi>\<close> have "safe_formula ?c\<phi>" by (rule safe_convert_multiway)
  moreover from \<open>safe_formula \<psi>\<close> have "safe_formula ?c\<psi>" by (rule safe_convert_multiway)
  ultimately show ?case
    unfolding c_eq
    using And_Not.IH
    by (auto simp: Min.union safe_progress_get_and)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  define t where "t = Formula.Trigger \<phi>' I \<psi>'"
  define f where "f = Formula.And \<phi> t"
  have t_not_safe_assign: "\<not>safe_assignment (fv \<phi>) t"
    unfolding safe_assignment_def
    by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have t_prog: "progress \<sigma> P (convert_multiway t) j = progress \<sigma> P t j"
    using And_Trigger(6-7)[of P]
    unfolding t_def
    by auto

  show ?case
  proof (cases "safe_formula t")
  case True
    then obtain l where l_props:
      "convert_multiway f = Formula.Ands l"
      "set l = set (get_and_list (convert_multiway \<phi>)) \<union> {convert_multiway t}"
      using t_not_safe_assign t_not_constraint And_Trigger(3)
      unfolding f_def t_def
      by (auto simp add: safe_dual_def split: if_splits)
  
    moreover have "progress \<sigma> P f j = Min (set (map (\<lambda>\<phi>. progress \<sigma> P \<phi> j) l))"
      using l_props(2) And_Trigger(5)[of P] t_prog safe_convert_multiway[OF And_Trigger(1)]
      unfolding f_def
    by (cases "convert_multiway \<phi>") (auto split: if_splits)
  
    ultimately show ?thesis 
      unfolding f_def t_def
      by auto
  next
    case False
    then have convert_f: "convert_multiway f 
      = Formula.And (convert_multiway \<phi>) (Formula.Trigger (convert_multiway \<phi>') I (convert_multiway \<psi>'))"
      using t_not_safe_assign t_not_constraint
      unfolding f_def t_def convert_multiway.simps
      by auto
    then show ?thesis
      using And_Trigger
      unfolding f_def t_def
      by (auto simp add: fv_convert_multiway safe_dual_def split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  then show ?case using progress_and_release_rewrite_bounded by auto
next
  case (Ands l)
  then show ?case
    unfolding progress.simps convert_multiway.simps
    by (force simp: list.pred_set convert_multiway_remove_neg intro!: Sup.SUP_cong)
next
  case (Trigger_0 \<phi> I \<psi>)
  show ?case
  proof (cases "safe_assignment (fv \<psi>) \<phi> \<or> is_constraint \<phi> 
  \<or> (case \<phi> of 
    formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' 
        \<and> (\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j) 
    | _ \<Rightarrow> False)")
    case True
    moreover {
      assume "safe_assignment (fv \<psi>) \<phi>"
      then have ?thesis
        unfolding safe_assignment_def
        using Trigger_0
        by (cases \<phi>) (auto)
    }
    moreover {
      assume assm: "is_constraint \<phi>"
      then have ?thesis
        using Trigger_0
      proof (cases \<phi>)
        case (Neg \<phi>')
        then show ?thesis using Trigger_0 assm by (cases \<phi>') (auto)
      qed (auto)
    }
    moreover {
      assume "(case \<phi> of 
        formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' 
          \<and> (\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j) 
        | _ \<Rightarrow> False)"
      then obtain \<phi>' where \<phi>'_props:
        "\<phi> = formula.Neg \<phi>'"
        "safe_formula \<phi>'"
        "\<forall>x. progress \<sigma> x (convert_multiway \<phi>') j = progress \<sigma> x \<phi>' j"
        by (auto split: formula.splits)
      then have ?thesis using Trigger_0 by auto
    }
    ultimately show ?thesis by blast
  next
    case False
    then show ?thesis using Trigger_0 by (cases \<phi>) (auto)
  qed
next
  case (Release_0 \<phi> I \<psi>)
  then show ?case using progress_release_rewrite_0 by auto
next
  case (MatchP I r)
  from MatchP show ?case
    unfolding progress.simps regex.map convert_multiway.simps regex.set_map image_image
    by (intro if_cong arg_cong[of _ _ Min] image_cong)
      (auto 0 4 simp: safe_atms_def elim!: disjE_Not2 dest: safe_regex_safe_formula)
next
  case (MatchF I r)
  from MatchF show ?case
    unfolding progress.simps regex.map convert_multiway.simps regex.set_map image_image
    by (intro if_cong arg_cong[of _ _ Min] arg_cong[of _ _ Inf] arg_cong[of _ _ "(\<le>) _"]
      image_cong Collect_cong all_cong1 imp_cong conj_cong image_cong)
      (auto 0 4 simp: safe_atms_def elim!: disjE_Not2 dest: safe_regex_safe_formula)
qed (auto simp add: nfv_convert_multiway)

unbundle MFODL_no_notation \<comment> \<open> enable notation \<close>

(*<*)
end
(*>*)