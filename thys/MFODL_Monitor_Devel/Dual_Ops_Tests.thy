
theory Dual_Ops_Tests
imports Monitor_Impl

begin


section \<open> Safety and monitor evaluation \<close>

lift_definition clopen_ivlR :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" is
  "\<lambda>l. \<lambda>r. (if enat l < r then (\<lambda>i. l \<le> i, \<lambda>i. enat i < r, r \<noteq> \<infinity>) else (\<lambda>_. True, \<lambda>_. True, False))"
  using enat_iless 
  apply (auto simp: upclosed_def downclosed_def not_le order_subst2)
  apply (meson enat_ord_simps(1) order_le_less_trans)
  using not_less_iff_gr_or_eq by blast

lift_definition clopen_ivlL :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" is
  "\<lambda>l. \<lambda>r. (if enat l < r then (\<lambda>i. l < i, \<lambda>i. enat i \<le> r, r \<noteq> \<infinity>) else (\<lambda>_. True, \<lambda>_. True, False))"
  using enat_iless Suc_ile_eq
  by (auto simp: upclosed_def downclosed_def not_le order_subst2)

notation clopen_ivlR ("\<^bold>[_,_\<^bold>\<rangle>")
    and clopen_ivlL ("\<^bold>\<langle>_,_\<^bold>]")

lemma memL_interval_simp[simp]: "memL \<^bold>[a,b\<^bold>] x \<longleftrightarrow> (a \<le> b \<and> a \<le> x) \<or> (a > b)"
  by transfer auto

lemma memL_clopen_ivlR_simp[simp]: "memL \<^bold>[a,b\<^bold>\<rangle> x \<longleftrightarrow> (a < b \<and> a \<le> x) \<or> (a \<ge> b)"
  by transfer auto

lemma memL_clopen_ivlL_simp[simp]: "memL \<^bold>\<langle>a,b\<^bold>] x \<longleftrightarrow> (a < b \<and> a < x) \<or> (a \<ge> b)"
  by transfer auto

lemma memR_interval_simp[simp]: "memR \<^bold>[a,b\<^bold>] x \<longleftrightarrow> (x \<le> b \<and> a \<le> b) \<or> (a > b)"
  by transfer auto

lemma memR_clopen_ivlR_simp[simp]: "memR \<^bold>[a,b\<^bold>\<rangle> x \<longleftrightarrow> (a < b \<and> x < b) \<or> (a \<ge> b)"
  by transfer auto

lemma memR_clopen_ivlL_simp[simp]: "memR \<^bold>\<langle>a,b\<^bold>] x \<longleftrightarrow> (a < b \<and> x \<le> b) \<or> (a \<ge> b)"
  by transfer auto

lemma mem_interval_simp[simp]: "mem \<^bold>[a,b\<^bold>] x \<longleftrightarrow> (a \<le> b \<and> a \<le> x \<and> x \<le> b) \<or> (a > b)"
  by transfer auto

lemma mem_clopen_ivlR_simp[simp]: "mem \<^bold>[a,b\<^bold>\<rangle> x \<longleftrightarrow> (a \<le> x \<and> x < b) \<or> (a \<ge> b)"
  by transfer auto

lemma mem_clopen_ivlL_simp[simp]: "mem \<^bold>\<langle>a,b\<^bold>] x \<longleftrightarrow> (a < x \<and> x \<le> b) \<or> (a \<ge> b)"
  by transfer auto


subsection \<open> MFOTL encodings and extra notation \<close>

fun list_to_neqs :: "nat list \<Rightarrow> ty Formula.formula" 
  where "list_to_neqs [] = \<not>\<^sub>F (\<^bold>c (EInt 0) =\<^sub>F \<^bold>c (EInt 0))"
  | "list_to_neqs [x] = \<not>\<^sub>F (\<^bold>v x =\<^sub>F \<^bold>v x)"
  | "list_to_neqs (x # xs) = \<not>\<^sub>F (\<^bold>v x =\<^sub>F \<^bold>v x) \<and>\<^sub>F list_to_neqs xs "

term Set.insert
value "list_to_neqs (let X = {0,2,6,2,7,10} in filter (\<lambda>x. x \<in> X) [0 ..< Suc (Max (Set.insert 0 (X)))])"

lemma fv_list_to_neqs [simp]: "FV (list_to_neqs xs) = set xs"
  by (induct xs rule: list_to_neqs.induct) auto

lemma non_sat_the_list_to_neqs: "\<not> \<langle>\<sigma>, v, V, i\<rangle> \<Turnstile>\<^sub>M list_to_neqs xs"
  by (induct xs rule: list_to_neqs.induct, simp_all)

lemma safe_formula_list_to_neqs: 
  "safe_formula (list_to_neqs [])"
  by simp

lemma unsafe_formula_list_to_neqs: 
  "xs \<noteq> [] \<Longrightarrow> \<not> safe_formula (list_to_neqs xs)"
  by (induct xs rule: list_to_neqs.induct) 
    simp_all

context
begin

abbreviation Bot_vars :: "ty Formula.formula \<Rightarrow> ty Formula.formula"
  where "Bot_vars \<alpha> \<equiv> list_to_neqs (filter (\<lambda>x. x \<in> FV \<alpha>) [0 ..< Suc (Max (Set.insert 0 (FV \<alpha>)))])"

abbreviation "Top_vars \<alpha> \<equiv> \<not>\<^sub>F (Bot_vars \<alpha>)"

abbreviation "Implies \<alpha> \<beta> \<equiv> \<not>\<^sub>F \<alpha> \<or>\<^sub>F \<beta>"

abbreviation "EventuallyV I \<alpha> \<equiv> (Top_vars \<alpha>) \<^bold>U I \<alpha>"

abbreviation "Globally_RelV I \<alpha> \<equiv> (Bot_vars \<alpha>) \<^bold>R I \<alpha>"

abbreviation "OnceV I \<alpha> \<equiv> (Top_vars \<alpha>) \<^bold>S I \<alpha>"

abbreviation "Historically_TrigV I \<alpha> \<equiv> (Bot_vars \<alpha>) \<^bold>T I \<alpha>"

end

bundle MFOTL_extra_no_notation
begin 

no_notation Top_vars ("\<top>\<^sub>v")
     and Bot_vars ("\<bottom>\<^sub>v")
     and EventuallyV ("\<^bold>F _ _" [55, 65] 65)
     and Globally_RelV ("\<^bold>G _ _" [55, 65] 65)
     and OnceV ("\<^bold>P _ _" [55, 65] 65)
     and Historically_TrigV ("\<^bold>H _ _" [55, 65] 65)
     and Implies (infixr "\<longrightarrow>\<^sub>F" 72)

end

bundle MFOTL_extra_notation
begin

notation Top_vars ("\<top>\<^sub>v")
     and Bot_vars ("\<bottom>\<^sub>v")
     and EventuallyV ("\<^bold>F _ _" [55, 65] 65)
     and Globally_RelV ("\<^bold>G _ _" [55, 65] 65)
     and OnceV ("\<^bold>P _ _" [55, 65] 65)
     and Historically_TrigV ("\<^bold>H _ _" [55, 65] 65)
     and Implies (infixr "\<longrightarrow>\<^sub>F" 72)

end


subsection \<open> Example evaluations \<close>

unbundle MFOTL_extra_notation \<comment> \<open> enable notation \<close>

subsubsection \<open> quality assessment - operations on globally \<close>

lemma "\<langle>\<sigma>, v, V, i\<rangle> \<Turnstile>\<^sub>M \<not>\<^sub>F (\<^bold>F \<^bold>[2,3\<^bold>] \<not>\<^sub>F ((STR ''P'') \<dagger> [\<^bold>v 0])) 
  \<longleftrightarrow> \<langle>\<sigma>, v, V, i\<rangle> \<Turnstile>\<^sub>M (\<^bold>G \<^bold>[2,3\<^bold>] ((STR ''P'') \<dagger> [\<^bold>v 0]))"
  by (auto simp add: enat_0)

term "(
  (\<^bold>F \<^bold>[0,2\<^bold>\<rangle> \<not>\<^sub>F (STR ''P1'' \<dagger> [\<^bold>v 0]))
  \<and>\<^sub>F (\<^bold>F \<^bold>[0,2\<^bold>\<rangle> \<not>\<^sub>F (STR ''P2'' \<dagger> [\<^bold>v 0]))
  \<and>\<^sub>F (\<^bold>F \<^bold>[0,2\<^bold>\<rangle> \<not>\<^sub>F (STR ''P3'' \<dagger> [\<^bold>v 0]))
 )"

definition "prod_line_best \<equiv> (
  (\<^bold>G \<^bold>[0,2\<^bold>\<rangle> (STR ''P1'' \<dagger> [\<^bold>v 0]))
  \<and>\<^sub>F (\<^bold>G \<^bold>[2,4\<^bold>\<rangle> (STR ''P2'' \<dagger> [\<^bold>v 0]))
  \<and>\<^sub>F (\<^bold>G \<^bold>[4,6\<^bold>\<rangle> (STR ''P3'' \<dagger> [\<^bold>v 0]))
  )"

definition "prod_line_good \<equiv> (
  (\<^bold>G \<^bold>[0,2\<^bold>\<rangle> (STR ''P1'' \<dagger> [\<^bold>v 0]))
  \<or>\<^sub>F (\<^bold>G \<^bold>[2,4\<^bold>\<rangle> (STR ''P2'' \<dagger> [\<^bold>v 0]))
  \<or>\<^sub>F (\<^bold>G \<^bold>[4,6\<^bold>\<rangle> (STR ''P3'' \<dagger> [\<^bold>v 0]))
  )"

lemma "\<not> safe_formula prod_line_best"
  "\<not> safe_formula prod_line_good"
  by (auto simp add: prod_line_best_def prod_line_good_def 
      enat_0 safe_assignment_def Let_def pairw_union_eq safe_dual_def)


definition "mbest \<equiv> minit prod_line_best"
definition "mbest0 \<equiv> mstep ({(STR ''P1'',[0]), (STR ''P1'',[1]), (STR ''P1'',[2]), (STR ''P1'',[3])}, 0) mbest"
definition "mbest1 \<equiv> mstep ({(STR ''P1'',[0]), (STR ''P1'',[1]), (STR ''P1'',[2]), (STR ''P1'',[3])}, 1) (snd mbest0)"
definition "mbest2 \<equiv> mstep ({(STR ''P2'',[0]), (STR ''P2'',[1]), (STR ''P1'',[2]), (STR ''P2'',[3])}, 2) (snd mbest1)"
definition "mbest3 \<equiv> mstep ({(STR ''P2'',[0]), (STR ''P2'',[1]), (STR ''P2'',[2]), (STR ''P2'',[3])}, 3) (snd mbest2)"
definition "mbest4 \<equiv> mstep ({(STR ''P3'',[0]), (STR ''P2'',[1]), (STR ''P2'',[2]), (STR ''P3'',[3])}, 4) (snd mbest3)"
definition "mbest5 \<equiv> mstep ({(STR ''P3'',[0]), (STR ''P3'',[1]), (STR ''P2'',[2]), (STR ''P3'',[3])}, 5) (snd mbest4)"
definition "mbest6 \<equiv> mstep ({(STR ''P1'',[4]), (STR ''P3'',[1]), (STR ''P3'',[2]), (STR ''P1'',[5])}, 6) (snd mbest5)"
definition "mbest7 \<equiv> mstep ({(STR ''P2'',[4])}, 12) (snd mbest6)"

value "mbest"  \<comment> \<open> @{value "mbest"} \<close>
value "mbest0" \<comment> \<open> @{value "mbest0"} \<close>
value "mbest1" \<comment> \<open> @{value "mbest1"} \<close>
value "mbest2" \<comment> \<open> @{value "mbest2"} \<close>
value "mbest3" \<comment> \<open> @{value "mbest3"} \<close>
value "mbest4" \<comment> \<open> @{value "mbest4"} \<close>
value "mbest5" \<comment> \<open> @{value "mbest5"} \<close>
value "mbest6" \<comment> \<open> @{value "mbest6"} \<close>
value "mbest7" \<comment> \<open> @{value "mbest7"} \<close>


subsubsection \<open> vaccine refrigeration times - conjunction negated historically \<close>

lemma "(p \<and> \<not> q) \<longleftrightarrow> \<not> (p \<longrightarrow> q)"
  by simp

lemma "\<langle>\<sigma>,v,V,i\<rangle> \<Turnstile> (STR ''arrived'' \<dagger> [\<^bold>v 0]) \<and>\<^sub>F (\<^bold>P \<^bold>[2, 3\<^bold>] \<not>\<^sub>F (STR ''travelling'' \<dagger> [\<^bold>v 0])) 
  \<longleftrightarrow> \<langle>\<sigma>,v,V,i\<rangle> \<Turnstile> (STR ''arrived'' \<dagger> [\<^bold>v 0]) \<and>\<^sub>F \<not>\<^sub>F (\<^bold>H \<^bold>[2, 3\<^bold>] (STR ''travelling'' \<dagger> [\<^bold>v 0]))"
  by simp

definition "safe_packages \<equiv> (
  (STR ''arrived'' \<dagger> [\<^bold>v 0])
  \<and>\<^sub>F \<not>\<^sub>F (\<^bold>H \<^bold>[2, 2\<^bold>] (STR ''travelling'' \<dagger> [\<^bold>v 0]))
  )"

lemma "\<not> safe_formula safe_packages"
  by (auto simp: safe_packages_def enat_0 safe_dual_def)

definition "mpackages \<equiv> minit safe_packages"
definition "mpackages0 \<equiv> mstep ({(STR ''travelling'',[1]), (STR ''standbySTR '',[2]), (STR ''standbySTR '',[3])}, 0) mpackages"
definition "mpackages1 \<equiv> mstep ({(STR ''travelling'',[1]), (STR ''standbySTR '',[2]), (STR ''standbySTR '',[3])}, 1) (snd mpackages0)"
definition "mpackages2 \<equiv> mstep ({(STR ''travelling'',[1]), (STR ''travelling'',[2]), (STR ''standbySTR '',[3])}, 2) (snd mpackages1)"
definition "mpackages3 \<equiv> mstep ({(STR ''travelling'',[1]), (STR ''arrived'',[2]), (STR ''travelling'',[3])}, 3) (snd mpackages2)"
definition "mpackages4 \<equiv> mstep ({(STR ''arrived'',[1]), (STR ''travelling'',[5]), (STR ''arrived'',[3])}, 4) (snd mpackages3)"
definition "mpackages5 \<equiv> mstep ({(STR ''travelling'',[4]), (STR ''travelling'',[5]), (STR ''travelling'',[6])}, 5) (snd mpackages4)"
definition "mpackages6 \<equiv> mstep ({(STR ''travelling'',[4]), (STR ''travelling'',[5]), (STR ''arrived'',[6])}, 6) (snd mpackages5)"
definition "mpackages7 \<equiv> mstep ({(STR ''travelling'',[4]), (STR ''arrived'',[5]), (STR ''travelling'',[7])}, 7) (snd mpackages6)"

value mpackages  \<comment> \<open> @{value "mpackages"} \<close>
value mpackages0 \<comment> \<open> @{value "mpackages0"} \<close>
value mpackages1 \<comment> \<open> @{value "mpackages1"} \<close>
value mpackages2 \<comment> \<open> @{value "mpackages2"} \<close>
value mpackages3 \<comment> \<open> @{value "mpackages3"} \<close>
value mpackages4 \<comment> \<open> @{value "mpackages4"} \<close>
value mpackages5 \<comment> \<open> @{value "mpackages5"} \<close>
value mpackages6 \<comment> \<open> @{value "mpackages6"} \<close>
value mpackages7 \<comment> \<open> @{value "mpackages7"} \<close>

(* other possible specifications *)

term "MFOTL_Safety.safe_formula (
  (STR ''arrived'' \<dagger> [\<^bold>v 0])
  \<and>\<^sub>F (\<^bold>P \<^bold>[0, 24\<^bold>] (\<^bold>H \<^bold>[0, 3\<^bold>] (STR ''travelling'' \<dagger> [\<^bold>v 0])))
  )"


subsubsection \<open> financial crime investigation - historically with many variables \<close>

definition "suspect \<equiv> (
  (\<^bold>H \<^bold>[30, 35\<^bold>] (\<exists>\<^sub>F:TInt. STR ''failed_trans_from_paid_to'' \<dagger> [\<^bold>v 0,\<^bold>v 1,\<^bold>v 2,\<^bold>v 3]))
  \<and>\<^sub>F (STR ''approved_trans_from_paid_to'' \<dagger> [\<^bold>v 0,\<^bold>v 1,\<^bold>v 2,\<^bold>v 3])
  )"

lemma "\<not> safe_formula suspect"
  by (auto simp: suspect_def enat_0 safe_dual_def)

(* other possible specifications *)

(* term "ssfv (
  (\<^bold>H \<^bold>[30, 35\<^bold>] (\<exists>\<^sub>F:TInt. (\<^bold>P \<^bold>[0, 10\<^bold>] STR ''trans_from_paid_to'' \<dagger> [\<^bold>v 0,\<^bold>v 1,\<^bold>v 2,\<^bold>v 3])
  \<and>\<^sub>F (STR ''declined'' \<dagger> [\<^bold>v 0])))
  \<and>\<^sub>F (\<^bold>P \<^bold>[0, 10\<^bold>] STR ''trans_from_paid_to'' \<dagger> [\<^bold>v 4,\<^bold>v 1,\<^bold>v 2,\<^bold>v 3])
  \<and>\<^sub>F (STR ''approved'' \<dagger> [\<^bold>v 4])
  )" *)


subsubsection \<open> monitoring piracy - applied release \<close>

abbreviation "off_route \<equiv> STR ''off_route''"
abbreviation "no_signal \<equiv> STR ''no_signal''"
abbreviation "received \<equiv> STR ''received''"
abbreviation "pir_upd pred vals mapp \<equiv> Mapping.update (pred,1) vals mapp"
abbreviation "pir_upd0 pred vals \<equiv> pir_upd pred vals Mapping.empty"

definition pirated :: "ty Formula.formula"
  where "pirated \<equiv> (off_route \<dagger> [\<^bold>v 0]) \<^bold>R \<^bold>[0,2\<^bold>] (no_signal \<dagger> [\<^bold>v 0])"

definition "right_pir \<equiv> no_signal \<dagger> [\<^bold>v 0]"
definition "left_pir \<equiv> off_route \<dagger> [\<^bold>v 0]"
definition "notin_pir \<equiv> received \<dagger> [\<^bold>v 0]"

lemma "safe_formula pirated"
  apply (auto simp: pirated_def enat_0 release_safe_0_def)
  by transfer (clarsimp simp: pirated_def enat_0)

definition "mpiracy \<equiv> minit right_pir"
definition "mpiracy0 \<equiv> mstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) mpiracy"
definition "mpiracy1 \<equiv> mstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd mpiracy0)"
definition "mpiracy2 \<equiv> mstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd mpiracy1)"
definition "mpiracy3 \<equiv> mstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd off_route [{[Some (EInt 1)]}] (pir_upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd mpiracy2)"
definition "mpiracy4 \<equiv> mstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd off_route [{[Some (EInt 1)]}] (pir_upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd mpiracy3)"
definition "mpiracy5 \<equiv> mstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd off_route [{[Some (EInt 1)]}] (pir_upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd mpiracy4)"

definition "vmpiracy \<equiv> vminit pirated"
definition "vmpiracy0 \<equiv> vmstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) vmpiracy"
definition "vmpiracy1 \<equiv> vmstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd vmpiracy0)"
definition "vmpiracy2 \<equiv> vmstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd vmpiracy1)"
definition "vmpiracy3 \<equiv> vmstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd off_route [{[Some (EInt 1)]}] (pir_upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd vmpiracy2)"
definition "vmpiracy4 \<equiv> vmstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd off_route [{[Some (EInt 1)]}] (pir_upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd vmpiracy3)"
definition "vmpiracy5 \<equiv> vmstep (pir_upd received [{[Some (EInt 3)]}] (pir_upd off_route [{[Some (EInt 1)]}] (pir_upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd vmpiracy4)"



value mpiracy  \<comment> \<open> @{value "mpiracy"}  \<close>
value mpiracy0 \<comment> \<open> @{value "mpiracy0"} \<close>
value mpiracy1 \<comment> \<open> @{value "mpiracy1"} \<close>
value mpiracy2 \<comment> \<open> @{value "mpiracy2"} \<close>
value mpiracy3 \<comment> \<open> @{value "mpiracy3"} \<close>
value mpiracy4 \<comment> \<open> @{value "mpiracy4"} \<close>
value mpiracy5 \<comment> \<open> @{value "mpiracy5"} \<close>



value vmpiracy  \<comment> \<open> @{value "vmpiracy"}  \<close>
value vmpiracy0 \<comment> \<open> @{value "vmpiracy0"} \<close>
value vmpiracy1 \<comment> \<open> @{value "vmpiracy1"} \<close>
value vmpiracy2 \<comment> \<open> @{value "vmpiracy2"} \<close>
value vmpiracy3 \<comment> \<open> @{value "vmpiracy3"} \<close>
value vmpiracy4 \<comment> \<open> @{value "vmpiracy4"} \<close>
value vmpiracy5 \<comment> \<open> @{value "vmpiracy5"} \<close>

end


