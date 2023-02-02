
theory Dual_Ops_Tests
imports Monitor_Impl

begin


section \<open> Safety and monitor evaluation \<close>


subsection \<open> MFOTL encodings and extra notation \<close>

unbundle MFODL_notation
unbundle ivl_notation

context
begin

(* For updating with the value of a single predicate *)
abbreviation "updS pred vals mapp \<equiv> Mapping.update (pred,1) vals mapp"

abbreviation "upd0 pred vals \<equiv> updS pred vals Mapping.empty"

abbreviation Top_const :: "ty Formula.formula"
  where "Top_const \<equiv> \<^bold>c (EInt 0) =\<^sub>F \<^bold>c (EInt 0)"

abbreviation Bot_const :: "ty Formula.formula"
  where "Bot_const \<equiv> Formula.Neg Top_const"

abbreviation "Implies \<alpha> \<beta> \<equiv> \<not>\<^sub>F \<alpha> \<or>\<^sub>F \<beta>"

abbreviation "EventuallyC I \<alpha> \<equiv> Top_const \<^bold>U I \<alpha>"

abbreviation "GloballyCE I \<alpha> \<equiv> Formula.Neg (EventuallyC I (Formula.Neg \<alpha>))"

abbreviation "GloballyCR I \<alpha> \<equiv> Bot_const \<^bold>R I \<alpha>"

abbreviation "OnceC I \<alpha> \<equiv> Top_const \<^bold>S I \<alpha>"

abbreviation "HistoricallyCO I \<alpha> \<equiv> Formula.Neg (OnceC I (Formula.Neg \<alpha>))"

abbreviation "HistoricallyCT I \<alpha> \<equiv> Bot_const \<^bold>T I \<alpha>"

end

bundle MFODL_extra_no_notation
begin 

no_notation Top_const ("\<top>\<^sub>c")
     and Bot_const ("\<bottom>\<^sub>c")
     and EventuallyC ("\<^bold>F _ _" [55, 65] 65)
     and GloballyCE ("\<^bold>G\<^sub>E _ _" [55, 65] 65)
     and GloballyCR ("\<^bold>G\<^sub>R _ _" [55, 65] 65)
     and OnceC ("\<^bold>P _ _" [55, 65] 65)
     and HistoricallyCO ("\<^bold>H\<^sub>O _ _" [55, 65] 65)
     and HistoricallyCT ("\<^bold>H\<^sub>T _ _" [55, 65] 65)
     and Implies (infixr "\<longrightarrow>\<^sub>F" 72)

end

bundle MFODL_extra_notation
begin

notation Top_const ("\<top>\<^sub>c")
     and Bot_const ("\<bottom>\<^sub>c")
     and EventuallyC ("\<^bold>F _ _" [55, 65] 65)
     and GloballyCE ("\<^bold>G\<^sub>E _ _" [55, 65] 65)
     and GloballyCR ("\<^bold>G\<^sub>R _ _" [55, 65] 65)
     and OnceC ("\<^bold>P _ _" [55, 65] 65)
     and HistoricallyCO ("\<^bold>H\<^sub>O _ _" [55, 65] 65)
     and HistoricallyCT ("\<^bold>H\<^sub>T _ _" [55, 65] 65)
     and Implies (infixr "\<longrightarrow>\<^sub>F" 72)

end


subsection \<open> Example evaluations \<close>

unbundle MFODL_extra_notation \<comment> \<open> enable notation \<close>

lemma "\<langle>\<sigma>, v, V, i\<rangle> \<Turnstile>\<^sub>M \<^bold>G\<^sub>E I \<phi> = \<langle>\<sigma>, v, V, i\<rangle> \<Turnstile>\<^sub>M \<^bold>G\<^sub>R I \<phi>"
  by auto

lemma "\<langle>\<sigma>, v, V, i\<rangle> \<Turnstile>\<^sub>M \<^bold>H\<^sub>O I \<phi> = \<langle>\<sigma>, v, V, i\<rangle> \<Turnstile>\<^sub>M \<^bold>H\<^sub>T I \<phi>"
  by auto


subsubsection \<open> monitoring bad quality - historically \<close>

abbreviation "heating \<equiv> STR ''heating''"

definition badT :: "ty Formula.formula"
  where "badT \<equiv> \<^bold>H\<^sub>T \<^bold>[0,3\<^bold>] (heating \<dagger> [\<^bold>v 0])"

definition badO :: "ty Formula.formula"
  where "badO \<equiv> \<^bold>H\<^sub>O \<^bold>[0,3\<^bold>] (heating \<dagger> [\<^bold>v 0])"

lemma "safe_formula badT"
  "\<not> safe_formula badO"
  by (simp_all add: badT_def badO_def safe_dual_def enat_0)

definition "mbad \<equiv> minit badT"
definition "mbad0 \<equiv> mstep ((upd0 heating [{[Some (EInt 1)], [Some (EInt 2)], [Some (EInt 3)]}]), 0) mbad"
definition "mbad1 \<equiv> mstep ((upd0 heating [{[Some (EInt 1)], [Some (EInt 2)], [Some (EInt 3)]}]), 1) (snd mbad0)"
definition "mbad2 \<equiv> mstep ((upd0 heating [{[Some (EInt 3)], [Some (EInt 4)], [Some (EInt 5)]}]), 2) (snd mbad1)"
definition "mbad3 \<equiv> mstep ((upd0 heating [{[Some (EInt 3)], [Some (EInt 4)], [Some (EInt 5)]}]), 3) (snd mbad2)"
definition "mbad4 \<equiv> mstep ((upd0 heating [{[Some (EInt 3)], [Some (EInt 4)], [Some (EInt 5)], [Some (EInt 6)]}]), 4) (snd mbad3)"
definition "mbad5 \<equiv> mstep ((upd0 heating [{[Some (EInt 6)]}]), 5) (snd mbad4)"
definition "mbad6 \<equiv> mstep ((upd0 heating [{[Some (EInt 6)]}]), 6) (snd mbad5)"
definition "mbad7 \<equiv> mstep (Mapping.empty, 6) (snd mbad6)"

value "mbad"  \<comment> \<open> @{value "mbad"} \<close> 
value "mbad0" \<comment> \<open> @{value "mbad0"} \<close>
value "mbad1" \<comment> \<open> @{value "mbad1"} \<close>
value "mbad2" \<comment> \<open> @{value "mbad2"} \<close>
value "mbad3" \<comment> \<open> @{value "mbad3"} \<close>
value "mbad4" \<comment> \<open> @{value "mbad4"} \<close>
value "mbad5" \<comment> \<open> @{value "mbad5"} \<close>
value "mbad6" \<comment> \<open> @{value "mbad6"} \<close>
value "mbad7" \<comment> \<open> @{value "mbad7"} \<close>



subsubsection \<open> financial crime investigation - historically with many variables \<close>

definition "suspect \<equiv> (
  (\<^bold>H\<^sub>T \<^bold>[30, 35\<^bold>] (\<exists>\<^sub>F:TInt. STR ''failed_trans_from_paid_to'' \<dagger> [\<^bold>v 0,\<^bold>v 1,\<^bold>v 2,\<^bold>v 3]))
  \<and>\<^sub>F (STR ''approved_trans_from_paid_to'' \<dagger> [\<^bold>v 0,\<^bold>v 1,\<^bold>v 2,\<^bold>v 3])
  )"

lemma "\<not> safe_formula suspect"
  by (auto simp: suspect_def enat_0 safe_dual_def)


subsubsection \<open> monitoring piracy - applied release \<close>

abbreviation "off_route \<equiv> STR ''off_route''"
abbreviation "no_signal \<equiv> STR ''no_signal''"
abbreviation "received \<equiv> STR ''received''"

definition pirated :: "ty Formula.formula"
  where "pirated \<equiv> (off_route \<dagger> [\<^bold>v 0]) \<^bold>R \<^bold>[0,2\<^bold>] (no_signal \<dagger> [\<^bold>v 0])"

definition right_pir :: "ty Formula.formula"
  where "right_pir \<equiv> no_signal \<dagger> [\<^bold>v 0]"

definition left_pir :: "ty Formula.formula"
  where "left_pir \<equiv> off_route \<dagger> [\<^bold>v 0]"

definition notin_pir :: "ty Formula.formula"
  where "notin_pir \<equiv> received \<dagger> [\<^bold>v 0]"

lemma "safe_formula pirated"
  apply (auto simp: pirated_def enat_0 release_safe_0_def)
  by transfer (clarsimp simp: pirated_def enat_0)

definition "mpiracy \<equiv> minit pirated"
definition "mpiracy0 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) mpiracy"
definition "mpiracy1 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd mpiracy0)"
definition "mpiracy2 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd mpiracy1)"
definition "mpiracy3 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd mpiracy2)"
definition "mpiracy4 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd mpiracy3)"
definition "mpiracy5 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd mpiracy4)"
definition "mpiracy6 \<equiv> mstep (Mapping.empty, 6) (snd mpiracy5)"
definition "mpiracy7 \<equiv> mstep (Mapping.empty, 7) (snd mpiracy6)"
definition "mpiracy8 \<equiv> mstep (Mapping.empty, 8) (snd mpiracy7)"
definition "mpiracy9 \<equiv> mstep (Mapping.empty, 9) (snd mpiracy8)"
definition "mpiracy10 \<equiv> mstep (Mapping.empty, 10) (snd mpiracy9)"

definition "vmpiracy \<equiv> vminit pirated"
definition "vmpiracy0 \<equiv> vmstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) vmpiracy"
definition "vmpiracy1 \<equiv> vmstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd vmpiracy0)"
definition "vmpiracy2 \<equiv> vmstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd vmpiracy1)"
definition "vmpiracy3 \<equiv> vmstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd vmpiracy2)"
definition "vmpiracy4 \<equiv> vmstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd vmpiracy3)"
definition "vmpiracy5 \<equiv> vmstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd vmpiracy4)"
definition "vmpiracy6 \<equiv> vmstep (Mapping.empty, 6) (snd vmpiracy5)"
definition "vmpiracy7 \<equiv> vmstep (Mapping.empty, 7) (snd vmpiracy6)"
definition "vmpiracy8 \<equiv> vmstep (Mapping.empty, 8) (snd vmpiracy7)"
definition "vmpiracy9 \<equiv> vmstep (Mapping.empty, 9) (snd vmpiracy8)"
definition "vmpiracy10 \<equiv> vmstep (Mapping.empty, 10) (snd vmpiracy9)"


value mpiracy  \<comment> \<open> @{value "mpiracy"}  \<close>    
value mpiracy0 \<comment> \<open> @{value "fst mpiracy0"} \<close>
value mpiracy1 \<comment> \<open> @{value "fst mpiracy1"} \<close>
value mpiracy2 \<comment> \<open> @{value "fst mpiracy2"} \<close>
value mpiracy3 \<comment> \<open> @{value "fst mpiracy3"} \<close>
value mpiracy4 \<comment> \<open> @{value "fst mpiracy4"} \<close>
value mpiracy5 \<comment> \<open> @{value "fst mpiracy5"} \<close>
value mpiracy6 \<comment> \<open> @{value "fst mpiracy6"} \<close>
value mpiracy7 \<comment> \<open> @{value "fst mpiracy7"} \<close>
value mpiracy8 \<comment> \<open> @{value "fst mpiracy8"} \<close>
value mpiracy9 \<comment> \<open> @{value "fst mpiracy9"} \<close>
value mpiracy10 \<comment> \<open> @{value "fst mpiracy10"} \<close>

value vmpiracy  \<comment> \<open> @{value "vmpiracy"}  \<close>    
value vmpiracy0 \<comment> \<open> @{value "fst vmpiracy0"} \<close>
value vmpiracy1 \<comment> \<open> @{value "fst vmpiracy1"} \<close>
value vmpiracy2 \<comment> \<open> @{value "fst vmpiracy2"} \<close>
value vmpiracy3 \<comment> \<open> @{value "fst vmpiracy3"} \<close>
value vmpiracy4 \<comment> \<open> @{value "fst vmpiracy4"} \<close>
value vmpiracy5 \<comment> \<open> @{value "fst vmpiracy5"} \<close>
value vmpiracy6 \<comment> \<open> @{value "fst vmpiracy6"} \<close>
value vmpiracy7 \<comment> \<open> @{value "fst vmpiracy7"} \<close>
value vmpiracy8 \<comment> \<open> @{value "fst vmpiracy8"} \<close>
value vmpiracy9 \<comment> \<open> @{value "fst vmpiracy9"} \<close>
value vmpiracy10 \<comment> \<open> @{value "fst vmpiracy10"} \<close>


definition "rpiracy \<equiv> minit right_pir"
definition "rpiracy0 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) rpiracy"
definition "rpiracy1 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd rpiracy0)"
definition "rpiracy2 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd rpiracy1)"
definition "rpiracy3 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd rpiracy2)"
definition "rpiracy4 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd rpiracy3)"
definition "rpiracy5 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd rpiracy4)"

definition "lpiracy \<equiv> minit left_pir"
definition "lpiracy0 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) lpiracy"
definition "lpiracy1 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd lpiracy0)"
definition "lpiracy2 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd lpiracy1)"
definition "lpiracy3 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd lpiracy2)"
definition "lpiracy4 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd lpiracy3)"
definition "lpiracy5 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd lpiracy4)"

value rpiracy 
value rpiracy0 
value rpiracy1
value rpiracy2
value rpiracy3
value rpiracy4
value rpiracy5

value lpiracy 
value lpiracy0 
value lpiracy1
value lpiracy2
value lpiracy3
value lpiracy4
value lpiracy5

lemma "pirated = left_pir \<^bold>R \<^bold>[0,2\<^bold>] right_pir"
  by (simp add: pirated_def left_pir_def right_pir_def)

thm sat_release_rewrite_0 release_safe_0_def[unfolded always_safe_0_def, of left_pir "\<^bold>[0,2\<^bold>]" right_pir]

definition "disjunct1 \<equiv> right_pir \<^bold>U \<^bold>[0,2\<^bold>] (right_pir \<and>\<^sub>F left_pir)"
definition "disjunct2 \<equiv> right_pir \<^bold>U (flip_int_double_upper \<^bold>[0,2\<^bold>]) (\<^bold>Y all right_pir)"
definition "disjunct3 \<equiv> right_pir \<^bold>U \<^bold>[0,2\<^bold>] (right_pir \<and>\<^sub>F (\<^bold>X (flip_int \<^bold>[0,2\<^bold>]) Formula.TT))"

lemma "disjunct1 = right_pir \<^bold>U \<^bold>[0,2\<^bold>] right_pir \<and>\<^sub>F left_pir"
  "disjunct2 = right_pir \<^bold>U flip_int_double_upper \<^bold>[0,2\<^bold>] \<^bold>Y all right_pir"
  "disjunct3 = right_pir \<^bold>U \<^bold>[0,2\<^bold>] right_pir \<and>\<^sub>F (\<^bold>X (flip_int \<^bold>[0,2\<^bold>]) Formula.TT)"
  by (simp_all add: disjunct1_def disjunct2_def disjunct3_def)

lemma "safe_formula right_pir"
  "safe_formula left_pir"
  "safe_formula disjunct1"
  "safe_formula disjunct2"
  "safe_formula disjunct3"
  "safe_formula (release_safe_0 left_pir \<^bold>[0,2\<^bold>] right_pir)"
  by (simp_all add: right_pir_def left_pir_def disjunct1_def 
      disjunct2_def disjunct3_def release_safe_0_def)

thm disjunct3_def[unfolded right_pir_def left_pir_def]

(* (no_signal x) \<^bold>U \<^bold>[0,2\<^bold>] (no_signal x \<and>\<^sub>F off_route x) *)
definition "mdisjunct1 \<equiv> minit disjunct1"
definition "mdisjunct1_0 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) mdisjunct1"
definition "mdisjunct1_1 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd mdisjunct1_0)"
definition "mdisjunct1_2 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd mdisjunct1_1)"
definition "mdisjunct1_3 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd mdisjunct1_2)"
definition "mdisjunct1_4 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd mdisjunct1_3)"
definition "mdisjunct1_5 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd mdisjunct1_4)"

(* (no_signal x) \<^bold>U \<^bold>[3,4\<^bold>] (\<^bold>Y (no_signal x)) *)
definition "mdisjunct2 \<equiv> minit disjunct2"
definition "mdisjunct2_0 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) mdisjunct2"
definition "mdisjunct2_1 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd mdisjunct2_0)"
definition "mdisjunct2_2 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd mdisjunct2_1)"
definition "mdisjunct2_3 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd mdisjunct2_2)"
definition "mdisjunct2_4 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd mdisjunct2_3)"
definition "mdisjunct2_5 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd mdisjunct2_4)"
definition "mdisjunct2_6 \<equiv> mstep (Mapping.empty, 6) (snd mdisjunct2_5)"
definition "mdisjunct2_7 \<equiv> mstep (Mapping.empty, 7) (snd mdisjunct2_6)"
definition "mdisjunct2_8 \<equiv> mstep (Mapping.empty, 8) (snd mdisjunct2_7)"
definition "mdisjunct2_9 \<equiv> mstep (Mapping.empty, 9) (snd mdisjunct2_8)"
definition "mdisjunct2_10 \<equiv> mstep (Mapping.empty, 10) (snd mdisjunct2_9)"

(* (no_signal x) \<^bold>U \<^bold>[0,2\<^bold>] ((no_signal x) \<and>\<^sub>F (\<^bold>X \<^bold>[3,\<infinity>\<^bold>) \<top>)) *)
definition "mdisjunct3 \<equiv> minit disjunct3"
definition "mdisjunct3_0 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 0) mdisjunct3"
definition "mdisjunct3_1 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 1) (snd mdisjunct3_0)"
definition "mdisjunct3_2 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (upd0 no_signal [{[Some (EInt 1)], [Some (EInt 2)]}]), 2) (snd mdisjunct3_1)"
definition "mdisjunct3_3 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 3) (snd mdisjunct3_2)"
definition "mdisjunct3_4 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 4) (snd mdisjunct3_3)"
definition "mdisjunct3_5 \<equiv> mstep (updS received [{[Some (EInt 3)]}] (updS off_route [{[Some (EInt 1)]}] (upd0 no_signal [{[Some (EInt 2)]}])), 5) (snd mdisjunct3_4)"

value mdisjunct1  
value mdisjunct1_0 
value mdisjunct1_1
value mdisjunct1_2
value mdisjunct1_3
value mdisjunct1_4
value mdisjunct1_5

value mdisjunct2  
value mdisjunct2_0 
value mdisjunct2_1
value mdisjunct2_2
value mdisjunct2_3
value mdisjunct2_4
value mdisjunct2_5
value mdisjunct2_6
value mdisjunct2_7
value mdisjunct2_8
value mdisjunct2_9
value mdisjunct2_10

value mdisjunct3  
value mdisjunct3_0 
value mdisjunct3_1
value mdisjunct3_2
value mdisjunct3_3
value mdisjunct3_4
value mdisjunct3_5

unbundle MFODL_no_notation
unbundle ivl_no_notation

end


