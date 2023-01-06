(*<*)
theory Monitor_Code
  imports Monitor_Impl RBT_set_opt
begin
(*>*)


thm default_mmasaux.init_since'_def 
thm default_mmauaux.init_until'_def
thm verimon_maux.init_trigger'_def
thm verimon_maux.init_and_trigger'_def
thm mtaux.init_and_trigger'_def
thm default_maux.meinit0.simps(13)[unfolded default_mmasaux.init_since'_def]


lemmas meinit0_code_simps = default_maux.meinit0.simps[unfolded verimon_maux.init_and_trigger'_def]
lemmas vmeinit0_code_simps = verimon_maux.meinit0.simps[unfolded verimon_maux.init_and_trigger'_def]
declare default_maux.meinit0.simps [code del]
declare meinit0_code_simps [code]
  and vmeinit0_code_simps [code]
declare default_mmasaux.init_since'_def [code_unfold]
  and default_mmauaux.init_until'_def [code_unfold]
  and verimon_maux.init_since'_def [code_unfold]
  and verimon_maux.init_until'_def [code_unfold]
  and verimon_maux.init_trigger'_def [code_unfold]
  and verimon_maux.init_and_trigger'_def [code_unfold]

(* code_thms vminit_safe *)


term default_mmasaux.init_since'
term default_mmauaux.init_until' 
term verimon_maux.init_trigger'


(*definition "my_fun \<phi> \<psi> = (if safe_assignment (fv \<phi>) \<psi> then True else False)"

export_code get_and_list checking Scala?
export_code my_fun checking OCaml?

export_code convert_multiway checking Scala?
export_code convert_multiway checking OCaml?
export_code vminit_safe checking OCaml?
export_code minit_safe checking OCaml?
export_code vmstep checking OCaml?
export_code mstep checking OCaml?*)


(* export_code convert_multiway mmonitorable_exec vminit_safe minit_safe vmstep mstep
   checking OCaml? *)

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval empty_db insert_into_db RBT_set rbt_fold Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*main functions*)
  convert_multiway mmonitorable_exec minit_safe mstep type_check vminit_safe vmstep  
  (*rewrite functions*)
  rewrite_trigger
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
