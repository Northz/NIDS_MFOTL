(*<*)
theory Monitor_Code
  imports Monitor_Impl RBT_set_opt
begin
(*>*)

export_code convert_multiway mmonitorable_exec vminit_safe minit_safe vmstep mstep
   checking OCaml?

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval empty_db insert_into_db RBT_set rbt_fold Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*main functions*)
<<<<<<< HEAD
  convert_multiway vminit_safe minit_safe vmstep mstep mmonitorable_exec
  (*rewrite functions*)
  rewrite_trigger
=======
  convert_multiway mmonitorable_exec minit_safe mstep type_check
>>>>>>> master
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
