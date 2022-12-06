(*<*)
theory Monitor_Code
  imports Monitor_Impl RBT_set_opt "HOL-Library.Code_Cardinality"
begin
(*>*)

(* understanding error from code generation *)

lemma "List.coset xs = {x. x \<notin> set xs}"
  using List.coset_def[unfolded uminus_set_def]
  thm bool_Compl_def
  by (simp add: set_eqI)

find_theorems "List.coset _"
typ "('a, bool) phantom"
thm insert_maggaux'.simps insert_maggaux'.simps [folded finite'_def]

lemma "Code_Cardinality.finite' (List.coset (xs::'a list)) 
  \<equiv> of_phantom (finite_UNIV:: ('a::finite_UNIV, bool) phantom)"
  apply simp
  unfolding finite_UNIV
  apply clarsimp
  done

term mstep

definition "my_fun \<phi> \<psi> = (if safe_assignment (fv \<phi>) \<psi> then True else False)"

export_code get_and_list checking Scala?
export_code my_fun checking Scala?

export_code convert_multiway checking Scala?

export_code mstep checking Haskell?

export_code convert_multiway mmonitorable_exec vminit_safe minit_safe vmstep mstep
   checking OCaml?

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
