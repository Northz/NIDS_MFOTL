open Extformula
open Predicate
open Relation
open Tuple
open MFOTL

(* Immutable version of types used in eformula *)
type mezinfo = { mezlastev: Neval.cell;
                 mezauxrels: (int * timestamp * relation) Dllist.dllist}

type meinfo  = { melastev: Neval.cell;
                 meauxrels: (timestamp * relation) Dllist.dllist}

(* Immutable version of eformula used for marshalling *)
type mformula =
  | MRel of relation * int
  | MPred of predicate * comp_one * info * int
  | MLet of predicate * comp_one * mformula * mformula * Neval.cell * int
  | MNeg of mformula * int
  | MAnd of comp_two * mformula * mformula * ainfo * int
  | MOr of comp_two * mformula * mformula * ainfo * int
  | MExists of comp_one * mformula * int
  | MAggreg of agg_info * Aggreg.aggregator * mformula * int
  | MAggOnce of agg_info * Aggreg.once_aggregator * mformula * int
  | MPrev of interval * mformula * pinfo * int
  | MNext of interval * mformula * ninfo * int
  | MSince of mformula * mformula * sinfo * int
  | MUntil of mformula * mformula * uinfo * int
  | MEventuallyZ of interval * mformula * mezinfo * int
  | MEventually of interval * mformula * meinfo * int

val free_vars: mformula -> Predicate.var list
val predicates: mformula -> Predicate.predicate list
