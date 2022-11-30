open Relation
open Predicate
open MFOTL
open Tuple

module Sk = Dllist
module Sj = Dllist

type info  = (int * timestamp * relation) Queue.t
type linfo = {mutable llast: Neval.cell}
type ainfo = {mutable arel: relation option}
type pinfo = {mutable plast: Neval.cell}
type ninfo = {mutable init: bool}

type agg_info = {op: agg_op; default: cst}

type sinfo = {mutable srel2: relation option;
              saux: Optimized_mtl.msaux}
type uinfo = {mutable ulast: Neval.cell;
              mutable urel2: relation option;
              uaux: Optimized_mtl.muaux}

type comp_one = relation -> relation
type comp_two = relation -> relation -> relation

type extformula =
  | ERel of relation * int
  | EPred of predicate * comp_one * info * int
  | ELet of predicate * comp_one * extformula * extformula * linfo * int
  | ENeg of extformula * int
  | EAnd of comp_two * extformula * extformula * ainfo * int
  | EOr of comp_two * extformula * extformula * ainfo * int
  | EExists of comp_one * extformula * int
  | EAggreg of agg_info * Aggreg.aggregator * extformula * int
  | EAggOnce of agg_info * Aggreg.once_aggregator * extformula * int
  | EPrev of interval * extformula * pinfo * int
  | ENext of interval * extformula * ninfo * int
  | ESince of extformula * extformula * sinfo * int
  | EUntil of extformula * extformula * uinfo * int

val contains_eventually: extformula -> bool

val prerr_auxel:  int * Relation.relation -> unit
val prerr_sauxel: MFOTL.timestamp * Relation.relation -> unit

val prerr_predinf: string -> info -> unit
val prerr_uinf: string -> uinfo -> unit

val prerr_extf: string -> extformula -> unit

val extf_structure: extformula -> string
