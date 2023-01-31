open Predicate
open MFOTL
open Relation
open Tuple

type msaux

val init_msaux: (tuple -> tuple option) option -> bool -> interval ->
  var list -> var list -> msaux
val add_new_ts_msaux: timestamp -> msaux -> unit
val join_msaux: relation -> msaux -> unit
val add_new_table_msaux: relation -> msaux -> unit
val result_msaux: msaux -> relation

type muaux

val init_muaux: (tuple -> tuple option) option -> bool -> interval ->
  var list -> var list -> muaux
val update_lookahead_muaux: int -> timestamp -> muaux -> unit
val take_result_muaux: muaux -> relation option
val add_new_tables_muaux: relation -> relation -> muaux -> unit
