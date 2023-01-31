(*
 * This file is part of MONPOLY.
 *
 * Copyright (C) 2011 Nokia Corporation and/or its subsidiary(-ies).
 * Contact:  Nokia Corporation (Debmalya Biswas: debmalya.biswas@nokia.com)
 *
 * Copyright (C) 2012 ETH Zurich.
 * Contact:  ETH Zurich (Eugen Zalinescu: eugen.zalinescu@inf.ethz.ch)
 *
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, version 2.1 of the
 * License.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library. If not, see
 * http://www.gnu.org/licenses/lgpl-2.1.html.
 *
 * As a special exception to the GNU Lesser General Public License,
 * you may link, statically or dynamically, a "work that uses the
 * Library" with a publicly distributed version of the Library to
 * produce an executable file containing portions of the Library, and
 * distribute that executable file under terms of your choice, without
 * any of the additional requirements listed in clause 6 of the GNU
 * Lesser General Public License. By "a publicly distributed version
 * of the Library", we mean either the unmodified Library as
 * distributed by Nokia, or a modified version of the Library that is
 * distributed under the conditions defined in clause 3 of the GNU
 * Lesser General Public License. This exception does not however
 * invalidate any other reasons why the executable file might be
 * covered by the GNU Lesser General Public License.
 *)



open Misc
open Tuple
open Predicate


module Tuple_set = Set.Make (
  struct type t = tuple
   let compare = Tuple.compare
  end)

include Tuple_set

type relation = Tuple_set.t


(*** printing functions ***)


let print_rel str rel =
  print_string str;
  let rel' = Tuple_set.elements rel in
  Misc.print_list Tuple.print_tuple rel'

let prerr_rel str rel =
  prerr_string str;
  let rel' = Tuple_set.elements rel in
  Misc.prerr_list Tuple.prerr_tuple rel'

let print_rel4 str rel =
  print_string str;
  let rel' = Tuple_set.elements rel in
  Misc.print_list4 Tuple.print_tuple rel'

let print_reln str rel =
  print_rel str rel;
  print_newline()

let prerr_reln str rel =
  prerr_rel str rel;
  prerr_newline()

let print_bigrel rel =
  let rel' = Tuple_set.elements rel in
  Misc.print_list3 Tuple.print_tuple rel'

let print_orel = function
  | None -> print_string "N"
  | Some rel -> print_rel "S" rel




(********************************)


let make_relation list =
  let rec make acc = function
  | [] -> acc
  | h::t -> make (Tuple_set.add h acc) t
  in make Tuple_set.empty list


(*******************************************************************)
(*** rigid predicates ***)

let trel = make_relation [Tuple.make_tuple []]
let frel = Tuple_set.empty

let eval_equal t1 t2 =
  match t1,t2 with
  | Var x, Cst c
  | Cst c, Var x -> make_relation [Tuple.make_tuple [c]]
  | Cst c, Cst c' when c = c' -> trel
  | Cst c, Cst c' -> frel
  | _ -> failwith "[Relation.eval_equal] (x=y)"

let eval_not_equal t1 t2 =
  match t1,t2 with
  | Var x, Var y when x = y -> frel
  | Cst c, Cst c' when c = c' -> frel
  | Cst c, Cst c' -> trel
  | _ -> failwith "[Relation.eval_not_equal] (x <> y)"



(**********************************************************************)

let nested_loop_join post matches rel1 rel2 =
  let joinrel = ref Tuple_set.empty in
  let process_rel_tuple t1 =
    (* For each tuple in [rel1] we compute the columns (i.e. positions)
       in rel2 for which there should be matching values and the values
       tuples in rel2 should have at these columns.

       For instance, for [matches] = [(0,1);(1,2);(3,0)] and t1 =
       [6;7;9] we obtain [(0,7);(1,9);(3,6)]. That is, from [rel2] we
       will select all tuples which have 7 on position 0, 9 on
       position 1, and 6 on position 3.  *)
    let pv = List.map
      (fun (pos2, pos1) -> (pos2, Tuple.get_at_pos t1 pos1))
      matches
    in
      Tuple_set.iter
        (fun t2 ->
           try
             match post (Tuple.join pv t1 t2) with
             | Some t -> joinrel := Tuple_set.add t !joinrel
             | None -> ()
           with Not_joinable -> ()
        )
        rel2
  in
  Tuple_set.iter process_rel_tuple rel1;
  !joinrel

let build_hash_index key_posl rel =
  let n = Tuple_set.cardinal rel / 4 in
  let tbl = Hashtbl.create n in
  Tuple_set.iter
    (fun t ->
      let k = List.map (Tuple.get_at_pos t) key_posl in
      Hashtbl.add tbl k t
    )
    rel;
  tbl

let hash_join_with_index post tbl key_posl join_fun rel =
  let joinrel = ref Tuple_set.empty in
  Tuple_set.iter
    (fun t1 ->
      let k = List.map (Tuple.get_at_pos t1) key_posl in
      List.iter
        (fun t2 ->
          match post (join_fun t1 t2) with
          | Some t -> joinrel := Tuple_set.add t !joinrel
          | None -> ()
        )
        (Hashtbl.find_all tbl k)
    )
    rel;
  !joinrel

let hash_join_with_cards post matches card1 rel1 card2 rel2 =
  let key_posl2, key_posl1 = List.split matches in
  if card1 < card2 then
    let tbl = build_hash_index key_posl1 rel1 in
    let join_fun t2 t1 = Tuple.join_unchecked matches t1 t2 in
    hash_join_with_index post tbl key_posl2 join_fun rel2
  else
    let tbl = build_hash_index key_posl2 rel2 in
    hash_join_with_index post tbl key_posl1 (Tuple.join_unchecked matches) rel1

(** [matches] gives the columns which should match in the two
    relations in form of a list of tuples [(pos2,pos1)]: column [pos2] in
    [rel2] should match column [pos1] in [rel1] *)
let natural_join post matches rel1 rel2 =
  let card1 = Tuple_set.cardinal rel1 in
  let card2 = Tuple_set.cardinal rel2 in
  if card1 = 0 || card2 = 0 then
    Tuple_set.empty
  else if matches = [] || card1 < 8 || card2 < 8 then
    nested_loop_join post matches rel1 rel2
  else
    hash_join_with_cards post matches card1 rel1 card2 rel2


let in_t2_not_in_t1 t2 matches =
  let len  = List.length (Tuple.get_constants t2) in
  (* these are the positions in t2 which also appear in t1 *)
  let t2_pos = List.map snd matches in
  let rec get_aux pos =
    if pos = len then []
    else if not (List.mem pos t2_pos) then
      let v = Tuple.get_at_pos t2 pos in
      v :: (get_aux (pos+1))
    else
      get_aux (pos+1)
  in
  get_aux 0




(* Misc.subset attr1 attr2 *)
(* Note that free_vars in (f1 AND f2) are ordered according to f1 not
   to f2!  Thus, for instance, for p(x,y) AND q(z,y,x) the fields
   should be ordered by (x,y,z).
*)
let natural_join_sc1 post matches rel1 rel2 =
  if Tuple_set.is_empty rel1 || Tuple_set.is_empty rel2 then
    Tuple_set.empty
  else
    begin
      let joinrel = ref Tuple_set.empty in
      Tuple_set.iter (fun t2 ->
        let t1_list =
          List.map
      (fun (pos1, pos2) ->
        (* x is at pos1 in t1 and at pos2 in t2 *)
        Tuple.get_at_pos t2 pos2)
      matches
        in
        let t1 = Tuple.make_tuple t1_list in
        if Tuple_set.mem t1 rel1 then

          let t2_list = in_t2_not_in_t1 t2 matches in
          match post (Tuple.make_tuple (t1_list @ t2_list)) with
          | Some t2' -> joinrel := Tuple_set.add t2' !joinrel
          | None -> ()
      ) rel2;
      !joinrel
    end

(* Misc.subset attr2 attr1 *)
(* TODO: rewrite using filter / filter_map, see minus *)
let natural_join_sc2 post matches rel1 rel2 =
  if Tuple_set.is_empty rel1 || Tuple_set.is_empty rel2 then
    Tuple_set.empty
  else
    begin
      let joinrel = ref Tuple_set.empty in
      Tuple_set.iter (fun t1 ->
        let t2 = Tuple.make_tuple (
          List.map
      (* x is at pos2 in t2 and at pos1 in t1 *)
      (fun (pos2, pos1) -> Tuple.get_at_pos t1 pos1)
      matches)
        in
        if Tuple_set.mem t2 rel2 then
          match post t1 with
          | Some t1' -> joinrel := Tuple_set.add t1' !joinrel
          | None -> ()
      ) rel1;
      !joinrel
    end

let filtermap_inter = function
  | None -> Tuple_set.inter
  | Some f ->
    let scan rel1 rel2 = Tuple_set.filter_map (fun t ->
      if Tuple_set.mem t rel2 then f t else None) rel1
    in
    (fun rel1 rel2 ->
      if Tuple_set.cardinal rel1 <= Tuple_set.cardinal rel2 then
        scan rel1 rel2
      else
        scan rel2 rel1
    )

let filtermap_diff = function
  | None -> Tuple_set.diff
  | Some f ->
    (fun rel1 rel2 ->
      Tuple_set.filter_map (fun t ->
      if Tuple_set.mem t rel2 then None else f t) rel1
    )

(* not set difference, but the diff operator as defined in Abiteboul, page 89 *)
let minus opt_post posl =
  match opt_post with
  | None ->
    (fun rel1 rel2 ->
      Tuple_set.filter
        (fun t ->
          let t' = Tuple.projections posl t in
          not (Tuple_set.mem t' rel2)
        )
        rel1
    )
  | Some f ->
    (fun rel1 rel2 ->
      Tuple_set.filter_map
        (fun t ->
          let t' = Tuple.projections posl t in
          if Tuple_set.mem t' rel2 then None else f t
        )
        rel1
    )

let reorder new_pos rel = Tuple_set.map (Tuple.projections new_pos) rel


(* Note: [proj] \cup [sel] = all positions and [proj] \cap [sel] = \emptyset
   special case when sel=[]? yes, then selectp is the identity function
   special case when proj=[]? no

   The approach below seems useless, because we have to iterate anyhow
   through all tuples and transform them individually (unless sel=[]).
   And then positions do not help us, see function [Tuple.satisfiesp].
*)
let no_constraints tlist =
  let rec iter vars = function
    | [] -> true
    | (Var x) :: tlist ->
      if List.mem x vars then
        false (* there are constraints *)
      else (* new variable, we record its position *)
        iter (x :: vars) tlist

    | _ :: tlist -> false  (* there are constraints *)
  in
  iter [] tlist


(* Given a predicate [f]=[p(t_1,\dots,t_n)], [eval_pred] returns a
   function from relations to relations; this function transforms
   [|p(x_1,\dots,x_n)|] into [|p(t_1,\dots,t_n)|]
*)
let eval_pred opt_post p =
  let tlist = Predicate.get_args p in
  if no_constraints tlist then
    begin
      match opt_post with
      | None -> (fun rel -> rel)
      | Some f -> Tuple_set.filter_map f
    end
  else
    begin
      match opt_post with
      | None -> Tuple_set.filter_map (fun t ->
            let b, t' = Tuple.satisfiesp tlist t in
            if b then Some t' else None
          )
      | Some f -> Tuple_set.filter_map (fun t ->
            let b, t' = Tuple.satisfiesp tlist t in
            if b then f t' else None
          )
    end
