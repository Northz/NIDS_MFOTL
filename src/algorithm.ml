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



(** This module implements the monitoring algorithm. This algorithm is
    described in the paper "Runtime Monitoring of Metric First-order
    Temporal Properties" by David Basin, Felix Klaedtke, Samuel
    Muller, and Birgit Pfitzmann, presented at FSTTCS'08.


    This is the MONPOLY's main module, all other modules can be seen
    as "helper" modules. The module's entry point is normally the
    [monitor] function. This function checks that the given formula is
    monitorable and then calls the [check_log] function which
    iteratively reads each log entry. To be able to incrementally
    process the entries, the input formula is first extended with
    additional information for each subformula, by calling the
    [add_ext] function.  Also, a queue [neval] of not-yet evaluated
    indexes of log entries is maintained.

    The function [check_log] reads each log entry, calls [add_index]
    to update the extended formula with the new information from the
    entry at index [i], adds index [i] to the queue of not-yet
    evaluated indexes, and finally calls [process_index] to process
    this entry.

    The function [process_index] iterativelly tries to evaluate the
    formula at each index (calling the function [eval]) from the queue
    of not-yet evaluated indexes. It stops when the formula cannot be
    evaluated or when the formula has been evaluated at all indexes in
    the queue. The function [eval] performs a bottom-up evaluation of
    the formula.
*)


open Dllist
open Misc
open Perf
open Predicate
open MFOTL
open Tuple
open Relation
open Table
open Db
open Sliding
open Helper

open Marshalling
open Splitting
open Extformula
open Mformula
open Hypercube_slicer

module Sk = Dllist
module Sj = Dllist

let resumefile = ref ""
let combine_files = ref ""
let lastts = ref MFOTL.ts_invalid
let slicer_heavy_unproc : (int * string list) array ref= ref [|(0, [])|]
let slicer_shares = ref [|[||]|]
let slicer_seeds  = ref [|[||]|]

(* For the sake of clarity, think about merging these types and all
   related functions. Some fields will be redundant, but we will not lose
   that much. *)

let crt_ts = ref MFOTL.ts_invalid
let crt_tp = ref (-1)

let make_db db =
  Db.make_db (List.map (fun (s,r) -> Table.make_table s r) db)

let mqueue_add_last auxrels tsq rel2 =
  if Mqueue.is_empty auxrels then
    Mqueue.add (tsq,rel2) auxrels
  else
    let tslast, rellast =  Mqueue.get_last auxrels in
    if tslast = tsq then
      Mqueue.update_last (tsq, Relation.union rellast rel2) auxrels
    else
      Mqueue.add (tsq,rel2) auxrels

let dllist_add_last auxrels tsq rel2 =
  if Dllist.is_empty auxrels then
    Dllist.add_last (tsq,rel2) auxrels
  else
    let tslast, rellast = Dllist.get_last auxrels in
    if tslast = tsq then
      let _ = Dllist.pop_last auxrels in
      Dllist.add_last (tsq, Relation.union rellast rel2) auxrels
    else
      Dllist.add_last (tsq,rel2) auxrels

let elim_old_eventually q tsq intv inf =
  let auxrels = inf.eauxrels in

  let rec elim_old_eauxrels () =
    (* remove old elements that fell out of the interval *)
    if not (Dllist.is_empty auxrels) then
      let (tsj, _) = Dllist.get_first auxrels in
      if not (MFOTL.in_right_ext (MFOTL.ts_minus tsj tsq) intv) then
        begin
          if inf.elast != Dllist.void && inf.elast == Dllist.get_first_cell auxrels then
            inf.elast <- Dllist.void;
          ignore(Dllist.pop_first auxrels);
          elim_old_eauxrels()
        end
  in

  elim_old_eauxrels ()


let warn_if_empty_aggreg {op; default} {Aggreg.empty_rel; Aggreg.rel} =
  if empty_rel then
    (match op with
    | Avg | Med | Min | Max ->
      let op_str = MFOTL.string_of_agg_op op in
      let default_str = string_of_cst default in
      let msg = Printf.sprintf "WARNING: %s applied on empty relation! \
                                Resulting value is %s, by (our) convention.\n"
        op_str default_str
      in
      prerr_string msg
    | Cnt | Sum -> ());
  rel


let add_let_index f n rels =
  let rec update = function
    | EPred ((p, a, _), comp, inf, _) ->
      if (p, a) = n then
        List.iter (fun (i,tsi,rel) -> Queue.add (i,tsi, comp rel) inf) rels
      else ()

    | ELet ((p, a, _), comp, f1, f2, inf, _) ->
      update f1;
      if (p, a) = n then () else update f2

    | ERel _ -> ()

    | ENeg (f1,_)
    | EExists (_,f1,_)
    | EAggOnce (_,_,f1,_)
    | EAggreg (_,_,f1,_)
    | ENext (_,f1,_,_)
    | EPrev (_,f1,_,_)
    | EEventuallyZ (_,f1,_,_)
    | EEventually (_,f1,_,_) ->
      update f1

    | EAnd (_,f1,f2,_,_)
    | EOr (_,f1,f2,_,_)
    | ESince (f1,f2,_,_)
    | EUntil (f1,f2,_,_) ->
      update f1;
      update f2
  in
  update f



(* Arguments:
   - [f] the current formula
   - [crt] the current evaluation point (an neval cell)
   - [discard] a boolean; if true then the result is not used
               (only a minimal amount of computation should be done);
               it should not be propagated for temporal subformulas
               (pitfall: possible source of bugs)
*)
let rec eval f crt discard =
  let (q,tsq) = Neval.get_data crt in

  if Misc.debugging Dbg_eval then
    begin
      prerr_extf "\n[eval] evaluating formula\n" f;
      Printf.eprintf "at (%d,%s) with discard=%b\n%!"
        q (MFOTL.string_of_ts tsq) discard
    end;

  let wrapper = function
  | ERel (rel,loc) -> Some rel, loc

  | EPred (p,_,inf,loc) ->
    if Misc.debugging Dbg_eval then
      begin
        prerr_string "[eval,Pred] ";
        Predicate.prerr_predicate p;
        prerr_predinf  ": " inf
      end;

    (if Queue.is_empty inf
    then None
    else begin
      let (cq,ctsq,rel) = Queue.pop inf in
      assert (cq = q && ctsq = tsq);
      Some rel
    end), loc

  | ELet ((p, a, _), comp, f1, f2, inf, loc) ->
      let rec eval_f1 rels =
        if Neval.is_last inf.llast then
          rels
        else
          let crt1 = Neval.get_next inf.llast in
          match eval f1 crt1 false with
          | Some rel ->
            inf.llast <- crt1;
            let (i, tsi) = Neval.get_data crt1 in
            eval_f1 ((i, tsi, comp rel) :: rels)
          | None -> rels
      in
      add_let_index f2 (p, a) (List.rev (eval_f1 []));
      eval f2 crt discard, loc

  | ENeg (f1,loc) ->
    (match eval f1 crt discard with
     | Some rel ->
       let res =
         if Relation.is_empty rel then (* false? *)
           Relation.singleton (Tuple.make_tuple [])
         else
           Relation.empty (* true *)
       in
       Some res
     | None -> None
    ), loc

  | EExists (comp,f1,loc) ->
    (match eval f1 crt discard with
     | Some rel ->
       Perf.profile_enter ~tp:q ~loc;
       let result = comp rel in
       Perf.profile_exit ~tp:q ~loc;
       Some result
     | None -> None
    ), loc

  | EAnd (comp,f1,f2,inf,loc) ->
    (* we have to store rel1, if f2 cannot be evaluated *)
    let eval_and rel1 =
      if Relation.is_empty rel1 then
        (match eval f2 crt true with
         | Some _ ->
           inf.arel <- None;
           Some rel1
         | None ->
           inf.arel <- Some rel1;
           None
        )
      else
        (match eval f2 crt discard with
         | Some rel2 ->
           inf.arel <- None;
           Perf.profile_enter ~tp:q ~loc;
           let result = comp rel1 rel2 in
           Perf.profile_exit ~tp:q ~loc;
           Some result
         | None ->
           inf.arel <- Some rel1;
           None
        )
    in
    (match inf.arel with
     | Some rel1 -> eval_and rel1
     | None ->
       (match eval f1 crt discard with
        | Some rel1 -> eval_and rel1
        | None -> None
       )
    ), loc

  | EAggreg (inf, comp, f, loc) ->
    (match eval f crt discard with
     | Some rel ->
       Some (if discard then Relation.empty
         else begin
           Perf.profile_enter ~tp:q ~loc;
           let result = comp rel in
           Perf.profile_exit ~tp:q ~loc;
           warn_if_empty_aggreg inf result
         end)
     | None -> None
    ), loc

  | EOr (comp, f1, f2, inf, loc) ->
    (* we have to store rel1, if f2 cannot be evaluated *)
    (match inf.arel with
     | Some rel1 ->
       (match eval f2 crt discard with
        | Some rel2 ->
          inf.arel <- None;
          Perf.profile_enter ~tp:q ~loc;
          let result = comp rel1 rel2 in
          Perf.profile_exit ~tp:q ~loc;
          Some result
        | None -> None
       )
     | None ->
       (match eval f1 crt discard with
        | Some rel1 ->
          (match eval f2 crt discard with
           | Some rel2 -> Some (comp rel1 rel2)
           | None ->
             inf.arel <- Some rel1;
             None
          )
        | None -> None
       )
    ), loc

  | EPrev (intv,f1,inf,loc) ->
    if Misc.debugging Dbg_eval then
      Printf.eprintf "[eval,Prev] inf.plast=%s\n%!" (Neval.string_of_cell inf.plast);

    (if q = 0 then
      Some Relation.empty
    else
      begin
        let pcrt = Neval.get_next inf.plast in
        let pq, ptsq = Neval.get_data pcrt in
        assert(pq = q-1);
        match eval f1 pcrt discard with
        | Some rel1 ->
          inf.plast <- pcrt;
          if MFOTL.in_interval (MFOTL.ts_minus tsq ptsq) intv then
            Some rel1
          else
            Some Relation.empty
        | None -> None
      end), loc

  | ENext (intv,f1,inf,loc) ->
    if Misc.debugging Dbg_eval then
      Printf.eprintf "[eval,Next] inf.init=%b\n%!" inf.init;

    if inf.init then
      begin
        match eval f1 crt discard with
        | Some _ -> inf.init <- false
        | _ -> ()
      end;

    (if Neval.is_last crt || inf.init then
      None
    else
      begin
        let ncrt = Neval.get_next crt in
        let nq, ntsq = Neval.get_data ncrt in
        assert (nq = q+1);
        match eval f1 ncrt discard with
        | Some rel1 ->
          if MFOTL.in_interval (MFOTL.ts_minus ntsq tsq) intv then
            Some rel1
          else
            Some Relation.empty
        | None -> None
      end), loc

  | ESince (f1,f2,inf,loc) ->
    if Misc.debugging Dbg_eval then
      Printf.eprintf "[eval,Since] q=%d\n" q;

    let eval_f1 rel2 =
      (match eval f1 crt false with
       | Some rel1 ->
         inf.srel2 <- None;
         Perf.profile_enter ~tp:q ~loc;
         Optimized_mtl.add_new_ts_msaux tsq inf.saux;
         Optimized_mtl.join_msaux rel1 inf.saux;
         Optimized_mtl.add_new_table_msaux rel2 inf.saux;
         Perf.profile_exit ~tp:q ~loc;
         Some (Optimized_mtl.result_msaux inf.saux)
       | None ->
         inf.srel2 <- Some rel2;
         None
      )
    in

    (match inf.srel2 with
     | Some rel2 -> eval_f1 rel2
     | None ->
       (match eval f2 crt false with
        | None -> None
        | Some rel2 -> eval_f1 rel2
       )
    ), loc

  | EAggOnce (inf, state, f, loc) ->
    (match eval f crt false with
     | Some rel ->
       Perf.profile_enter ~tp:q ~loc;
       state#update tsq rel;
       let result = Some (if discard then Relation.empty
         else warn_if_empty_aggreg inf state#get_result) in
       Perf.profile_exit ~tp:q ~loc;
       result
     | None -> None
    ), loc

  | EUntil (f1,f2,inf,loc) ->
    if Misc.debugging Dbg_eval then
      Printf.eprintf "[eval,Until] q=%d\n" q;

    let rec update_and_get_result () =
      if Neval.is_last inf.ulast then
        None
      else
        begin
          let ncrt = Neval.get_next inf.ulast in
          let (i, tsi) = Neval.get_data ncrt in
          Perf.profile_enter ~tp:q ~loc;
          Optimized_mtl.update_lookahead_muaux i tsi inf.uaux;
          let result = Optimized_mtl.take_result_muaux inf.uaux in
          Perf.profile_exit ~tp:q ~loc;
          match result with
          | Some _ as x -> x
          | None ->
            (match inf.urel2 with
             | Some rel2 -> eval_f1 rel2 ncrt
             | None ->
               (match eval f2 ncrt false with
                | None -> None
                | Some rel2 -> eval_f1 rel2 ncrt
               )
            )
        end
    and eval_f1 rel2 ncrt =
      match eval f1 ncrt false with
      | Some rel1 ->
        inf.urel2 <- None;
        inf.ulast <- ncrt;
        Perf.profile_enter ~tp:q ~loc;
        Optimized_mtl.add_new_tables_muaux rel1 rel2 inf.uaux;
        Perf.profile_exit ~tp:q ~loc;
        update_and_get_result ()
      | None -> inf.urel2 <- Some rel2; None
    in
    update_and_get_result (), loc

  | EEventuallyZ (intv,f2,inf,loc) ->
    (* contents of inf:
       elastev: Neval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info       the auxiliary relations (up to elastev)
    *)
    if Misc.debugging Dbg_eval then
      prerr_ezinf "[eval,EventuallyZ] inf: " inf;

    let rec ez_update () =
      if Neval.is_last inf.ezlastev then
        None
      else
        let ncrt = Neval.get_next inf.ezlastev in
        let (i,tsi) = Neval.get_data ncrt in
        (* Printf.eprintf "[eval,Eventually] e_update: ncrt.i = %d\n%!" i; *)
        if not (MFOTL.in_left_ext (MFOTL.ts_minus tsi tsq) intv) then
          (* we have the lookahead, we can compute the result *)
          begin
            Perf.profile_enter ~tp:q ~loc;
            if Misc.debugging Dbg_eval then
              Printf.eprintf "[eval,EventuallyZ] evaluation possible q=%d tsq=%s tsi=%s\n%!"
                q (MFOTL.string_of_ts tsq) (MFOTL.string_of_ts tsi);

            let auxrels = inf.ezauxrels in
            let result =
            if Dllist.is_empty auxrels then
              Some Relation.empty
            else if discard then
              begin
                let lw, _, _ = Dllist.get_first auxrels in
                if lw = q then (* at next iteration this first element will be too old *)
                  begin
                    if inf.ezlast != Dllist.void && inf.ezlast == Dllist.get_first_cell auxrels then
                      inf.ezlast <- Dllist.void;
                    ignore(Dllist.pop_first auxrels);
                  end;
                Some Relation.empty
              end
            else
              begin
                if inf.ezlast != Dllist.void && inf.ezlast == Dllist.get_first_cell auxrels then
                  (* TODO: when can such a case occur? *)
                  inf.ezlast <- Dllist.void;

                let lw, _, _ = Dllist.get_first auxrels in
                assert (lw >= q); (* TODO: when lw > q *)
                let cond = fun (_,tsj,_) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) intv in
                let f = fun (j,_,rel) -> (j,rel) in
                let subseq, new_last = get_new_elements auxrels inf.ezlast cond f in
                let rw =
                  if subseq = [] then
                    (* TODO: why j? when does this case occur? *)
                    let j, _, _  = Dllist.get_data inf.ezlast in j
                  else
                    begin
                      assert (new_last != Dllist.void);
                      inf.ezlast <- new_last;
                      let rw = fst (List.hd subseq) in
                      assert (rw = let j, _, _ = Dllist.get_data new_last in j);
                      rw
                    end
                in

                if Misc.debugging Dbg_eval then
                  begin
                    Printf.eprintf "[eval,EventuallyZ] lw = %d rw = %d " lw rw;
                    Misc.prerrnl_list "subseq = " prerr_auxel subseq;
                  end;

                let newt = Sliding.slide string_of_int Relation.union subseq (lw, rw) inf.eztree in

                if lw = q then (* at next iteration this first element will be too old *)
                  begin
                    if new_last == Dllist.get_first_cell auxrels then
                      inf.ezlast <- Dllist.void;
                    ignore(Dllist.pop_first auxrels);
                  end;

                inf.eztree <- newt;
                Some (Sliding.stree_res newt)
              end
            in
            Perf.profile_exit ~tp:q ~loc;
            result
          end
        else (* we don't have the lookahead -> we cannot compute the result *)
          begin
            match eval f2 ncrt false with
            | None -> None
            | Some rel2 ->
              (* we update the auxiliary relations *)
              if not (Relation.is_empty rel2) then
                Dllist.add_last (i,tsi,rel2) inf.ezauxrels;
              inf.ezlastev <- ncrt;
              ez_update ()
          end
    in
    ez_update (), loc


  | EEventually (intv,f2,inf,loc) ->
    (* contents of inf:
       elastev:  Neval.cell  last cell of neval for which f2 is evaluated
       eauxrels: info        the auxiliary relations (up to elastev)
    *)
    if Misc.debugging Dbg_eval then
      prerr_einfn "[eval,Eventually] inf: " inf;

    (* we could in principle do this update less often: that is, we
       can do after each evaluation, but we need to find out the
       value of ts_{q+1} *)
    Perf.profile_enter ~tp:q ~loc;
    elim_old_eventually q tsq intv inf;
    Perf.profile_exit ~tp:q ~loc;

    let rec e_update () =
      if Neval.is_last inf.elastev then
        None
      else
        let ncrt = Neval.get_next inf.elastev in
        let (i,tsi) = Neval.get_data ncrt in
        (* Printf.eprintf "[eval,Eventually] e_update: ncrt.i = %d\n%!" i; *)
        if not (MFOTL.in_left_ext (MFOTL.ts_minus tsi tsq) intv) then
          (* we have the lookahead, we can compute the result *)
          begin
            Perf.profile_enter ~tp:q ~loc;
            if Misc.debugging Dbg_eval then
              Printf.eprintf "[eval,Eventually] evaluation possible q=%d tsq=%s tsi=%s\n%!"
                q (MFOTL.string_of_ts tsq) (MFOTL.string_of_ts tsi);

            let auxrels = inf.eauxrels in
            let result =
            if Dllist.is_empty auxrels || discard then
              Some Relation.empty
            else
              let lw, _ = Dllist.get_first auxrels in
              if MFOTL.in_left_ext (MFOTL.ts_minus lw tsq) intv then
                (* the new window is not empty *)
                let cond = fun (tsj,_) -> MFOTL.in_left_ext (MFOTL.ts_minus tsj tsq) intv in
                let subseq, new_last = get_new_elements auxrels inf.elast cond (fun x -> x) in
                let rw =
                  if subseq = [] then
                    fst (Dllist.get_data inf.elast)
                  else
                    begin
                      assert (new_last != Dllist.void);
                      inf.elast <- new_last;
                      let rw = fst (List.hd subseq) in
                      assert (rw = fst (Dllist.get_data new_last));
                      rw
                    end
                in
                if Misc.debugging Dbg_eval then
                  begin
                    Printf.eprintf "[eval,Eventually] lw = %s rw = %s "
                      (MFOTL.string_of_ts lw)
                      (MFOTL.string_of_ts rw);
                    Misc.prerrnl_list "subseq = " prerr_sauxel subseq;
                  end;
                let newt = Sliding.slide MFOTL.string_of_ts Relation.union subseq (lw, rw) inf.etree in
                inf.etree <- newt;
                Some (Sliding.stree_res newt)
              else
                begin
                  (* the new window is empty,
                     because not even the oldest element satisfies the constraint *)
                  inf.etree <- LNode {l = MFOTL.ts_invalid;
                                      r = MFOTL.ts_invalid;
                                      res = Some (Relation.empty)};
                  inf.elast <- Dllist.void;
                  Some Relation.empty
                end
            in
            Perf.profile_exit ~tp:q ~loc;
            result
          end
        else
          begin
            match eval f2 ncrt false with
            | None -> None
            | Some rel2 ->
              (* we update the auxiliary relations *)
              if (MFOTL.in_right_ext (MFOTL.ts_minus tsi tsq) intv) &&
                 not (Relation.is_empty rel2) then
                dllist_add_last inf.eauxrels tsi rel2;
              inf.elastev <- ncrt;
              e_update ()
          end
    in
    e_update (), loc
  in
  let result, loc = wrapper f in
  if !Perf.profile_enabled then
    begin
      match result with
      | None -> ()
      | Some rel -> Perf.profile_int ~tag:Perf.tag_eval_result ~tp:q ~loc
          (Relation.cardinal rel)
    end;
  result

let add_index f i tsi db =
  let rec update lets = function
    | EPred (p, comp, inf, _) ->
      let name = Predicate.get_name p in
      if List.mem name lets
      then ()
      else
        let rel =
          (try Hashtbl.find db name
           with Not_found ->
           match name with
           | "tp" -> Relation.singleton (Tuple.make_tuple [Int (Z.of_int i)])
           | "ts" -> Relation.singleton (Tuple.make_tuple [Int tsi])
           | "tpts" ->
             Relation.singleton (Tuple.make_tuple [Int (Z.of_int i); Int tsi])
           | _ -> Relation.empty
          )
        in
        let rel = comp rel in
        Queue.add (i,tsi,rel) inf

    | ELet (p, comp, f1, f2, inf, _) ->
      update lets f1;
      update (Predicate.get_name p :: lets) f2

    | ERel _ -> ()

    | ENeg (f1,_)
    | EExists (_,f1,_)
    | EAggOnce (_,_,f1,_)
    | EAggreg (_,_,f1,_)
    | ENext (_,f1,_,_)
    | EPrev (_,f1,_,_)
    | EEventuallyZ (_,f1,_,_)
    | EEventually (_,f1,_,_) ->
      update lets f1

    | EAnd (_,f1,f2,_,_)
    | EOr (_,f1,f2,_,_)
    | ESince (f1,f2,_,_)
    | EUntil (f1,f2,_,_) ->
      update lets f1;
      update lets f2
  in
  update [] f

let add_ext neval f =
  let neval0 = Neval.get_last neval in
  let loc = ref 0 in
  let next_loc () = incr loc; !loc in
  let rec add_ext = function
  | Pred p ->
    EPred (p, Relation.eval_pred p, Queue.create(), next_loc())

  | Let (p, f1, f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attrp = Predicate.pvars p in
    let new_pos = List.map snd (Table.get_matches attr1 attrp) in
    let comp = Relation.reorder new_pos in
    ELet (p, comp, add_ext f1, add_ext f2, {llast = neval0}, next_loc())

  | LetPast _ -> failwith "LETPAST is not supported except in -verified mode"

  | Equal (t1, t2) ->
    let rel = Relation.eval_equal t1 t2 in
    ERel (rel, next_loc())

  | Neg (Equal (t1, t2)) ->
    let rel = Relation.eval_not_equal t1 t2 in
    ERel (rel, next_loc())

  | Neg f -> ENeg (add_ext f, next_loc())

  | Exists (vl, f1) ->
    let ff1 = add_ext f1 in
    let attr1 = MFOTL.free_vars f1 in
    let pos = List.map (fun v -> Misc.get_pos v attr1) vl in
    let pos = List.sort Stdlib.compare pos in
    let comp = Relation.project_away pos in
    EExists (comp,ff1,next_loc())

  | Or (f1, f2) ->
    let ff1 = add_ext f1 in
    let ff2 = add_ext f2 in
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let comp =
      if attr1 = attr2 then
        Relation.union
      else
        let matches = Table.get_matches attr2 attr1 in
        let new_pos = List.map snd matches in
        (* first reorder rel2 *)
        (fun rel1 rel2 ->
           let rel2' = Relation.reorder new_pos rel2 in
           Relation.union rel1 rel2'
        )
    in
    EOr (comp, ff1, ff2, {arel = None}, next_loc())

  | And (f1, f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let ff1 = add_ext f1 in
    let f2_is_special = Rewriting.is_special_case attr1 f2 in
    let ff2 =
      if f2_is_special then ERel (Relation.empty, next_loc())
      else match f2 with
        | Neg f2' -> add_ext f2'
        | _ -> add_ext f2
    in
    let comp =
      if f2_is_special then
        if Misc.subset attr2 attr1 then
          let filter_cond = Tuple.get_filter attr1 f2 in
          fun rel1 _ -> Relation.filter filter_cond rel1
        else
          let process_tuple = Tuple.get_tf attr1 f2 in
          fun rel1 _ ->
            Relation.fold
              (fun t res ->
                match process_tuple t with
                | None -> res
                | Some t' -> Relation.add t' res)
              rel1 Relation.empty
      else
        match f2 with
        | Neg _ ->
          if attr1 = attr2 then
            fun rel1 rel2 -> Relation.diff rel1 rel2
          else
            begin
              assert(Misc.subset attr2 attr1);
              let posl = List.map (fun v -> Misc.get_pos v attr1) attr2 in
              fun rel1 rel2 -> Relation.minus posl rel1 rel2
            end

        | _ ->
          let matches1 = Table.get_matches attr1 attr2 in
          let matches2 = Table.get_matches attr2 attr1 in
          if attr1 = attr2 then
            fun rel1 rel2 -> Relation.inter rel1 rel2
          else if Misc.subset attr1 attr2 then
            fun rel1 rel2 -> Relation.natural_join_sc1 matches2 rel1 rel2
          else if Misc.subset attr2 attr1 then
            fun rel1 rel2 -> Relation.natural_join_sc2 matches1 rel1 rel2
          else
            fun rel1 rel2 -> Relation.natural_join matches1 rel1 rel2
    in
    EAnd (comp, ff1, ff2, {arel = None}, next_loc())

  | Aggreg (t_y, y, op, x, glist, Once (intv, f)) ->
    let t_y = match t_y with TCst a -> a | _ -> failwith "Internal error" in
    let default = MFOTL.aggreg_default_value op t_y in
    let attr = MFOTL.free_vars f in
    let posx = Misc.get_pos x attr in
    let posG = List.map (fun z -> Misc.get_pos z attr) glist in
    let state =
      match op with
      | Cnt -> Aggreg.cnt_once default intv 0 posG
      | Min -> Aggreg.min_once default intv 0 posx posG
      | Max -> Aggreg.max_once default intv 0 posx posG
      | Sum -> Aggreg.sum_once default intv 0 posx posG
      | Avg -> Aggreg.avg_once default intv 0 posx posG
      | Med -> Aggreg.med_once default intv 0 posx posG
    in
    EAggOnce ({op; default}, state, add_ext f, next_loc())

  | Aggreg (t_y, y, op, x, glist, f)  ->
    let t_y = match t_y with TCst a -> a | _ -> failwith "Internal error" in
    let default = MFOTL.aggreg_default_value op t_y in
    let attr = MFOTL.free_vars f in
    let posx = Misc.get_pos x attr in
    let posG = List.map (fun z -> Misc.get_pos z attr) glist in
    let comp =
      match op with
      | Cnt -> Aggreg.cnt default 0 posG
      | Sum -> Aggreg.sum default 0 posx posG
      | Min -> Aggreg.min default 0 posx posG
      | Max -> Aggreg.max default 0 posx posG
      | Avg -> Aggreg.avg default 0 posx posG
      | Med -> Aggreg.med default 0 posx posG
    in
    EAggreg ({op; default}, comp, add_ext f, next_loc())

  | Prev (intv, f) ->
    let ff = add_ext f in
    EPrev (intv, ff, {plast = neval0}, next_loc())

  | Next (intv, f) ->
    let ff = add_ext f in
    ENext (intv, ff, {init = true}, next_loc())

  | Since (intv,f1,f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let ef1, pos =
      (match f1 with
       | Neg f1' -> f1', false
       | _ -> f1, true
      )
    in
    let ff1 = add_ext ef1 in
    let ff2 = add_ext f2 in
    let saux = Optimized_mtl.init_msaux pos intv attr1 attr2 in
    let inf = {srel2 = None; saux} in
    ESince (ff1,ff2,inf, next_loc())

  | Once (intv,f) ->
    let attr = MFOTL.free_vars f in
    let ff1 = ERel (Relation.make_relation [Tuple.make_tuple []], next_loc()) in
    let ff2 = add_ext f in
    let saux = Optimized_mtl.init_msaux true intv [] attr in
    let inf = {srel2 = None; saux} in
    ESince (ff1,ff2,inf, next_loc())

  | Until (intv,f1,f2) ->
    let attr1 = MFOTL.free_vars f1 in
    let attr2 = MFOTL.free_vars f2 in
    let ef1, pos =
      (match f1 with
       | Neg f1' -> f1', false
       | _ -> f1, true
      )
    in
    let ff1 = add_ext ef1 in
    let ff2 = add_ext f2 in
    let uaux = Optimized_mtl.init_muaux pos intv attr1 attr2 in
    let inf = {ulast = neval0; urel2 = None; uaux} in
    EUntil (ff1,ff2,inf, next_loc())

  | Eventually (intv,f) ->
    let ff = add_ext f in
    if fst intv = CBnd MFOTL.ts_null then
      EEventuallyZ (intv,ff,{eztree = LNode {l = -1;
                                             r = -1;
                                             res = Some (Relation.empty)};
                             ezlast = Dllist.void;
                             ezlastev = neval0;
                             ezauxrels = Dllist.empty()}, next_loc())
    else
      EEventually (intv,ff,{etree = LNode {l = MFOTL.ts_invalid;
                                           r = MFOTL.ts_invalid;
                                           res = Some (Relation.empty)};
                            elast = Dllist.void;
                            elastev = neval0;
                            eauxrels = Dllist.empty()}, next_loc())

  | _ -> failwith "[add_ext] internal error"
  in
  add_ext f, neval0


type 'a state = {
  s_posl: int list; (** variable position list for output tuples *)
  s_extf: 'a; (** extended formula *)
  s_neval: Neval.queue; (** NEval queue *)
  mutable s_log_tp: int; (** most recent time-point in log *)
  mutable s_log_ts: MFOTL.timestamp; (** most recent time-stamp in log *)
  mutable s_skip: bool; (** whether the current time-point should be skipped *)
  mutable s_db: (string, relation) Hashtbl.t; (** db being parsed *)
  mutable s_in_tp: int; (** most recent time-point after filtering *)
  mutable s_last: Neval.cell; (** most recently evaluated time-point *)
}

let map_state f s = {
  s_posl = s.s_posl;
  s_extf = f s.s_extf;
  s_neval = s.s_neval;
  s_log_tp = s.s_log_tp;
  s_log_ts = s.s_log_ts;
  s_skip = s.s_skip;
  s_db = s.s_db;
  s_in_tp = s.s_in_tp;
  s_last = s.s_last;
}

(*
  STATE MANAGEMENT CALLS
  - (Un-)Marshalling, Splitting, Merging
 *)

let saved_state_msg = "Saved state"
let slicing_parameters_updated_msg = "Slicing parameters updated"
let restored_state_msg = "Loaded state"
let combined_state_msg = "Loaded state"
let get_index_prefix_msg = "Current timepoint:"

 (*
  Helper function used in "marshal" and "split_and_save" functions.
  Saves state to specified dumpfile
 *)
let dump_to_file dumpfile value =
  let ch = open_out_bin dumpfile in
  Marshal.to_channel ch value [Marshal.Closures];
  close_out ch

(*
  Helper function used in "unmarshal" and "merge_formulas" functions.
  Reads state from specified dumpfile.
*)
let read_m_from_file file =
  let ch = open_in_bin file in
  let value = (Marshal.from_channel ch : mformula state) in
  close_in ch;
  value

let empty_db: (string, relation) Hashtbl.t = Hashtbl.create 1

let prepare_state_for_marshalling state =
  state.s_skip <- false;
  Hashtbl.reset state.s_db;
  let rec eval_loop () =
    let crt = Neval.get_next state.s_last in
    match eval state.s_extf crt false with
    | Some rel ->
      let (q, tsq) = Neval.get_data crt in
      show_results state.s_posl state.s_in_tp q tsq rel;
      state.s_last <- crt;
      if Neval.is_last crt then () else eval_loop ()
    | None -> ()
  in
  if (state.s_in_tp < state.s_log_tp) then
    begin
      state.s_in_tp <- state.s_log_tp;
      ignore (Neval.append (state.s_log_tp, state.s_log_ts) state.s_neval);
      add_index state.s_extf state.s_log_tp state.s_log_ts empty_db;
      eval_loop ()
    end

(* Converts extformula to mformula form used for storage. Saves formula + state in specified dumpfile. *)
let marshal dumpfile state =
  prepare_state_for_marshalling state;
  dump_to_file dumpfile (map_state Marshalling.ext_to_m state)

(*
  Reads mformula + state from specified dumpfile and restores it to extformula form with full state
  information using m_to_ext function.
*)
let unmarshal resumefile =
  map_state Marshalling.m_to_ext (read_m_from_file resumefile)

let split_save filename state =
  let heavy_unproc = !slicer_heavy_unproc in
  let shares = !slicer_shares in
  let seeds = !slicer_seeds in

  prepare_state_for_marshalling state;

  let mf = Marshalling.ext_to_m state.s_extf in
  let heavy = Hypercube_slicer.convert_heavy mf heavy_unproc in
  let slicer = Hypercube_slicer.create_slicer mf heavy shares seeds in
  let result = Splitting.split_with_slicer (Hypercube_slicer.add_slices_of_valuation slicer) slicer.degree mf in

  let format_filename index =
    Printf.sprintf "%s-%d.bin" filename index
  in

  Array.iteri (fun index mf ->
    let mstate = map_state (fun _ -> mf) state in
    dump_to_file (format_filename index) mstate
  ) result;
  Printf.printf "%s\n%!" saved_state_msg

(* Convert comma separated filenames to list of strings *)
let files_to_list f =
  String.split_on_char ',' f

(*
  Merge states contained in list of dumpfiles. Assumption is made that formulas are identical and
  only states differ.
  In the fold operation, always two mformulas are combined using recursion, with one being formula
  being the accumulator which is initialized as the first element of the list. The rest of the list
  is then folded over.
 *)
let merge_states files =
  if List.length files == 1 then unmarshal (List.hd files)
  else
    let mstate =
      List.fold_right (fun filename mstate ->
        let mstate' = read_m_from_file filename in
        assert (mstate.s_log_tp = mstate'.s_log_tp);
        assert (mstate.s_log_ts = mstate'.s_log_ts);
        assert (mstate.s_in_tp = mstate'.s_in_tp);
        assert (fst (Neval.get_data mstate.s_last) =
          fst (Neval.get_data mstate'.s_last));
        map_state (fun mf ->
          Splitting.comb_m mstate.s_last mf mstate'.s_extf) mstate
      ) (List.tl files) (read_m_from_file (List.hd files))
    in
    map_state Marshalling.m_to_ext mstate


(* MONITORING FUNCTION *)

let process_index state =
  if !Misc.verbose then
    Printf.printf "At time point %d:\n%!" state.s_in_tp;

  let rec eval_loop () =
    let crt = Neval.get_next state.s_last in
    let (q, tsq) = Neval.get_data crt in
    if tsq < MFOTL.ts_max then
      begin
        Perf.profile_enter ~tp:q ~loc:Perf.loc_eval_root;
        let result = eval state.s_extf crt false in
        Perf.profile_exit ~tp:q ~loc:Perf.loc_eval_root;
        match result with
        | Some rel ->
          show_results state.s_posl state.s_in_tp q tsq rel;
          state.s_last <- crt;
          if !Misc.stop_at_first_viol && not (Relation.is_empty rel) then false
          else if Neval.is_last crt then true
          else eval_loop ()
        | None -> true
      end
    else false
  in
  eval_loop ()

let set_slicer_parameters (heavy, shares, seeds) =
  slicer_heavy_unproc := heavy;
  slicer_shares := shares;
  slicer_seeds := seeds;
  Printf.printf "%s\n%!" slicing_parameters_updated_msg

module Monitor = struct
  type t = extformula state

  let begin_tp ctxt ts =
    ctxt.s_log_tp <- ctxt.s_log_tp + 1;
    if ts >= ctxt.s_log_ts then
      ctxt.s_log_ts <- ts
    else
      if !Misc.stop_at_out_of_order_ts then
        begin
          Printf.eprintf "ERROR: Out of order timestamp %s (previous: %s)\n"
            (MFOTL.string_of_ts ts) (MFOTL.string_of_ts ctxt.s_log_ts);
          exit 1
        end
      else
        begin
          Printf.eprintf "WARNING: Skipping out of order timestamp %s\
            \ (previous: %s)\n"
            (MFOTL.string_of_ts ts) (MFOTL.string_of_ts ctxt.s_log_ts);
          ctxt.s_log_tp <- ctxt.s_log_tp - 1;
          ctxt.s_skip <- true
        end;
    if Misc.debugging Dbg_perf then
      Perf.check_log ctxt.s_log_tp ctxt.s_log_ts

  let tuple ctxt (name, tl) sl =
    if not ctxt.s_skip && (not !Filter_rel.enabled || Filter_rel.rel_OK name)
    then
      let tuple =
        try Tuple.make_tuple2 sl tl with
        | Invalid_argument _ ->
          Printf.eprintf "ERROR: Wrong tuple length for predicate %s\
            \ (expected: %d, actual: %d)\n"
            name (List.length tl) (List.length sl);
          exit 1
        | Type_error msg ->
          Printf.eprintf "ERROR: Wrong type for predicate %s: %s\n"
            name msg;
          exit 1
      in
      if not !Filter_rel.enabled || Filter_rel.tuple_OK name tuple then
        try
          let rel = Hashtbl.find ctxt.s_db name in
          Hashtbl.replace ctxt.s_db name (Relation.add tuple rel)
        with Not_found -> Hashtbl.add ctxt.s_db name (Relation.singleton tuple)

  let eval_tp ctxt =
    ctxt.s_in_tp <- ctxt.s_log_tp;
    ignore (Neval.append (ctxt.s_log_tp, ctxt.s_log_ts) ctxt.s_neval);
    add_index ctxt.s_extf ctxt.s_log_tp ctxt.s_log_ts ctxt.s_db;
    Hashtbl.clear ctxt.s_db;
    if not (process_index ctxt) then
      raise Log_parser.Stop_parser

  let end_tp ctxt =
    if ctxt.s_skip then
      ctxt.s_skip <- false
    else if !Filter_empty_tp.enabled && Hashtbl.length ctxt.s_db = 0 then
      Hashtbl.clear ctxt.s_db
    else
      eval_tp ctxt;
    Perf.profile_exit ~tp:ctxt.s_log_tp ~loc:Perf.loc_read_tp

  let command ctxt name params =
    match name with
    | "print" ->
        (* TODO: Should be printed to stdout. *)
        prerr_extf "Current extended formula:\n" ctxt.s_extf;
        prerr_newline ()
    | "terminate" ->
        Printf.printf "Terminated at timepoint: %d\n%!" ctxt.s_log_tp;
        raise Log_parser.Stop_parser
    | "print_and_exit" ->
        (* TODO: Should be printed to stdout. *)
        prerr_extf "Current extended formula:\n" ctxt.s_extf;
        prerr_newline ();
        Printf.printf "Terminated at timepoint: %d\n%!" ctxt.s_log_tp;
        raise Log_parser.Stop_parser
    | "get_pos" ->
        Printf.printf "Current timepoint: %d\n%!" ctxt.s_log_tp;
    | "save_state" ->
        (match params with
        | Some (Argument filename) ->
            marshal filename ctxt;
            Printf.printf "%s\n%!" saved_state_msg
        | _ ->
            prerr_endline "ERROR: Bad arguments for save_state command";
            if not !Misc.ignore_parse_errors then exit 1)
    | "save_and_exit" ->
        (match params with
        | Some (Argument filename) ->
            marshal filename ctxt;
            Printf.printf "%s\n%!" saved_state_msg;
            raise Log_parser.Stop_parser
        | _ ->
            prerr_endline "ERROR: Bad arguments for save_and_exit command";
            exit 1)
    | "set_slicer" ->
        (match params with
        | Some (SplitSave sp) -> set_slicer_parameters sp
        | _ ->
            prerr_endline "ERROR: Bad arguments for set_slicer command";
            if not !Misc.ignore_parse_errors then exit 1)
    | "split_save" ->
        (match params with
        | Some (Argument filename) -> split_save filename ctxt
        | _ ->
            prerr_endline "ERROR: Bad arguments for split_save command";
            if not !Misc.ignore_parse_errors then exit 1)
    | _ ->
        Printf.eprintf "ERROR: Unrecognized command: %s\n" name;
        if not !Misc.ignore_parse_errors then exit 1

  let end_log ctxt =
    if !Misc.new_last_ts then
      begin
        begin_tp ctxt MFOTL.ts_max;
        eval_tp ctxt (* skip empty tp filter *)
      end;
    if Misc.debugging Dbg_perf then
      Perf.check_log_end ctxt.s_log_tp ctxt.s_log_ts

  let parse_error ctxt pos msg =
    prerr_endline "ERROR while parsing log:";
    prerr_endline (Log_parser.string_of_position pos ^ ": " ^ msg);
    if not !Misc.ignore_parse_errors then exit 1

end

module Parser = Log_parser.Make (Monitor)

let init_monitor_state dbschema fv f =
  (* compute permutation for output tuples *)
  let fv_pos = List.map snd (Table.get_matches (MFOTL.free_vars f) fv) in
  assert (List.length fv_pos = List.length fv);
  let neval = Neval.create () in
  let extf, last = add_ext neval f in
  Perf.profile_string ~tag:Perf.tag_extformula (extf_structure extf);
  { s_posl = fv_pos;
    s_extf = extf;
    s_neval = neval;
    s_log_tp = -1;
    s_log_ts = MFOTL.ts_invalid;
    s_skip = false;
    s_db = Hashtbl.create (List.length dbschema);
    s_in_tp = -1;
    s_last = last; }

let monitor_string dbschema log fv f =
  let lexbuf = Lexing.from_string log in
  let ctxt = init_monitor_state dbschema fv f in
  ignore (Parser.parse dbschema lexbuf ctxt)

let monitor dbschema logfile fv f =
  let ctxt = init_monitor_state dbschema fv f in
  Perf.profile_enter ~tp:(-1) ~loc:Perf.loc_main_loop;
  ignore (Parser.parse_file dbschema logfile ctxt);
  Perf.profile_exit ~tp:(-1) ~loc:Perf.loc_main_loop

(* Unmarshals formula & state from resume file and then starts processing
   logfile. *)
let resume dbschema logfile =
  let ctxt = unmarshal !resumefile in
  Printf.printf "%s\n%!" restored_state_msg;
  ignore (Parser.parse_file dbschema logfile ctxt)

(* Combines states from files which are marshalled from an identical extformula. Same as resume
   the log file then processed from the beginning *)
let combine dbschema logfile =
  let files = files_to_list !combine_files in
  let ctxt = merge_states files in
  Printf.printf "%s\n%!" combined_state_msg;
  ignore (Parser.parse_file dbschema logfile ctxt)
