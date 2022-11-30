open MFOTL
open Tuple

type args = {
  a_intv: interval;
  a_bounded: bool;
  a_gap: bool;
  a_pos: bool;
  a_prop1: bool;
  a_key2: int list;
}

let init_args pos intv attr1 attr2 =
  let matches = Table.get_matches attr2 attr1 in
  {
    a_intv = intv;
    a_bounded = not (infinite_interval intv);
    a_gap = not (in_right_ext ts_null intv);
    a_pos = pos;
    a_prop1 = (attr1 = []);
    a_key2 = List.map snd matches;
  }

type idx_table = (tuple, (tuple, unit) Hashtbl.t) Hashtbl.t

let idx_table_insert args ixt rel =
  Relation.iter (fun tup ->
    let key = Misc.get_positions args.a_key2 tup in
    match Hashtbl.find_opt ixt key with
    | None ->
        let inner = Hashtbl.create 1 in
        Hashtbl.add inner tup ();
        Hashtbl.add ixt key inner
    | Some inner ->
        if not (Hashtbl.mem inner tup) then Hashtbl.add inner tup ()
  ) rel

let idx_table_remove args ixt rel =
  Relation.iter (fun tup ->
    let key = Misc.get_positions args.a_key2 tup in
    match Hashtbl.find_opt ixt key with
    | None -> ()
    | Some inner ->
        Hashtbl.remove inner tup;
        if Hashtbl.length ixt = 0 then Hashtbl.remove ixt key
  ) rel

let idx_table_inv_semijoin args ixt rel =
  if Hashtbl.length ixt = 0 || (Relation.is_empty rel && not args.a_pos) then
    Relation.empty
  else
    begin
      let res = ref Relation.empty in
      let add_keys inner =
        Hashtbl.iter (fun tup () -> res := Relation.add tup !res) inner in
      if args.a_pos || Hashtbl.length ixt <= Relation.cardinal rel then
        Hashtbl.iter (fun key inner ->
          if Relation.mem key rel <> args.a_pos then add_keys inner) ixt
      else
        Relation.iter (fun key ->
          match Hashtbl.find_opt ixt key with
          | Some inner -> add_keys inner
          | None -> ()) rel;
      !res
    end

type msaux = {
  ms_args: args;
  mutable ms_t: timestamp;
  mutable ms_gc: timestamp;
  ms_prevq: (timestamp * Relation.relation) Queue.t;
  ms_inq: (timestamp * Relation.relation) Queue.t;
  ms_in_map: (tuple, timestamp) Hashtbl.t;
  ms_in_idx: idx_table;
  mutable ms_in: Relation.relation;
  ms_since: (tuple, timestamp) Hashtbl.t;
}

let init_msaux pos intv attr1 attr2 =
  {
    ms_args = init_args pos intv attr1 attr2;
    ms_t = ts_null;
    ms_gc = ts_null;
    ms_prevq = Queue.create();
    ms_inq = Queue.create();
    ms_in_map = Hashtbl.create 1;
    ms_in_idx = Hashtbl.create 1;
    ms_in = Relation.empty;
    ms_since = Hashtbl.create 1;
  }

let rec drop_while (p: 'a -> bool) (q: 'a Queue.t) =
  if Queue.is_empty q then ()
  else if p (Queue.peek q) then (ignore (Queue.pop q); drop_while p q)
  else ()

let rec do_drop_while (p: 'a -> bool) (c: 'a -> unit) (q: 'a Queue.t) =
  if Queue.is_empty q then ()
  else if p (Queue.peek q) then (c (Queue.pop q); do_drop_while p c q)
  else ()

let add_new_ts_msaux nt aux =
  let intv = aux.ms_args.a_intv in
  (* shift end *)
  let discard = ref Relation.empty in
  drop_while (fun (t, _) -> not (in_left_ext (ts_minus nt t) intv)) aux.ms_prevq;
  do_drop_while (fun (t, _) -> not (in_left_ext (ts_minus nt t) intv))
    (fun (t, rel) ->
      Relation.iter (fun tup ->
        match Hashtbl.find_opt aux.ms_in_map tup with
        | Some t' when t' = t ->
            Hashtbl.remove aux.ms_in_map tup;
            discard := Relation.add tup !discard
        | _ -> ()
      ) rel
    )
    aux.ms_inq;
  if not aux.ms_args.a_prop1 then
    idx_table_remove aux.ms_args aux.ms_in_idx !discard;
  aux.ms_in <- Relation.diff aux.ms_in !discard;
  (* add new ts *)
  let add = ref Relation.empty in
  do_drop_while (fun (t, _) -> in_right_ext (ts_minus nt t) intv)
    (fun (t, rel) ->
      if aux.ms_args.a_bounded then
        Queue.add (t, rel) aux.ms_inq;
      Relation.iter (fun tup ->
        match Hashtbl.find_opt aux.ms_since tup with
        | Some t' when t' <= t ->
            if aux.ms_args.a_bounded then
              Hashtbl.replace aux.ms_in_map tup t;
            add := Relation.add tup !add
        | _ -> ()
      ) rel
    )
    aux.ms_prevq;
  if not aux.ms_args.a_prop1 then
    idx_table_insert aux.ms_args aux.ms_in_idx !add;
  aux.ms_in <- Relation.union aux.ms_in !add;
  aux.ms_t <- nt

let join_msaux rel aux =
  if aux.ms_args.a_prop1 then
    begin
      if Relation.is_empty rel = aux.ms_args.a_pos then
        begin
          Hashtbl.clear aux.ms_in_map;
          aux.ms_in <- Relation.empty;
          Hashtbl.clear aux.ms_since
        end
    end
  else
    begin
      let discard = idx_table_inv_semijoin aux.ms_args aux.ms_in_idx rel in
      Relation.iter (fun tup ->
          let key = Misc.get_positions aux.ms_args.a_key2 tup in
          if aux.ms_args.a_bounded then
            Hashtbl.remove aux.ms_in_map tup;
          Hashtbl.remove aux.ms_in_idx key;
          if aux.ms_args.a_gap then
            Hashtbl.remove aux.ms_since tup
        )
        discard;
      aux.ms_in <- Relation.diff aux.ms_in discard
    end;
  if aux.ms_args.a_gap &&
    not (in_left_ext (ts_minus aux.ms_t aux.ms_gc) aux.ms_args.a_intv) then
    begin
      (*gc*)
      let keep = ref Relation.empty in
      let collect (_, rel) = keep := Relation.union !keep rel in
      Queue.iter collect aux.ms_prevq;
      Queue.iter collect aux.ms_inq;
      Hashtbl.filter_map_inplace (fun tup t ->
        if Relation.mem tup !keep then Some t else None) aux.ms_since;
      aux.ms_gc <- aux.ms_t
    end

let add_new_table_msaux rel aux =
  let t = aux.ms_t in
  if aux.ms_args.a_gap then
    begin
      Relation.iter (fun tup ->
        if not (Hashtbl.mem aux.ms_since tup) then
          Hashtbl.add aux.ms_since tup t
        ) rel;
      Queue.add (t, rel) aux.ms_prevq
    end
  else
    begin
      if aux.ms_args.a_bounded then
        begin
          Queue.add (t, rel) aux.ms_inq;
          Relation.iter (fun tup -> Hashtbl.replace aux.ms_in_map tup t) rel
        end;
      if not aux.ms_args.a_prop1 then
        idx_table_insert aux.ms_args aux.ms_in_idx rel;
      aux.ms_in <- Relation.union aux.ms_in rel
    end

let result_msaux aux = aux.ms_in


type muaux = {
  mu_args: args;
  mutable mu_in_tp: int; (** current lookahead time-point *)
  mutable mu_in_ts: timestamp; (** current lookahead time-stamp *)
  mutable mu_ts_cnt: int; (** occurrences of lookahead time-stamp *)
  mutable mu_out_tp: int; (** next result time-point *)
  mutable mu_out_cnt: int; (** number of consecutive time-points that are ready
    to be returned without consulting [mu_inq] *)
  mutable mu_lb_tp: int; (** highest time-point for which the lookahead
    satisfies the lower interval bound *)
  mutable mu_buf1: Relation.relation option; (** buffer to delay insertion of
    left operand's result by one step (used to get the next time-stamp in the
    case of a negated operand) *)
  mutable mu_gc: timestamp; (** last gc run of mu_seq1 in the case of a negated
    operand *)
  mu_prevq: (int * timestamp * int) Queue.t; (** compressed sequence (highest
    tp, ts, count) of time-points for which the lookahead does not yet satisfy
    the lower interval bound *)
  mu_inq: (int * timestamp * int) Queue.t; (** compressed sequence (highest tp,
    ts, count) of time-points relative to which the lookahead is in the interval
    *)
  mu_seq1: (tuple, int * timestamp) Hashtbl.t; (** mapping of keys (tuples
    projected to the common free variables) to the earliest time-point from
    which on the left operand (including a possible negation) is satisfied *)
  mu_useq: (int, (tuple, int) Hashtbl.t) Hashtbl.t; (** mapping from the
    earliest, not yet evaluated time-point to mappings from tuples to the latest
    time-point in between which the tuple is in the result *)
  mu_acc: (tuple, int) Hashtbl.t; (** accumulator to be merged with the next
    mapping in [mu_useq] *)
  mutable mu_res: Relation.relation; (** most recent result *)
  mutable mu_delmap: (int, Tuple.tuple list) Hashtbl.t; (** canidates for
    deletion from [mu_res] *)
}

let debug_muaux aux =
  let string_of_list f = Misc.string_of_list_ext "(" ")" ", " f in
  let string_of_queue q =
    let l = List.of_seq (Queue.to_seq q) in
    string_of_list (fun (jn, t, n) ->
      Printf.sprintf "%d * %s [.. %d]" n (MFOTL.string_of_ts t) jn) l
  in
  let string_of_tbl1 f tbl =
    let l = List.of_seq (Hashtbl.to_seq tbl) in
    let l = List.sort (fun (a,_) (b,_) -> Stdlib.compare a b) l in
    string_of_list (fun (tup, x) ->
      Printf.sprintf "%s -> %d" (Tuple.string_of_tuple tup) (f x)) l
  in
  let string_of_seq1 = string_of_tbl1 (fun (j,_) -> j) in
  let string_of_useq tbl =
    let l = List.of_seq (Hashtbl.to_seq tbl) in
    let l = List.sort (fun (a,_) (b,_) -> Stdlib.compare a b) l in
    string_of_list (fun (j, tbl1) ->
      Printf.sprintf "%d -> %s" j (string_of_tbl1 (fun k -> k) tbl1)) l
  in
  let string_of_delmap tbl =
    let l = List.of_seq (Hashtbl.to_seq tbl) in
    let l = List.sort (fun (a,_) (b,_) -> Stdlib.compare a b) l in
    string_of_list (fun (k, tupl) ->
      Printf.sprintf "%d -> %s" k (string_of_list Tuple.string_of_tuple tupl)) l
  in
  print_endline "[DEBUG] uaux = {";
  Printf.printf "  mu_in_tp = %d\n" aux.mu_in_tp;
  Printf.printf "  mu_in_ts = %s\n" (MFOTL.string_of_ts aux.mu_in_ts);
  Printf.printf "  mu_ts_cnt = %d\n" aux.mu_ts_cnt;
  Printf.printf "  mu_out_tp = %d\n" aux.mu_out_tp;
  Printf.printf "  mu_out_cnt = %d\n" aux.mu_out_cnt;
  Printf.printf "  mu_lb_tp = %d\n" aux.mu_lb_tp;
  (match aux.mu_buf1 with
  | None -> print_endline "  mu_buf1 = None"
  | Some r -> Relation.print_reln "  mu_buf1 = " r
  );
  Printf.printf "  mu_gc = %s\n" (MFOTL.string_of_ts aux.mu_gc);
  Printf.printf "  mu_prevq = %s\n" (string_of_queue aux.mu_prevq);
  Printf.printf "  mu_inq = %s\n" (string_of_queue aux.mu_inq);
  Printf.printf "  mu_seq1 = %s\n" (string_of_seq1 aux.mu_seq1);
  Printf.printf "  mu_useq = %s\n" (string_of_useq aux.mu_useq);
  Printf.printf "  mu_acc = %s\n" (string_of_tbl1 (fun j -> j) aux.mu_acc);
  Relation.print_reln "  mu_res = " aux.mu_res;
  Printf.printf "  mu_delmap = %s\n" (string_of_delmap aux.mu_delmap);
  print_endline "}"

let init_muaux pos intv attr1 attr2 =
  {
    mu_args = init_args pos intv attr1 attr2;
    mu_in_tp = -1;
    mu_in_ts = ts_invalid;
    mu_ts_cnt = 0;
    mu_out_tp = 0;
    mu_out_cnt = 0;
    mu_lb_tp = -1;
    mu_buf1 = None;
    mu_gc = ts_null;
    mu_prevq = Queue.create();
    mu_inq = Queue.create();
    mu_seq1 = Hashtbl.create 1;
    mu_useq = Hashtbl.create 1;
    mu_acc = Hashtbl.create 1;
    mu_res = Relation.empty;
    mu_delmap = Hashtbl.create 1;
  }

let apply_buf1 i tsi aux =
  match aux.mu_buf1 with
  | None -> ()
  | Some rel1 ->
      if not (in_left_ext (ts_minus tsi aux.mu_gc) aux.mu_args.a_intv) then
        begin
          (*gc*)
          Hashtbl.filter_map_inplace (fun _ ((_, t) as x) ->
            if in_left_ext (ts_minus tsi t) aux.mu_args.a_intv then
              Some x
            else
              None
            ) aux.mu_seq1;
          aux.mu_gc <- tsi
        end;
      Relation.iter (fun key -> Hashtbl.replace aux.mu_seq1 key (i, tsi)) rel1;
      aux.mu_buf1 <- None

let shift_lookahead tsi aux =
  if tsi = aux.mu_in_ts then
    aux.mu_ts_cnt <- succ aux.mu_ts_cnt
  else
    begin
      if aux.mu_ts_cnt >= 1 then
        begin
          if aux.mu_args.a_gap then
            begin
              Queue.add (aux.mu_in_tp - 1, aux.mu_in_ts, aux.mu_ts_cnt)
                aux.mu_prevq;
              do_drop_while
                (fun (_, t, _) ->
                  in_right_ext (ts_minus tsi t) aux.mu_args.a_intv)
                (fun ((j, _, _) as x) ->
                  Queue.add x aux.mu_inq; aux.mu_lb_tp <- j)
                aux.mu_prevq
            end
          else
            Queue.add (aux.mu_in_tp - 1, aux.mu_in_ts, aux.mu_ts_cnt) aux.mu_inq
        end;
      aux.mu_in_ts <- tsi;
      aux.mu_ts_cnt <- 1
    end

let update_lookahead_muaux i tsi aux =
  if i > aux.mu_in_tp then
    begin
      aux.mu_in_tp <- i;
      apply_buf1 i tsi aux;
      shift_lookahead tsi aux
    end

let take_result_muaux aux =
  if aux.mu_out_cnt = 0 && not (Queue.is_empty aux.mu_inq) &&
    (let (_, t, _) = Queue.peek aux.mu_inq in
      not (in_left_ext (ts_minus aux.mu_in_ts t) aux.mu_args.a_intv))
  then
    begin
      let (_, _, n) = Queue.take aux.mu_inq in
      aux.mu_out_cnt <- n
    end;
  if aux.mu_out_cnt = 0 then
    None
  else
    begin
      let j = aux.mu_out_tp in
      let res1 = ref Relation.empty in
      (match Hashtbl.find_opt aux.mu_useq j with
      | None -> ()
      | Some tbl ->
          Hashtbl.remove aux.mu_useq j;
          Hashtbl.iter (fun tup k ->
            if k = j then
              res1 := Relation.add tup !res1
            else
              begin
                aux.mu_res <- Relation.add tup aux.mu_res;
                (match Hashtbl.find_opt aux.mu_acc tup with
                | None -> Hashtbl.add aux.mu_acc tup k
                | Some k' -> if k' < k then Hashtbl.replace aux.mu_acc tup k
                );
                (match Hashtbl.find_opt aux.mu_delmap k with
                | None -> Hashtbl.add aux.mu_delmap k [tup]
                | Some tupl -> Hashtbl.replace aux.mu_delmap k (tup :: tupl)
                )
              end
            )
            tbl
      );
      let result = Relation.union aux.mu_res !res1 in
      (match Hashtbl.find_opt aux.mu_delmap j with
      | Some tupl ->
          Hashtbl.remove aux.mu_delmap j;
          let del = List.fold_left (fun del tup ->
              match Hashtbl.find_opt aux.mu_acc tup with
              | None -> Relation.add tup del
              | Some k when k <= j ->
                  Hashtbl.remove aux.mu_acc tup;
                  Relation.add tup del
              | _ -> del
            ) Relation.empty tupl
          in
          aux.mu_res <- Relation.diff aux.mu_res del
      | None -> ()
      );
      aux.mu_out_tp <- aux.mu_out_tp + 1;
      aux.mu_out_cnt <- aux.mu_out_cnt - 1;
      Some result
    end

let add_new_tables_muaux rel1 rel2 aux =
  if not aux.mu_args.a_gap then
    aux.mu_lb_tp <- aux.mu_in_tp;
  if aux.mu_lb_tp >= 0 then
    begin
      if aux.mu_args.a_prop1 then
        begin
          let j =
            match Hashtbl.find_opt aux.mu_seq1 [] with
            | None -> if aux.mu_args.a_pos then aux.mu_in_tp else aux.mu_out_tp
            | Some (j, _) -> max j aux.mu_out_tp
          in
          if j <= aux.mu_lb_tp then
            match Hashtbl.find_opt aux.mu_useq j with
            | None ->
                let tbl = Hashtbl.create (Relation.cardinal rel2) in
                Relation.iter (fun tup -> Hashtbl.add tbl tup aux.mu_lb_tp)
                  rel2;
                Hashtbl.add aux.mu_useq j tbl
            | Some tbl ->
                Relation.iter (fun tup -> Hashtbl.replace tbl tup aux.mu_lb_tp)
                  rel2
        end
      else
        Relation.iter (fun tup ->
          let key = Misc.get_positions aux.mu_args.a_key2 tup in
          let j =
            match Hashtbl.find_opt aux.mu_seq1 key with
            | None -> if aux.mu_args.a_pos then aux.mu_in_tp else aux.mu_out_tp
            | Some (j, _) -> max j aux.mu_out_tp
          in
          if j <= aux.mu_lb_tp then
            match Hashtbl.find_opt aux.mu_useq j with
            | None ->
                let tbl = Hashtbl.create 1 in
                Hashtbl.add tbl tup aux.mu_lb_tp;
                Hashtbl.add aux.mu_useq j tbl
            | Some tbl -> Hashtbl.replace tbl tup aux.mu_lb_tp
        )
        rel2
    end;
  if aux.mu_args.a_pos then
    begin
      Hashtbl.filter_map_inplace (fun key x ->
        if Relation.mem key rel1 then Some x else None) aux.mu_seq1;
      Relation.iter (fun key ->
        if not (Hashtbl.mem aux.mu_seq1 key) then
          Hashtbl.add aux.mu_seq1 key (aux.mu_in_tp, aux.mu_in_ts)
        ) rel1
    end
  else
    aux.mu_buf1 <- Some rel1

