open MFOTL
open Tuple

type args = {
  a_intv: interval;
  a_bounded: bool;
  a_pos: bool;
  a_prop1: bool;
  a_key2: int list;
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
  let matches = Table.get_matches attr2 attr1 in
  {
    ms_args = {
      a_intv = intv;
      a_bounded = not (infinite_interval intv);
      a_pos = pos;
      a_prop1 = (attr1 = []);
      a_key2 = List.map snd matches;
    };
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
          Hashtbl.remove aux.ms_since tup
        )
        discard;
      aux.ms_in <- Relation.diff aux.ms_in discard
    end;
  if not (in_left_ext (ts_minus aux.ms_t aux.ms_gc) aux.ms_args.a_intv) then
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
  Relation.iter (fun tup ->
    if not (Hashtbl.mem aux.ms_since tup) then
      Hashtbl.add aux.ms_since tup t
    ) rel;
  if in_right_ext ts_null aux.ms_args.a_intv then
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
  else
    Queue.add (t, rel) aux.ms_prevq

let result_msaux aux = aux.ms_in
