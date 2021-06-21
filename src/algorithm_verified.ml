open MFOTL
open Verified_adapter
open Verified
open Helper
open Misc

let no_mw = ref false

module IntMap = Map.Make(struct type t = int let compare = Stdlib.compare end)
open IntMap

let rec string_of_term (t: Verified.Monitor.trm): string = begin match t with
| Var n -> "Var"
| Const c -> "Const"
| Plus (t1, t2) -> "Plus (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| Minus (t1, t2) -> "Minus (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| UMinus t -> "UMinus (" ^ (string_of_term t) ^ ")"
| Mult (t1, t2) -> "Mult (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| Div (t1, t2) -> "Div (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| Mod (t1, t2) -> "Mod (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| F2i t -> "F2i (" ^ (string_of_term t) ^ ")"
| I2f t -> "I2f (" ^ (string_of_term t) ^ ")"
end

let rec string_of_formula (f: Verified.Monitor.formula): string = begin match f with
| Pred (s, trms) -> "Pred '" ^ s ^ "'"
| Let (s, f1, f2) -> "Let " ^ s ^ " = (" ^ (string_of_formula f1) ^ ") in (" ^ (string_of_formula f2) ^")"
| Eq (t1, t2) -> "Eq (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| Less (t1, t2) -> "Less (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| LessEq (t1, t2) -> "LessEq (" ^ (string_of_term t1) ^ ") (" ^ (string_of_term t2) ^ ")"
| Neg f -> "Neg (" ^ (string_of_formula f) ^ ")"
| Or (f1, f2) -> "Or (" ^ (string_of_formula f1) ^ ") I (" ^ (string_of_formula f2) ^ ")"
| And (f1, f2) -> "And (" ^ (string_of_formula f1) ^ ") I (" ^ (string_of_formula f2) ^ ")"
| Ands fs -> "Ands (" ^ (String.concat ", " (List.map string_of_formula fs)) ^ ")"
| Exists f -> "Exists (" ^ (string_of_formula f) ^ ")"
| Agg (n, agg, m, t, f) -> ""
| Prev (i, f) -> "Prev I (" ^ (string_of_formula f) ^ ")"
| Next (i, f) -> "Next I (" ^ (string_of_formula f) ^ ")"
| Since (f1, i, f2) -> "Since (" ^ (string_of_formula f1) ^ ") I (" ^ (string_of_formula f2) ^ ")"
| Until (f1, i, f2) -> "Until (" ^ (string_of_formula f1) ^ ") I (" ^ (string_of_formula f2) ^ ")"
| Trigger (f1, i, f2) -> "Trigger (" ^ (string_of_formula f1) ^ ") I (" ^ (string_of_formula f2) ^ ")"
| Release (f1, i, f2) -> "Release (" ^ (string_of_formula f1) ^ ") I (" ^ (string_of_formula f2) ^ ")"
| MatchF (i, r) -> ""
| MatchP (i, r) -> ""
end

let monitor dbschema logfile f =
  let closed = (free_vars f = []) in
  let cf = convert_formula dbschema f in
  let _ = Printf.printf "%s\n" (string_of_formula cf); flush stdout in
  let cf = if !Misc.no_trigger then Verified.Monitor.rewrite_trigger cf else cf in
  let s = Verified.Monitor.mmonitorable_exec cf in
  let _ = if s then
	  (Printf.printf "ok\n"; flush stdout)
	else
	  (Printf.printf "not ok\n"; flush stdout)
  in
  let _ = Printf.printf "%s\n" (string_of_formula cf); flush stdout in
  let cf = if !no_mw then cf else Monitor.convert_multiway cf in
  let init_state = Monitor.minit_safe cf in
  let lexbuf = Log.log_open logfile in
  let init_i = 0 in
  let init_ts = MFOTL.ts_invalid in
  let rec loop state tpts tp ts =
    let finish () =
      if Misc.debugging Dbg_perf then
        Perf.check_log_end tp ts
    in
    if Misc.debugging Dbg_perf then
      Perf.check_log tp ts;
    match Log.get_next_entry lexbuf with
    | MonpolyCommand {c; parameters} -> finish ()
    | MonpolyTestTuple st -> finish ()
    | MonpolyError s -> finish ()
    | MonpolyData d ->
    if d.ts >= ts then
      begin
        (* let _ = Printf.printf "Last: %b TS: %f TP: %d !Log.TP: %d d.TP: %d\n" !Log.last d.ts tp !Log.tp d.tp in *)
        if !Misc.verbose then
          Printf.printf "At time point %d:\n%!" d.tp;
        let tpts = add d.tp d.ts tpts in
        let (vs, new_state) = Monitor.mstep (convert_db d) state in
        let vs = convert_violations vs in
        List.iter (fun (qtp, rel) ->
            let qts = find qtp tpts in
            if qts < MFOTL.ts_max then
              show_results closed d.tp qtp qts rel
          ) vs;
        let tpts = List.fold_left (fun map (qtp,_) -> remove qtp map) tpts vs in
        loop new_state tpts d.tp d.ts
      end
    else
      if !Misc.stop_at_out_of_order_ts then
        let msg = Printf.sprintf "[Algorithm.check_log] Error: OUT OF ORDER TIMESTAMP: %s \
                                  (last_ts: %s)" (MFOTL.string_of_ts d.ts) (MFOTL.string_of_ts ts) in
        failwith msg
      else
        let _ = Printf.eprintf "[Algorithm.check_log] skipping OUT OF ORDER TIMESTAMP: %s \
                          (last_ts: %s)\n%!" (MFOTL.string_of_ts d.ts) (MFOTL.string_of_ts ts) in
        loop state tpts tp ts
  in
  loop init_state empty init_i init_ts
