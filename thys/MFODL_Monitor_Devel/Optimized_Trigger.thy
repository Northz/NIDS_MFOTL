theory Optimized_Trigger
  imports
    Optimized_MTL_TEMP
begin

type_synonym ts = nat

record targs =
  targs_ivl :: \<I>
  targs_n :: nat (* max|L|, |R|), number of free variables *)
  targs_L :: "nat set" (* free variables of the lhs *)
  targs_R :: "nat set" (* free variables of the rhs *)

(* simply stores all tables for \<phi> and \<psi> in [0, b] *)
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"

definition init_targs :: "\<I> \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> targs" where
  "init_targs I n L R = \<lparr>targs_ivl = I, targs_n = n, targs_L = L, targs_R = R\<rparr>"

definition trigger_results :: "\<I> \<Rightarrow> ts \<Rightarrow> 'a mtaux \<Rightarrow> 'a table" where
  "trigger_results I cur auxlist = {
    tuple.
      \<comment> \<open>pretty much the definition of trigger\<close>
      (\<exists>t relL relR. (t, relL, relR) \<in> (set auxlist) \<and> mem I (cur - t) \<and> 
        \<comment> \<open>either \<psi> holds or there is a later database where the same tuple satisfies \<phi>\<close>
        (tuple \<in> relR \<or> (\<exists>t' relL' relR'. (t', relL', relR') \<in> (set auxlist) \<and> t < t' \<and> tuple \<in> relL'))
      )
}"

locale mtaux =
  fixes valid_mtaux :: "targs \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "targs \<Rightarrow> 'mtaux"
    and update_mtaux :: "targs \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "targs \<Rightarrow> 'mtaux \<Rightarrow> event_data table"

  (* the initial state should be valid *)
  assumes valid_init_mtaux: "(
    if (mem I 0)
      then
        L \<subseteq> R
      else 
        L = R
    ) \<Longrightarrow>
    let args = init_targs I n L R in
    valid_mtaux args 0 (init_mtaux args) []"

  (* assuming the previous state outputted the same result, the next will as well *)
  assumes valid_update_mtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (targs_n args) (targs_L args) relL \<Longrightarrow>
    table (targs_n args) (targs_R args) relR \<Longrightarrow>
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    valid_mtaux
      args
      cur
      (update_mtaux args nt relL relR aux)
      ((filter (\<lambda> (t, relL, relR). memR (targs_ivl args) (nt - t)) auxlist) @ [(nt, relL, relR)])
  "

  and valid_result_mtaux: "
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    result_mtaux args aux = trigger_results (targs_ivl args) cur auxlist
  "

type_synonym 'a mmtaux = "
  ts \<times>                                 \<comment> \<open>the newest timestamp\<close>
  bool list \<times>                          \<comment> \<open>maskL, i.e. all free variables of R \\ L are masked\<close>
  bool list \<times>                          \<comment> \<open>maskR, i.e. all free variables of L \\ R are masked\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_prev: all databases containing the tuples satisfying the lhs or the rhs where the timestamp doesn't yet satisfy memL\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_in: all databases containing the tuples satisfying the lhs or the rhs where the ts is in the interval\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_in for once\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_since for historically\<close>
  (('a tuple, ts) mapping)             \<comment> \<open>tuple_since for \<psi> S (\<psi> \<and> \<phi>)\<close>
"

definition ts_tuple_rel_binary :: "(ts \<times> 'a table \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple \<times> 'a tuple) set" where
  "ts_tuple_rel_binary ys = {(t, as, bs). \<exists>X Y. as \<in> X \<and> bs \<in> Y \<and> (t, X, Y) \<in> ys}"

definition valid_tuple :: "(('a tuple, ts) mapping) \<Rightarrow> (ts \<times> 'a tuple) \<Rightarrow> bool" where
  "valid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
  | Some t' \<Rightarrow> t \<ge> t')"

fun valid_mmtaux :: "targs \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since) ys \<longleftrightarrow>
    (targs_L args) \<subseteq> (targs_R args) \<and>
    maskL = join_mask (targs_n args) (targs_L args) \<and>
    maskR = join_mask (targs_n args) (targs_R args) \<and>
    (\<forall>(t, X, Y) \<in> set ys. table (targs_n args) (targs_R args) X \<and> table (targs_n args) (targs_L args) Y) \<and>
    table (targs_n args) (targs_R args) (Mapping.keys tuple_in_once) \<and>
    table (targs_n args) (targs_R args) (Mapping.keys tuple_since_hist) \<and>
    table (targs_n args) (targs_R args) (Mapping.keys tuple_since_since) \<and>
    (\<forall>as \<in> \<Union>((fst o snd) ` (set (linearize data_prev))). wf_tuple (targs_n args) (targs_R args) as) \<and>
    (\<forall>as \<in> \<Union>((snd o snd) ` (set (linearize data_prev))). wf_tuple (targs_n args) (targs_R args) as) \<and>
    cur = nt \<and>
     \<comment> \<open>ts_tuple_rel_binary (set ys) =
    {tas \<in> ts_tuple_rel_binary (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas} \<and>\<close>  \<comment> \<open>all tuples in data_prev and data_in have a (valid) entry in the mapping\<close>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (targs_ivl args) (nt - t)) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> memL (targs_ivl args) (nt - t)) \<and>
    valid_tuple_in ts_tuple_rel_binary data_in tuple_in (\<lambda>x. True) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since_hist. case Mapping.lookup tuple_since_hist as of Some t \<Rightarrow> t \<le> nt) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since_since. case Mapping.lookup tuple_since_since as of Some t \<Rightarrow> t \<le> nt)
  "

fun init_mmtaux :: "targs \<Rightarrow> event_data mmtaux" where
  "init_mmtaux args = (0, [], [], empty_queue, empty_queue, Mapping.empty, Mapping.empty, Mapping.empty)"

lemma valid_init_mtaux: "(
    if (mem I 0)
      then
        L \<subseteq> R
      else 
        L = R
    ) \<Longrightarrow>
    valid_mmtaux args 0 (init_mmtaux args) []"
  by (auto simp add: trigger_results_def)


fun result_mmtaux :: "targs \<Rightarrow> event_data mmtaux \<Rightarrow> event_data table" where
  "result_mmtaux args (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since) = 
  {}
"

(* tail recursive function to split a list into two based on a predicate while maintaining the order *)
fun split_list :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "split_list p [] t f = (t, f)"
| "split_list p (x#xs) t f = (if (p x) then split_list p xs (x#t) f else split_list p xs t (x#f))"




(*
fun valid_mmsaux :: "targs \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_mmsaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<longleftrightarrow>
    (targs_L args) \<subseteq> (targs_R args) \<and> \<comment> \<open>free variables of the lhs are a subset of the rhs\<close>
    maskL = join_mask (targs_n args) (targs_L args) \<and> \<comment> \<open>check if maskL & masR were computed correctly\<close>
    maskR = join_mask (targs_n args) (targs_R args) \<and>
    (\<forall>(t, X) \<in> set ys. table (targs_n args) (targs_R args) X) \<and> \<comment> \<open>check whether all tuples in ys are well-formed using the free variables of the rhs\<close>
    table (targs_n args) (targs_R args) (Mapping.keys tuple_in) \<and> \<comment> \<open>check if all tuples in tuple_in\<close>
    table (targs_n args) (targs_R args) (Mapping.keys tuple_since) \<and> \<comment> \<open>and tuple_since are well-formed\<close>
    \<comment> \<open> (\<forall>x\<in>X. wf_tuple n V x) \<close>
    (table (targs_n args) (targs_R args) (\<Union>(snd ` (set data_prev)))) \<and> \<comment> \<open>union all tables and check whether it's tuples are valid\<close>
    \<comment> \<open>(\<forall>as \<in> \<Union>(snd ` (set data_prev)). wf_tuple (targs_n args) (targs_R args) as) \<and> \<close>
    cur = nt \<and> \<comment> \<open>???\<close>
    ts_tuple_rel (set ys) = \<comment> \<open>all tuples with timestamp in ys = all tuples in data_prev and data_in\<close>
    {tas \<in> ts_tuple_rel (set data_prev \<union> set data_in). valid_tuple tuple_since tas} \<and>

    sorted (map fst data_prev) \<and> \<comment> \<open>data_prev should be sorted by timestamp\<close>
    (\<forall>t \<in> fst ` set data_prev. t \<le> nt \<and> \<not> memL (targs_ivl args) (nt - t)) \<and>
    \<comment> \<open>the ts cannot be in the future and by definition of data_prev, the timestamps shouldn't be in the interval yet\<close>
    sorted (map fst data_in) \<and> \<comment> \<open>data_prev should be sorted by timestamp\<close>
    (\<forall>t \<in> fst ` set data_in. t \<le> nt \<and> memL (targs_ivl args) (nt - t)) \<and>
    \<comment> \<open>the ts cannot be in the future and by definition of data_in, the timestamps should be in the interval\<close>

    \<comment> \<open>tuple_in should point to the latest entry of a given tuple in data_in (which aren't in the future)\<close>
    (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set data_in). valid_tuple tuple_since tas \<and> as = snd tas})
    ) \<and>
    \<comment> \<open>tuple_since can't be in the future\<close>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt)"
*)

end