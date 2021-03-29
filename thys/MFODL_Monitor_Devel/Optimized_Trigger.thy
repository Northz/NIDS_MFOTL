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
  fixes init_mtaux :: "targs \<Rightarrow> 'mtaux"
    and update_mtaux :: "targs \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "targs \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data table"

  (* the initial state should be valid *)
  (* TODO: safe_formula definition *)
  assumes valid_init_mtaux: "L \<subseteq> R \<Longrightarrow>
    let args = init_targs I n L R in
    result_mtaux args 0 (init_mtaux args) = trigger_results I 0 []"

  (* assuming the previous state outputted the same result, the next will as well *)
  assumes valid_update_mtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (targs_n args) (targs_L args) relL \<Longrightarrow>
    table (targs_n args) (targs_R args) relR \<Longrightarrow>
    result_mtaux args cur aux = trigger_results (targs_ivl args) cur auxlist \<Longrightarrow>
    result_mtaux args cur (update_mtaux args nt relL relR aux) =
      trigger_results
        (targs_ivl args)
        cur
        ((filter (\<lambda> (t, relL, relR). memR (targs_ivl args) (nt - t)) auxlist) @ [(nt, relL, relR)])
  "

type_synonym 'a mmtaux = "
  ts \<times>                              \<comment> \<open>the newest timestamp\<close>
  bool list \<times>                       \<comment> \<open>maskL, i.e. all free variables of R \\ L are masked\<close>
  bool list \<times>                       \<comment> \<open>maskR, i.e. all free variables of L \\ R are masked\<close>
  (ts \<times> 'a table) list \<times>            \<comment> \<open>data_prev: all databases containing the tuples satisfying the trigger condition where the timestamp doesn't yet satisfy memL\<close>
  (ts \<times> 'a table) list \<times>            \<comment> \<open>data_in: all databases containing the tuples satisfying the trigger condition where the ts is in the interval\<close>
  nat \<times>                             \<comment> \<open>the length of data_in\<close>
  (('a tuple, nat) mapping)          \<comment> \<open>for every tuple the number of databases inside the interval satisfying the trigger condition\<close>
"



fun init_mmtaux :: "targs \<Rightarrow> event_data mmtaux" where
  "init_mmtaux args = (0, [], [], [], [], 0, Mapping.empty)"


fun result_mmtaux :: "targs \<Rightarrow> event_data mmtaux \<Rightarrow> event_data table" where
  "result_mmtaux args (nt, maskL, maskR, data_prev, data_in, data_in_count, tuple_sat_count) = 
  {tuple \<in> (Mapping.keys tuple_sat_count).
    case (Mapping.lookup tuple_sat_count tuple) of \<comment> \<open>return all tuples where the count is equal to data_in_count\<close>
      (Some n) \<Rightarrow> n = data_in_count
      | _ \<Rightarrow> False
  }
"

lemma valid_init_mtaux: "L \<subseteq> R \<Longrightarrow>
    (result_mmtaux (init_targs I n L R) (init_mmtaux (init_targs I n L R))) = (trigger_results I 0 [])"
  by (auto simp add: trigger_results_def)

(* tail recursive function to split a list into two based on a predicate while maintaining the order *)
fun split_list :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
  "split_list p [] t f = (t, f)"
| "split_list p (x#xs) t f = (if (p x) then split_list p xs (x#t) f else split_list p xs t (x#f))"

(*
   - move entries data_prev to data_in and remove entries from data_in
   - update data_in_count and tuple_sat_count accordingly
*)
fun remove_old_entries_mmtaux :: "targs \<Rightarrow> ts \<Rightarrow> event_data mmtaux \<Rightarrow> event_data mmtaux" where
  "remove_old_entries_mmtaux args t (nt, maskL, maskR, data_in, data_prev, data_in_count, tuple_sat_count) = (
    \<comment> \<open>split data_in based on whether the db is still in the interval\<close>
    \<comment> \<open>TODO: optimize. if sorted can stop early\<close>
    let (filtered_data_in, data_in_dropout) = split_list (\<lambda> (t, _).
      memR (targs_ivl args) (nt - t) \<comment> \<open>data_in satisfied memL so now remove the ones not satisfying memR anymore\<close>
    ) [] [] data_in in
    \<comment> \<open>split data_prev based on whether the db already is in the interval\<close>
    \<comment> \<open>TODO: optimize. if sorted can stop early\<close>
    let (data_prev_filtered, data_prev_dropout) = split_list (\<lambda> (t, _).
      memL (targs_ivl args) (nt - t) \<comment> \<open>split dbs on whether they're already in the interval\<close>
    ) [] [] data_prev in
    \<comment> \<open>from the ones that aren't before the lower boundary, remove those that directly drop out\<close>
    \<comment> \<open>TODO: optimize. if sorted can stop early\<close>
    let data_prev_move = filter (\<lambda> (t, _).
      memR (targs_ivl args) (nt -t) \<comment> \<open>drop databases that directly go from data_prev to outside the interval\<close>
    ) data_prev_dropout in
    \<comment> \<open>based on data_in_dropout and data_prev_move, update data_in_count and tuple_sat_count\<close>
    \<comment> \<open>first subtract one for all removed occurences of a tuple\<close>
    let (updated_count, updated_mapping) = foldr (\<lambda> (t, table) (count, mapping).
      (
        count - 1, \<comment> \<open>subtract one from the number of databases in the interval\<close>
        Finite_Set.fold (\<lambda> tuple mapping.
          case (Mapping.lookup mapping tuple)
            of (Some n) \<Rightarrow>
              if n = 1 then \<comment> \<open>instead of setting a value in the mapping to zero, we can simply remove it\<close>
                Mapping.delete tuple mapping
              else
                Mapping.update tuple (n-1) mapping
            | _ \<Rightarrow> undefined \<comment> \<open>crash since the mapping should contain the tuple because of the invariant\<close>
          ) mapping table
      )
    ) data_in_dropout (data_in_count, tuple_sat_count) in
    \<comment> \<open>next add one for all added occurences of a tuple\<close>
    let (updated_count, updated_mapping) = foldr (\<lambda> (t, table) (count, mapping).
      (
        count + 1, \<comment> \<open>add one to the number of databases in the interval\<close>
        Finite_Set.fold (\<lambda> tuple mapping.
          Mapping.update tuple (
            case (Mapping.lookup mapping tuple)
              of (Some n) \<Rightarrow> n+1
              | _ \<Rightarrow> 1 \<comment> \<open>if the tuple wasn't present yet, set it's value to one\<close>
          ) mapping
        ) mapping table
      )
    ) data_prev_move (updated_count, updated_mapping) in
    (t, maskL, maskR, filtered_data_in @ data_prev_move, data_prev_filtered, updated_count, updated_mapping)
  )"

(*
   - add new table to data_in / data_prev
   - add tuples for which relL / \<phi> is satisfied to all dbs and set their counts to data_in_count
*)
fun add_new_table :: "targs \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> event_data mmtaux \<Rightarrow> event_data mmtaux" where
  "add_new_table args relL relR (nt, maskL, maskR, data_in, data_prev, data_in_count, tuple_sat_count) = (
    \<comment> \<open>add the new table to data_in or data_prev depending on whether 0 is in the interval
       if 0 is in the interval, also update tuple_sat_count\<close>
    let (data_in, data_prev, data_in_count, tuple_sat_count) = (
      if (mem (targs_ivl args) 0) then
        (case (data_in) of
            ([]) \<Rightarrow> (
              [(nt, relR)], \<comment> \<open>is the first entry\<close>
              data_prev,
              data_in_count+1,
              Finite_Set.fold (\<lambda> tuple mapping.
                Mapping.update tuple (
                case (Mapping.lookup mapping tuple)
                  of (Some n) \<Rightarrow> n+1
                  | _ \<Rightarrow> 1 \<comment> \<open>if the tuple wasn't present yet, set it's value to one\<close>
                ) mapping
              ) tuple_sat_count relR \<comment> \<open>add one for all tuples satisfying the rhs\<close>
            )
          | ((t', rel')#xs) \<Rightarrow> (
             \<comment> \<open>if the ts of the last db is the same, merge the databases\<close>
            if (t' = nt) then
              ((t', rel' \<union> relR)#xs, data_prev, data_in_count, tuple_sat_count)
            else
              (
                (nt, relR)#data_in,
                data_prev,
                data_in_count,
                \<comment> \<open>a new db was added to data_in and 0 is in the interval, hence update tuple_sat_count\<close>
                (Finite_Set.fold (\<lambda> tuple mapping.
                  Mapping.update tuple (
                  case (Mapping.lookup mapping tuple)
                    of (Some n) \<Rightarrow> n+1
                    | _ \<Rightarrow> 1 \<comment> \<open>if the tuple wasn't present yet, set it's value to one\<close>
                  ) mapping
                ) tuple_sat_count relR \<comment> \<open>add one for all tuples satisfying the rhs\<close>)
            )
          )
        )
      else
        (case data_prev of
          \<comment> \<open>if the ts of the last db is the same, merge them\<close>
            ([])   \<Rightarrow> (data_in, (nt, relR)#data_prev, data_in_count, tuple_sat_count)
          | ((t', rel')#xs) \<Rightarrow> (data_in, (t', rel' \<union> relR)#xs, data_in_count, tuple_sat_count)
        )
    ) in
     \<comment> \<open>independent of the interval, for all tuples that satisfy \<phi>, set tuple_sat_count to data_in_count
        and add the tuple to all entries in data_in and data_prev s.t. the count is reduced when
        the respective table is removed\<close>
    \<comment> \<open>TODO: optimize somehow\<close>
    let data_in = map (\<lambda> (t, table). (t, table \<union> relL)) data_in in
    let data_prev = map (\<lambda> (t, table). (t, table \<union> relL)) data_prev in
    let tuple_sat_count = Finite_Set.fold (\<lambda> tuple mapping.
      \<comment> \<open>simply set the entries for which \<phi> holds to data_in_count \<close>
      Mapping.update tuple data_in_count mapping
    ) tuple_sat_count relL in
    (nt, maskL, maskR, data_in, data_prev, data_in_count, tuple_sat_count)
  )"

fun update_mmtaux :: "targs \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> event_data mmtaux \<Rightarrow> event_data mmtaux" where
  "update_mmtaux args t relL relR aux = (
    let aux = remove_old_entries_mmtaux args t aux in
    let aux = add_new_table args relL relR aux in
    aux
  )"



lemma valid_update_mmtaux:
  assumes "nt \<ge> cur"
  assumes "table (args_n args) (args_L args) relL"
  assumes "table (args_n args) (args_R args) relR"
  assumes aux_def:  "aux = (nt, maskL, maskR, data_in, data_prev, data_in_count, tuple_sat_count)"
  assumes aux'_def: "aux' = (nt', maskL', maskR', data_in', data_prev', data_in_count', tuple_sat_count')"
                    "aux' = (update_mmtaux args nt relL relR aux)"
  assumes IH: "result_mmtaux args aux = trigger_results (targs_ivl args) cur auxset"
  shows "result_mmtaux args aux' =
      trigger_results
        (targs_ivl args)
        nt
        ({(t, relL, relR) \<in> auxset. memR (targs_ivl args) (nt - t)} \<union> {(nt, relL, relR)})"
proof -
  define I where "I = targs_ivl args"
  define auxset' where "auxset' = {(t, relL, relR) \<in> auxset. memR I (nt - t)} \<union> {(nt, relL, relR)}"
  {
    fix tuple
    assume "tuple \<in> result_mmtaux args aux'"
    then have tuple_props: "tuple \<in> (Mapping.keys tuple_sat_count')"
      "(case (Mapping.lookup tuple_sat_count' tuple) of
        (Some n) \<Rightarrow> n = data_in_count'
        | _ \<Rightarrow> False)"
      using aux'_def by auto
    then obtain n where n_props: "Mapping.lookup tuple_sat_count' tuple = Some n" "n = data_in_count'"
      using case_optionE
      by blast
    then have "tuple \<in> (trigger_results (targs_ivl args) nt auxset')"
    proof (cases "tuple \<in> result_mmtaux args aux")
      case True
      then have "tuple \<in> trigger_results (targs_ivl args) cur auxset" using IH by auto
      then have "\<exists>t relL relR. (t, relL, relR) \<in> auxset \<and> mem I (cur - t) \<and> 
        (tuple \<in> relR \<or> (\<exists>t' relL' relR'. (t', relL', relR') \<in> auxset \<and> t < t' \<and> tuple \<in> relL'))"
        using I_def
        by (auto simp add: trigger_results_def)
      then obtain t relL relR where rel_props: "(t, relL, relR) \<in> auxset" "mem I (cur - t)"
        "tuple \<in> relR \<or> (\<exists>t' relL' relR'. (t', relL', relR') \<in> auxset \<and> t < t' \<and> tuple \<in> relL')"
        by blast
      show ?thesis
      proof (cases "memR I (nt - t)")
        case True
        then have "memR I (nt - t)" by auto
        then have mem: "mem I (nt - t)" using assms(1) rel_props(2) by auto
        then have set: "(t, relL, relR) \<in> auxset'" using rel_props(1) auxset'_def by auto
        {
          assume "tuple \<in> relR"
          then have "\<exists>t relL relR. (t, relL, relR) \<in> auxset' \<and> memL I (nt - t) \<and> memR I (nt - t) \<and> 
          (tuple \<in> relR \<or> (\<exists>t' relL' relR'. (t', relL', relR') \<in> auxset' \<and> t < t' \<and> tuple \<in> relL'))"
            using mem set
            by auto
        }
        moreover {
          assume "\<exists>t' relL' relR'. (t', relL', relR') \<in> auxset \<and> t < t' \<and> tuple \<in> relL'"
          then obtain t' relL' relR' where rel'_props: "(t', relL', relR') \<in> auxset \<and> t < t' \<and> tuple \<in> relL'" by blast
          then have "memR I (nt - t')" using mem assms(1) by auto
          then have "(t', relL', relR') \<in> auxset'" using rel'_props(1) auxset'_def by auto
          then have "\<exists>t relL relR. (t, relL, relR) \<in> auxset' \<and> memL I (nt - t) \<and> memR I (nt - t) \<and> 
          (tuple \<in> relR \<or> (\<exists>t' relL' relR'. (t', relL', relR') \<in> auxset' \<and> t < t' \<and> tuple \<in> relL'))"
            using set mem rel'_props by blast
        }
        ultimately have "\<exists>t relL relR. (t, relL, relR) \<in> auxset' \<and> memL I (nt - t) \<and> memR I (nt - t) \<and> 
        (tuple \<in> relR \<or> (\<exists>t' relL' relR'. (t', relL', relR') \<in> auxset' \<and> t < t' \<and> tuple \<in> relL'))"
          using rel_props(3)
          by blast
        then show ?thesis using I_def by (auto simp add: trigger_results_def)
      next
        case notMem: False
        have "mem I (cur - t)" using rel_props by auto
        then show ?thesis sorry
      qed
    next
      case False
      then show ?thesis sorry
    qed
  }
  moreover {
    fix t
    assume "t \<in> (trigger_results (targs_ivl args) nt auxset')"
    then have "t \<in> result_mmtaux args (update_mmtaux args nt relL relR aux)"
      sorry
  }
  ultimately show ?thesis
    using assms auxset'_def I_def
    by blast
qed

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