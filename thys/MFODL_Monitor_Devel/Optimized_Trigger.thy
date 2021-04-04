theory Optimized_Trigger
  imports
    Optimized_MTL_TEMP
begin

type_synonym ts = nat

(* simply stores all tables for \<phi> and \<psi> in [0, b] *)
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"

fun trigger_results :: "\<I> \<Rightarrow> ts \<Rightarrow> 'a mtaux \<Rightarrow> 'a table" where
  "trigger_results I cur auxlist = {
    tuple.
      (length (filter (\<lambda> (t, _, _). mem I (cur - t)) auxlist) > 0) \<and>
      \<comment> \<open>pretty much the definition of trigger\<close>
      (\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem I (cur - t) \<longrightarrow> 
        \<comment> \<open>either \<psi> holds or there is a later database where the same tuple satisfies \<phi>\<close>
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            let (t', l', r') = auxlist!j in
            tuple \<in> l' \<comment> \<open>t < t' is given as the list is sorted\<close>
          )
        )
      )
}"

locale mtaux =
  fixes valid_mtaux :: "args \<Rightarrow> ts \<Rightarrow> 'mtaux \<Rightarrow> event_data mtaux \<Rightarrow> bool"
    and init_mtaux :: "args \<Rightarrow> 'mtaux"
    and update_mtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'mtaux \<Rightarrow> 'mtaux"
    and result_mtaux :: "args \<Rightarrow> 'mtaux \<Rightarrow> event_data table"

  (* the initial state should be valid *)
  assumes valid_init_mtaux: "(
    if (mem I 0)
      then
        L \<subseteq> R
      else 
        L = R
    ) \<Longrightarrow>
    let args = init_args I n L R false in
    valid_mtaux args 0 (init_mtaux args) []"

  (* assuming the previous state outputted the same result, the next will as well *)
  assumes valid_update_mtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (args_n args) (args_L args) l \<Longrightarrow>
    table (args_n args) (args_R args) r \<Longrightarrow>
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    valid_mtaux
      args
      nt
      (update_mtaux args nt l r aux)
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "

  and valid_result_mtaux: "
    valid_mtaux args cur aux auxlist \<Longrightarrow>
    result_mtaux args aux = trigger_results (args_ivl args) cur auxlist
  "

type_synonym 'a mmtaux = "
  ts \<times>                                 \<comment> \<open>the newest timestamp\<close>
  bool list \<times>                          \<comment> \<open>maskL, i.e. all free variables of R \\ L are masked\<close>
  bool list \<times>                          \<comment> \<open>maskR, i.e. all free variables of L \\ R are masked\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_prev: all databases containing the tuples satisfying the lhs or the rhs where the timestamp doesn't yet satisfy memL\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_in: all databases containing the tuples satisfying the lhs or the rhs where the ts is in the interval\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_in for once\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_since for historically\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_since for \<psi> S (\<psi> \<and> \<phi>)\<close>
  ('a table)                            \<comment> \<open>the set of tuples currently satisfying trigger\<close>
"

fun mmtaux_data_prev :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue" where
  "mmtaux_data_prev (_, _, _, data_prev, _) = data_prev"

fun mmtaux_data_in :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue" where
  "mmtaux_data_in (_, _, _, _, data_in, _) = data_in"

fun time :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> ts" where
  "time db = fst db"

fun relL :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relL db = (fst o snd) db"

fun relR :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relR db = (snd o snd) db"

definition ts_tuple_rel_binary :: "(ts \<times> 'a table \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple \<times> 'a tuple) set" where
  "ts_tuple_rel_binary ys = {(t, as, bs). \<exists>X Y. as \<in> X \<and> bs \<in> Y \<and> (t, X, Y) \<in> ys}"

abbreviation "ts_tuple_rel_binary_lhs ys \<equiv> ts_tuple_rel_f ys fst"
abbreviation "ts_tuple_rel_binary_rhs ys \<equiv> ts_tuple_rel_f ys snd"

definition auxlist_data_prev :: "args \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_prev args auxlist = filter (\<lambda>(t, _, _). \<not>memL (args_ivl args) t) auxlist"

definition auxlist_data_in :: "args \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_in args auxlist = filter (\<lambda>(t, _, _). mem (args_ivl args) t) auxlist"

fun valid_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist \<longleftrightarrow>
    (if mem (args_ivl args) 0 then (args_L args) \<subseteq> (args_R args) else (args_L args) = (args_R args)) \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, X, Y) \<in> set auxlist. table (args_n args) (args_R args) X \<and> table (args_n args) (args_L args) Y) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_in_once) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since_hist) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since_since) \<and>
    (\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    (\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    cur = mt \<and>
    \<comment> \<open>all valid lhs/\<phi> tuples in data_prev should have a valid entry in tuple_in_once, as it is shifted\<close>
    ts_tuple_rel_binary_lhs (set (auxlist_data_prev args auxlist)) =
    {(t, l). \<exists>r. (t, l, r) \<in> ts_tuple_rel_binary (set (linearize data_prev)) \<and>
    valid_tuple tuple_in_once (t, l)} \<and>
    \<comment> \<open>all valid rhs/\<psi> tuples in data_in should have a valid entry in tuple_since_hist, as it is shifted\<close>
    ts_tuple_rel_binary_rhs (set (auxlist_data_in args auxlist)) =
    {(t, r). \<exists>l. (t, l, r) \<in> ts_tuple_rel_binary (set (linearize data_in)) \<and>
    valid_tuple tuple_since_hist (t, r)} \<and>
    \<comment> \<open>all valid \<phi>\<and>\<psi> tuples in data_in should have a valid entry in tuple_since_since, as it is shifted\<close>
    ts_tuple_rel_binary (set (auxlist_data_in args auxlist)) =
    {(t, l, r) \<in> ts_tuple_rel_binary (set (linearize data_in)).
    valid_tuple tuple_since_since (t, l) \<and> valid_tuple tuple_since_since (t, r)} \<and>
    \<comment> \<open>the entries stored should be the same, hence they're sorted as well\<close>
    sorted (map fst auxlist) \<and>
    auxlist = (linearize data_in) @ (linearize data_prev) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> mt \<and> \<not> memL (args_ivl args) (mt - t)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> mt \<and> mem (args_ivl args) (mt - t)) \<and>
     \<comment> \<open>check whether tuple_in once contains the newest occurence of the tuple satisfying the lhs\<close>
    newest_tuple_in_mapping fst data_in tuple_in_once (\<lambda>x. True) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since_hist. case Mapping.lookup tuple_since_hist as of Some t \<Rightarrow> t \<le> mt) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since_since. case Mapping.lookup tuple_since_since as of Some t \<Rightarrow> t \<le> mt) \<and>
     \<comment> \<open>conditions for sat / trigger conditions\<close>
    (\<forall>tuple. tuple \<in> sat \<longleftrightarrow>
      (set (linearize data_in) \<noteq> {}) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
        (\<forall>i \<in> {0..<(length (linearize data_in))}.
          let (t, l, r) = (linearize data_in)!i in
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length (linearize data_in))}.
            let (t', l', r') = (linearize data_in)!j in
            tuple \<in> l'
          )
        ) \<or>
        (\<exists>(t, l, r) \<in> set (linearize data_prev).
          tuple \<in> l
        )
      )
    )
  "

definition init_mmtaux :: "args \<Rightarrow> 'a mmtaux" where
  "init_mmtaux args = (0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue, Mapping.empty, Mapping.empty, Mapping.empty, {})"

lemma valid_init_mtaux: "(
    if (mem I 0)
      then
        L \<subseteq> R
      else 
        L = R
    ) \<Longrightarrow>
    let args = init_args I n L R false in
    valid_mmtaux args 0 (init_mmtaux args) []"
  unfolding init_mmtaux_def
  by (auto simp add: init_args_def empty_queue_rep
      Mapping.lookup_empty safe_max_def table_def newest_tuple_in_mapping_def
      ts_tuple_rel_binary_def ts_tuple_rel_f_def
      auxlist_data_prev_def auxlist_data_in_def)

(* analogous to add_new_ts_mmsaux' except that tuple_in doesn't exist / isn't updated *)
fun add_new_ts_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mmtaux" where
  "add_new_ts_mmtaux args nt (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) = (
    let I = args_ivl args;
     \<comment> \<open>split into the part that still is data_prev and the dbs that are no longer before I\<close>
    (data_prev, move) = takedropWhile_queue (\<lambda>(t, _). memL I (nt - t)) data_prev;
     \<comment> \<open>next the data from data_prev that is larger than the lower boundary is appended to data_in\<close>
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    \<comment> \<open>next the data from data_prev that is larger than the lower boundary is appended to data_in\<close>
    (data_in, drop) = takedropWhile_queue (\<lambda>(t, _). memR I (nt - t)) data_in
    in
    (
      nt,                  \<comment> \<open>update ts\<close>
      maskL,               \<comment> \<open>keep masks\<close>
      maskR,
      data_prev,           \<comment> \<open>updated according to I\<close>
      data_in,             \<comment> \<open>updated according to I\<close>
      tuple_in_once,       \<comment> \<open>kept as we only do operations regarding the new ts here and 
                              this mapping should only be updated for the new db\<close>
      tuple_since_hist,    \<comment> \<open>kept\<close>
      tuple_since_since,   \<comment> \<open>kept\<close>
      sat                  \<comment> \<open>kept\<close>
    )
  )"

lemma valid_add_new_ts_mmtaux:
  assumes "nt \<ge> cur"
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  shows "valid_mmtaux
      args
      nt
      (add_new_ts_mmtaux args nt (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat))
      (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)
  "
proof -
  define I where "I = args_ivl args"
  
  have aux_valid: "(if mem (args_ivl args) 0 then (args_L args) \<subseteq> (args_R args) else (args_L args) = (args_R args))"
    "maskL = join_mask (args_n args) (args_L args)"
    "maskR = join_mask (args_n args) (args_R args)"
    "(\<forall>(t, X, Y) \<in> set auxlist. table (args_n args) (args_R args) X \<and> table (args_n args) (args_L args) Y)"
    "table (args_n args) (args_R args) (Mapping.keys tuple_in_once)"
    "table (args_n args) (args_R args) (Mapping.keys tuple_since_hist)"
    "table (args_n args) (args_R args) (Mapping.keys tuple_since_since)"
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    "cur = mt"
    "ts_tuple_rel_binary_lhs (set (auxlist_data_prev args auxlist)) =
    {(t, l). \<exists>r. (t, l, r) \<in> ts_tuple_rel_binary (set (linearize data_prev)) \<and>
    valid_tuple tuple_in_once (t, l)}"
    "ts_tuple_rel_binary_rhs (set (auxlist_data_in args auxlist)) =
    {(t, r). \<exists>l. (t, l, r) \<in> ts_tuple_rel_binary (set (linearize data_in)) \<and>
    valid_tuple tuple_since_hist (t, r)}"
    "ts_tuple_rel_binary (set (auxlist_data_in args auxlist)) =
    {(t, l, r) \<in> ts_tuple_rel_binary (set (linearize data_in)).
    valid_tuple tuple_since_since (t, l) \<and> valid_tuple tuple_since_since (t, r)}"
    "sorted (map fst auxlist)"
    "auxlist = (linearize data_in) @ (linearize data_prev)"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> mt \<and> \<not> memL (args_ivl args) (mt - t))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> mt \<and> mem (args_ivl args) (mt - t))"
    "newest_tuple_in_mapping fst data_in tuple_in_once (\<lambda>x. True)"
    "(\<forall>as \<in> Mapping.keys tuple_since_hist. case Mapping.lookup tuple_since_hist as of Some t \<Rightarrow> t \<le> mt)"
    "(\<forall>as \<in> Mapping.keys tuple_since_since. case Mapping.lookup tuple_since_since as of Some t \<Rightarrow> t \<le> mt)"
    "(\<forall>tuple. tuple \<in> sat \<longleftrightarrow>
      (set (linearize data_in) \<noteq> {}) \<and> (
        (\<forall>i \<in> {0..<(length (linearize data_in))}.
          let (t, l, r) = (linearize data_in)!i in
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length (linearize data_in))}.
            let (t', l', r') = (linearize data_in)!j in
            tuple \<in> l'
          )
        ) \<or>
        (\<exists>(t, l, r) \<in> set (linearize data_prev).
          tuple \<in> l
        )
      )
    )" using assms(2) by auto
  (*define aux' where "aux' = (add_new_ts_mmtaux args nt aux)"
  define data_prev' where "data_prev' = mmtaux_data_prev aux'"
  define data_in' where "data_in' = mmtaux_data_prev aux'"

  define auxlist' where "auxlist' = filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist"


  then have "valid_mmtaux args nt aux' auxlist'" by auto*)
  then show ?thesis by auto
qed


fun update_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mmtaux" where
  "update_mmtaux args nt l r (cur, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) =


  (
    nt,
    maskL,
    maskR,
    data_prev,
    data_in,
    tuple_in_once,
    tuple_since_hist,
    tuple_since_since,
    sat
  )"

lemma valid_update_mmtaux: "
    nt \<ge> cur \<Longrightarrow>
    table (args_n args) (args_L args) l \<Longrightarrow>
    table (args_n args) (args_R args) r \<Longrightarrow>
    valid_mmtaux args cur aux auxlist \<Longrightarrow>
    valid_mmtaux
      args
      nt
      (update_mmtaux args nt l r aux)
      ((filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist) @ [(nt, l, r)])
  "
  by auto

fun result_mmtaux :: "args \<Rightarrow> event_data mmtaux \<Rightarrow> event_data table" where
  "result_mmtaux args (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) = 
  sat
"

lemma data_in_mem:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "db \<in> set (linearize data_in)"
  shows "mem (args_ivl args) (nt - (time db))"
  using assms by auto

lemma data_prev_mem:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "db \<in> set (linearize data_prev)"
  shows "\<not>memL (args_ivl args) (nt - (time db))"
  using assms by auto

lemma auxlist_mem_data_in:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "db \<in> (set auxlist)"
  assumes "mem (args_ivl args) (nt - (time db))"
  shows "db \<in> set (linearize data_in)"
proof -
  have "db \<in> set (linearize data_in) \<or> db \<in> set (linearize data_prev)"
    using assms by auto
  moreover have "db \<in> set (linearize data_prev) \<Longrightarrow> False"
  using data_prev_mem[OF assms(1)] assms(3)
    by auto
  ultimately have "db \<in> set (linearize data_in)" by auto
  then show ?thesis by blast
qed

lemma data_sorted:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  shows "sorted (map fst (linearize data_prev))" "sorted (map fst (linearize data_in))"
proof -
  from assms have "sorted (map fst auxlist)"
    by auto
  moreover from assms have "auxlist = (linearize data_in) @ (linearize data_prev)"
    by auto
  ultimately show "sorted (map fst (linearize data_prev))" "sorted (map fst (linearize data_in))"
    using sorted_append by auto
qed

lemma auxlist_index_time_mono:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "i \<le> j" "j \<in> {0..<(length auxlist)}"
  shows "fst (auxlist!i) \<le> fst (auxlist!j)"
proof -
  from assms have "sorted (map fst auxlist)" by auto
  then have sorted: "\<forall>i. \<forall>j \<in> {0..<(length auxlist)}.
    i \<le> j \<longrightarrow> fst (auxlist!i) \<le> fst (auxlist!j)"
    by (simp add: sorted_iff_nth_mono)
  then show "fst (auxlist!i) \<le> fst (auxlist!j)"
    using sorted assms(2-3)
    by auto
qed

lemma auxlist_time_index_strict_mono:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "i \<in> {0..<(length auxlist)}"
  assumes "fst (auxlist!i) < fst (auxlist!j)" (* t < t' *)
  shows "i < j"
proof -
    {
      assume assm: "j \<le> i"
      then have "False"
        using auxlist_index_time_mono[OF assms(1) assm assms(2)] assms(3)
        by auto
    }
    then show "i < j" using le_def by blast
  qed

lemma data_prev_auxlist_index:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "i \<in> {0..<(length (linearize data_prev))}"
  shows "auxlist!((length (linearize data_in)) + i) = (linearize data_prev)!i" "(length (linearize data_in)) + i < (length auxlist)"
proof -
  from assms(1) have "auxlist = (linearize data_in) @ (linearize data_prev)" by auto
  then show "auxlist!((length (linearize data_in)) + i) = (linearize data_prev)!i"
    using nth_append_length_plus
    by blast
next
  from assms(1) have "auxlist = (linearize data_in) @ (linearize data_prev)" by auto
  then show "(length (linearize data_in)) + i < (length auxlist)" using assms(2) by auto
qed

lemma data_prev_auxlist_index_rev:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "i \<in> {(length (linearize data_in))..<(length auxlist)}"
  shows "auxlist!i = (linearize data_prev)!(i - (length (linearize data_in)))"
        "i - (length (linearize data_in)) < (length (linearize data_prev))"
proof -
  from assms(1) have "auxlist = (linearize data_in) @ (linearize data_prev)" by auto
  then show "auxlist!i = (linearize data_prev)!(i - (length (linearize data_in)))"
    using assms(2)
  by (simp add: nth_append)
next
  from assms(1) have "auxlist = (linearize data_in) @ (linearize data_prev)" by auto
  then show "i - (length (linearize data_in)) < (length (linearize data_prev))"
    using assms(2)
    by auto
qed

lemma data_prev_set_mem:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "i \<in> {(length (linearize data_in))..<(length auxlist)}"
  shows "auxlist!i \<in> set (linearize data_prev)"
proof - 
  have "auxlist!i = (linearize data_prev)!(i - (length (linearize data_in)))"
       "i - (length (linearize data_in)) < (length (linearize data_prev))"
    using data_prev_auxlist_index_rev[OF assms(1) assms(2)] by auto
  then show ?thesis by simp
qed

lemma data_in_auxlist_index:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  assumes "i \<in> {0..<(length (linearize data_in))}"
  shows "auxlist!i = (linearize data_in)!i" "i < length (auxlist)" "auxlist!i \<in> set (linearize data_in)"
proof -
  from assms(1) have "auxlist = (linearize data_in) @ (linearize data_prev)" by auto
  then show "auxlist!i = (linearize data_in)!i" "i < length (auxlist)" "auxlist!i \<in> set (linearize data_in)"
    using nth_append[of "(linearize data_in)" "(linearize data_prev)" i] assms(2)
    by auto
qed

lemma data_in_auxlist_nonempty:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  shows "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist) > 0) = (set (linearize data_in) \<noteq> {})"
proof (rule iffI)
  assume assm: "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist) > 0"
  {
    assume empty: "set (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist) = {}"
    {
      assume "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist) > 0"
      then have "\<exists>x. x \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist)"
        using nth_mem by blast
      then have "False" using empty by auto
    }
    then have "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist) = 0"
      by auto
    then have "False" using assm by auto
  }
  then obtain db where db_props: "db \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist)"
    by auto
  then have "db \<in> set auxlist" "mem (args_ivl args) (nt - fst db)" by auto
  then have "db \<in> set (linearize data_in)" using auxlist_mem_data_in[OF assms(1)] by auto
  then show "set (linearize data_in) \<noteq> {}" by auto
  next
    assume "set (linearize data_in) \<noteq> {}"
    then obtain db where db_props: "db \<in> set (linearize data_in)" by (meson nonemptyE)
    then have db_mem: "db \<in> set auxlist" using assms(1) by auto
    then have "mem (args_ivl args) (nt - fst db)"
      using data_in_mem[OF assms(1)] db_props
      by auto
    then have "db \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist)"
      using db_mem
      by auto
    then show auxlist_nonempty: "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist) > 0)"
      using length_pos_if_in_set[of db "filter (\<lambda> (t, _, _). mem (args_ivl args) (nt - t)) auxlist"]
      by auto
  qed

lemma valid_result_mmtaux: 
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) auxlist"
  shows "result_mmtaux args (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat) = trigger_results (args_ivl args) cur auxlist"
proof -
  define aux where "aux = (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, tuple_since_since, sat)"
  define I where "I = args_ivl args"
  from assms(1) have time: "nt = cur" by auto
  {
    fix tuple
    assume "tuple \<in> result_mmtaux args aux"
    then have mem_sat: "tuple \<in> sat" using aux_def by auto
    then have "set (linearize data_in) \<noteq> {}" using assms(1) by auto
    then have auxlist_nonempty: "(length (filter (\<lambda> (t, _, _). mem I (nt - t)) auxlist) > 0)"
      using data_in_auxlist_nonempty[OF assms(1)] I_def
      by auto
    then have "(\<forall>i \<in> {0..<(length (linearize data_in))}.
        let (t, l, r) = (linearize data_in)!i in
        tuple \<in> r \<or>
        (\<exists>j \<in> {i<..<(length (linearize data_in))}.
          let (t', l', r') = (linearize data_in)!j in
          tuple \<in> l'
        )
      ) \<or>
      (\<exists>(t, l, r) \<in> set (linearize data_prev).
        tuple \<in> l
      )" using mem_sat assms
      by auto
    moreover {
      assume "\<exists>(t, l, r) \<in> set (linearize data_prev). tuple \<in> l"
      then obtain t l r where 
          db_props: "(t, l, r) \<in> set (linearize data_prev)"
          "tuple \<in> l"
        by blast
      then have "\<not>memL I (nt - t)"
        using I_def data_prev_mem[OF assms(1)]
        by auto
      then have int: "\<forall>t'. mem I (nt - t') \<longrightarrow> t' < t"
        by (meson diff_le_mono2 leI memL_mono)
      have auxlist_mem: "(t, l, r) \<in> set auxlist"
        using db_props assms
        by auto
      then obtain j where j_props: "(t, l, r) = auxlist!j" "j <(length auxlist)"
        using in_set_conv_nth[of "(t, l, r)" auxlist] by force
      then have t_props: "t = fst ((auxlist)!j)"
        by (metis eq_fst_iff)
      {
        fix i
        assume i_props: "i \<in> {0..<(length auxlist)}"
        define dbi where "dbi = auxlist!i"
        define t' where "t' = fst dbi"
        define l' where "l' = relL dbi"
        define r' where "r' = relR dbi"
        assume "mem I (nt - t')"
        then have "t' < t" using int by auto
        then have "i < j"
          using auxlist_time_index_strict_mono[OF assms(1) i_props] dbi_def t'_def t_props
          by auto
        then have "(\<exists>j \<in> {i<..<(length auxlist)}.
          let (t', l', r') = auxlist!j in
          tuple \<in> l'
        )" using i_props j_props db_props(2) by force
      }
      then have "(\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem I (nt - t) \<longrightarrow> (\<exists>j \<in> {i<..<(length auxlist)}.
          let (t', l', r') = auxlist!j in
          tuple \<in> l'
        )
      )" by auto
      then have "tuple \<in> trigger_results I nt auxlist"
        using auxlist_nonempty
        by auto
    }
    moreover {
      assume assm: "(\<forall>i \<in> {0..<(length (linearize data_in))}.
        let (t, l, r) = (linearize data_in)!i in
        tuple \<in> r \<or>
        (\<exists>j \<in> {i<..<(length (linearize data_in))}.
          let (t', l', r') = (linearize data_in)!j in
          tuple \<in> l'
        )
      )"
      {
        assume hist: "\<forall>i \<in> {0..<(length (linearize data_in))}.
        let (t, l, r) = (linearize data_in)!i in
        tuple \<in> r"
        {
          fix i
          define dbi where "dbi = auxlist!i"
          define t where "t = time dbi"
          define l where "l = relL dbi"
          define r where "r = relR dbi"
          assume i_props: "i \<in> {0..<(length auxlist)}" "mem I (nt - t)"
          {
            assume "i \<ge> (length (linearize data_in))"
            then have "dbi \<in> set (linearize data_prev)"
              using data_prev_set_mem[OF assms(1)] i_props dbi_def
              by auto
            then have "\<not>memL I (nt - t)"
              using data_prev_mem[OF assms(1)] t_def I_def
              by auto
          }
          then have i_le: "i < (length (linearize data_in))" using i_props(2) le_def by blast
          moreover have "(linearize data_in)!i = auxlist!i"
            using i_le data_in_auxlist_index[OF assms(1)]
            by auto
          ultimately have
            "i \<in> {0..<(length (linearize data_in))}"
            "(t, l, r) = (linearize data_in)!i"
            using t_def l_def r_def dbi_def
            by auto
          then have "tuple \<in> r" using hist by fastforce
        }
        then have "\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem I (nt - t) \<longrightarrow> tuple \<in> r"
          by (simp add: case_prod_beta')
        then have "tuple \<in> trigger_results I nt auxlist"
          using auxlist_nonempty
          by auto
      }
      moreover {
        define A where "A = {i \<in> {0..<(length (linearize data_in))}. tuple \<notin> relR ((linearize data_in)!i)}"
        define i where "i = Max A"
        assume "\<not>(\<forall>i \<in> {0..<(length (linearize data_in))}.
        let (t, l, r) = (linearize data_in)!i in
        tuple \<in> r)"
        then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
        then have "i \<in> A" using i_def by auto
        then have i_props:
          "i \<in> {0..<(length (linearize data_in))}"
          "tuple \<notin> relR ((linearize data_in)!i)"
          using A_def
          by auto
        then obtain j where j_props:
          "j \<in> {i<..<(length (linearize data_in))}"
          "let (t', l', r') = (linearize data_in)!j in
          tuple \<in> l'"
          using assm
          by fastforce
        then have j_idx:
          "(linearize data_in)!j = auxlist!j"
          "j < (length auxlist)"
          using data_in_auxlist_index[OF assms(1)]
          by auto
        {
          fix k
          define dbk where "dbk = auxlist!k"
          define t_k where "t_k = time dbk"
          define l_k where "l_k = relL dbk"
          define r_k where "r_k = relR dbk"
          assume k_props: "k \<in> {0..<(length auxlist)}" "mem I (nt - t_k)"
          {
            assume "k \<ge> (length (linearize data_in))"
            then have "dbk \<in> set (linearize data_prev)"
              using data_prev_set_mem[OF assms(1)] k_props dbk_def
              by auto
            then have "\<not>memL I (nt - t_k)"
              using data_prev_mem[OF assms(1)] t_k_def I_def
              by auto
          }
          then have k_le: "k < (length (linearize data_in))" using k_props(2) le_def by blast
          then have k_idx: "(linearize data_in)!k = auxlist!k"
            using data_in_auxlist_index[OF assms(1)]
            by auto
          {
            assume "tuple \<notin> r_k"
            then have "k \<in> A" using k_le A_def r_k_def dbk_def k_idx by auto
            then have "k \<le> i" using i_def A_props by auto
            then have "j \<in> {k<..<(length auxlist)}"
              "let (t', l', r') = auxlist!j in
              tuple \<in> l'"
              using j_props j_idx
              by auto
            then have "\<exists>j \<in> {k<..<(length auxlist)}.
              let (t', l', r') = auxlist!j in
              tuple \<in> l'"
              by blast
          }
          then have "tuple \<in> r_k \<or>
          (\<exists>j \<in> {k<..<(length auxlist)}.
            let (t', l', r') = auxlist!j in
            tuple \<in> l'
          )" by blast
        }
        then have "\<forall>i \<in> {0..<(length auxlist)}.
          mem I (nt - time (auxlist!i)) \<longrightarrow> 
          (
            tuple \<in> relR (auxlist!i) \<or>
            (\<exists>j \<in> {i<..<(length auxlist)}.
              let (t', l', r') = auxlist!j in
              tuple \<in> l'
            )
          )"
          by auto
        then have "tuple \<in> trigger_results I nt auxlist"
          using auxlist_nonempty
          by auto
      }
      ultimately have "tuple \<in> trigger_results I nt auxlist"
        by blast
    }
    ultimately have "tuple \<in> trigger_results I nt auxlist" by blast
    then have "tuple \<in> trigger_results (args_ivl args) cur auxlist"
      using I_def time
      by auto
  }
  then have subset: "result_mmtaux args aux \<subseteq> trigger_results (args_ivl args) cur auxlist"
    by blast
  {
    fix tuple
    assume "tuple \<in> trigger_results (args_ivl args) cur auxlist"
    then have el: "tuple \<in> trigger_results I cur auxlist"
      by (simp add: I_def)
    then have data_in_nonempty: "(set (linearize data_in) \<noteq> {})"
      using data_in_auxlist_nonempty[OF assms(1)] I_def time
      by auto
    from el have trigger: "(\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem I (cur - t) \<longrightarrow> 
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            let (t', l', r') = auxlist!j in
            tuple \<in> l'
          )
        )
      )" by auto
    {
      (* historically *)
      assume hist: "\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem I (cur - t) \<longrightarrow> tuple \<in> r"
      {
        fix i
        define dbi where "dbi = (linearize data_in)!i"
        assume i_props: "i \<in> {0..<(length (linearize data_in))}"
        then have i_props:
          "dbi \<in> set (linearize data_in)"
          "i < length auxlist"
          "auxlist ! i = linearize data_in ! i"
          using data_in_auxlist_index[OF assms(1) i_props] dbi_def
          by auto
        then have "mem I (cur - time dbi)"
          using data_in_mem[OF assms(1)] dbi_def I_def time
          by auto
        then have "tuple \<in> relR dbi"
          using hist dbi_def i_props
          by (smt atLeastLessThan_iff case_prod_beta' comp_apply relR.simps time.simps zero_le)
      }
      then have "(\<forall>i \<in> {0..<(length (linearize data_in))}.
          let (t, l, r) = (linearize data_in)!i in
          tuple \<in> r
        )"
        by fastforce
      then have "tuple \<in> sat"
        using assms(1) data_in_nonempty
        by auto
    }
    moreover {
      define A where "A = {i \<in> {0..<(length auxlist)}. mem I (cur - time (auxlist!i)) \<and> tuple \<notin> relR (auxlist!i)}"
      define i where "i = Max A"
      assume "\<not>(\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem I (cur - t) \<longrightarrow> tuple \<in> r)"
      then have "\<not>(\<forall>i \<in> {0..<(length auxlist)}.
        mem I (cur - time (auxlist!i)) \<longrightarrow> tuple \<in> relR (auxlist!i))"
        by fastforce
      then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
      then have "i \<in> A" using i_def by auto
      then have i_props:
        "i \<in> {0..<(length auxlist)}"
        "mem I (cur - time (auxlist!i))"
        "tuple \<notin> relR (auxlist!i)"
        using A_def
        by auto
      then have "(\<exists>j \<in> {i<..<(length auxlist)}.
        let (t', l', r') = auxlist!j in
        tuple \<in> l'
      )"
        using trigger
        by fastforce
      then obtain j where j_props:
        "j \<in> {i<..<(length auxlist)}"
        "let (t', l', r') = auxlist!j in
        tuple \<in> l'"
        by auto
      {
        (* \<phi> in data_prev *)
        define j' where "j' = (j - length (linearize data_in))"
        assume assm: "j \<ge> (length (linearize data_in))"
        then have j'_props:
          "auxlist!j = linearize data_prev!j'"
          "j' < length (linearize data_prev)"
          using data_prev_auxlist_index_rev[OF assms(1)] j_props(1) j'_def
          by auto
        then have "auxlist!j \<in> set (linearize data_prev)"
          using j_props assm nth_mem
          by fastforce
        then have "\<exists>(t, l, r) \<in> set (linearize data_prev). tuple \<in> l"
          using j_props(2)
          by meson
        then have "tuple \<in> sat"
          using data_in_nonempty assms(1)
          by auto
      }
      moreover {
        (* \<psi> S \<psi> \<and> \<phi> in data_in *)
        assume j_le: "j < (length (linearize data_in))"
        then have j_idx:
          "(linearize data_in)!j = auxlist!j"
          "j < length auxlist"
          "auxlist ! j \<in> set (linearize data_in)"
          using data_in_auxlist_index[OF assms(1)] j_props
          by auto
        {
          fix k
          define db where "db = (linearize data_in)!k"
          define r where "r = relR db"
          assume k_props: "k \<in> {0..<(length (linearize data_in))}"
          then have k_idx:
            "(linearize data_in)!k = auxlist!k"
            "k < length auxlist"
            "auxlist ! k \<in> set (linearize data_in)"
            using data_in_auxlist_index[OF assms(1)]
            by auto
          then have k_mem: "mem I (nt - time (auxlist!k))"
            using data_in_mem[OF assms(1) k_idx(3)] I_def
            by auto
          {
            assume "tuple \<notin> r"
            then have "k \<in> A" using A_def k_idx k_mem time r_def db_def by auto
            then have "k \<le> i" using i_def A_props by auto
            then have "j \<in> {k<..<(length (linearize data_in))}"
            "let (t', l', r') = (linearize data_in)!j in
            tuple \<in> l'"
              using j_le j_props j_idx
              by auto
            then have "\<exists>j \<in> {k<..<(length (linearize data_in))}.
            let (t', l', r') = (linearize data_in)!j in
            tuple \<in> l'"
              by fastforce
          }
          then have "tuple \<in> r \<or>
          (\<exists>j \<in> {k<..<(length (linearize data_in))}.
            let (t', l', r') = (linearize data_in)!j in
            tuple \<in> l'
          )" by blast
        }
        then have "(\<forall>i \<in> {0..<(length (linearize data_in))}.
          let (t, l, r) = (linearize data_in)!i in
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length (linearize data_in))}.
            let (t', l', r') = (linearize data_in)!j in
            tuple \<in> l'
          )
        )"
          by (simp add: case_prod_beta')
        then have "tuple \<in> sat"
          using data_in_nonempty assms(1)
          by auto
      }
      ultimately have "tuple \<in> sat" using not_le by blast
    }
    ultimately have "tuple \<in> sat" by blast
    then have "tuple \<in> result_mmtaux args aux" using aux_def by auto
  }
  then have "trigger_results (args_ivl args) cur auxlist \<subseteq> result_mmtaux args aux"
    by auto
  then have "trigger_results (args_ivl args) cur auxlist = result_mmtaux args aux"
    using subset
    by blast
  then show ?thesis using aux_def by auto
qed


(*
fun valid_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_mmsaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<longleftrightarrow>
    (args_L args) \<subseteq> (args_R args) \<and> \<comment> \<open>free variables of the lhs are a subset of the rhs\<close>
    maskL = join_mask (args_n args) (args_L args) \<and> \<comment> \<open>check if maskL & masR were computed correctly\<close>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, X) \<in> set ys. table (args_n args) (args_R args) X) \<and> \<comment> \<open>check whether all tuples in ys are well-formed using the free variables of the rhs\<close>
    table (args_n args) (args_R args) (Mapping.keys tuple_in) \<and> \<comment> \<open>check if all tuples in tuple_in\<close>
    table (args_n args) (args_R args) (Mapping.keys tuple_since) \<and> \<comment> \<open>and tuple_since are well-formed\<close>
    \<comment> \<open> (\<forall>x\<in>X. wf_tuple n V x) \<close>
    (table (args_n args) (args_R args) (\<Union>(snd ` (set data_prev)))) \<and> \<comment> \<open>union all tables and check whether it's tuples are valid\<close>
    \<comment> \<open>(\<forall>as \<in> \<Union>(snd ` (set data_prev)). wf_tuple (args_n args) (args_R args) as) \<and> \<close>
    cur = nt \<and> \<comment> \<open>???\<close>
    ts_tuple_rel (set ys) = \<comment> \<open>all tuples with timestamp in ys = all tuples in data_prev and data_in\<close>
    {tas \<in> ts_tuple_rel (set data_prev \<union> set data_in). valid_tuple tuple_since tas} \<and>

    sorted (map fst data_prev) \<and> \<comment> \<open>data_prev should be sorted by timestamp\<close>
    (\<forall>t \<in> fst ` set data_prev. t \<le> nt \<and> \<not> memL (args_ivl args) (nt - t)) \<and>
    \<comment> \<open>the ts cannot be in the future and by definition of data_prev, the timestamps shouldn't be in the interval yet\<close>
    sorted (map fst data_in) \<and> \<comment> \<open>data_prev should be sorted by timestamp\<close>
    (\<forall>t \<in> fst ` set data_in. t \<le> nt \<and> memL (args_ivl args) (nt - t)) \<and>
    \<comment> \<open>the ts cannot be in the future and by definition of data_in, the timestamps should be in the interval\<close>

    \<comment> \<open>tuple_in should point to the latest entry of a given tuple in data_in (which aren't in the future)\<close>
    (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set data_in). valid_tuple tuple_since tas \<and> as = snd tas})
    ) \<and>
    \<comment> \<open>tuple_since can't be in the future\<close>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt)"
*)

end