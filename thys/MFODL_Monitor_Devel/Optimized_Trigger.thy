theory Optimized_Trigger
  imports
    Optimized_MTL_TEMP
begin

type_synonym ts = nat

(* simply stores all tables for \<phi> and \<psi> in [0, b] *)
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"

definition time :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> ts" where
  "time db = fst db"

definition relL :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relL db = (fst o snd) db"

definition relR :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relR db = (snd o snd) db"

fun trigger_results :: "args \<Rightarrow> ts \<Rightarrow> 'a mtaux \<Rightarrow> 'a table" where
  "trigger_results args cur auxlist = {
    tuple.
      (length (filter (\<lambda> (t, _, _). mem (args_ivl args) (cur - t)) auxlist) > 0) \<and>
      \<comment> \<open>pretty much the definition of trigger\<close>
      (\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (cur - t) \<longrightarrow> 
        \<comment> \<open>either \<psi> holds or there is a later database where the same tuple satisfies \<phi>\<close>
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j) \<comment> \<open>t < t' is given as the list is sorted\<close>
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
    result_mtaux args aux = trigger_results args cur auxlist
  "

type_synonym 'a mmtaux = "
  ts \<times>                                 \<comment> \<open>the newest timestamp\<close>
  bool list \<times>                          \<comment> \<open>maskL, i.e. all free variables of R \\ L are masked\<close>
  bool list \<times>                          \<comment> \<open>maskR, i.e. all free variables of L \\ R are masked\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_prev: all databases containing the tuples satisfying the lhs or the rhs where the timestamp doesn't yet satisfy memL\<close>
  (ts \<times> 'a table) queue \<times>              \<comment> \<open>data_in: all databases containing the tuples satisfying the rhs where the ts is in the interval\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_in for once\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_since for historically\<close>
  ('a table) \<times>                         \<comment> \<open>the set of tuples currently satisfying historically\<close>
  ('a table)                            \<comment> \<open>the set of tuples currently satisfying \<psi> S_[0, \<infinity>] (\<psi> \<and> \<phi>)\<close>
"

fun mmtaux_data_prev :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue" where
  "mmtaux_data_prev (_, _, _, data_prev, _) = data_prev"

fun mmtaux_data_in :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table) queue" where
  "mmtaux_data_in (_, _, _, _, data_in, _) = data_in"

definition ts_tuple_rel_binary :: "(ts \<times> 'a table \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple \<times> 'a tuple) set" where
  "ts_tuple_rel_binary ys = {(t, as, bs). \<exists>X Y. as \<in> X \<and> bs \<in> Y \<and> (t, X, Y) \<in> ys}"

abbreviation "ts_tuple_rel_binary_lhs \<equiv> ts_tuple_rel_f fst"
abbreviation "ts_tuple_rel_binary_rhs \<equiv> ts_tuple_rel_f snd"

definition auxlist_data_prev :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_prev args mt auxlist = filter (\<lambda>(t, _, _). \<not>memL (args_ivl args) (mt - t)) auxlist"

definition auxlist_data_in :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_in args mt auxlist = filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist"

fun valid_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist \<longleftrightarrow>
    (if mem (args_ivl args) 0 then (args_L args) \<subseteq> (args_R args) else (args_L args) = (args_R args)) \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, X, Y) \<in> set auxlist. table (args_n args) (args_R args) X \<and> table (args_n args) (args_L args) Y) \<and>
    table (args_n args) (args_L args) (Mapping.keys tuple_in_once) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since_hist) \<and>
    (\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as) \<and>
    (\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    cur = mt \<and>
    \<comment> \<open>all valid lhs/\<phi> tuples in data_prev should have a valid entry in tuple_in_once, as it is shifted\<close>
    ts_tuple_rel_binary_lhs (set (auxlist_data_prev args mt auxlist)) =
    {(t, l). (t, l) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)) \<and>
    valid_tuple tuple_in_once (t, l)} \<and>
    \<comment> \<open>all valid rhs/\<psi> tuples in data_in should have a valid entry in tuple_since_hist, as it is shifted\<close>
    ts_tuple_rel_binary_rhs (set (auxlist_data_in args mt auxlist)) =
    {(t, r). (t, r) \<in> ts_tuple_rel (set (linearize data_in)) \<and>
    valid_tuple tuple_since_hist (t, r)} \<and>
    \<comment> \<open>the entries stored should be the same, hence they're sorted as well\<close>
    sorted (map fst auxlist) \<and>
    auxlist_data_prev args mt auxlist = (linearize data_prev) \<and>
    auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist \<and>
    map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in) \<and>
    auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist \<and>
    \<comment> \<open>also all tuples in auxlist (and hence data_prev/data_in) satisfy memR \<close>
    (\<forall>db \<in> set auxlist. memR (args_ivl args) (mt - time db)) \<and>
     \<comment> \<open>check whether tuple_in once contains the newest occurence of the tuple satisfying the lhs\<close>
    newest_tuple_in_mapping fst (restrict (args_L args)) data_prev tuple_in_once (\<lambda>x. True) \<and>
    (\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> (restrict (args_L args) as) \<in> l) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since_hist. case Mapping.lookup tuple_since_hist as of Some t \<Rightarrow> t \<le> mt) \<and>
     \<comment> \<open>conditions for sat / trigger conditions\<close>
    (\<forall>tuple. tuple \<in> hist_sat \<longleftrightarrow>
      (\<not>is_empty data_in) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
        \<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r
      )
    ) \<and>
    (\<forall>tuple. tuple \<in> since_sat \<longleftrightarrow>
      (\<not>is_empty data_in) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
        \<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}. \<comment> \<open>dropping less then length guarantees length suffix > 0\<close>
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (restrict (args_L args) tuple) \<in> relL (suffix!0)
        )
      )
    )
  "

definition init_mmtaux :: "args \<Rightarrow> 'a mmtaux" where
  "init_mmtaux args = (0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue, Mapping.empty, Mapping.empty, {}, {})"

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
      auxlist_data_prev_def auxlist_data_in_def is_empty_alt)

(* analogous to add_new_ts_mmsaux' except that tuple_in doesn't exist / isn't updated *)
fun add_new_ts_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mmtaux" where
  "add_new_ts_mmtaux args nt (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) = (
    let I = args_ivl args;
     \<comment> \<open>split into the part that still is data_prev and the dbs that are no longer before I\<close>
    (data_prev, move) = takedropWhile_queue (\<lambda>(t, _). memL I (nt - t)) data_prev;
     \<comment> \<open>next the data from data_prev that is larger than the lower boundary is appended to data_in\<close>
    data_in = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move data_in;
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
      hist_sat,            \<comment> \<open>kept\<close>
      since_sat            \<comment> \<open>kept\<close>
    )
  )"

fun result_mmtaux :: "args \<Rightarrow> event_data mmtaux \<Rightarrow> event_data table" where
  "result_mmtaux args (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) = 
  (
    \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
    if (is_empty data_in) then
      {}
    else
      Mapping.keys tuple_in_once \<union> hist_sat \<union> since_sat
  )
"

lemma data_in_mem:
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set (linearize data_in)"
  shows "mem (args_ivl args) (mt - (fst db))"
proof (cases db)
  case (Pair t r)
  from assms(1) have "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    by auto
  then have "(t, r) \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
    using Pair assms(2)
    by auto
  then obtain l where "(t, l, r) \<in> set (auxlist_data_in args mt auxlist)"
    by auto
  then show ?thesis
    unfolding auxlist_data_in_def
    using set_filter[of "\<lambda>(t, _, _). mem (args_ivl args) (mt - t)" auxlist] Pair
    by auto
qed

lemma data_prev_mem:
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set (linearize data_prev)"
  shows "\<not>memL (args_ivl args) (mt - (time db))"
proof -
  from assms(1) have "auxlist_data_prev args mt auxlist = linearize data_prev"
    by simp
  then have "db \<in> set (auxlist_data_prev args mt auxlist)" using assms(2) by auto
  then show ?thesis
    unfolding auxlist_data_prev_def time_def
    using set_filter[of "\<lambda>(t, _, _). \<not>memL (args_ivl args) (mt - t)" auxlist]
    by auto
qed

lemma auxlist_mem_or:
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> (set auxlist)"
  shows "(((\<lambda> (t, l, r). (t, r)) db) \<in> set (linearize data_in) \<and> db \<notin> set (linearize data_prev)) \<and> memL (args_ivl args) (mt - time db) \<or> (((\<lambda> (t, l, r). (t, r)) db) \<notin> set (linearize data_in) \<and> db \<in> set (linearize data_prev)) \<and> \<not>memL (args_ivl args) (mt - time db)"
proof (cases "memL (args_ivl args) (mt - (time db))")
  define db' where "db' = ((\<lambda> (t, l, r). (t, r)) db)"
  case True
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    by auto
  from assms have mem: "memR (args_ivl args) (mt - time db)" by auto

  {
    assume "db \<in> set (linearize data_prev)"
    then have "db \<in> set (auxlist_data_prev args mt auxlist)"
      using data_props(1)
      by auto
    then have "\<not>memL (args_ivl args) (mt - (time db))"
      unfolding auxlist_data_prev_def time_def
      by auto
    then have "False"
      using True
      by auto
  }
  then have not_prev: "db \<notin> set (linearize data_prev)" by auto

  have db_mem: "db \<in> set (auxlist_data_in args mt auxlist)"
    using True assms(2) mem
    unfolding auxlist_data_in_def time_def
    by auto
  then have "(\<lambda> (t, l, r). (t, r)) db \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
    by auto
  then have "db' \<in> set (linearize data_in)"
    using data_props(2) db'_def
    by auto
  moreover have "memL (args_ivl args) (mt - time db)"
    using db_mem
    unfolding auxlist_data_in_def time_def
    by auto
  ultimately show ?thesis using db'_def not_prev by blast
next
  define db' where "db' = ((\<lambda> (t, l, r). (t, r)) db)"
  case False
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    by auto
  from assms have mem: "memR (args_ivl args) (mt - time db)" by auto
  have time_eq: "fst db = fst db'" using db'_def by (simp add: case_prod_beta)

  {
    assume "db' \<in> set (linearize data_in)"
    then have "db' \<in> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
      using data_props(2)
      by auto
    then have "\<exists>l. (fst db', l, snd db') \<in> set (auxlist_data_in args mt auxlist)"
      by auto
    then have "mem (args_ivl args) (mt - (time db))"
      using time_eq
      unfolding auxlist_data_in_def time_def
      by auto
    then have "False"
      using False
      by auto
  }
  then have not_in: "db' \<notin> set (linearize data_in)" by auto
  
  have "db \<in> set (auxlist_data_prev args mt auxlist)"
    using False assms(2)
    unfolding auxlist_data_prev_def time_def
    by auto
  then have "db \<in> set (linearize data_prev)"
    using data_props(1) db'_def
    by auto
  then show ?thesis using not_in db'_def False by blast
qed

lemma auxlist_mem_data_in:
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  assumes "db \<in> set auxlist"
  assumes "mem (args_ivl args) (mt - (time db))"
  shows "(\<lambda> (t, l, r). (t, r)) db \<in> set (linearize data_in)"
  using auxlist_mem_or[OF assms(1) assms(2)] assms(3)
  by auto

lemma data_sorted:
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "sorted (map fst (linearize data_prev))" "sorted (map fst (linearize data_in))"
proof -
  from assms have sorted: "sorted (map fst auxlist)"
    by auto
  from assms have data_props: 
    "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    by auto
  
  show "sorted (map fst (linearize data_prev))"
    using data_props(1) sorted sorted_filter
    unfolding auxlist_data_prev_def
    by metis

  have "\<forall>tuple. fst ((\<lambda> (t, l, r). (t, r)) tuple) = fst tuple"
    by auto
  then have "map fst (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)) = map fst (auxlist_data_in args mt auxlist)"
    by auto

  moreover from sorted have "sorted (map fst (auxlist_data_in args mt auxlist))"
    unfolding auxlist_data_in_def
    using sorted_filter
    by simp

  ultimately have "sorted (map fst (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist)))"
    by (simp only: )

  then show "sorted (map fst (linearize data_in))"
    using data_props(2)
    by simp
qed

lemma auxlist_index_time_mono:
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
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
  assumes "valid_mmtaux args cur (nt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
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

lemma data_in_auxlist_nonempty:
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0) = (\<not> is_empty (data_in))"
proof (rule iffI)
  assume assm: "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
  {
    assume empty: "set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) = {}"
    {
      assume "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
      then have "\<exists>x. x \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
        using nth_mem by blast
      then have "False" using empty by auto
    }
    then have "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) = 0"
      by auto
    then have "False" using assm by auto
  }
  then obtain db where db_props: "db \<in> set (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
    by auto
  then have "db \<in> set auxlist" "mem (args_ivl args) (mt - fst db)" by auto
  then have "(\<lambda> (t, l, r). (t, r)) db \<in> set (linearize data_in)"
    using auxlist_mem_data_in[OF assms(1), of db]
    unfolding time_def
    by blast
  then have "set (linearize data_in) \<noteq> {}" by auto
  then show "\<not> is_empty (data_in)"
    using is_empty_alt
    by auto
next
    from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
      by auto

    assume "\<not> is_empty (data_in)"
    then have "set (linearize data_in) \<noteq> {}" using is_empty_alt by auto
    then obtain db where db_props: "db \<in> set (linearize data_in)" by (meson nonemptyE)
    then have db_mem: "db \<in> set (map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist))"
      using data_props(2)
      unfolding auxlist_data_in_def
      by auto
    then obtain l where "(fst db, l, snd db) \<in> set (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist)"
      by auto
    then show auxlist_nonempty: "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0)"
      using length_pos_if_in_set[of "(fst db, l, snd db)" "filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist"]
      by auto
  qed

lemma valid_mmtaux_nonempty:
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "(length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0) = (\<not> is_empty data_in)"
proof -
  from assms(1) have data_in_equiv:
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
      by auto
    show ?thesis
    proof (rule iffI)
      assume "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
      then have "length (auxlist_data_in args mt auxlist) > 0"
        using auxlist_data_in_def[of args mt auxlist]
        by auto
      then have "{} \<noteq> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"        
        by auto
      then have "(linearize data_in) \<noteq> []"
        using data_in_equiv
        by auto
      then show "\<not> is_empty data_in"
        using is_empty_alt
        by auto
    next
      assume "\<not> is_empty data_in"
      then have "\<exists>e. e \<in> set (linearize data_in)"
        using is_empty_alt nth_mem
        by blast
      then have "{} \<noteq> set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
        using data_in_equiv
        by auto
      then have "{} \<noteq> set (auxlist_data_in args mt auxlist)"
        by auto
      then have "length (auxlist_data_in args mt auxlist) > 0"
        by auto 
      then show "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
        unfolding auxlist_data_in_def 
        by auto
    qed
qed

(*lemma auxlist_in_before_prev: 
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "set (take (length (linearize data_in)) (map (\<lambda> (t, l, r). (t, r)) auxlist)) = set (linearize data_in)"
proof -
  from assms(1) have data_in_equiv:
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    by auto
  then have "length (linearize data_in) \<le> length (auxlist_data_in args mt auxlist)"
    using length_map[of "\<lambda> (t, l, r). (t, r)" "auxlist_data_in args mt auxlist"]
    by auto
  then have data_in_len: "length (linearize data_in) \<le> length auxlist"
    unfolding auxlist_data_in_def
    using
      length_filter_le[of "(\<lambda>(t, _, _). mem (args_ivl args) (mt - t))" auxlist]
      order.trans[of "length (linearize data_in)" "length (filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist)" "length auxlist"]
    by simp
  then have same_length: "length (take (length (linearize data_in)) (map (\<lambda> (t, l, r). (t, r)) auxlist)) = length (linearize data_in)"
    by auto
  from assms(1) have dbs_memR: "\<forall>db \<in> set auxlist. memR (args_ivl args) (mt - time db)"
    by auto
  from assms(1) have sorted: "sorted (map fst auxlist)"
    by auto
  {
    define A where "A = {i \<in> {0..<(length auxlist)}. \<exists>t l r. (t, l, r) = auxlist!i \<and> \<not>memL (args_ivl args) (mt - t)}"
    define i where "i = Inf A"
    assume "\<exists>i\<in> {0..<(length auxlist)}. (\<lambda>(t, _, _). \<not>mem (args_ivl args) (mt - t)) (auxlist!i)"
    then have "\<exists>i\<in> {0..<(length auxlist)}. (\<lambda>(t, _, _). \<not>memL (args_ivl args) (mt - t)) (auxlist!i)"
      using dbs_memR
      unfolding time_def
      by (simp add: case_prod_beta')
    then have A_props: "A \<noteq> {}"
      using A_def
      by auto
    then have "i \<in> A" using i_def Inf_nat_def1
      by auto
    then obtain t l r where i_props:
      "i \<in> {0..<(length auxlist)}" "(t, l, r) = auxlist!i"
      "\<not>memL (args_ivl args) (mt - t)"
      using A_def
      by auto
    {
      fix j
      assume j_props: "j \<in> {i..<(length auxlist)}"
      then have "time (auxlist!i) \<le> time (auxlist!j)"
        unfolding time_def
        using sorted
        by (simp add: sorted_iff_nth_mono)
      then have "\<not>memL (args_ivl args) (mt - (time (auxlist!j)))"
        using memL_mono i_props
        unfolding time_def
        by (metis diff_le_mono2 fstI)
    }
    moreover {
      fix j
      assume j_props: "j \<in> {0..<i}"
      then have "time (auxlist!j) \<le> time (auxlist!i)"
        unfolding time_def
        using sorted i_props
        by (simp add: sorted_iff_nth_mono)
      moreover {
        assume "\<not> memL (args_ivl args) (mt - (time (auxlist!j)))"
        then have "\<exists>t l r. (t, l, r) = auxlist ! j \<and> \<not> memL (args_ivl args) (mt - t)"
          using j_props i_props(2) time_def
          by (metis eq_fst_iff)
        then have "j \<in> A" using A_def j_props i_props(1) by auto
        then have "False"
          using i_def A_props j_props cInf_lower[of j A]
          by auto
      }
      ultimately have "memL (args_ivl args) (mt - (time (auxlist!j)))"
        by blast
    }
    ultimately have list_split:
      "\<forall>j\<in>{0..<i}. memL (args_ivl args) (mt - (time (auxlist!j)))"
      "\<forall>j\<in>{i..<(length auxlist)}. \<not>memL (args_ivl args) (mt - (time (auxlist!j)))"
      by auto
    then have take_memL: "\<forall>db \<in> set (take i auxlist). memL (args_ivl args) (mt - (time db))"
      by (metis (no_types, lifting) atLeastLessThan_iff i_props(1) imageE less_imp_le_nat list_split(1) nth_image)
    {
      fix db
      assume db_props: "db \<in> set (take i auxlist)"
      then have auxlust_mem: "db \<in> set auxlist"
        by (meson in_set_takeD)
      moreover have "mem (args_ivl args) (mt - (time db))"
        using db_props take_memL auxlust_mem dbs_memR
        by auto
      ultimately have "db \<in> set (auxlist_data_in args mt auxlist)"
        unfolding auxlist_data_in_def time_def
        by (simp add: case_prod_beta')
    }
    then have "set (take i auxlist) \<subseteq> set (auxlist_data_in args mt auxlist)" by blast
    moreover {
      fix db
      assume db_props: "db \<in> set (auxlist_data_in args mt auxlist)"
      then have db_memL: "memL (args_ivl args) (mt - (time db))"
        unfolding auxlist_data_in_def time_def
        by auto
      from db_props obtain j where j_props: "auxlist!j = db" "j\<in>{0..<length auxlist}"
        unfolding auxlist_data_in_def
        using nth_the_index the_index_bounded
        by fastforce
      {
        assume "j \<ge> i"
        then have " \<not>memL (args_ivl args) (mt - (time (auxlist!j)))"
          using list_split(2) j_props
          by auto
        then have "False" using db_memL j_props(1)
          by auto
      }
      then have "j < i" using le_def by blast
      then have "db \<in> set (take i auxlist)"
        using j_props(1) i_props(1)
        by (metis atLeastLessThan_iff image_eqI le0 nat_le_linear not_le nth_image)
    }
    ultimately have "set (auxlist_data_in args mt auxlist) = set (take i auxlist)" by blast
    then have "(\<lambda> (t, l, r). (t, r)) ` set (take i auxlist) = (\<lambda> (t, l, r). (t, r)) ` set (auxlist_data_in args mt auxlist)"
      by auto
    then have "set (map (\<lambda> (t, l, r). (t, r)) (take i auxlist)) = set (map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist))"
      by auto
    then have "set (map (\<lambda> (t, l, r). (t, r)) (take i auxlist)) = set (linearize data_in)"
      using data_in_equiv
      by auto
    then have "set (take i (map (\<lambda> (t, l, r). (t, r)) auxlist)) = set (linearize data_in)"
      by (simp add: take_map)
  }
  moreover {
    fix i
    assume "i \<in> {0..<(length (linearize data_in))}"
    then have "(take (length (linearize data_in)) (map (\<lambda> (t, l, r). (t, r)) auxlist))!i = (linearize data_in)!i"
      by auto
  }
  ultimately show ?thesis
    using nth_equalityI[of
        "take (length (linearize data_in)) (map (\<lambda>(t, l, r). (t, r)) auxlist)"
        "linearize data_in"
    ]
    by auto
qed*)

lemma valid_result_mmtaux: 
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "result_mmtaux args (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) = trigger_results args cur auxlist"
proof -
  define aux where "aux = (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat)"
  define I where "I = args_ivl args"
  from assms(1) have time: "mt = cur" by auto
  from assms(1) have data_props:
    "auxlist_data_prev args mt auxlist = linearize data_prev"
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = linearize data_in"
    by auto
  from assms(1) have sorted: "sorted (map fst auxlist)"
    by auto
  {
    fix tuple
    assume assm: "tuple \<in> result_mmtaux args aux"
    then have "\<not>is_empty data_in"
      by (simp add: aux_def split: if_splits)
    then have non_empty: "length (filter (\<lambda> (t, _, _). mem (args_ivl args) (mt - t)) auxlist) > 0"
      using valid_mmtaux_nonempty[OF assms(1)]
      by auto
    
    from assm have "tuple \<in> (Mapping.keys tuple_in_once) \<or> tuple \<in> hist_sat \<or> tuple \<in> since_sat"
      by (simp add: aux_def split: if_splits)
    moreover {
      assume assm: "tuple \<in> (Mapping.keys tuple_in_once)"
      then have "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev tuple_in_once (\<lambda>x. True)"
        using assms(1)
        by auto
      then have "Mapping.lookup tuple_in_once tuple =
        safe_max (
          fst ` {
           tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
           restrict (args_L args) tuple = snd tas
          }
        )"
        unfolding newest_tuple_in_mapping_def
        by auto
      moreover have "\<exists>t. Mapping.lookup tuple_in_once tuple = Some t"
        using assm
        by (simp add: Mapping_keys_dest)
      then obtain t where t_props: "Mapping.lookup tuple_in_once tuple = Some t"
        by auto
      from assms(1) have "\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> (restrict (args_L args) as) \<in> l"
        by auto
      then have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> (restrict (args_L args) tuple) \<in> l"
        using assm t_props
        by auto
      then obtain db l r where db_props: "db = (t, l, r)" "db \<in> set (linearize data_prev)" "(restrict (args_L args) tuple) \<in> l"
        unfolding ts_tuple_rel_f_def
        by auto
      then obtain j where j_props: "db = auxlist!j" "j \<in> {0..<(length auxlist)}"
        using data_props(1)
        unfolding auxlist_data_prev_def
        by (metis (no_types, lifting) atLeastLessThan_iff filter_is_subset in_set_conv_nth leI not_less_zero subsetD)
      
      {
        fix i
        define dbi where "dbi = auxlist!i"
        assume i_props: "i \<in> {0..<(length auxlist)}" "mem (args_ivl args) (mt - time dbi)"
        {
          assume "j \<le> i"
          then have "fst (auxlist ! j) \<le> fst (auxlist ! i)"
            using sorted i_props(1)
            by (simp add: sorted_iff_nth_mono)
          then have j_memL: "memL (args_ivl args) (mt - time (auxlist!j))"
            using i_props(2) memL_mono[of "args_ivl args" "mt - time dbi" "mt - time (auxlist!j)"]
            unfolding time_def dbi_def
            by auto
          then have "auxlist!j \<in> set (linearize data_prev)"
            using j_props db_props
            by auto
          then have "\<not>memL (args_ivl args) (mt - time (auxlist!j))"
            using data_prev_mem[OF assms(1)]
            by auto
          then have "False" using j_memL by blast
        }
        then have j_ge_i: "i < j" using le_def by blast
        then have "j \<in> {i<..<(length auxlist)}" using j_props(2)
          by simp
        moreover have "(restrict (args_L args) tuple) \<in> (fst o snd) (auxlist!j)"
          using db_props j_props(1)
          by auto
        ultimately have "(\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )"
        using relL_def by blast
      }
      then have "(\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (mt - t) \<longrightarrow>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )
      )"
        by (simp add: case_prod_beta' time_def)
      then have "tuple \<in> trigger_results args mt auxlist"
        using non_empty
        by auto
    }
    moreover {
      assume "tuple \<in> hist_sat"
      then have hist:
        "(\<not>is_empty data_in)"
        "\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r"
        using assms(1)
        by auto
      {
        fix i
        assume i_props: "i \<in> {0..<(length auxlist)}" "mem (args_ivl args) (mt - fst (auxlist!i))"
        then have "auxlist!i \<in> set (auxlist_data_in args mt auxlist)"
          by (simp add: auxlist_data_in_def case_prod_unfold)
        then have "tuple \<in> (snd o snd) (auxlist!i)" using hist(2) by auto
      }
      then have "(\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (mt - t) \<longrightarrow> tuple \<in> r
      )" by (simp add: case_prod_beta')
      then have "tuple \<in> trigger_results args mt auxlist"
        using non_empty
        by auto
    }
    moreover {
      assume "tuple \<in> since_sat"
      then have "(
        \<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (restrict (args_L args) tuple) \<in> relL (suffix!0)
        )
      )" using assms(1)
        by (simp only: valid_mmtaux.simps)
      then obtain n where n_def:
        "n \<in> {0..<length (auxlist_data_in args mt auxlist)}"
        "let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (restrict (args_L args) tuple) \<in> relL (suffix!0)
        )"
        by blast
      define suffix where "suffix = drop n (auxlist_data_in args mt auxlist)"
      then have suffix_rhs: "\<forall>(t, l, r) \<in> set suffix. tuple \<in> r"
        using n_def(2)
        by meson
      have suffix_length: "length suffix > 0" "length suffix = length (auxlist_data_in args mt auxlist) - n"
        using suffix_def n_def(1)
        by auto
      have idx_shift: "\<forall>i\<in>{0..<length suffix}. suffix!i = (auxlist_data_in args mt auxlist)!(i+n)"
        using suffix_def n_def(1)
        by (simp add: add.commute)
      have suffix_lhs: "(restrict (args_L args) tuple) \<in> relL (suffix!0)"
        using suffix_def n_def(2)
        by meson
      moreover have data_in_equiv: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
        using assms(1)
        by auto
      moreover have "(auxlist_data_in args mt auxlist)!n = auxlist!n"
        using n_def(1)
        by (simp add: calculation(2))
      ultimately have since: "(restrict (args_L args) tuple) \<in> relL (auxlist!n)"
        using idx_shift suffix_length
        by auto
      
      have n_le_auxlist: "n < (length auxlist)"
        using n_def(1)
        unfolding auxlist_data_in_def
        by (meson atLeastLessThan_iff diff_le_self length_filter_le less_le_trans)
      {
        fix i
        assume i_props: "i \<in> {0..<n}"
        then have "n \<in> {i<..<(length auxlist)}"
          using n_le_auxlist
          by auto
        moreover have
          "(restrict (args_L args) tuple) \<in> relL (auxlist!n)"
          using since
          by auto
        ultimately have "(\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )"
          using relL_def by blast
      }
      then have "(\<forall>i \<in> {0..<n}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (mt - t) \<longrightarrow> 
          (\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )
      )"
        by (simp add: case_prod_beta')
      then have trigger_res_1: "(\<forall>i \<in> {0..<n}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (mt - t) \<longrightarrow> 
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )
        )
      )" by auto
      {
        fix i
        assume i_props: "i \<in> {n..<(length auxlist)}" "mem (args_ivl args) (mt - time (auxlist!i))"
        {
          assume "i \<ge> n + length suffix"
          then have i_ge: "i \<ge> length (auxlist_data_in args mt auxlist)"
            using suffix_length n_def(1)
            by auto
          then have idx_shift: "auxlist!i = (drop (length (auxlist_data_in args mt auxlist)) auxlist)!(i - length (auxlist_data_in args mt auxlist))"
            by (simp add: data_in_equiv)
          have
            "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
            "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
            using assms(1)
            by auto
          then have data_prev_equiv: "auxlist_data_prev args mt auxlist = drop (length (auxlist_data_in args mt auxlist)) auxlist"
            by (metis length_map)
          then have "auxlist!i = (auxlist_data_prev args mt auxlist)!(i - length (auxlist_data_in args mt auxlist))"
            using idx_shift
            by auto
          then have "auxlist!i \<in> set (auxlist_data_prev args mt auxlist)"
            using i_ge i_props(1) data_prev_equiv
            by (metis (no_types, lifting) add.commute atLeastLessThan_iff in_set_conv_nth le_add_diff_inverse length_drop less_diff_conv)
          moreover have "auxlist_data_prev args mt auxlist = (linearize data_prev)"
            using assms(1)
            by auto
          ultimately have "auxlist!i \<in> set (linearize data_prev)" by auto
          then have "\<not> memL (args_ivl args) (mt - time (auxlist!i))"
            using data_prev_mem[OF assms(1), of "auxlist!i"]
            by auto
          then have "False" using i_props(2) by auto
        }
        then have "i < n + length suffix" using le_def by blast
        then have "i < length (auxlist_data_in args mt auxlist)"
          using suffix_length
          by auto
        then have i_props': "i \<in> {n..<length (auxlist_data_in args mt auxlist)}"
          using i_props
          by auto
        then have "suffix!(i-n) = (auxlist_data_in args mt auxlist)!i"
          unfolding suffix_def
          by simp
        moreover have "(auxlist_data_in args mt auxlist)!i = auxlist!i"
          using data_in_equiv i_props'
          by simp
        ultimately have "suffix!(i-n) = auxlist!i" by auto
        then have "auxlist!i \<in> set suffix"
          using i_props'
          by (smt atLeastLessThan_iff dual_order.trans less_diff_iff less_or_eq_imp_le nth_mem suffix_length(2))
        (* "\<forall>i\<in>{0..<length suffix}. suffix!i = (auxlist_data_in args mt auxlist)!(i+n)" *)
        then have "tuple \<in> (snd o snd) (auxlist!i)"
          using suffix_rhs
          by auto
      }
      then have "(\<forall>i \<in> {n..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (mt - t) \<longrightarrow> tuple \<in> r
      )"
        unfolding time_def
        by (simp add: case_prod_beta')
      then have "(\<forall>i \<in> {n..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (mt - t) \<longrightarrow> 
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )
        )
      )"
        by auto
      then have "(\<forall>i \<in> {0..<(length auxlist)}.
        let (t, l, r) = auxlist!i in
        mem (args_ivl args) (mt - t) \<longrightarrow> 
        (
          tuple \<in> r \<or>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )
        )
      )"
        using trigger_res_1
        by (meson atLeastLessThan_iff le_def)
      then have "tuple \<in> trigger_results args mt auxlist"
        using non_empty
        by auto
    }
    ultimately have "tuple \<in> trigger_results args mt auxlist" by blast
    then have "tuple \<in> trigger_results args cur auxlist"
      using time
      by auto
  }
  then have subset: "result_mmtaux args aux \<subseteq> trigger_results args cur auxlist"
    by blast
  {
    fix tuple
    assume el: "tuple \<in> trigger_results args cur auxlist"
    then have data_in_nonempty: "\<not> is_empty (data_in)"
      using data_in_auxlist_nonempty[OF assms(1)] I_def time
      by auto
    
    from el have tuple_props: "(\<forall>i \<in> {0..<(length auxlist)}.
        mem (args_ivl args) (cur - time (auxlist!i)) \<longrightarrow> 
        (
          tuple \<in> relR (auxlist!i) \<or>
          (\<exists>j \<in> {i<..<(length auxlist)}.
            (restrict (args_L args) tuple) \<in> relL (auxlist!j)
          )
        )
      )"
      unfolding time_def relR_def
      by auto
    {
      assume hist: "\<forall>i \<in> {0..<(length auxlist)}.
        mem (args_ivl args) (cur - time (auxlist!i)) \<longrightarrow> tuple \<in> relR (auxlist!i)"
      {
        fix db
        assume "db \<in> set (auxlist_data_in args mt auxlist)"
        then have db_props: "mem (args_ivl args) (cur - time db)" "db \<in> set auxlist"
          using time
          unfolding auxlist_data_in_def time_def
          by auto
        from db_props(2) obtain j where j_props:
            "j \<in> {0..<(length auxlist)}"
            "db = auxlist!j"
          by (metis atLeastLessThan_iff in_set_conv_nth leI not_less0)
        then have "tuple \<in> relR db"
          using hist db_props j_props
          by auto
      }
      then have "\<forall>db \<in> set (auxlist_data_in args mt auxlist). tuple \<in> relR db"
        by auto
      then have "tuple \<in> hist_sat"
        using data_in_nonempty assms(1)
        unfolding relR_def
        by auto
      then have "tuple \<in> result_mmtaux args aux"
        using data_in_nonempty
        unfolding aux_def
        by auto
    }
    moreover {
      assume "\<exists>i \<in> {0..<(length auxlist)}.
        mem (args_ivl args) (cur - time (auxlist!i)) \<and> tuple \<notin> relR (auxlist!i)"      
      then obtain i where i_props:
        "i \<in> {0..<(length auxlist)}"
        "mem (args_ivl args) (cur - time (auxlist!i))"
        "tuple \<notin> relR (auxlist!i)"
        by auto

      define A where "A = {j \<in> {i<..<(length auxlist)}. (restrict (args_L args) tuple) \<in> relL (auxlist!j)}"
      define j where "j = Max A"

      have "\<exists>j \<in> {i<..<(length auxlist)}.
        (restrict (args_L args) tuple) \<in> relL (auxlist!j)
      "
        using i_props el tuple_props
        unfolding time_def relR_def
        by auto
      then have A_props: "A \<noteq> {}" "finite A" unfolding A_def by auto
      then have "j \<in> A" unfolding j_def by auto
      then have j_props:
        "j \<in> {i<..<(length auxlist)}"
        "(restrict (args_L args) tuple) \<in> relL (auxlist!j)"
        using A_def
        by auto

      {
        define suffix where "suffix = drop j (auxlist_data_in args mt auxlist)"
        assume j_le: "j < length (linearize data_in)"
        (* length (auxlist_data_in args mt auxlist)-1 *)
        moreover have data_in_props: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
          using assms(1)
          by auto
        ultimately have "suffix!0 = auxlist!j"
          using data_props(2)
          unfolding suffix_def
          by (metis (no_types, lifting) Cons_nth_drop_Suc length_map nth_Cons_0 nth_take)
        

        then have suffix_first: "(restrict (args_L args) tuple) \<in> relL (suffix!0)"
          using j_props
          by auto

        have "length (auxlist_data_in args mt auxlist) = length (linearize data_in)"
          using data_props(2)
          by (metis length_map)
        then have j_le: "j < length (auxlist_data_in args mt auxlist)"
          using j_le
          by auto

        {
          fix db
          assume suffix_mem: "db \<in> set suffix"
          then obtain k where k_props:
            "k \<in> {0..<length suffix}"
            "suffix!k = db"
            by (meson atLeastLessThan_iff less_eq_nat.simps(1) nth_the_index the_index_bounded)
          then have kj_props:
            "(k+j) \<in> {0..<length (auxlist_data_in args mt auxlist)}"
            "(auxlist_data_in args mt auxlist)!(k+j) = db"
            using suffix_def
            by (auto simp add: add.commute)
          then have "(k+j) \<in> {0..<length auxlist}"
            unfolding auxlist_data_in_def
            by (simp add: less_le_trans)

          moreover have "\<forall>i \<in> {0..<(length auxlist)}.
            mem (args_ivl args) (cur - time (auxlist!i)) \<longrightarrow> 
            (
              tuple \<in> relR (auxlist!i) \<or>
              (\<exists>j \<in> {i<..<(length auxlist)}.
                (restrict (args_L args) tuple) \<in> relL (auxlist!j)
              )
            )"
            using el
            unfolding relR_def time_def
            by auto
          ultimately have cond: "
            mem (args_ivl args) (cur - time (auxlist!(k+j))) \<longrightarrow> 
            (
              tuple \<in> relR (auxlist!(k+j)) \<or>
              (\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                (restrict (args_L args) tuple) \<in> relL (auxlist!j)
              )
            )" by auto


          have "db \<in> set (auxlist_data_in args mt auxlist)"
            using kj_props
            by auto
          then have "mem (args_ivl args) (cur - time db)"
            using time
            unfolding auxlist_data_in_def time_def
            by auto
          moreover have auxlist_idx: "(auxlist_data_in args mt auxlist)!(k+j) = auxlist!(k+j)"
            using data_in_props kj_props(1)
            by auto
          ultimately have "mem (args_ivl args) (cur - time (auxlist!(k+j)))"
            using kj_props(2)
            by auto
          
          then have "tuple \<in> relR (auxlist!(k+j)) \<or>
              (\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                (restrict (args_L args) tuple) \<in> relL (auxlist!j)
              )"
            using cond
            by auto

          moreover {
            assume "(\<exists>j \<in> {(k+j)<..<(length auxlist)}.
                (restrict (args_L args) tuple) \<in> relL (auxlist!j)
              )"
            then obtain j' where j'_props:
              "j' \<in> {(k+j)<..<(length auxlist)}"
              "(restrict (args_L args) tuple) \<in> relL (auxlist!j')"
              by blast

            then have "j' \<in> A" using A_def j_props by auto
            then have "j' \<le> j" using A_props j_def by auto
            then have "False" using j'_props by auto
          }

          ultimately have "tuple \<in> relR (auxlist!(k+j))" by blast
          then have "tuple \<in> relR db" using kj_props auxlist_idx by auto
        }
        then have "(\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            )"
            "(restrict (args_L args) tuple) \<in> relL (suffix!0)"
          using suffix_first
          unfolding relR_def
          by (auto simp add: relR_def case_prod_beta')
        then have "\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (restrict (args_L args) tuple) \<in> relL (suffix!0)
        )"
          using j_le suffix_def
          by auto
        
        then have "tuple \<in> since_sat" using data_in_nonempty assms(1) by auto
        then have "tuple \<in> result_mmtaux args aux"
          using data_in_nonempty
          unfolding aux_def
          by auto
      }
      moreover {
        define j' where "j' = j - length (linearize data_in)"
        assume j_geq: "j \<ge> length (linearize data_in)"
        moreover have data_prev_props: "auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist"
          using assms(1)
          by auto
        ultimately have "auxlist!j = (auxlist_data_prev args mt auxlist)!j'"
          using j_props(1)
          unfolding j'_def
          by auto
        then have idx_shift: "auxlist!j = (linearize data_prev)!j'"
          using data_props(1)
          by auto
        have data_in_props: "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
          using assms(1)
          by auto
        have "length (linearize data_prev) + length (linearize data_in) = length auxlist"
          using data_in_props data_prev_props data_props
          by (smt add.commute append_take_drop_id length_append length_map)
        then have j'_le: "j' < length (linearize data_prev)"
          using j_geq j_props(1)
          unfolding j'_def
          by auto
        define r_tuple where "r_tuple = restrict (args_L args) tuple"
        define B where "B = fst ` {
          tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
          r_tuple = snd tas
        }"
        (* "A = {j \<in> {i<..<(length auxlist)}. (restrict (args_L args) tuple) \<in> relL (auxlist!j)}"*)
        from assms(1) have "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev tuple_in_once (\<lambda>x. True)"
          by auto
        then have mapping_val: "Mapping.lookup tuple_in_once tuple = safe_max B"
          unfolding newest_tuple_in_mapping_def B_def r_tuple_def
          by auto

        define t where "t = fst ((linearize data_prev) ! j')"
        define X where "X = snd ((linearize data_prev) ! j')"
        have "restrict (args_L args) tuple \<in> fst X"
          using j_props idx_shift
          unfolding relL_def X_def
          by auto
        moreover have
          "(t, X) \<in> (set (linearize data_prev))"
          using j'_le
          unfolding t_def X_def
          by auto
        ultimately have "(t, r_tuple) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev))"
          unfolding r_tuple_def ts_tuple_rel_f_def
          by blast
        then have t_mem_B: "t \<in> B"
          unfolding B_def
          by (simp add: image_iff)
        then have B_props: "B \<noteq> {}" "finite B"
          using B_def
          by (auto simp add: finite_fst_ts_tuple_rel)
        then have "safe_max B = Some (Max B)"
          unfolding safe_max_def
          by auto
        then have "Mapping.lookup tuple_in_once tuple = Some (Max B)"
          using mapping_val
          by auto
        then have "tuple \<in> Mapping.keys tuple_in_once"
          by (simp add: Mapping_keys_intro)
        then have "tuple \<in> result_mmtaux args aux"
          using data_in_nonempty
          unfolding aux_def r_tuple_def
          by auto
      }
      ultimately have "tuple \<in> result_mmtaux args aux" using le_def by blast
    }
    ultimately have "tuple \<in> result_mmtaux args aux" by blast
  }
  then have "trigger_results args cur auxlist \<subseteq> result_mmtaux args aux"
    by auto
  then have "trigger_results args cur auxlist = result_mmtaux args aux"
    using subset
    by blast
  then show ?thesis using aux_def by auto
qed


lemma valid_add_new_ts_mmtaux:
  assumes "nt \<ge> cur"
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) auxlist"
  shows "valid_mmtaux
      args
      nt
      (add_new_ts_mmtaux args nt (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat))
      (filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist)
  "
proof -
  define I where "I = args_ivl args"
  
  (*define aux' where "aux' = (add_new_ts_mmtaux args nt aux)"
  define data_prev' where "data_prev' = mmtaux_data_prev aux'"
  define data_in' where "data_in' = mmtaux_data_prev aux'"

  define auxlist' where "auxlist' = filter (\<lambda> (t, _). memR (args_ivl args) (nt - t)) auxlist"


  then have "valid_mmtaux args nt aux' auxlist'" by auto*)
  then show ?thesis by auto
qed


fun update_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mmtaux" where
  "update_mmtaux args nt l r (cur, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, hist_sat, since_sat) =


  (
    nt,
    maskL,
    maskR,
    data_prev,
    data_in,
    tuple_in_once,
    tuple_since_hist,
    hist_sat,
    since_sat
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

end