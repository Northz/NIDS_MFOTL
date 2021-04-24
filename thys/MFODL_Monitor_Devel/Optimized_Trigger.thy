theory Optimized_Trigger
  imports
    Optimized_MTL_TEMP
begin

type_synonym ts = nat

(* simply stores all tables for \<phi> and \<psi> in [0, b] *)
type_synonym 'a mtaux = "(ts \<times> 'a table \<times> 'a table) list"

definition time :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> ts" where
  "time = fst"

definition relL :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relL = (fst o snd)"

definition relR :: "(ts \<times> 'a table \<times> 'a table) \<Rightarrow> 'a table" where
  "relR = (snd o snd)"

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
  nat \<times> nat \<times> nat \<times>                   \<comment> \<open>index of the first queue entry in data_prev, data_in and the last index of data_in\<close>
  bool list \<times>                          \<comment> \<open>maskL, i.e. all free variables of R \\ L are masked\<close>
  bool list \<times>                          \<comment> \<open>maskR, i.e. all free variables of L \\ R are masked\<close>
  (ts \<times> 'a table \<times> 'a table) queue \<times>  \<comment> \<open>data_prev: all databases containing the tuples satisfying the lhs or the rhs where the timestamp doesn't yet satisfy memL\<close>
  (ts \<times> 'a table) queue \<times>              \<comment> \<open>data_in: all databases containing the tuples satisfying the rhs where the ts is in the interval\<close>
  (('a tuple, ts) mapping) \<times>           \<comment> \<open>tuple_in for once\<close>
  (('a tuple, nat) mapping) \<times>          \<comment> \<open>tuple_since for historically. stores the index since when the rhs of the formula holds\<close>
  ('a table)                            \<comment> \<open>the set of tuples currently satisfying \<psi> S_[0, \<infinity>] (\<psi> \<and> \<phi>)\<close>
"

fun mmtaux_data_prev :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue" where
  "mmtaux_data_prev (_, _, _, _, _, _, data_prev, _) = data_prev"

fun mmtaux_data_in :: "'a mmtaux \<Rightarrow> (ts \<times> 'a table) queue" where
  "mmtaux_data_in (_, _, _, _, _, _, _, data_in, _) = data_in"

definition ts_tuple_rel_binary :: "(ts \<times> 'a table \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple \<times> 'a tuple) set" where
  "ts_tuple_rel_binary ys = {(t, as, bs). \<exists>X Y. as \<in> X \<and> bs \<in> Y \<and> (t, X, Y) \<in> ys}"

abbreviation "ts_tuple_rel_binary_lhs \<equiv> ts_tuple_rel_f fst"
abbreviation "ts_tuple_rel_binary_rhs \<equiv> ts_tuple_rel_f snd"

definition auxlist_data_prev :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_prev args mt auxlist = filter (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) auxlist"

definition auxlist_data_in :: "args \<Rightarrow> ts \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list" where
  "auxlist_data_in args mt auxlist = filter (\<lambda>(t, _, _). mem (args_ivl args) (mt - t)) auxlist"

fun valid_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mtaux \<Rightarrow> bool" where
  "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist \<longleftrightarrow>
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
    {db \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
    \<exists>db'. db = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db'} \<and>
    \<comment> \<open>all valid rhs/\<psi> tuples in data_in should have a valid entry in tuple_since_hist, as it is shifted\<close>
    ts_tuple_rel_binary_rhs (set (auxlist_data_in args mt auxlist)) =
    ts_tuple_rel (set (linearize data_in)) \<and>
    \<comment> \<open>the entries stored should be the same, hence they're sorted as well\<close>
    sorted (map fst auxlist) \<and>
    auxlist_data_prev args mt auxlist = (linearize data_prev) \<and>
    auxlist_data_prev args mt auxlist = drop (length (linearize data_in)) auxlist \<and>
    length (linearize data_prev) + idx_mid = idx_next  \<and>  \<comment> \<open>length (linearize data_prev) = idx_next - idx_mid\<close>
    map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in) \<and>
    auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist \<and>
    length (linearize data_in) + idx_oldest = idx_mid \<and> \<comment> \<open>length (linearize data_in) = idx_mid - idx_oldest\<close>
    \<comment> \<open>also all tuples in auxlist (and hence data_prev/data_in) satisfy memR \<close>
    (\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db)) \<and>
     \<comment> \<open>check whether tuple_in once contains the newest occurence of the tuple satisfying the lhs\<close>
    newest_tuple_in_mapping fst (restrict (args_L args)) data_prev tuple_in_once (\<lambda>x. True) \<and>
    (\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> (restrict (args_L args) as) \<in> l) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since_hist. (case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow>
      idx < idx_mid \<and>
      (\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
        as \<in> r
      ) \<and>
      (idx > idx_oldest \<longrightarrow> (restrict (args_L args) as) \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1)))))
    ) \<and>
    (\<forall>as. \<forall>idx.
      (
        (\<not>is_empty data_in) \<and>
        idx < idx_mid \<and>
        (\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
          as \<in> r
        ) \<and>
        (idx > idx_oldest \<longrightarrow> (restrict (args_L args) as) \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))
      ) \<longrightarrow> (\<exists>idx'\<le>idx. Mapping.lookup tuple_since_hist as = Some idx')
    ) \<and>
    (\<forall>tuple. tuple \<in> since_sat \<longleftrightarrow>
      (\<not>is_empty data_in) \<and> ( \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
        \<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}. \<comment> \<open>dropping less then length guarantees length suffix > 0\<close>
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (restrict (args_L args) tuple) \<in> relL (hd suffix)
        )
      )
    )
  "

definition init_mmtaux :: "args \<Rightarrow> 'a mmtaux" where
  "init_mmtaux args = (0, 0, 0, 0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue, Mapping.empty, Mapping.empty, {})"

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

fun result_mmtaux :: "args \<Rightarrow> event_data mmtaux \<Rightarrow> event_data table" where
  "result_mmtaux args (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) = 
  (
    \<comment> \<open>with an empty data_in, all tuples satisfy trigger\<close>
    if (is_empty data_in) then
      {}
    else
      Mapping.keys tuple_in_once \<union> (Mapping.keys (Mapping.filter (\<lambda>tuple idx. idx \<le> idx_oldest) tuple_since_hist)) \<union> since_sat
  )
"

lemma sorted_filter_dropWhile_memL:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). memL (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs"
      by auto
    moreover have "dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) xs)"
      by auto
    have dropWhile_IH: "dropWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#xs"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _).\<not> memL (args_ivl args) (mt - t)) (x#xs) = x#xs"
        using filter_IH
        by auto
      then show ?thesis using dropWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) x)" by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma sorted_filter_dropWhile_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs"
      by auto
    moreover have "dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) xs)"
      by auto
    have dropWhile_IH: "dropWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#xs"
      using mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). memR (args_ivl args) (mt - t)) (x#xs) = x#xs"
        using filter_IH
        by auto
      then show ?thesis using dropWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x)" using memR_antimono by auto
      then show ?thesis using mem by auto
    qed
  qed
qed

lemma sorted_filter_takeWhile_memL:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). memL (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).memL (args_ivl args) (mt - t)) xs)"
      by auto
    moreover have "takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = x#(takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = (filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) xs)"
      by auto
    have takeWhile_IH: "takeWhile (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = []"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). \<not>memL (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). memL (args_ivl args) (mt - t)) (x#xs) = []"
        using filter_IH
        by (simp add: case_prod_beta')
      then show ?thesis using takeWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). memL (args_ivl args) (mt - t)) x)" by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma sorted_filter_takeWhile_not_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs = takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs"
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _).\<not>memR (args_ivl args) (mt - t)) xs)"
      by auto
    moreover have "takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = x#(takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = (filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) xs)"
      by auto
    have takeWhile_IH: "takeWhile (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = []"
      using not_mem
      by auto
    show ?thesis
    proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR (args_ivl args) (mt - t)) db")
      case True
      then have "filter (\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (x#xs) = []"
        using filter_IH
        by (simp add: case_prod_beta')
      then show ?thesis using takeWhile_IH by auto
    next
      case False
      then obtain j where j_props: "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
        by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
      then have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) ((x#xs)!(Suc j)))"
        by auto
      moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
        using Cons(2) j_props
        by auto
      ultimately have "((\<lambda>(t, _). \<not>memR (args_ivl args) (mt - t)) x)"
        using memR_antimono by auto
      then show ?thesis using not_mem by auto
    qed
  qed
qed

lemma data_in_mem:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
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
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
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


lemma data_sorted:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  shows "sorted (map fst (linearize data_prev))" "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` (set (linearize data_in)). \<forall>t' \<in> fst ` (set (linearize data_prev)). t < t'"
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

  {
    fix t t'
    assume "t \<in> fst ` (set (linearize data_in))" "t' \<in> fst ` (set (linearize data_prev))"
    then have memL: "\<not>memL (args_ivl args) (mt - t')" "memL (args_ivl args) (mt - t)"
      using data_in_mem[OF assms(1)] data_prev_mem[OF assms(1)]
      unfolding time_def
      by auto
    {
      assume "t \<ge> t'"
      then have "False" using memL memL_mono by auto
    }
    then have "t < t'" using le_def by blast
  }
  then show "\<forall>t \<in> fst ` (set (linearize data_in)). \<forall>t' \<in> fst ` (set (linearize data_prev)). t < t'" by auto
qed

lemma tuple_in_once_mem0:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  assumes "mem (args_ivl args) 0"
  shows "tuple_in_once = Mapping.empty"
proof -
  from assms(2) have memL_all: "\<forall>t. memL (args_ivl args) t" by auto
  from assms(1) have "auxlist_data_prev args mt auxlist = linearize data_prev"
    by simp
  then have "linearize data_prev = []"
    using memL_all
    unfolding auxlist_data_prev_def
    by auto
  moreover from assms(1) have "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> (restrict (args_L args) as) \<in> l)"
    by simp
  ultimately have "Mapping.keys tuple_in_once = {}"
    using Mapping_keys_dest
    by fastforce
  then show ?thesis
    by (simp add: Mapping.lookup_empty keys_dom_lookup mapping_eqI)
qed

lemma auxlist_mem_or:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
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
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  assumes "db \<in> set auxlist"
  assumes "mem (args_ivl args) (mt - (time db))"
  shows "(\<lambda> (t, l, r). (t, r)) db \<in> set (linearize data_in)"
  using auxlist_mem_or[OF assms(1) assms(2)] assms(3)
  by auto


lemma data_prev_ts_props:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  shows "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL (args_ivl args) (cur - t)"
proof -
  from assms have data_props:
    "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    by auto
  from assms have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
    by auto
  moreover from assms have time: "cur = mt" by auto
  ultimately have memR: "(\<forall>db \<in> set auxlist. time db \<le> cur \<and> memR (args_ivl args) (cur - time db))"
    by auto

  {
    fix t
    assume "t \<in> fst ` set (linearize data_prev)"
    then obtain db where db_props: "t = fst db" "db \<in> set (linearize data_prev)"
      by auto
    then have "db \<in> set (auxlist_data_prev args mt auxlist)" using data_props by auto
    then have "\<not>memL (args_ivl args) (cur - t)" "db \<in> set auxlist"
      unfolding auxlist_data_prev_def db_props(1)
      using time
      by auto
    moreover have "t \<le> cur"
      using calculation(2) memR
      unfolding time_def db_props(1)
      by auto
    ultimately have "t \<le> cur" "\<not>memL (args_ivl args) (cur - t)" by auto
  }
  then show ?thesis by auto
qed

lemma data_in_ts_props:
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  shows "\<forall>t \<in> fst ` set (linearize data_in). t \<le> cur \<and> memL (args_ivl args) (cur - t)"
proof -
  from assms have data_props:
    "map (\<lambda> (t, l, r). (t, r)) (auxlist_data_in args mt auxlist) = (linearize data_in)"
    "auxlist_data_in args mt auxlist = take (length (linearize data_in)) auxlist"
    by auto
  from assms have "(\<forall>db \<in> set auxlist. time db \<le> mt \<and> memR (args_ivl args) (mt - time db))"
    by auto
  moreover from assms have time: "cur = mt" by auto
  ultimately have memR: "(\<forall>db \<in> set auxlist. time db \<le> cur \<and> memR (args_ivl args) (cur - time db))"
    by auto

  {
    fix t
    assume "t \<in> fst ` set (linearize data_in)"
    then obtain db where db_props: "t = fst db" "db \<in> set (linearize data_in)"
      by auto
    then obtain db' where db'_props: "db = (\<lambda> (t, l, r). (t, r)) db'" "db' \<in> set (auxlist_data_in args mt auxlist)"
      using data_props(1)
      by (metis (no_types, lifting) image_iff image_set)
    then have same_time: "fst db' = t"
      unfolding db_props(1)
      by (simp add: case_prod_beta)

    then have "mem (args_ivl args) (cur - t)" "db' \<in> set auxlist"
      using db'_props(2) time
      unfolding auxlist_data_in_def
      by auto
    moreover have "t \<le> cur"
      using calculation(2) memR same_time
      unfolding time_def db_props(1)
      by auto
    ultimately have "t \<le> cur" "memL (args_ivl args) (cur - t)" by auto
  }
  then show ?thesis by auto
qed

lemma auxlist_index_time_mono:
  assumes "valid_mmtaux args cur (nt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
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
  assumes "valid_mmtaux args cur (nt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
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
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
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
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
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

lemma valid_result_mmtaux: 
  assumes "valid_mmtaux args cur (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  shows "result_mmtaux args (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) = trigger_results args cur auxlist"
proof -
  define aux where "aux = (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat)"
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
    
    from assm have "tuple \<in> (Mapping.keys tuple_in_once) \<or> tuple \<in> (Mapping.keys (Mapping.filter (\<lambda>tuple idx. idx \<le> idx_oldest) tuple_since_hist)) \<or> tuple \<in> since_sat"
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
        using relL_def
        by metis
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
      assume "tuple \<in> Mapping.keys (Mapping.filter (\<lambda>tuple idx. idx \<le> idx_oldest) tuple_since_hist)"
      then obtain idx where idx_props: "Mapping.lookup tuple_since_hist tuple = Some idx" "idx \<le> idx_oldest"
        by (meson Mapping_keys_filterD)
      moreover have "(\<forall>as \<in> Mapping.keys tuple_since_hist. (case Mapping.lookup tuple_since_hist as of Some idx \<Rightarrow>
        idx < idx_mid \<and>
        (\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
          as \<in> r
        ) \<and>
        (idx > idx_oldest \<longrightarrow> (restrict (args_L args) as) \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1)))))
      )" using assms(1) by auto
      ultimately have
        "idx < idx_mid \<and>
        (\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
          tuple \<in> r
        ) \<and>
        (idx > idx_oldest \<longrightarrow> (restrict (args_L args) tuple) \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))"
        using Mapping_keys_intro by force
      then have
        "idx \<le> idx_oldest"
        "(\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
          tuple \<in> r
        )"
        "(idx > idx_oldest \<longrightarrow> (restrict (args_L args) tuple) \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))"
        using idx_props by auto
      then have
        "idx \<le> idx_oldest"
        "(\<forall>(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). tuple \<in> r)"
        using data_props by auto
      then have hist: "idx \<le> idx_oldest"
                "(\<forall>(t, l, r) \<in> set (auxlist_data_in args mt auxlist). tuple \<in> r)"
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
            (restrict (args_L args) tuple) \<in> relL (hd suffix)
        )
      )" using assms(1)
        by (simp only: valid_mmtaux.simps)
      then obtain n where n_def:
        "n \<in> {0..<length (auxlist_data_in args mt auxlist)}"
        "let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (restrict (args_L args) tuple) \<in> relL (hd suffix)
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
      have suffix_lhs: "(restrict (args_L args) tuple) \<in> relL (hd suffix)"
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
        unfolding suffix_def
        by (simp add: hd_drop_conv_nth)
      
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
      then have "\<forall>(t, r) \<in> set (map (\<lambda>(t, l, r). (t, r)) (auxlist_data_in args mt auxlist)). tuple \<in> r"
        unfolding relR_def
        by auto
      then have "\<forall>(t, r) \<in> set (linearize data_in). tuple \<in> r"
        using data_props(2)
        by auto
      then have hist: "\<forall>(t, r) \<in> set (drop (idx_oldest-idx_oldest) (linearize data_in)). tuple \<in> r"
        by auto
      from assms(1) have "length (linearize data_in) + idx_oldest = idx_mid" by auto
      then have "idx_oldest < idx_mid" using data_in_nonempty is_empty_alt[of data_in] by auto
      then have "(
          (\<not>is_empty data_in) \<and>
          idx_oldest < idx_mid \<and>
          (\<forall>(t, r) \<in> set (drop (idx_oldest-idx_oldest) (linearize data_in)). 
            tuple \<in> r
          ) \<and>
          (idx_oldest > idx_oldest \<longrightarrow> (restrict (args_L args) tuple) \<notin> (snd ((linearize data_in)!(idx_oldest-idx_oldest-1))))
        )"
        using hist data_in_nonempty
        by auto
      moreover have "(\<forall>idx.
        (
          (\<not>is_empty data_in) \<and>
          idx < idx_mid \<and>
          (\<forall>(t, r) \<in> set (drop (idx-idx_oldest) (linearize data_in)). 
            tuple \<in> r
          ) \<and>
          (idx > idx_oldest \<longrightarrow> (restrict (args_L args) tuple) \<notin> (snd ((linearize data_in)!(idx-idx_oldest-1))))
        ) \<longrightarrow> (\<exists>idx' \<le> idx. Mapping.lookup tuple_since_hist tuple = Some idx')
      )" using assms(1) by auto
      ultimately obtain idx' where "Mapping.lookup tuple_since_hist tuple = Some idx'" "idx' \<le> idx_oldest"
        by blast
      then have "tuple \<in> Mapping.keys (Mapping.filter (\<lambda>tuple idx. idx \<le> idx_oldest) tuple_since_hist)"
        by (simp add: Mapping_keys_filterI)
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
        ultimately have "hd suffix = auxlist!j"
          using data_props(2)
          unfolding suffix_def
          by (metis (no_types, lifting) hd_drop_conv_nth length_map nth_take)
        

        then have suffix_first: "(restrict (args_L args) tuple) \<in> relL (hd suffix)"
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
            "(restrict (args_L args) tuple) \<in> relL (hd suffix)"
          using suffix_first
          unfolding relR_def
          by (auto simp add: relR_def case_prod_beta')
        then have "\<exists>n \<in> {0..<length (auxlist_data_in args mt auxlist)}.
          let suffix = drop n (auxlist_data_in args mt auxlist) in (
            (\<forall>(t, l, r) \<in> set suffix.
              tuple \<in> r
            ) \<and>
            (restrict (args_L args) tuple) \<in> relL (hd suffix)
        )"
          using j_le suffix_def
          by (meson atLeastLessThan_iff less_eq_nat.simps(1))
        
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


fun shift_end_queues_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (ts \<times> 'a table \<times> 'a table) queue \<Rightarrow> (ts \<times> 'a table) queue \<Rightarrow> (('a tuple, ts) mapping) \<Rightarrow> (nat \<times> nat \<times> (ts \<times> 'a table \<times> 'a table) queue \<times> (ts \<times> 'a table \<times> 'a table) list \<times> (ts \<times> 'a table) queue \<times> (('a tuple, ts) mapping))" where
  "shift_end_queues_mmtaux args nt idx_mid idx_oldest data_prev data_in tuple_in_once = (
    \<comment> \<open>in a first step, we update tuple_in_once by removing all tuples where currently a ts
       is stored, that points to a db that with the new ts (nt) no longer is part of
       [0, a-1] / data_prev\<close>
    let (_, data_prev, move, tuple_in_once) = shift_end
      (flip_int_less_lower (args_ivl args)) \<comment> \<open>[0, a-1]\<close>
      nt  \<comment> \<open>the new timestamp\<close>
      fst \<comment> \<open>here we look at the lhs tuples / \<phi>\<close>
      (restrict (args_L args)) \<comment> \<open>we have to restrict the tuples of the lhs to the respective cols\<close>
      (empty_queue::(ts \<times> nat) queue, data_prev, tuple_in_once); \<comment> \<open>add type\<close>
    \<comment> \<open>pass empty_queue as the first argument as it would filter out all: [0, a-1] \<inter> [a, b] = {}.
       idx_mid can be moved forward by the number of all tuples dropped from data_prev (move)\<close>
    move_len = length move;
    idx_mid = idx_mid + move_len;
    \<comment> \<open>in a next step, we drop all entries from data_in that are no longer relevant \<close>
    (data_in, drop) = takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in;
     \<comment> \<open>instead of first appending and then filtering, we filter move separately. this saves us the append
       operation for all entries in move\<close>
    move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move;
    \<comment> \<open>idx_ildest has to be moved forward by the number of dbs dropped from data_in and the ones
        dropped from data_prev because they don't satisfy memR anymore (move')\<close>
    drop_prev_len = move_len - length move';
    idx_oldest = idx_oldest + length drop + drop_prev_len;
    
    \<comment> \<open>next, the right hand side of entries in move have to be appended to data_in. these all already
       satisfy memR as we just filtered them for it\<close>
    data_in = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in
    in
    (idx_mid, idx_oldest, data_prev, move, data_in, tuple_in_once)
  )"


lemma ts_tuple_rel_empty: "ts_tuple_rel_f (\<lambda>_. {}) A = {}"
  unfolding ts_tuple_rel_f_def
  by auto

lemma Mapping_empty_filter: "Mapping.filter f Mapping.empty = Mapping.empty"
  by (metis Mapping.lookup_empty Mapping_lookup_filter_not_None mapping_eqI)

lemma fold_Mapping_filter_empty: "fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty = Mapping.empty"
proof (induction xs arbitrary: )
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs Mapping.empty) = Mapping.empty"
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs (Mapping.filter (f x Mapping.empty) Mapping.empty)) = Mapping.empty"
    using Mapping_empty_filter[of "f x Mapping.empty"]
    by auto
  then have "(fold (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) xs \<circ> (\<lambda>el tuple_in. Mapping.filter (f el tuple_in) tuple_in) x) Mapping.empty = Mapping.empty"
    by auto
  then show ?case by simp
qed

lemma Mapping_filter_Some:
  assumes "Mapping.lookup mapping k = Some v"
  assumes "f k v = True"
  shows "Mapping.lookup (Mapping.filter f mapping) k = Some v"
  using assms
  by (simp add: Mapping_keys_filterI Mapping_lookup_filter_keys)

lemma Mapping_filter_None:
  assumes "Mapping.lookup mapping k = None"
  shows "Mapping.lookup (Mapping.filter f mapping) k = None"
  using assms Mapping_lookup_filter_not_None
  by fastforce

lemma restrict_double_appl: "restrict M t = restrict M (restrict M t)"
  by (auto simp: restrict_def)

lemma filter_order_inv: "filter f (filter g xs) = filter g (filter f xs)"
  by (metis (mono_tags, lifting) filter_cong filter_filter)

lemma not_memL_imp_memR: "\<not> memL (args_ivl args) t \<Longrightarrow> memR (args_ivl args) t"
proof -
  assume "\<not> memL (args_ivl args) t"
  then have memL: "\<forall>t'\<le>t. \<not>mem (args_ivl args) t'" using memL_mono by auto
  have "(memL (args_ivl args), memR (args_ivl args), bounded (args_ivl args)) \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using Rep_\<I>[of "(args_ivl args)"]
    by (simp add: bounded.rep_eq memL.rep_eq memR.rep_eq)
  then obtain t_ex where t_ex_props: "mem (args_ivl args) t_ex"
    by auto
  {
    assume memR: "\<not>memR (args_ivl args) t"
    {
      fix t'
      assume t'_leq_t: "t' \<ge> t"
      then have "\<not>memR (args_ivl args) t'"
        using memR memR_antimono
        by auto
    }
    then have "\<forall>t'\<ge>t. \<not>mem (args_ivl args) t'" by auto
    then have "\<forall>t'. \<not>mem (args_ivl args) t'"
      using memL nat_le_linear
      by auto
    then have "False" using t_ex_props by auto
  }
  then show "memR (args_ivl args) t" by auto
qed

lemma not_memR_imp_memL: "\<not> memR (args_ivl args) t \<Longrightarrow> memL (args_ivl args) t"
proof -
  assume "\<not> memR (args_ivl args) t"
  then have memR: "\<forall>t'\<ge>t. \<not>memR (args_ivl args) t'" using memR_antimono by auto
  have "(memL (args_ivl args), memR (args_ivl args), bounded (args_ivl args)) \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using Rep_\<I>[of "(args_ivl args)"]
    by (simp add: bounded.rep_eq memL.rep_eq memR.rep_eq)
  then obtain t_ex where t_ex_props: "mem (args_ivl args) t_ex"
    by auto
  {
    assume memL: "\<not>memL (args_ivl args) t"
    {
      fix t'
      assume t'_leq_t: "t' \<le> t"
      then have "\<not>memL (args_ivl args) t'"
        using memL memL_mono
        by auto
    }
    then have "\<forall>t'\<le>t. \<not>mem (args_ivl args) t'" by auto
    then have "\<forall>t'. \<not>mem (args_ivl args) t'"
      using memR nat_le_linear
      by auto
    then have "False" using t_ex_props by auto
  }
  then show "memL (args_ivl args) t" by auto
qed

lemma fold_append_queue_map: "linearize (fold (\<lambda>(t, l, r) q. append_queue (t, r) q) xs q) = linearize q @ (map (\<lambda>(t, l, r). (t, r)) xs)"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma filter_imp: "(\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> length (filter P xs) \<le> length (filter Q xs)"
  by (metis (mono_tags, lifting) filter_cong filter_filter length_filter_le)

lemma valid_shift_end_queues_mmtaux:
  assumes valid_before: "valid_mmtaux args cur
    (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  assumes nt_mono: "nt \<ge> cur"
  assumes "(idx_mid', idx_oldest', data_prev', move, data_in'', tuple_in_once') = shift_end_queues_mmtaux args nt idx_mid idx_oldest data_prev data_in tuple_in_once"
  shows
    "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as)"
    "ts_tuple_rel_binary_lhs (set (auxlist_data_prev args nt auxlist)) =
    {db \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')).
    \<exists>db'. db = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once' db'}"
    "auxlist_data_prev args nt auxlist = (linearize data_prev')"
    "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev' tuple_in_once' (\<lambda>x. True)"
    "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> (restrict (args_L args) as) \<in> l)"
    "length (linearize data_prev') = idx_next - idx_mid'"
    "length (linearize data_in'') = idx_mid' - idx_oldest'"
    "move = filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)"
    "data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move) (dropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
proof - 
  define shift_res where "shift_res = shift_end
      (flip_int_less_lower (args_ivl args))
      nt
      fst
      (restrict (args_L args))
      (empty_queue::(ts \<times> 'a option list set \<times> 'a option list set) queue, data_prev, tuple_in_once)"
  define empty_queue' where "empty_queue' = fst shift_res"
  
  have data_prev'_def: "data_prev' = (fst o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp add: Let_def split: prod.splits) 
  
  have move_def: "move = (fst o snd o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp add: Let_def split: prod.splits) 
  
  define move' where "move' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move"

  have tuple_in_once'_def: "tuple_in_once' = (snd o snd o snd) shift_res"
    using assms(3)
    unfolding shift_res_def
    by (auto simp add: Let_def split: prod.splits)

  define data_in' where "data_in' = fst (takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
  define drop where "drop = snd (takedropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
  have data_in''_def: "data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' data_in'"
    using assms(3)
    unfolding shift_res_def data_in'_def data_in'_def move'_def
    by (auto simp only: shift_end_queues_mmtaux.simps Let_def fst_def split: prod.splits)

  then show "data_in'' = fold (\<lambda>(t, l, r) data_in. append_queue (t, r) data_in) move' (dropWhile_queue (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) data_in)"
    unfolding data_in'_def move'_def
    using takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
    by auto

  define drop_prev_len where "drop_prev_len = length move - length move'"

  have idx_mid'_def: "idx_mid' = idx_mid + length move"
    using assms(3)
    unfolding shift_res_def move_def drop_prev_len_def
    by (auto simp add: Let_def split: prod.splits)

  have idx_oldest'_def: "idx_oldest' = idx_oldest + length drop + drop_prev_len"
    unfolding shift_res_def drop_def drop_prev_len_def move'_def
    using assms(3) takedropWhile_queue_snd[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
    by (auto simp add: Let_def split: prod.splits)

  have shift_end_res: "(empty_queue', data_prev', move, tuple_in_once') = shift_end
      (flip_int_less_lower (args_ivl args))
      nt
      fst
      (restrict (args_L args))
      (empty_queue::(ts \<times> 'a option list set \<times> 'a option list set) queue, data_prev, tuple_in_once)"
    using empty_queue'_def data_prev'_def move_def tuple_in_once'_def shift_res_def
    by auto

  from assms(1) have table_tuple_in: "table (args_n args) (args_L args) (Mapping.keys tuple_in_once)"
    by auto

  from assms(1) have time: "cur = mt" by auto

  from assms(1) have "ts_tuple_rel_binary_lhs (set (auxlist_data_prev args mt auxlist)) =
    {db \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
     \<exists>db'. db = (fst db', restrict (args_L args) (snd db')) \<and> valid_tuple tuple_in_once db'}"
    unfolding valid_mmtaux.simps
    apply -
    apply (erule conjE)+
    apply assumption
    done

  then have auxlist_tuples_lhs: "ts_tuple_rel_binary_lhs (set ((auxlist_data_prev args mt) auxlist)) =
    {tas \<in> (ts_tuple_rel_f (\<lambda>_. {}) (set (linearize empty_queue))) \<union> (ts_tuple_rel_binary_lhs (set (linearize data_prev))).
    \<exists>db'. tas = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db'}"
    using ts_tuple_rel_empty
    by auto

  (* ts_tuple_rel_binary_lhs (set (auxlist_data_prev args mt auxlist)) =
    {tas \<in> ts_tuple_rel_binary_lhs (set (linearize empty_queue)) \<union> ts_tuple_rel_f (\<lambda>_. {}) (set (linearize data_prev)). valid_tuple tuple_in_once tas}*)

  from assms(1) have
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    by (auto simp only: valid_mmtaux.simps)

  moreover have "sorted (map fst (linearize data_prev))"
    using data_sorted[OF assms(1)]
    by auto

  moreover have "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL (args_ivl args) (cur - t))"
    using data_prev_ts_props[OF assms(1)]
    by auto
  ultimately have
    (*"(\<forall>as \<in> \<Union>(relL ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>(relR ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"*)
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> \<not> memL (args_ivl args) (cur - t))"
    by auto
  then have data_prev_props:
    "sorted (map fst (linearize data_prev))"
    "(\<forall>t \<in> fst ` set (linearize data_prev). t \<le> cur \<and> memL (flip_int_less_lower (args_ivl args)) (cur - t))"
    using flip_int_less_lower_memL
    by auto
  
  have data_in_props:
    "sorted (map fst (linearize data_in))"
    "(\<forall>t \<in> fst ` set (linearize data_in). t \<le> cur \<and> memL (args_ivl args) (cur - t))"
    using data_sorted[OF assms(1)] data_in_ts_props[OF assms(1)]
    by auto

  have empty_queue_props:
    "(\<forall>as \<in> \<Union>((fst o snd) ` (set (linearize empty_queue))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((snd o snd) ` (set (linearize empty_queue))). wf_tuple (args_n args) (args_R args) as)"
    "sorted (map fst (linearize empty_queue))"
    "(\<forall>t \<in> fst ` set (linearize empty_queue). t \<le> cur \<and> \<not> memL (flip_int_less_lower (args_ivl args)) (cur - t))"
    by (auto simp add: empty_queue_rep)

  from assms(1) have max_ts_tuple_in:
    "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev tuple_in_once (\<lambda>x. True)"
    by auto

  (*

  "ts_tuple_rel_binary_lhs (set ((auxlist_data_prev args mt) auxlist)) =
    {tas \<in> (ts_tuple_rel_binary_lhs (set (linearize data_prev))) \<union> (ts_tuple_rel_f (\<lambda>_. {}) (set (linearize data_in))).
    valid_tuple tuple_in_once tas}"

*)
  have shift_end_props:
    "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
    "ts_tuple_rel_binary_lhs (set (filter (\<lambda>(t, rel). memR (flip_int_less_lower (args_ivl args)) (nt - t)) (auxlist_data_prev args mt auxlist))) =
    {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')).
    \<exists>db'. tas = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db'}"
    "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev' tuple_in_once' (\<lambda>x. True)"
    "sorted (map fst (linearize data_prev'))"
    "\<forall>t\<in>fst ` set (linearize data_prev'). t \<le> cur \<and> mem (flip_int_less_lower (args_ivl args)) (cur - t)"
    "move = snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev)"
    "linearize data_prev' = filter (\<lambda>(t, X). memR (flip_int_less_lower (args_ivl args)) (nt - t)) (linearize data_prev)"
    "tuple_in_once' =
    fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) tuple_in) move tuple_in_once"
    unfolding relL_def relR_def
    using valid_shift_end_unfolded [of
        "(args_n args)" "(args_L args)" tuple_in_once fst "(auxlist_data_prev args mt)" auxlist
        "(\<lambda>_. {})" empty_queue fst data_prev "(\<lambda>db. \<exists>db'. db = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db')" fst "(args_L args)"
        cur "flip_int_less_lower (args_ivl args)" fst "(restrict (args_L args))" "(\<lambda>x. True)" nt empty_queue' data_prev' move tuple_in_once',
        OF table_tuple_in auxlist_tuples_lhs empty_queue_props(1, 3-4) 
        data_prev_props max_ts_tuple_in nt_mono shift_end_res
      ]
    by (auto simp add: ts_tuple_rel_empty)

  show
    "table (args_n args) (args_L args) (Mapping.keys tuple_in_once')"
    "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev' tuple_in_once' (\<lambda>x. True)"
    using shift_end_props(1,3)
    by auto

  from assms(1) have auxlist_prev: "auxlist_data_prev args mt auxlist = (linearize data_prev)"
    by auto

  {
    assume "mem (args_ivl args) 0"
    then have "(linearize data_prev) = []"
      using auxlist_prev memL_mono
      unfolding auxlist_data_prev_def
      by auto
    moreover have empty: "linearize data_prev' = []"
      using shift_end_props(7) calculation(1)
      by auto
    ultimately have "(linearize data_prev) = (linearize data_prev')" "(linearize data_prev) = []"  by auto
  }
  then have data_prev_eq_mem_0: "mem (args_ivl args) 0 \<longrightarrow> (linearize data_prev) = (linearize data_prev') \<and> (linearize data_prev) = []"
    by blast

  
  have data_prev'_eq: "linearize data_prev' = filter (\<lambda>(t, X). \<not>memL (args_ivl args) (nt - t)) (linearize data_prev)"
  proof (cases "mem (args_ivl args) 0")
    case True
    then show ?thesis
      using data_prev_eq_mem_0
      by auto
  next
    case False
    then have not_mem: "\<not> memL (args_ivl args) 0" by auto
    show ?thesis
      using shift_end_props(7) flip_int_less_lower_memR[OF not_mem]
      by auto
  qed

  have move_def: "move = snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev)"
  proof (cases "mem (args_ivl args) 0")
    case True
    then show ?thesis
      using shift_end_props(6) data_prev_eq_mem_0
      by (metis takeWhile.simps(1) takedropWhile_queue_snd)
  next
    case False
    then have not_mem: "\<not> memL (args_ivl args) 0" by auto
    then show ?thesis
      using shift_end_props(6) flip_int_less_lower_memR[OF not_mem]
      by auto
  qed
  then have move_takeWhile: "move = takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)"
    using takedropWhile_queue_snd
    by auto
  then show move_filter: "move = filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)"
    using data_sorted[OF assms(1)] sorted_filter_takeWhile_memL[of "linearize data_prev" args nt]
    by auto
  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t,_). (memL (args_ivl args) (nt - t)) \<and> (memR (args_ivl args) (nt - t)))"
    by auto
  have move'_eq: "move' = filter (\<lambda>(t,_). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t)) (linearize data_prev)"
    using move'_def move_filter filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by (auto simp add: filter_simp)

  have filter_data_prev_nt: "filter (\<lambda>(t, _). \<not>memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist) = (linearize data_prev')"
    using auxlist_prev data_prev'_eq
    by auto
  then have auxlist_prev_eq: "(filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) auxlist) = (linearize data_prev')"
    unfolding auxlist_data_prev_def
    using filter_filter[of "(\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t))" "(\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t))" auxlist]
    by auto
  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (mt - t)) \<and> (case x of (t, uu_) \<Rightarrow> \<not> memL (args_ivl args) (nt - t))) = (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t))"
    by auto
  have "(filter (\<lambda>(t, _). \<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t)) auxlist) = (linearize data_prev')"
    using auxlist_prev_eq
    by (simp add: filter_simp)
  moreover have "\<forall>t. (\<not> memL (args_ivl args) (mt - t) \<and>  \<not> memL (args_ivl args) (nt - t)) = (\<not> memL (args_ivl args) (nt - t))"
    using nt_mono time memL_mono[of "args_ivl args"]
    by auto
  ultimately have "filter (\<lambda>(t, X). \<not>memL (args_ivl args) (nt - t)) auxlist = (linearize data_prev')"
    by auto
  then show auxlist_prev_eq: "auxlist_data_prev args nt auxlist = (linearize data_prev')"
    unfolding auxlist_data_prev_def
    by auto
  then have filter_data_prev_nt: "filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist) = auxlist_data_prev args nt auxlist"
    using filter_data_prev_nt
    by auto

  
  {
    assume mem0: "mem (args_ivl args) 0"
    then have "Mapping.keys tuple_in_once = {}" using tuple_in_once_mem0[OF assms(1)] by auto
    then have "\<forall>k. Mapping.lookup tuple_in_once k = None"
      using Mapping_keys_intro
      by fastforce
    then have "{tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). \<exists>db'. snd tas = (restrict (args_L args) (snd db')) \<and> valid_tuple tuple_in_once db'} = {}"
      unfolding valid_tuple_def
      by auto
    moreover {
      from mem0 have "(set (filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist))) = {}"
        by auto
      then have "ts_tuple_rel_binary_lhs (set (filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist))) = {}"
        unfolding ts_tuple_rel_f_def
        by auto
    }
    ultimately have "ts_tuple_rel_binary_lhs (set (filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist))) =
    {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). \<exists>db'. tas = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db'}"
      using shift_end_props(2)
      by auto
  }
  moreover {
    define f1 :: "ts \<times> 'a table \<times> 'a table \<Rightarrow> bool" where "f1 = (\<lambda>(t, rel). memR (flip_int_less_lower (args_ivl args)) (nt - t))"
    define f2 :: "ts \<times> 'a table \<times> 'a table \<Rightarrow> bool" where "f2 = (\<lambda>(t, rel). \<not>memL (args_ivl args) (nt - t))"

    assume "\<not>mem (args_ivl args) 0"
    then have not_memL: "\<not>memL (args_ivl args) 0" by auto

    have mem_simp: "\<forall>t.
      ( memR (flip_int_less_lower (args_ivl args)) (nt - t))  =
      (\<not>memL (args_ivl args) (nt - t))"
      using flip_int_less_lower_memR[OF not_memL]
      by auto
    {
      fix x::"ts \<times> 'a table \<times> 'a table"

      have "f1 x = (memR (flip_int_less_lower (args_ivl args)) (nt - fst x))"
        unfolding f1_def
        by auto
      moreover have "f2 x = (\<not>memL (args_ivl args) (nt - fst x))"
        unfolding f2_def
        by auto
      ultimately have "f1 x = f2 x"
        using mem_simp
        by auto
    }
    then have "f1 = f2"
      by auto

    then have filter_eq: "(filter f1 (auxlist_data_prev args mt auxlist)) =
                    (filter f2 (auxlist_data_prev args mt auxlist))"
      by auto

    have "(filter (\<lambda>(t, rel).  memR (flip_int_less_lower (args_ivl args)) (nt - t)) (auxlist_data_prev args mt auxlist)) =
          (filter (\<lambda>(t, rel). \<not>memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist))"
      using filter_eq
      unfolding f1_def f2_def
      by (auto simp only:)

    then have "ts_tuple_rel_binary_lhs (set (filter (\<lambda>(t, rel). memR (flip_int_less_lower (args_ivl args)) (nt - t)) (auxlist_data_prev args mt auxlist))) =
               ts_tuple_rel_binary_lhs (set (filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist)))"
      by auto
    then have "ts_tuple_rel_binary_lhs (set (filter (\<lambda>(t, rel). \<not> memL (args_ivl args) (nt - t)) (auxlist_data_prev args mt auxlist))) =
    {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). \<exists>db'. tas = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db'}"
      using shift_end_props(2)
      by auto
  }
  ultimately have ts_tuple: "ts_tuple_rel_binary_lhs (set (auxlist_data_prev args nt auxlist)) =
    {db \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). \<exists>db'. db = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db'}"
    using filter_data_prev_nt
    by auto
  

  {
    assume assm: "mem (args_ivl args) 0"
    then have tuple_in_once_empty: "tuple_in_once = Mapping.empty" using tuple_in_once_mem0[OF assms(1)] by auto
    have filter_simp:"(\<lambda>el tuple_in. Mapping.filter ((case el of (t, X) \<Rightarrow> \<lambda>tuple_in. filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) tuple_in) tuple_in) =
      (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) tuple_in)"
      by auto
    have "fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) tuple_in)
   (snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev)) Mapping.empty = Mapping.empty"
      (* Mapping.filter (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) *)
      using 
        fold_Mapping_filter_empty[of
          "\<lambda>(t, X) tuple_in. (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t)"
          "(snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR (flip_int_less_lower (args_ivl args)) (nt - t)) data_prev))"]
      by (auto simp only: filter_simp)
   
    then have "tuple_in_once' = Mapping.empty" "tuple_in_once = Mapping.empty"
      using tuple_in_once_empty shift_end_props(6) shift_end_props(8)
      by auto
  }
  then have mem0: "mem (args_ivl args) 0 \<Longrightarrow> tuple_in_once = Mapping.empty \<and> tuple_in_once' = Mapping.empty"
    by auto

  {
    assume "\<not>mem (args_ivl args) 0"
    then have False: "\<not>memL (args_ivl args) 0" by auto

    have "tuple_in_once' = fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) tuple_in)
        move tuple_in_once"
      using shift_end_props(8)
      by auto
    then have tuple_in_once'_eq: "tuple_in_once' = fold (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) tuple_in)
      (snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev)) tuple_in_once"
      unfolding move_def
      using flip_int_less_lower_memR[OF False]
      by auto
    define fold_fn :: "(nat \<times> 'a option list set \<times> 'a option list set) \<Rightarrow> ('a option list, nat) mapping \<Rightarrow> ('a option list, nat) mapping"
      where "fold_fn = (\<lambda>(t, X) tuple_in. Mapping.filter (filter_cond_r (fst X) (restrict (args_L args)) tuple_in t) tuple_in)"
    define fold_list where "fold_list = (snd (takedropWhile_queue (\<lambda>(t, X). memL (args_ivl args) (nt - t)) data_prev))"
    then have tuple_in_once'_eq: "tuple_in_once' = fold fold_fn fold_list tuple_in_once"
      using tuple_in_once'_eq
      unfolding fold_fn_def fold_list_def
      by simp

    from fold_list_def have fold_list_props: "\<forall>(t, X) \<in> set fold_list. memL (args_ivl args) (nt - t)"
      using takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
      set_takeWhileD
      unfolding fold_list_def
      by fastforce

    {
      fix tuple
      assume t'_props: "Mapping.lookup tuple_in_once tuple = None"     
      then have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = None"
        using fold_Mapping_filter_None[of tuple_in_once tuple "(restrict (args_L args))" fst fold_list]
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
        using tuple_in_once'_eq t'_props
        by auto
    }
    then have none: "\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      by auto

    {
      fix t tuple
      assume t_props: "Mapping.lookup tuple_in_once tuple = Some t" "memL (args_ivl args) (nt - t)"
      from assms(1) have "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> (restrict (args_L args) as) \<in> l)"
        by auto
      then obtain X where X_props: "(t, X) \<in> set (linearize data_prev)" "(restrict (args_L args) tuple) \<in> fst X"
        using t_props
        by (smt Mapping_keys_intro fst_conv option.simps(3) option.simps(5))
      then obtain i where i_props: "i \<in> {0..<length (linearize data_prev)}" "(linearize data_prev)!i = (t, X)"
        by (meson atLeastLessThan_iff leI not_less0 nth_the_index the_index_bounded)
      {
        assume assm: "(t, X) \<notin> set (takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        then have "\<exists>j. j<i \<and> \<not>((\<lambda>(t, X). memL (args_ivl args) (nt - t)) ((linearize data_prev)!j))"
        (* generated subproof *)
        proof -
          have f1: "i = length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) \<or> length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) < i"
            using assm i_props(2)
            by (metis (no_types) in_set_conv_nth linorder_neqE_nat takeWhile_nth)
          have "length (takeWhile (\<lambda>(n, p). memL (args_ivl args) (nt - n)) (linearize data_prev)) < length (linearize data_prev)"
            using X_props(1) assm
            by (metis (no_types) length_takeWhile_less takeWhile_eq_all_conv)
          then show ?thesis
            using f1 i_props(2) t_props(2) nth_length_takeWhile
            by fastforce
        qed
        then obtain j where j_props: "j<i" "\<not>memL (args_ivl args) (nt - (fst ((linearize data_prev)!j)))"
          by fastforce
        moreover have "fst ((linearize data_prev)!j) \<le> fst ((linearize data_prev)!i)"
          using i_props(1) j_props(1) data_sorted[OF assms(1)]
          by (smt atLeastLessThan_iff le_less_trans length_map less_imp_le_nat nth_map sorted_nth_mono)
        ultimately have "\<not>memL (args_ivl args) (nt - (fst ((linearize data_prev)!i)))"
          using j_props memL_mono
          by auto
        then have "False" using i_props t_props by auto
      }
      then have "(t, X) \<in> set (takeWhile (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev))"
        using t_props(2)
        by auto
      then have "(t, X) \<in> set fold_list"
        unfolding fold_list_def
        using takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
        by auto
      then have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = None"
        using fold_Mapping_filter_Some_None[of tuple_in_once tuple t "(restrict (args_L args))" fst _ fold_list] t_props(1) X_props(2)
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once' tuple = None"
        using tuple_in_once'_eq
        by auto
    }
    then have Some_none:
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None"
      by auto

    {
      fix t tuple
      assume t_props: "Mapping.lookup tuple_in_once tuple = Some t" "\<not>memL (args_ivl args) (nt - t)"
      {
        fix X
        assume "(t, X) \<in> set fold_list"
        then have "memL (args_ivl args) (nt - t)"
          using fold_list_props
          by auto
        then have "False" using t_props by auto
      }
      then have "(\<And>X. (t, X) \<in> set fold_list \<Longrightarrow> restrict (args_L args) tuple \<notin> fst X)" by auto
      moreover have "Mapping.lookup tuple_in_once tuple = Some t" using t_props by auto
      ultimately have "Mapping.lookup (fold fold_fn fold_list tuple_in_once) tuple = Mapping.lookup tuple_in_once tuple"
        using fold_Mapping_filter_Some_Some[of tuple_in_once tuple t fold_list "(restrict (args_L args))" fst]
        unfolding fold_fn_def
        by auto
      then have "Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
        using tuple_in_once'_eq
        by auto
    }
    then have tuple_in_once_eq_Some:
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      "\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None"
      "\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      using none Some_none
      by auto
  }
  then have
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t  \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    by auto

  moreover {
    assume "mem (args_ivl args) 0"
    then have "\<forall>tuple. Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
      using mem0
      by auto
  }
  ultimately have tuple_in_once_lookup:
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t  \<and> \<not> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> memL (args_ivl args) (nt - t)) \<longrightarrow> Mapping.lookup tuple_in_once' tuple = None)"
    "\<not>mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = None \<longrightarrow> Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    "mem (args_ivl args) 0 \<longrightarrow> (\<forall>tuple. Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple)"
    by auto

  have tuple_in_once'_subseteq: "Mapping.keys tuple_in_once' \<subseteq> Mapping.keys tuple_in_once"
  proof (cases "mem (args_ivl args) 0")
  case True
    then show ?thesis using mem0 by blast
  next
    case False
    {
      fix k
      assume "k \<in> Mapping.keys tuple_in_once'"
      then have "k \<in> Mapping.keys tuple_in_once"
        using False tuple_in_once_lookup(3)
        by (metis domIff keys_dom_lookup)
    }
    then show ?thesis by auto
  qed

  {
    fix timed_tuple
    assume assm: "(fst timed_tuple, (restrict (args_L args) (snd timed_tuple))) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev'))"
    define t where "t = fst timed_tuple"
    define tuple where "tuple = (snd timed_tuple)"
    
    (* as we update tuple_in_once here and used it at the same time as a condition (in mmsaux, the condition is with since
       we have to show separately that the condition is the same for the old & new mapping *)
    have "valid_tuple tuple_in_once timed_tuple = valid_tuple tuple_in_once' timed_tuple"
    proof (cases "mem (args_ivl args) 0")
      case True
      then show ?thesis
        using mem0
        unfolding valid_tuple_def
        by auto
    next
      define A where "A = fst ` {
          tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev)).
          restrict (args_L args) tuple = snd tas
        }"
      case False
      have "(t, (restrict (args_L args) tuple)) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev))"
        using assm shift_end_props(7)
        unfolding t_def tuple_def ts_tuple_rel_f_def
        by auto
      then have t_mem: "t \<in> A"
        using restrict_double_appl[of "args_L args" tuple]
        unfolding A_def
        by force
      then have A_props: "A \<noteq> {}" "finite A"
        unfolding A_def
        by (auto simp add: finite_fst_ts_tuple_rel)
      have zero_not_memL: "\<not> memL (args_ivl args) 0" using False by auto
      from assm obtain X where X_props: "(t, X) \<in> (set (linearize data_prev'))"
        unfolding ts_tuple_rel_f_def t_def
        by auto
      then have "memR (flip_int_less_lower (args_ivl args)) (nt - t)"
        using shift_end_props(7)
        by auto
      then have t_not_memL: "\<not>memL (args_ivl args) (nt - t)"
        using flip_int_less_lower_memR[OF zero_not_memL]
        by auto
      
      show ?thesis
      proof (rule iffI)
        assume "valid_tuple tuple_in_once timed_tuple"
        then obtain t' where t'_props: "Mapping.lookup tuple_in_once tuple = Some t'" "fst timed_tuple \<ge> t'"
          unfolding valid_tuple_def tuple_def
          by (metis (no_types, lifting) case_optionE case_prod_beta)
        from assms(1) have "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev tuple_in_once (\<lambda>x. True)"
          by auto
        then have "Mapping.lookup tuple_in_once tuple = safe_max A"
          unfolding newest_tuple_in_mapping_def A_def
          by auto
        then have "t' \<ge> t" using A_props t_mem t'_props
          unfolding safe_max_def
          by auto
        then have t'_not_memL: "\<not>memL (args_ivl args) (nt - t')"
          using t_not_memL memL_mono
          by auto
        then have "Mapping.lookup tuple_in_once' tuple = Some t'" "fst timed_tuple \<ge> t'"
          using False t'_props tuple_in_once_lookup(1)
          by auto
        then have "\<exists>t'. Mapping.lookup tuple_in_once' tuple = Some t' \<and> fst timed_tuple \<ge> t'" by auto
        then show "valid_tuple tuple_in_once' timed_tuple"
          unfolding tuple_def valid_tuple_def
          by auto
      next
        assume "valid_tuple tuple_in_once' timed_tuple"
        then obtain t' where t'_props:
          "Mapping.lookup tuple_in_once' tuple = Some t'"
          "fst timed_tuple \<ge> t'"
          unfolding valid_tuple_def tuple_def
          by (metis (no_types, lifting) case_optionE case_prod_beta')
        {
          assume "Mapping.lookup tuple_in_once tuple \<noteq> Mapping.lookup tuple_in_once' tuple"
          then have "Mapping.lookup tuple_in_once tuple = None \<or> (\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> t\<noteq>t')"
            using t'_props option.exhaust_sel
            by auto
          moreover {
            assume "Mapping.lookup tuple_in_once tuple = None"
            then have "False"
              using False t'_props tuple_in_once_lookup(3)
              by auto
          }
          moreover {
            assume "\<exists>t. Mapping.lookup tuple_in_once tuple = Some t \<and> t\<noteq>t'"
            then obtain t'' where t''_props: "Mapping.lookup tuple_in_once tuple = Some t''" "t''\<noteq>t'"
              by auto
            from assms(1) have "newest_tuple_in_mapping fst (restrict (args_L args)) data_prev tuple_in_once (\<lambda>x. True)"
              by auto
            then have "Mapping.lookup tuple_in_once tuple = safe_max A"
              unfolding newest_tuple_in_mapping_def A_def
              by auto
            then have "t'' \<ge> t"
              using A_props t_mem t''_props(1)
              unfolding safe_max_def
              by auto
            then have "\<not>memL (args_ivl args) (nt - t'')"
              using t_not_memL memL_mono
              by auto
            then have "False"
              using False t'_props t''_props tuple_in_once_lookup(1)
              by auto
          }
          ultimately have "False" by blast
        }
        then have "Mapping.lookup tuple_in_once tuple = Mapping.lookup tuple_in_once' tuple"
          by blast
        then have "Mapping.lookup tuple_in_once tuple = Some t' \<and> fst timed_tuple \<ge> t'"
          using tuple_in_once_lookup(1) t'_props
          unfolding tuple_def
          by auto
        then have "\<exists>t'. Mapping.lookup tuple_in_once tuple = Some t' \<and> fst timed_tuple \<ge> t'" by auto
        then show "valid_tuple tuple_in_once timed_tuple"
          unfolding tuple_def valid_tuple_def
          by auto
      qed
    qed
  }
  then have valid_tuple_in_once: "\<forall>timed_tuple. (fst timed_tuple, restrict (args_L args) (snd timed_tuple)) \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')) \<longrightarrow>
  valid_tuple tuple_in_once timed_tuple = valid_tuple tuple_in_once' timed_tuple"
    by auto
  then have "{db \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). \<exists>db'. db = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once db'} =
    {db \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')). \<exists>db'. db = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once' db'}"
    by blast
  then show ts_tuple_rel_binary_lhs_data_prev: "ts_tuple_rel_binary_lhs (set (auxlist_data_prev args nt auxlist)) =
    {tas \<in> ts_tuple_rel_binary_lhs (set (linearize data_prev')).
    \<exists>db'. tas = (fst db', (restrict (args_L args) (snd db'))) \<and> valid_tuple tuple_in_once' db'}"
    using ts_tuple shift_end_props(2)
    by auto


  from assms(1) have
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as)"
    by auto

  then show
    "(\<forall>as \<in> \<Union>((relL) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_L args) as)"
    "(\<forall>as \<in> \<Union>((relR) ` (set (linearize data_prev'))). wf_tuple (args_n args) (args_R args) as)"
    using shift_end_props(7)
    by auto

  from assms(1) have tuple_in_once_props:
    "(\<forall>as \<in> Mapping.keys tuple_in_once. case Mapping.lookup tuple_in_once as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev) \<and> (restrict (args_L args) as) \<in> l)"
    by auto
  {
    fix as t
    assume assm: "Mapping.lookup tuple_in_once' as = Some t"
    then have "\<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> (restrict (args_L args) as) \<in> l"
    proof (cases "mem (args_ivl args) 0")
      case True
      then show ?thesis
        using assm mem0
        by (simp add: Mapping.lookup_empty)
    next
      case False
      from assm have "as \<in> Mapping.keys tuple_in_once'"
        by (simp add: Mapping_keys_intro)
      then have as_mem: "as \<in> Mapping.keys tuple_in_once"
        using assm tuple_in_once'_subseteq
        by auto
      then obtain t' where t'_props: "Mapping.lookup tuple_in_once as = Some t'"
        using Mapping_keys_dest[of as tuple_in_once]
        by auto
      show ?thesis
      proof (cases "memL (args_ivl args) (nt - t')")
        case True
        then have "Mapping.lookup tuple_in_once' as = None"
          using False t'_props tuple_in_once_lookup(2)
          by auto
        then show ?thesis using assm by auto
      next
        case not_memL: False
        then have "Mapping.lookup tuple_in_once' as = Some t'"
          using False t'_props tuple_in_once_lookup(1)
          by auto
        then have t_eq: "t=t'" "Mapping.lookup tuple_in_once as = Some t"
          using assm t'_props
          by auto
        then obtain l r where tlr_props: "(t, l, r) \<in> set (linearize data_prev)" "(restrict (args_L args) as) \<in> l"
          using as_mem tuple_in_once_props
          by fastforce
        then have "(t, l, r) \<in> set (linearize data_prev')"
          using False not_memL data_prev'_eq t_eq(1)
          by auto
        then show ?thesis
          using tlr_props  
          by auto
      qed
    qed
  }
  then show "(\<forall>as \<in> Mapping.keys tuple_in_once'. case Mapping.lookup tuple_in_once' as of Some t \<Rightarrow> \<exists>l r. (t, l, r) \<in> set (linearize data_prev') \<and> (restrict (args_L args) as) \<in> l)"
    using Mapping_keys_dest
    by fastforce

  have filter_simp: "(\<lambda>(t, _). mem (args_ivl args) (nt - t)) = (\<lambda>x. (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t)))" by auto
  have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    unfolding drop_prev_len_def move_filter move'_eq
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_prev))"
    by (auto simp add: filter_simp)
  then have "drop_prev_len = length (filter (\<lambda>(t, X). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by auto
  moreover have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) =
    length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) +
    length (filter (\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t))) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)"]
    by auto
  ultimately have "drop_prev_len = length (filter (\<lambda>x. \<not> (case x of (t, _) \<Rightarrow> memR (args_ivl args) (nt - t))) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    by (simp add: case_prod_beta')
  then have "drop_prev_len = length (filter (\<lambda>x. (case x of (t, _) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, _) \<Rightarrow> \<not> memR (args_ivl args) (nt - t))) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by auto
  then have "drop_prev_len = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by (simp add: case_prod_beta')
  moreover have "\<forall>t. (memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) = (\<not> memR (args_ivl args) (nt - t))"
    using not_memR_imp_memL[of args]
    by auto
  ultimately have drop_prev_len_eq: "drop_prev_len = length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  from assms(1) have data_prev_len: "length (linearize data_prev) = idx_next - idx_mid" by auto

  have "length (linearize data_prev') = length (filter (\<lambda>(t, _). \<not> memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using data_prev'_eq
    by auto (* not_memL_imp_memR *)
  then have lin_prev'_len: "length (linearize data_prev') = length (filter (\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t))) (linearize data_prev))"
    by (metis (mono_tags, lifting) case_prod_beta' filter_cong)
  
  have idx_mid_eq: "idx_mid' = idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using idx_mid'_def move_filter
    by blast

  then have "idx_mid' - idx_mid = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto

  then have "length (linearize data_prev') + (idx_mid' - idx_mid) = length (linearize data_prev)"
    using lin_prev'_len sum_length_filter_compl[of "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  
  then show "length (linearize data_prev') = idx_next - idx_mid'"
    using data_prev_len
    by (simp add: idx_mid'_def)

  from assms(1) have data_in_len: "length (linearize data_in) + idx_oldest = idx_mid" by auto
  then have mid_geq_old: "idx_mid \<ge> idx_oldest" by auto

  have idx_oldest'_eq: "idx_oldest' = idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len"
    using idx_oldest'_def
    unfolding drop_def
    using takedropWhile_queue_snd[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
      data_sorted[OF assms(1)] sorted_filter_takeWhile_not_memR[of "linearize data_in" args nt]
    by auto
  then have "idx_mid' + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len = idx_oldest' + idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using idx_mid_eq
    by auto
  then have len_eq: "idx_mid' + idx_oldest + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) + drop_prev_len = idx_oldest' + idx_mid + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  have "(\<forall>x. (\<not> memR (args_ivl args) (fst x)) \<longrightarrow> (memL (args_ivl args) (fst x)))"
    using not_memR_imp_memL[of args]
    by auto
  then have prev_not_memR_leq_prev_memL: "length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) \<le> length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_imp[of "\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)" "\<lambda>(t, _). memL (args_ivl args) (nt - t)" "linearize data_prev"]
    by auto
  have "idx_oldest' \<le> idx_mid + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    unfolding idx_oldest'_eq drop_prev_len_eq
    using data_in_len
    by auto
  then have mid'_geq_old': "idx_oldest' \<le> idx_mid'"
    unfolding idx_mid_eq
    using prev_not_memR_leq_prev_memL
    by auto

  have "linearize data_in'' = linearize data_in' @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) move)"
    using data_in''_def fold_append_queue_map[of move' data_in'] move'_def
    by auto
  then have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)))"
    using data_in'_def takedropWhile_queue_fst[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
          data_sorted[OF assms(1)]
          dropWhile_queue_rep[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" data_in]
          sorted_filter_dropWhile_memR[of "linearize data_in" args nt] move_def
          takedropWhile_queue_snd[of "(\<lambda>(t, X). memL (args_ivl args) (nt - t))" data_prev]
          sorted_filter_takeWhile_memL[of "linearize data_prev" args nt]
    by auto
  moreover have "filter (\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_prev) = filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev)"
    by (simp add: case_prod_beta')
  ultimately have "linearize data_in'' = filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in) @ map (\<lambda>(t, l, r). (t, r)) (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  then have "length (linearize data_in'') = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (linearize data_in)) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "(linearize data_prev)"]
    by auto
  then have "length (linearize data_in'') + length (filter (\<lambda>x. \<not> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(linearize data_in)"]
    by auto
  then have data_in''_len: "length (linearize data_in'') + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by (auto simp add: case_prod_beta')

  have filter_simp: "(\<lambda>x. (case x of (t, uu_) \<Rightarrow> memL (args_ivl args) (nt - t)) \<and> (case x of (t, uu_) \<Rightarrow> memR (args_ivl args) (nt - t))) = (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t))"
    by auto

  have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    using sum_length_filter_compl[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)"]
          filter_filter[of "(\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by (auto simp add: case_prod_beta')
  moreover have "\<forall>t. (memL (args_ivl args) (nt - t) \<and> \<not> memR (args_ivl args) (nt - t)) = (\<not> memR (args_ivl args) (nt - t))"
    using not_memR_imp_memL[of args]
    by auto
  ultimately have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memR (args_ivl args) (nt - t)) (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  then have "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t) \<and> memR (args_ivl args) (nt - t)) (linearize data_prev)) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev))"
    using filter_filter[of "(\<lambda>(t, _). memR (args_ivl args) (nt - t))" "(\<lambda>(t, _). memL (args_ivl args) (nt - t))" "linearize data_prev"]
    by (auto simp add: filter_simp)
  then have len_simp: "length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) = length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by auto
  have "idx_mid' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)) + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + idx_oldest' + length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev))"
    using len_eq idx_mid_eq data_in_len drop_prev_len_eq
    by auto
  then have "idx_mid' - idx_oldest' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + (length (filter (\<lambda>(t, _). memL (args_ivl args) (nt - t)) (linearize data_prev)) - length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_prev)))"
    using mid'_geq_old' prev_not_memR_leq_prev_memL
    by auto
  then have "idx_mid' - idx_oldest' + length (filter (\<lambda>(t, _). \<not> memR (args_ivl args) (nt - t)) (linearize data_in)) = length (linearize data_in) + length (filter (\<lambda>(t, _). mem (args_ivl args) (nt - t)) (linearize data_prev))"
    by (auto simp only: len_simp)
  then show "length (linearize data_in'') = idx_mid' - idx_oldest'"
    using data_in''_len
    by auto
qed


fun shift_end_hist_mmtaux :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> (ts \<times> 'a table \<times> 'a table) list \<Rightarrow> (ts \<times> 'a table) queue \<Rightarrow> (('a tuple, ts) mapping) \<Rightarrow> (('a tuple, ts) mapping)" where
  "shift_end_hist_mmtaux idx_move idx_oldest maskR move data_in tuple_since_hist = (
  let \<comment> \<open>we now have to update hist_since using the tables in move. in particular, for all dbs inside move,
       we have to do some sort of join with the keys of hist_since\<close>
    (tuple_since_hist, idx_move) = fold (\<lambda>(t, l, r) (tuple_since_hist, idx_move).
      let tuple_since_hist = Mapping.filter (\<lambda>as _. proj_tuple_in_join True maskR as r) tuple_since_hist in \<comment> \<open>filter entries that are not present in the current db\<close>
      (
        Finite_Set.fold (\<lambda>as tuple_since_hist. Mapping.update as idx_move tuple_since_hist) tuple_since_hist r, \<comment> \<open>then add entries for the ones that are present in the current db\<close>
        idx_move+1 \<comment> \<open>increase index by one every db\<close>
      ) 
    ) move (tuple_since_hist, idx_move) in
    tuple_since_hist
  )"

lemma valid_shift_end_hist_mmtaux:
  assumes valid_before: "valid_mmtaux args cur
    (mt, idx_next, idx_mid, idx_oldest, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  assumes nt_mono: "nt \<ge> cur"
  assumes "(idx_mid', idx_oldest', data_prev', move, data_in', tuple_in_once') = shift_end_queues_mmtaux args nt idx_mid idx_oldest data_prev data_in tuple_in_once"
  assumes "tuple_since_hist' = shift_end_hist_mmtaux idx_mid idx_oldest maskL move data_in' tuple_since_hist"
  shows "valid_mmtaux args cur
    (nt, idx_next', idx_mid', idx_oldest', maskL, maskR, data_prev', data_in', tuple_in_once', tuple_since_hist', since_sat) auxlist"
proof -

qed

(* analogous to add_new_ts_mmsaux' except that tuple_in doesn't exist / isn't updated *)
fun add_new_ts_mmtaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmtaux \<Rightarrow> 'a mmtaux" where
  "add_new_ts_mmtaux args nt (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) = (
    \<comment> \<open>in a first step, we update tuple_in_once by removing all tuples where currently a ts
       is stored, that points to a db that with the new ts (nt) no longer is part of
       [0, a-1] / data_prev\<close>
    let (data_in, in_discard, data_prev, prev_discard, tuple_in_once) = shift_end
      (flip_int_less_lower (args_ivl args)) \<comment> \<open>[0, a-1]\<close>
      nt \<comment> \<open>the new timestamp\<close>
      fst \<comment> \<open>here we look at the lhs tuples / \<phi>\<close>
      (restrict (args_L args)) \<comment> \<open>we have to restrict the tuples of the lhs to the respective cols\<close>
      (data_in, data_prev, tuple_in_once) \<comment> \<open>pass data_in as the first argument as we simply want
                                             the filtered queue & the discarded values separated.
                                             the since mappings do not have to be updated here\<close>
    in
    \<comment> \<open>the only thing we actually did was to update tuple_in_once.
       the first return value will of course be empty again and the second one
       is data_prev filtered by [0, a-1] which would be okay but the results
       are discarded which is not what we want.\<close>

    \<comment> \<open>in a next step, we drop all entries of data_prev where the entries are not part of the
       new interval. this can be done without issue as the only possible inconsistency would
       be regarding tuple_in_once which we already updated. (if the tuple isn't part of [0, b] anymore,
       then it obviously isn't part of [0, a-1] either and hence was already removed from the mapping)\<close>
    \<comment> \<open>it is tempting to do the same with data_in, the issue there is that this needs more careful
       handling as for the dropped out tuples, different conditions have to be checked and
       mappings might have to be updated. in particular it is possible, that the tuples in the
       dropped db now satisfy the historically condition and hence have to be added to this mapping.\<close>
    ()
  )"

lemma valid_add_new_ts_mmtaux:
  assumes "nt \<ge> cur"
  assumes "valid_mmtaux args cur (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) auxlist"
  shows "valid_mmtaux
      args
      nt
      (add_new_ts_mmtaux args nt (mt, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat))
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
  "update_mmtaux args nt l r (cur, maskL, maskR, data_prev, data_in, tuple_in_once, tuple_since_hist, since_sat) =


  (
    nt,
    maskL,
    maskR,
    data_prev,
    data_in,
    tuple_in_once,
    tuple_since_hist,
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