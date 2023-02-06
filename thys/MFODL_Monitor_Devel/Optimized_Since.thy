(*<*)
theory Optimized_Since
  imports Optimized_Common
begin
(*>*)

section \<open>Optimized data structure for Since\<close>

type_synonym 'a mmsaux = "ts \<times> ts \<times> bool list \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times>
  'a table \<times> 'a wf_table \<times> (('a tuple, ts) mapping) \<times> 'a wf_table \<times> (('a tuple, ts) mapping)"

fun time_mmsaux :: "'a mmsaux \<Rightarrow> ts" where
  "time_mmsaux aux = (case aux of (nt, _) \<Rightarrow> nt)"

fun valid_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool" where
  "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, 
  tuple_in, wf_table_since, tuple_since) ys 
  \<longleftrightarrow>
    (args_L args) \<subseteq> (args_R args) \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, X) \<in> set ys. table (args_n args) (args_R args) X) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_in) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_in))). wf_tuple (args_n args) (args_R args) as) \<and>
    cur = nt \<and>
    ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas} \<and>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> \<not> memL (args_ivl args) (nt - t)) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> memL (args_ivl args) (nt - t)) \<and>
    table_in = Mapping.keys tuple_in \<and>
    wf_table_sig wf_table_in = (args_n args, args_R args) \<and>
    wf_table_set wf_table_in = Mapping.keys tuple_in \<and>
    wf_table_sig wf_table_since = (args_n args, args_R args) \<and>
    wf_table_set wf_table_since = Mapping.keys tuple_since \<and>
    (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas \<and> as = snd tas})) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt)"

lemma valid_mmsaux_tuple_in_keys: "valid_mmsaux args cur
  (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys \<Longrightarrow>
  Mapping.keys tuple_in = snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
  valid_tuple tuple_since tas}"
  by (auto intro!: Mapping_keys_intro safe_max_Some_intro
      dest!: Mapping.in_keysD safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel]
      simp add: newest_tuple_in_mapping_def)+

definition wf_table_of_set_args :: "args \<Rightarrow> 'a table \<Rightarrow> 'a wf_table" where
  "wf_table_of_set_args args X = wf_table_of_idx (wf_idx_of_set (args_n args) (args_R args) (args_L args) X)"

lemma wf_table_sig_args: "wf_table_sig (wf_table_of_set_args args X) = (args_n args, args_R args)"
  by (auto simp: wf_table_of_set_args_def wf_idx_sig_of_set)

lemma wf_table_of_set_args: "table (args_n args) (args_R args) X \<Longrightarrow>
  wf_table_set (wf_table_of_set_args args X) = X"
  by (auto simp: wf_table_of_set_args_def wf_idx_set_of_set table_def)

lemma wf_table_of_set_args_wf_table_set: "wf_table_sig t = (args_n args, args_R args) \<Longrightarrow>
  wf_table_of_set_args args (wf_table_set t) = t"
  by (auto simp: wf_table_sig_args wf_table_of_set_args[OF wf_table_set_table] intro: wf_table_eqI)

fun init_mmsaux :: "args \<Rightarrow> 'a mmsaux" where
  "init_mmsaux args = (0, 0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue,
  {}, wf_table_of_idx (wf_idx_of_set (args_n args) (args_R args) (args_L args) {}), Mapping.empty,
  wf_table_of_set_args args {}, Mapping.empty)"

lemma valid_init_mmsaux: "L \<subseteq> R \<Longrightarrow> valid_mmsaux (init_args I n L R b agg) 0
  (init_mmsaux (init_args I n L R b agg)) []"
  by (auto simp add: init_args_def empty_queue_rep ts_tuple_rel_f_def join_mask_def
      safe_max_def table_def wf_table_of_set_args_def wf_idx_sig_of_set wf_idx_set_of_set)

fun shift_end :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" 
  where "shift_end args nt (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, 
  tuple_in, wf_table_since, tuple_since) =
    (let I = args_ivl args;
    data_prev' = dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev;
    (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in;
    (tuple_in, del) = fold filter_set discard (tuple_in, {}) in
    (t, gc, maskL, maskR, data_prev', data_in,
     table_in - del, wf_table_antijoin wf_table_in (wf_table_of_set_args args del), tuple_in,
     wf_table_since, tuple_since))"

lemma valid_shift_end_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args cur (shift_end args nt
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
proof -
  define I where "I = args_ivl args"
  define data_in' where "data_in' \<equiv>
    fst (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
  define data_prev' where "data_prev' \<equiv>
    dropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_prev"
  define discard where "discard \<equiv>
    snd (takedropWhile_queue (\<lambda>(t, X). \<not> memR I (nt - t)) data_in)"
  have set_discard: "\<Union>(snd ` set discard) \<subseteq> \<Union>(snd ` (set (linearize data_in)))"
    by (auto simp: discard_def takedropWhile_queue_snd simp del: takedropWhile_queue.simps dest: set_takeWhileD)
  obtain tuple_in' del where fold_filter_set: "fold filter_set discard (tuple_in, {}) = (tuple_in', del)"
    by (cases "fold filter_set discard (tuple_in, {})") auto
  have tuple_in_Some_None: "Mapping.lookup tuple_in' as = None" "as \<in> del"
    if "Mapping.lookup tuple_in as = Some t" "as \<in> X" "(t, X) \<in> set discard" for as t X
    using fold_filter_set_Some_None[OF _ _ _ fold_filter_set] that
    by auto
  have tuple_in_Some_Some: "Mapping.lookup tuple_in' as = Some t" "as \<notin> del"
    if "Mapping.lookup tuple_in as = Some t" "\<And>X. (t, X) \<in> set discard \<Longrightarrow> as \<notin> X" for as t
    using fold_filter_set_Some_Some[OF _ _ fold_filter_set] that
    by auto
  have tuple_in_None: "Mapping.lookup tuple_in' as = None" "as \<notin> del"
    if "Mapping.lookup tuple_in as = None" for as
    using fold_filter_set_None[OF _ fold_filter_set] that
    by auto
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_Some_None tuple_in_Some_Some tuple_in_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using valid_before nt_mono by auto
  have lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1(1)] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  have "sorted (map fst (linearize data_in))"
    using valid_before by auto
  then have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter by auto
  have discard_alt: "discard = filter (\<lambda>(t, X). \<not> memR I (nt - t)) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1(1)] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). memR I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F2(1)] ..
  have "sorted (map fst (linearize data_prev))"
    using valid_before by auto
  then have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter by auto
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using ts_tuple_rel_mono[OF set_lin_data_in'] by auto
      then show ?thesis
        unfolding tuple_in_None[OF None] 
        using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> as \<in> X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "as \<in> X"
          by auto
        have "\<not> memR I (nt - t)"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        ultimately have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (fastforce simp add: ts_tuple_rel_f_def memR_antimono)
        then show ?thesis
          unfolding tuple_in_Some_None[OF Some X_def(2,1)]
          using iffD2[OF safe_max_empty, symmetric] by blast
      next
        case False
        then have lookup_Some: "Mapping.lookup tuple_in' as = Some t"
          using tuple_in_Some_Some[OF Some] by auto
        have t_as: "(t, as) \<in> ts_tuple_rel (set (linearize data_in))"
          "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then obtain X where X_def: "as \<in> X" "(t, X) \<in> set (linearize data_in)"
          by (auto simp add: ts_tuple_rel_f_def)
        have "(t, X) \<in> set (linearize data_in')"
          using X_def False unfolding discard_alt lin_data_in' by auto
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}"
          using t_as(2) X_def(1) by (auto simp add: ts_tuple_rel_f_def image_iff)
        have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel, OF _ t_in_fst]
            ts_tuple_rel_mono[OF set_lin_data_in'] by fastforce
        then show ?thesis
          unfolding lookup_Some using t_in_fst by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    and table_in': "table (args_n args) (args_R args) (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  then have keys_tuple_in': "table_in - del = Mapping.keys tuple_in'"
    using tuple_in_None tuple_in'_keys tuple_in_Some_Some tuple_in_Some_None
    by auto (metis Mapping.in_keysD Mapping_keys_intro option.distinct(1))+
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_antijoin wf_table_in (wf_table_of_set_args args del)) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_antijoin)
  have "table (args_n args) (args_R args) (\<Union>(snd ` (set (linearize data_in))))"
    using valid_before
    by (auto simp: table_def)
  then have table_del: "table (args_n args) (args_R args) del"
    using fold_filter_set_sub[OF fold_filter_set] set_discard New_max.wf_atable_subset
    by fastforce
  have keys_tuple_in'': "wf_table_set (wf_table_antijoin wf_table_in (wf_table_of_set_args args del)) = Mapping.keys tuple_in'"
    by (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_antijoin[OF sig_in wf_table_sig_args subset_refl]
        join_False_alt join_eq[OF table_del wf_table_set_table[OF sig_in]]
        wf_table_set_table[OF wf_table_sig_args] wf_table_of_set_args[OF table_del])
  have "ts_tuple_rel (set auxlist) =
    {as \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since as}"
    using valid_before by auto
  then have "ts_tuple_rel (set (filter (\<lambda>(t, rel). memR I (nt - t)) auxlist)) =
    {as \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since as}"
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter by auto
  then show ?thesis
    using data_prev'_def data_in'_def fold_filter_set discard_def valid_before nt_mono
      sorted_lin_data_prev' sorted_lin_data_in' lin_data_prev' lin_data_in' lookup_tuple_in'
      table_in' keys_tuple_in' sig_in'' keys_tuple_in'' sig_since keys_since unfolding I_def
    unfolding valid_mmsaux.simps shift_end.simps Let_def split_beta
    by auto
qed

lemma valid_shift_end_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args cur (shift_end args nt aux)
  (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_shift_end_mmsaux_unfolded by (cases aux) fast

fun add_new_ts_mmsaux' :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux' args nt (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let I = args_ivl args;
    (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    (tuple_in, add) = fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})) move (tuple_in, {}) in
    (nt, gc, maskL, maskR, data_prev, data_in, table_in \<union> add, wf_table_union wf_table_in (wf_table_of_set_args args add), tuple_in, wf_table_since, tuple_since))"

lemma Mapping_keys_fold_upd_set: "k \<in> Mapping.keys (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z t X))
  xs m) \<Longrightarrow> k \<in> Mapping.keys m \<or> (\<exists>(t, X) \<in> set xs. k \<in> Z t X)"
  by (induction xs arbitrary: m) (fastforce simp add: Mapping_upd_set_keys)+

lemma valid_add_new_ts_mmsaux'_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux' args nt
    (ot, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)) auxlist"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define data_prev' where "data_prev' \<equiv> dropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev"
  define move where "move \<equiv> takeWhile (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev)"
  define data_in' where "data_in' \<equiv> fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in)
    move data_in"
  obtain tuple_in' add where aux:
    "fold (upd_set_keys (\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)})) move (tuple_in, {}) = (tuple_in', add)"
    by fastforce
  note tuple_in'_def = fold_upd_set_keys(1)[OF aux]
  note add_def = fold_upd_set_keys(2)[OF aux]
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in \<or>
    (\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)})"
    using Mapping_keys_fold_upd_set[of _ "\<lambda>t X. {as \<in> X. valid_tuple tuple_since (t, as)}"]
    by (auto simp add: tuple_in'_def)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_in). t \<le> ot \<and> memL I (ot - t)"
    using valid_before nt_mono unfolding I_def by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> ot \<and> \<not> memL I (ot - t)"
    using valid_before nt_mono unfolding I_def by auto
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). \<not> memL I (nt - t)) (linearize data_prev)"
    unfolding data_prev'_def dropWhile_queue_rep dropWhile_filter'[OF F2(1)] ..
  have move_filter: "move = filter (\<lambda>(t, X). memL I (nt - t)) (linearize data_prev)"
    unfolding move_def takeWhile_filter'[OF F2(1)] ..
  then have sorted_move: "sorted (map fst move)"
    using sorted_filter F2 by auto
  have "\<forall>t\<in>fst ` set move. t \<le> ot \<and> \<not> memL I (ot - t)"
    using move_filter F2(3) set_filter by auto
  then have fst_set_before: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t \<le> t'"
    using F1(3) by (meson le_diff_iff' memL_mono nat_le_linear)
  then have fst_ts_tuple_rel_before: "\<forall>t\<in>fst ` ts_tuple_rel (set (linearize data_in)).
    \<forall>t'\<in>fst ` ts_tuple_rel (set move). t \<le> t'"
    by (fastforce simp add: ts_tuple_rel_f_def)
  have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter F2 by auto
  have lin_data_in': "linearize data_in' = linearize data_in @ move"
    unfolding data_in'_def using fold_append_queue_rep by fastforce
  have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using F1(1) sorted_move fst_set_before by (simp add: sorted_append)
  have set_lin_prev'_in': "set (linearize data_prev') \<union> set (linearize data_in') =
    set (linearize data_prev) \<union> set (linearize data_in)"
    using lin_data_prev' lin_data_in' move_filter by auto
  have ts_tuple_rel': "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since tas}"
    unfolding set_lin_prev'_in' using valid_before by auto
  have lookup': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')).
    valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "{(t, X) \<in> set move. as \<in> X \<and> valid_tuple tuple_since (t, as)} = {}")
      case True
      have move_absorb: "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        {tas \<in> ts_tuple_rel (set (linearize data_in @ move)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        using True by (auto simp add: ts_tuple_rel_f_def)
      have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        using valid_before by auto
      then have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding lin_data_in' move_absorb .
      then show ?thesis
        using Mapping_lookup_fold_upd_set_idle[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}"] True
        unfolding tuple_in'_def by auto
    next
      case False
      have split: "fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas} \<union>
        fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        unfolding lin_data_in' set_append ts_tuple_rel_Un by auto
      have max_eq: "Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}) =
        Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding split using False fst_ts_tuple_rel_before
        by (fastforce simp add: ts_tuple_rel_f_def
            intro!: Max_Un_absorb[OF finite_fst_ts_tuple_rel _ finite_fst_ts_tuple_rel, symmetric])
      have "fst ` {(t, X). (t, X) \<in> set move \<and> as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas}"
        by (auto simp add: ts_tuple_rel_f_def image_iff)
      then have "Mapping.lookup tuple_in' as = Some (Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}))"
        using Mapping_lookup_fold_upd_set_max[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}", OF _ sorted_move] False
        unfolding tuple_in'_def by (auto simp add: ts_tuple_rel_f_def)
      then show ?thesis
        unfolding max_eq using False
        by (auto simp add: safe_max_def lin_data_in' ts_tuple_rel_f_def)
    qed
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
  proof -
    {
      fix as
      assume assm: "as \<in> Mapping.keys tuple_in'"
      have "wf_tuple n R as"
        using tuple_in'_keys[OF assm]
      proof (rule disjE)
        assume "as \<in> Mapping.keys tuple_in"
        then show "wf_tuple n R as"
          using valid_before by (auto simp add: table_def n_def R_def)
      next
        assume "\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}"
        then obtain t X where tX_def: "(t, X) \<in> set move" "as \<in> X"
          by auto
        then have "as \<in> \<Union>(snd ` set (linearize data_prev))"
          unfolding move_def using set_takeWhileD by force
        then show "wf_tuple n R as"
          using valid_before by (auto simp add: n_def R_def)
      qed
    }
    then show ?thesis
      by (auto simp add: table_def)
  qed
  have table_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  note keys_tuple_in' = add_def[symmetric]
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_union wf_table_in (wf_table_of_set_args args add)) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_union wf_table_sig_args)
  have "table (args_n args) (args_R args) (\<Union>(snd ` (set (linearize data_prev))))"
    using valid_before
    by (auto simp: table_def)
  moreover have "\<Union> (snd ` set move) \<subseteq> \<Union> (snd ` set (linearize data_prev))"
    by (auto simp: move_filter)
  ultimately have table_add: "table (args_n args) (args_R args) add"
    using fold_upd_set_keys_sub[OF _ aux] New_max.wf_atable_subset
    by fastforce
  have keys_tuple_in'': "wf_table_set (wf_table_union wf_table_in (wf_table_of_set_args args add)) = Mapping.keys tuple_in'"
    by (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_union[OF trans[OF sig_in wf_table_sig_args[symmetric]]]
        wf_table_of_set_args[OF table_add])
  have data_prev'_move: "(data_prev', move) =
    takedropWhile_queue (\<lambda>(t, X). memL I (nt - t)) data_prev"
    using takedropWhile_queue_fst takedropWhile_queue_snd data_prev'_def move_def
    by (metis surjective_pairing)
  moreover have "valid_mmsaux args nt (nt, gc, maskL, maskR, data_prev', data_in', table_in \<union> add,
    wf_table_union wf_table_in (wf_table_of_set_args args add), tuple_in', wf_table_since, tuple_since) auxlist"
    using lin_data_prev' sorted_lin_data_prev' lin_data_in' move_filter sorted_lin_data_in'
      nt_mono valid_before ts_tuple_rel' lookup' memL_mono[of "args_ivl args" "ot - a" "nt - a" for a]
      table_in' keys_tuple_in' sig_in'' keys_tuple_in'' sig_since keys_since unfolding I_def
    unfolding valid_mmsaux.simps Let_def n_def R_def
    by (auto split: option.splits) (* takes long *)
  ultimately show ?thesis
    by (auto simp only: add_new_ts_mmsaux'.simps Let_def data_in'_def aux tuple_in'_def I_def
        split: prod.splits)
qed


lemma valid_add_new_ts_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args nt (add_new_ts_mmsaux' args nt aux) auxlist"
  using valid_add_new_ts_mmsaux'_unfolded by (cases aux) fast

definition add_new_ts_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux args nt aux = add_new_ts_mmsaux' args nt (shift_end args nt aux)"

lemma valid_add_new_ts_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux args nt aux)
    (filter (\<lambda>(t, rel). memR (args_ivl args) (nt - t)) auxlist)"
  using valid_add_new_ts_mmsaux'[OF valid_shift_end_mmsaux[OF assms] assms(2)]
  unfolding add_new_ts_mmsaux_def .

fun join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let pos = args_pos args in
    (if (\<forall>i \<in> set maskL. \<not>i) then
      (let nones = replicate (length maskL) None;
      take_all = (pos \<longleftrightarrow> nones \<in> X);
      table_in' = (if take_all then table_in else {});
      wf_table_in' = (if take_all then wf_table_in else wf_table_of_set_args args {});
      tuple_in' = (if take_all then tuple_in else Mapping.empty);
      wf_table_since' = (if take_all then wf_table_since else wf_table_of_set_args args {});
      tuple_since' = (if take_all then tuple_since else Mapping.empty) in
      (t, gc, maskL, maskR, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'))
     else (let wf_X = wf_table_of_idx (wf_idx_of_set (args_n args) (args_L args) (args_L args) X);
      wf_in_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_in wf_X;
      in_del = wf_table_set wf_in_del;
      tuple_in' = mapping_delete_set tuple_in in_del;
      table_in' = table_in - in_del;
      wf_table_in' = wf_table_antijoin wf_table_in wf_in_del;
      wf_since_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_since wf_X;
      since_del = wf_table_set wf_since_del;
      tuple_since' = mapping_delete_set tuple_since since_del;
      wf_table_since' = wf_table_antijoin wf_table_since wf_since_del in
      (t, gc, maskL, maskR, data_prev, data_in, table_in', wf_table_in', tuple_in', wf_table_since', tuple_since'))))"

fun join_mmsaux_abs :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux_abs args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let pos = args_pos args in
    (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
    tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
    (t, gc, maskL, maskR, data_prev, data_in,
     Mapping.keys tuple_in, wf_table_of_set_args args (Mapping.keys tuple_in), tuple_in,
     wf_table_of_set_args args (Mapping.keys tuple_since), tuple_since)))"

lemma Mapping_filter_cong:
  assumes cong: "(\<And>k v. k \<in> Mapping.keys m \<Longrightarrow> f k v = f' k v)"
  shows "Mapping.filter f m = Mapping.filter f' m"
proof -
  have "\<And>k. Mapping.lookup (Mapping.filter f m) k = Mapping.lookup (Mapping.filter f' m) k"
    using cong
    by (fastforce simp add: Mapping.lookup_filter intro: Mapping_keys_intro split: option.splits)
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma Mapping_keys_filter: "Mapping.keys (Mapping.filter (\<lambda>x _. P x) m) = Set.filter P (Mapping.keys m)"
  by transfer (auto simp: Set.filter_def split: option.splits if_splits)

lemma join_mmsaux_abs_eq:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_left: "table (args_n args) (args_L args) X"
  shows "join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    join_mmsaux_abs args X (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have L_R: "args_L args \<subseteq> args_R args"
    and maskL_def: "join_mask (args_n args) (args_L args) = maskL"
    using valid_before
    by auto
  have table_in_def: "Mapping.keys tuple_in = table_in"
    and table_table_in: "table (args_n args) (args_R args) table_in"
    and table_tuple_since: "table (args_n args) (args_R args) (Mapping.keys tuple_since)"
    using valid_before
    by auto
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    and set_args_in: "wf_table_set (wf_table_of_set_args args table_in) = table_in"
    using wf_table_of_set_args valid_before
    by auto
  have sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and set_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    and set_args_since: "wf_table_set (wf_table_of_set_args args (Mapping.keys tuple_since)) = Mapping.keys tuple_since"
    using wf_table_of_set_args valid_before
    by auto
  show ?thesis
  proof (cases "\<forall>i \<in> set maskL. \<not>i")
    case True
    have length_maskL: "length maskL = n"
      using valid_before by (auto simp add: join_mask_def n_def)
    have proj_rep: "\<And>as. wf_tuple n R as \<Longrightarrow> proj_tuple maskL as = replicate (length maskL) None"
      using True proj_tuple_replicate by (force simp add: length_maskL wf_tuple_def)
    have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_in) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_in else Mapping.empty) as"
      using proj_rep[OF keys_wf_in]
      by (auto simp add: Mapping.lookup_filter proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    then have filter_in: "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in =
      (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X) then tuple_in else Mapping.empty)"
      by (auto intro!: mapping_eqI)
    have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_since) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_since else Mapping.empty) as"
      using proj_rep[OF keys_wf_since]
      by (auto simp add: Mapping.lookup_filter proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    then have filter_since: "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since =
      (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X) then tuple_since else Mapping.empty)"
      by (auto intro!: mapping_eqI)
    show ?thesis
      using True
      by (auto simp: Let_def pos_def[symmetric] filter_in filter_since table_in_def wf_table_sig_args
          sig_in set_in set_args_in sig_since set_since set_args_since intro!: wf_table_eqI)
  next
    case False
    define wf_X where "wf_X = wf_table_of_idx (wf_idx_of_set (args_n args) (args_L args) (args_L args) X)"
    define wf_in_del where "wf_in_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_in wf_X"
    define in_del where "in_del = wf_table_set wf_in_del"
    define tuple_in' where "tuple_in' = mapping_delete_set tuple_in in_del"
    define table_in' where "table_in' = table_in - in_del"
    define wf_table_in' where "wf_table_in' = wf_table_antijoin wf_table_in wf_in_del"
    define wf_since_del where "wf_since_del = (if pos then wf_table_antijoin else wf_table_join) wf_table_since wf_X"
    define since_del where "since_del = wf_table_set wf_since_del"
    define tuple_since' where "tuple_since' = mapping_delete_set tuple_since since_del"
    define wf_table_since' where "wf_table_since' = wf_table_antijoin wf_table_since wf_since_del"
    have wf_in_set: "wf_table_set wf_table_in = table_in"
      by (auto simp: set_in table_in_def)
    have wf_X_sig: "wf_table_sig wf_X = (args_n args, args_L args)"
      by (auto simp: wf_X_def wf_idx_sig_of_set)
    have wf_X_set: "wf_table_set wf_X = X"
      using table_left
      by (auto simp: wf_X_def wf_idx_set_of_set table_def)
    have wf_in_del_sig: "wf_table_sig wf_in_del = (args_n args, args_R args)"
      using L_R
      by (auto simp: wf_in_del_def wf_table_sig_join wf_table_sig_antijoin sig_in wf_X_sig)
    have in_del_set: "in_del = join table_in (\<not>pos) X"
      by (auto simp: in_del_def wf_in_del_def wf_table_set_antijoin[OF sig_in wf_X_sig L_R]
          wf_table_set_join[OF sig_in wf_X_sig refl] wf_in_set wf_X_set)
    have table_in': "Mapping.keys tuple_in' = table_in'"
      using keys_filter
      unfolding tuple_in'_def table_in'_def table_in_def[symmetric]
      by auto
    have wf_in'_sig: "wf_table_sig wf_table_in' = (args_n args, args_R args)"
      by (auto simp: wf_table_in'_def wf_table_sig_antijoin sig_in)
    have wf_in'_set: "wf_table_set wf_table_in' = table_in'"
      unfolding wf_table_in'_def table_in'_def wf_table_set_antijoin[OF sig_in wf_in_del_sig subset_refl]
        join_eq[OF wf_table_set_table[OF wf_in_del_sig] wf_table_set_table[OF sig_in]]
      unfolding wf_in_set in_del_def
      by auto
    have tuple_in': "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in = tuple_in'"
      unfolding tuple_in'_def
      by (cases pos) (auto simp: mapping_delete_set_def in_del_set table_in_def
          join_sub[OF L_R table_left table_table_in] maskL_def proj_tuple_in_join_def intro!: Mapping_filter_cong)
    have wf_since_del_sig: "wf_table_sig wf_since_del = (args_n args, args_R args)"
      using L_R
      by (auto simp: wf_since_del_def wf_table_sig_join wf_table_sig_antijoin sig_since wf_X_sig)
    have since_del_set: "since_del = join (Mapping.keys tuple_since) (\<not>pos) X"
      by (auto simp: since_del_def wf_since_del_def wf_table_set_antijoin[OF sig_since wf_X_sig L_R]
          wf_table_set_join[OF sig_since wf_X_sig refl] set_since wf_X_set)
    have wf_since'_sig: "wf_table_sig wf_table_since' = (args_n args, args_R args)"
      by (auto simp: wf_table_since'_def wf_table_sig_antijoin sig_since)
    have wf_since'_set: "wf_table_set wf_table_since' = Mapping.keys tuple_since'"
      unfolding wf_table_since'_def wf_table_set_antijoin[OF sig_since wf_since_del_sig subset_refl]
        join_eq[OF wf_table_set_table[OF wf_since_del_sig] wf_table_set_table[OF sig_since]]
      unfolding tuple_since'_def since_del_def set_since
      by auto
    have table_tuple_since': "table (args_n args) (args_R args) (Mapping.keys tuple_since')"
      using table_tuple_since
      by (auto simp: tuple_since'_def table_def)
    have tuple_since': "Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since = tuple_since'"
      unfolding tuple_since'_def
      by (cases pos) (auto simp: mapping_delete_set_def since_del_set
          join_sub[OF L_R table_left table_tuple_since] maskL_def proj_tuple_in_join_def intro!: Mapping_filter_cong)
    show ?thesis
      using False
      by (auto simp only:join_mmsaux.simps join_mmsaux_abs.simps Let_def pos_def[symmetric] wf_X_def[symmetric]
          wf_in_del_def[symmetric] in_del_def[symmetric] tuple_in'_def[symmetric] table_in'_def[symmetric] wf_table_in'_def[symmetric]
          wf_since_del_def[symmetric] since_del_def[symmetric] tuple_since'_def[symmetric] wf_table_since'_def[symmetric]
          table_in' wf_in'_set[symmetric] wf_table_of_set_args_wf_table_set[OF wf_in'_sig] tuple_in'
          wf_since'_set[symmetric] wf_table_of_set_args_wf_table_set[OF wf_since'_sig] tuple_since' split: if_splits)
  qed
qed

lemma valid_join_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_left': "table (args_n args) (args_L args) X"
  shows "valid_mmsaux args cur
    (join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  note table_left = table_left'[unfolded n_def[symmetric] L_def[symmetric]]
  define tuple_in' where "tuple_in' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in"
  define tuple_since' where "tuple_since' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since"
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    unfolding tuple_in'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  have ts_tuple_rel': "ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
    then obtain t as Z where tas_def: "tas = (t, as)" "as \<in> join Z pos X" "(t, Z) \<in> set auxlist"
      "(t, join Z pos X) \<in> set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
      by (fastforce simp add: ts_tuple_rel_f_def)
    from tas_def(3) have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    have proj: "as \<in> Z" "proj_tuple_in_join pos maskL as X"
      using tas_def(2) join_sub[OF _ table_left table_Z] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then have "(t, as) \<in> ts_tuple_rel (set (auxlist))"
      using tas_def(3) by (auto simp add: ts_tuple_rel_f_def)
    then have tas_in: "(t, as) \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in))" "valid_tuple tuple_since (t, as)"
      using valid_before by auto
    then obtain t' where t'_def: "Mapping.lookup tuple_since as = Some t'" "t \<ge> t'"
      by (auto simp add: valid_tuple_def split: option.splits)
    then have valid_tuple_since': "valid_tuple tuple_since' (t, as)"
      using proj(2)
      by (auto simp add: tuple_since'_def Mapping_lookup_filter_Some valid_tuple_def)
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
      valid_tuple tuple_since' tas}"
      using tas_in valid_tuple_since' unfolding tas_def(1)[symmetric] by auto
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in)). valid_tuple tuple_since' tas}"
    then obtain t as where tas_def: "tas = (t, as)" "valid_tuple tuple_since' (t, as)"
      by (auto simp add: ts_tuple_rel_f_def)
    from tas_def(2) have "valid_tuple tuple_since (t, as)"
      unfolding tuple_since'_def using Mapping_lookup_filter_not_None
      by (force simp add: valid_tuple_def split: option.splits)
    then have "(t, as) \<in> ts_tuple_rel (set auxlist)"
      using valid_before assm tas_def(1) by auto
    then obtain Z where Z_def: "as \<in> Z" "(t, Z) \<in> set auxlist"
      by (auto simp add: ts_tuple_rel_f_def)
    then have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    from tas_def(2) have "proj_tuple_in_join pos maskL as X"
      unfolding tuple_since'_def using Mapping_lookup_filter_Some_P
      by (fastforce simp add: valid_tuple_def split: option.splits)
    then have as_in_join: "as \<in> join Z pos X"
      using join_sub[OF _ table_left table_Z] Z_def(1) valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then show "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
      using Z_def unfolding tas_def(1) by (auto simp add: ts_tuple_rel_f_def)
  qed
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before
        by (auto simp add: newest_tuple_in_mapping_def dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas} = {}"
        using Mapping_lookup_filter_not_None
        by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric]
        by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "proj_tuple_in_join pos maskL as X")
        case True
        then have lookup_tuple_in': "Mapping.lookup tuple_in' as = Some t"
          using Some unfolding tuple_in'_def by (simp add: Mapping_lookup_filter_Some)
        have "(t, as) \<in> ts_tuple_rel (set (linearize data_in))" "valid_tuple tuple_since (t, as)"
          using valid_before Some
          by (auto simp add: newest_tuple_in_mapping_def dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using True by (auto simp add: image_iff valid_tuple_def tuple_since'_def
            Mapping_lookup_filter_Some split: option.splits)
        have "\<And>t'. valid_tuple tuple_since' (t', as) \<Longrightarrow> valid_tuple tuple_since (t', as)"
          using Mapping_lookup_filter_not_None
          by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
        then have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since' (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff newest_tuple_in_mapping_def)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of _ "linearize data_in"],
            OF _ t_in_fst] by fastforce
        then show ?thesis
          unfolding lookup_tuple_in' using t_in_fst by (auto simp add: safe_max_def)
      next
        case False
        then have lookup_tuple': "Mapping.lookup tuple_in' as = None"
          "Mapping.lookup tuple_since' as = None"
          unfolding tuple_in'_def tuple_since'_def
          by (auto simp add: Mapping_lookup_filter_None)
        then have "\<And>tas. \<not>(valid_tuple tuple_since' tas \<and> as = snd tas)"
          by (auto simp add: valid_tuple_def split: option.splits)
        then show ?thesis
          unfolding lookup_tuple' by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_join': "\<And>t ys. (t, ys) \<in> set auxlist \<Longrightarrow> table n R (join ys pos X)"
  proof -
    fix t ys
    assume "(t, ys) \<in> set auxlist"
    then have table_ys: "table n R ys"
      using valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    show "table n R (join ys pos X)"
      using join_table[OF table_ys table_left, of pos R] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using tuple_since'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  show ?thesis
    unfolding join_mmsaux_abs_eq[OF valid_before table_left']
    using valid_before ts_tuple_rel' lookup_tuple_in' tuple_in'_def tuple_since'_def table_join'
      Mapping_filter_keys[of tuple_since "\<lambda>as. case as of Some t \<Rightarrow> t \<le> nt"]
      table_in' wf_table_of_set_args[OF table_in'[unfolded n_def R_def]]
      table_since' wf_table_of_set_args[OF table_since'[unfolded n_def R_def]]
    by (auto simp add: n_def L_def R_def pos_def table_def Let_def wf_table_sig_args)
qed

lemma valid_join_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  table (args_n args) (args_L args) X \<Longrightarrow> valid_mmsaux args cur
  (join_mmsaux args X aux) (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
  using valid_join_mmsaux_unfolded by (cases aux) fast

fun gc_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
    tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
    (nt, nt, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in,
     wf_table_of_set_args args (Mapping.keys tuple_since'), tuple_since'))"

lemma valid_gc_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in,
    table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) ys"
  shows "valid_mmsaux args cur (gc_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in,
    table_in, wf_table_in, tuple_in, wf_table_since, tuple_since)) ys"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define all_tuples where "all_tuples \<equiv> \<Union>(snd ` (set (linearize data_prev) \<union>
    set (linearize data_in)))"
  define tuple_since' where "tuple_since' \<equiv> Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since"
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping.in_keysD)
  then have table_since': "table n R (Mapping.keys tuple_since')"
    using valid_before by (auto simp add: table_def n_def R_def)
  have data_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in)) \<Longrightarrow> valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
  proof -
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in))"
    define t where "t \<equiv> fst tas"
    define as where "as \<equiv> snd tas"
    have "as \<in> all_tuples"
      using assm by (force simp add: as_def all_tuples_def ts_tuple_rel_f_def)
    then have "Mapping.lookup tuple_since' as = Mapping.lookup tuple_since as"
      by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits)
    then show "valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
      by (auto simp add: valid_tuple_def as_def split: option.splits) metis
  qed
  then have data_in_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
    valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
    by (auto simp add: ts_tuple_rel_Un)
  have "ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
    using data_cong valid_before by auto
  moreover have "(\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas}))"
    using valid_before by (auto simp add: newest_tuple_in_mapping_def) (meson data_in_cong)
  moreover have "(\<forall>as \<in> Mapping.keys tuple_since'. case Mapping.lookup tuple_since' as of
    Some t \<Rightarrow> t \<le> nt)"
    using Mapping.keys_filter valid_before
    by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits
        intro!: Mapping_keys_intro dest: Mapping.in_keysD)
  ultimately show ?thesis
    using all_tuples_def tuple_since'_def valid_before table_since'
      wf_table_of_set_args[OF table_since'[unfolded n_def R_def]]
    by (auto simp add: n_def R_def Let_def wf_table_sig_args)
qed

lemma valid_gc_mmsaux: "valid_mmsaux args cur aux ys \<Longrightarrow> valid_mmsaux args cur (gc_mmsaux args aux) ys"
  using valid_gc_mmsaux_unfolded by (cases aux) fast

fun gc_join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (if \<not> memR (args_ivl args) (t - gc) then join_mmsaux args X (gc_mmsaux args (t, gc, maskL, maskR,
      data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    else join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))"

lemma gc_join_mmsaux_alt: "gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 (gc_mmsaux args aux) \<or>
  gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 aux"
  by (cases aux) (auto simp only: gc_join_mmsaux.simps split: if_splits)

lemma valid_gc_join_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "table (args_n args) (args_L args) rel1"
  shows "valid_mmsaux args cur (gc_join_mmsaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
  using gc_join_mmsaux_alt[of args rel1 aux]
  using valid_join_mmsaux[OF valid_gc_mmsaux[OF assms(1)] assms(2)]
    valid_join_mmsaux[OF assms]
  by auto

definition "minus_keys X m = X - Mapping.keys m"

lemma minus_keys_code[code]: "minus_keys X m = {x \<in> X. case Mapping.lookup m x of None \<Rightarrow> True | _ \<Rightarrow> False}"
  by (auto simp: minus_keys_def Mapping.keys_dom_lookup split: option.splits)

fun add_new_table_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_table_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    (let X' = (minus_keys X tuple_since);
         wf_table_since' = wf_table_union wf_table_since (wf_table_of_set_args args X');
         tuple_since' = upd_set tuple_since (\<lambda>_. t) X' in
    (if memL (args_ivl args) 0 then
      (t, gc, maskL, maskR, data_prev, append_queue (t, X) data_in, table_in \<union> X, wf_table_union wf_table_in (wf_table_of_set_args args X), upd_set tuple_in (\<lambda>_. t) X, wf_table_since', tuple_since')
    else (t, gc, maskL, maskR, append_queue (t, X) data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since', tuple_since')))"

lemma valid_add_new_table_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X
    (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since))
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
proof -
  have cur_nt: "cur = nt"
    using valid_before by auto
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define tuple_in' where "tuple_in' \<equiv> upd_set tuple_in (\<lambda>_. nt) X"
  define X' where "X' \<equiv> X - Mapping.keys tuple_since"
  define wf_table_since' where "wf_table_since' \<equiv> wf_table_union wf_table_since (wf_table_of_set_args args X')"
  define tuple_since' where "tuple_since' \<equiv> upd_set tuple_since (\<lambda>_. nt) X'"
  define data_prev' where "data_prev' \<equiv> append_queue (nt, X) data_prev"
  define data_in' where "data_in' \<equiv> append_queue (nt, X) data_in"
  define auxlist' where "auxlist' \<equiv> (case auxlist of
    [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  have table_in': "table n R (Mapping.keys tuple_in')"
    using table_X valid_before
    by (auto simp add: table_def tuple_in'_def Mapping_upd_set_keys n_def R_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using table_X valid_before
    by (auto simp add: table_def tuple_since'_def Mapping_upd_set_keys n_def R_def X'_def)
  have tuple_since'_keys: "Mapping.keys tuple_since \<subseteq> Mapping.keys tuple_since'"
    using Mapping_upd_set_keys by (fastforce simp add: tuple_since'_def)
  have lin_data_prev': "linearize data_prev' = linearize data_prev @ [(nt, X)]"
    unfolding data_prev'_def append_queue_rep ..
  have wf_data_prev': "\<And>as. as \<in> \<Union>(snd ` (set (linearize data_prev'))) \<Longrightarrow> wf_tuple n R as"
    unfolding lin_data_prev' using table_X valid_before
    by (auto simp add: table_def n_def R_def)
  have lin_data_in': "linearize data_in' = linearize data_in @ [(nt, X)]"
    unfolding data_in'_def append_queue_rep ..
  have table_auxlist': "\<forall>(t, X) \<in> set auxlist'. table n R X"
    using table_X table_Un valid_before
    by (auto simp add: auxlist'_def n_def R_def split: list.splits if_splits)
  have lookup_tuple_since': "\<forall>as \<in> Mapping.keys tuple_since'.
    case Mapping.lookup tuple_since' as of Some t \<Rightarrow> t \<le> nt"
    unfolding tuple_since'_def using valid_before Mapping_lookup_upd_set[of tuple_since]
    by (auto dest: Mapping.in_keysD intro!: Mapping_keys_intro split: if_splits option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    ts_tuple_rel (set auxlist) \<union> ts_tuple_rel {(nt, X)}"
    unfolding auxlist'_def
    using ts_tuple_rel_ext[of _ id] ts_tuple_rel_ext'[of _ id]
      ts_tuple_rel_ext_Cons ts_tuple_rel_ext_Cons'
    by (fastforce simp: ts_tuple_rel_f_def split: list.splits if_splits)
  have valid_tuple_nt_X: "\<And>tas. tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow> valid_tuple tuple_since' tas"
    using valid_before by (auto simp add: X'_def ts_tuple_rel_f_def valid_tuple_def tuple_since'_def
        Mapping_lookup_upd_set dest: Mapping.in_keysD split: option.splits)
  have valid_tuple_mono: "\<And>tas. valid_tuple tuple_since tas \<Longrightarrow> valid_tuple tuple_since' tas"
    by (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
        intro: Mapping_keys_intro split: option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in) \<union> {(nt, X)}).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set auxlist')"
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
      using assm[unfolded ts_tuple_rel_auxlist' ts_tuple_rel_Un]
    proof (rule UnE)
      assume assm: "tas \<in> ts_tuple_rel (set auxlist)"
      then have "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)). valid_tuple tuple_since tas}"
        using valid_before by auto
      then show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm by (auto simp only: ts_tuple_rel_Un intro: valid_tuple_mono)
    next
      assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm valid_before by (auto simp add: X'_def ts_tuple_rel_Un tuple_since'_def
            valid_tuple_def Mapping_lookup_upd_set ts_tuple_rel_f_def dest: Mapping.in_keysD
            split: option.splits if_splits)
    qed
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
    then have "tas \<in> (ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in)) - ts_tuple_rel {(nt, X)}) \<union> ts_tuple_rel {(nt, X)}"
      by (auto simp only: ts_tuple_rel_Un)
    then show "tas \<in> ts_tuple_rel (set auxlist')"
    proof (rule UnE)
      assume assm': "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)) - ts_tuple_rel {(nt, X)}"
      then have tas_in: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in))"
        by (auto simp only: ts_tuple_rel_f_def)
      obtain t as where tas_def: "tas = (t, as)"
        by (cases tas) auto
      have "t \<in> fst ` (set (linearize data_prev) \<union> set (linearize data_in))"
        using assm' unfolding tas_def by (force simp add: ts_tuple_rel_f_def)
      then have t_le_nt: "t \<le> nt"
        using valid_before by auto
      have valid_tas: "valid_tuple tuple_since' tas"
        using assm by auto
      have "valid_tuple tuple_since tas"
      proof (cases "as \<in> Mapping.keys tuple_since")
        case True
        then show ?thesis
          using valid_tas tas_def by (auto simp add: X'_def valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set split: option.splits if_splits)
      next
        case False
        then have "t = nt" "as \<in> X"
          using valid_tas t_le_nt unfolding tas_def
          by (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
              intro: Mapping_keys_intro split: option.splits if_splits)
        then have "False"
          using assm' unfolding tas_def ts_tuple_rel_f_def by (auto simp only: ts_tuple_rel_f_def id_def)
        then show ?thesis
          by simp
      qed
      then show "tas \<in> ts_tuple_rel (set auxlist')"
        using tas_in valid_before by (auto simp add: ts_tuple_rel_auxlist')
    qed (auto simp only: ts_tuple_rel_auxlist')
  qed
  have table_since: "table (args_n args) (args_R args) (Mapping.keys tuple_since)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_since': "Mapping.keys tuple_since \<union> X' = Mapping.keys tuple_since'"
    using valid_before
    by (auto simp: tuple_since'_def Mapping_upd_set_keys)
  have sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and set_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by auto
  have sig_since'': "wf_table_sig (wf_table_union wf_table_since (wf_table_of_set_args args X')) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_union wf_table_sig_args)
  have table_X': "table (args_n args) (args_R args) X'"
    using assms(2)
    by (auto simp: X'_def table_def)
  have keys_tuple_since'': "wf_table_set (wf_table_union wf_table_since (wf_table_of_set_args args X')) = Mapping.keys tuple_since'"
    by (auto simp: keys_tuple_since'[symmetric] set_since[symmetric]
        wf_table_set_union[OF trans[OF sig_since wf_table_sig_args[symmetric]]]
        wf_table_of_set_args[OF table_X'])
  have table_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in)"
    using valid_before by (auto simp add: table_def)
  have keys_tuple_in: "table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have keys_tuple_in': "table_in \<union> X = Mapping.keys tuple_in'"
    using valid_before
    by (auto simp: tuple_in'_def Mapping_upd_set_keys)
  have sig_in: "wf_table_sig wf_table_in = (args_n args, args_R args)"
    and set_in: "wf_table_set wf_table_in = Mapping.keys tuple_in"
    using valid_before
    by auto
  have sig_in'': "wf_table_sig (wf_table_union wf_table_in (wf_table_of_set_args args X)) = (args_n args, args_R args)"
    and sig_since: "wf_table_sig wf_table_since = (args_n args, args_R args)"
    and keys_since: "wf_table_set wf_table_since = Mapping.keys tuple_since"
    using valid_before
    by (auto simp: wf_table_sig_union wf_table_sig_args)
  have keys_tuple_in'': "wf_table_set (wf_table_union wf_table_in (wf_table_of_set_args args X)) = Mapping.keys tuple_in'"
    by (auto simp: keys_tuple_in keys_tuple_in'[symmetric] set_in[symmetric]
        wf_table_set_union[OF trans[OF sig_in wf_table_sig_args[symmetric]]]
        wf_table_of_set_args[OF table_X])
  show ?thesis
  proof (cases "memL I 0")
    case True
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = (nt, gc, maskL, maskR, data_prev, data_in',
      table_in \<union> X, wf_table_union wf_table_in (wf_table_of_set_args args X), tuple_in', wf_table_since', tuple_since')"
      using data_in'_def tuple_in'_def tuple_since'_def
      by (auto simp: Let_def I_def minus_keys_def wf_table_since'_def X'_def)
    have "\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> memL I (nt - t)"
      using valid_before True by (auto simp add: lin_data_in')
    moreover have "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof -
      fix as
      show "Mapping.lookup tuple_in' as = safe_max (fst `
        {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since' tas \<and> as = snd tas})"
      proof (cases "as \<in> X")
        case True
        have "valid_tuple tuple_since' (nt, as)"
          using True valid_before by (auto simp add: X'_def valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set dest: Mapping.in_keysD split: option.splits)
        moreover have "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          using True by (auto simp add: ts_tuple_rel_f_def)
        ultimately have nt_in: "nt \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas}"
        proof -
          assume a1: "valid_tuple tuple_since' (nt, as)"
          assume "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          then have "\<exists>p. nt = fst p \<and> p \<in> ts_tuple_rel (insert (nt, X)
            (set (linearize data_in))) \<and> valid_tuple tuple_since' p \<and> as = snd p"
            using a1 by simp
          then show "nt \<in> fst ` {p \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in))).
            valid_tuple tuple_since' p \<and> as = snd p}"
            by blast
        qed
        moreover have "\<And>t. t \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas} \<Longrightarrow> t \<le> nt"
          using valid_before by (auto split: option.splits)
            (metis (no_types, lifting) eq_imp_le fst_conv insertE ts_tuple_rel_dest)
        ultimately have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)
          \<union> set [(nt, X)]). valid_tuple tuple_since' tas \<and> as = snd tas}) = nt"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of _ "linearize data_in'"],
              unfolded lin_data_in' set_append]
          by (metis (mono_tags) Un_empty_right Un_insert_right empty_set list.simps(15))
        then show ?thesis
          using nt_in True
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set safe_max_def lin_data_in')
      next
        case False
        have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since tas \<and> as = snd tas} =
          {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using False by (fastforce simp add: X'_def lin_data_in' ts_tuple_rel_f_def valid_tuple_def
              tuple_since'_def Mapping_lookup_upd_set intro: Mapping_keys_intro
              split: option.splits if_splits)
        then show ?thesis
          using valid_before False
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set newest_tuple_in_mapping_def)
      qed
    qed
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_in)"]
        lookup_tuple_since' ts_tuple_rel_auxlist'
        table_in' keys_tuple_in' sig_in'' keys_tuple_in''
        table_since' keys_tuple_since' sig_since'' keys_tuple_since''
      unfolding add_def auxlist'_def[symmetric] wf_table_since'_def[symmetric] cur_nt I_def
      by (auto simp only: valid_mmsaux.simps lin_data_in' n_def R_def) (auto simp: table_def)
  next
    case False
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = (nt, gc, maskL, maskR, data_prev', data_in,
      table_in, wf_table_in, tuple_in, wf_table_since', tuple_since')"
      using data_prev'_def tuple_since'_def unfolding I_def 
      by (auto simp: Let_def minus_keys_def X'_def wf_table_since'_def)
    have "\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> \<not> memL I (nt - t)"
      using valid_before False by (auto simp add: lin_data_prev' I_def)
    moreover have "\<And>as. {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since tas \<and> as = snd tas} =
      {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since' tas \<and> as = snd tas}"
    proof (rule set_eqI, rule iffI)
      fix as tas
      assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas}"
      then obtain t Z where Z_def: "tas = (t, as)" "as \<in> Z" "(t, Z) \<in> set (linearize data_in)"
        "valid_tuple tuple_since' (t, as)"
        by (auto simp add: ts_tuple_rel_f_def)
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
      using assm
      proof (cases "as \<in> Mapping.keys tuple_since")
        case False
        then have "t \<ge> nt"
          using Z_def(4) by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set intro: Mapping_keys_intro split: option.splits if_splits)
        then show ?thesis
          using Z_def(3) valid_before \<open>\<not> memL I 0\<close> unfolding I_def by auto
      qed (auto simp add: X'_def valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
           dest: Mapping.in_keysD split: option.splits)
    qed (auto simp add: X'_def Mapping_lookup_upd_set valid_tuple_def tuple_since'_def
         intro: Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_prev)"]
        False lookup_tuple_since' ts_tuple_rel_auxlist' wf_data_prev'
        valid_before table_since' keys_tuple_since' sig_since'' keys_tuple_since'' table_in'
      unfolding add_def auxlist'_def[symmetric] wf_table_since'_def[symmetric] cur_nt I_def n_def R_def
        valid_mmsaux.simps
      by (fastforce simp: lin_data_prev') (* SLOW *)
  qed
qed

lemma valid_add_new_table_mmsaux:
  assumes valid_before: "valid_mmsaux args cur aux auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X aux)
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
  using valid_add_new_table_mmsaux_unfolded assms
  by (cases aux) fast

lemma foldr_ts_tuple_rel:
  "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {} \<longleftrightarrow>
  (\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t)"
  by (auto simp: foldr_union ts_tuple_rel_f_def)

fun result_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a table" where
  "result_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) = table_in"

lemma valid_result_mmsaux_unfolded:
  assumes "valid_mmsaux args cur
    (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) auxlist"
  shows "result_mmsaux args (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
proof -
  have res: "result_mmsaux args (t, gc, maskL, maskR, data_prev, data_in, table_in, wf_table_in, tuple_in, wf_table_since, tuple_since) =
    snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas}"
    using assms valid_mmsaux_tuple_in_keys[OF assms]
    by auto
  have ts_tuple_rel_in: "(a, b) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow> memL (args_ivl args) (cur - a)" for a b
    using assms
    by (auto dest!: ts_tuple_rel_dest)
  have ts_tuple_rel_prev: "(a, b) \<in> ts_tuple_rel (set (linearize data_prev)) \<Longrightarrow> \<not>memL (args_ivl args) (cur - a)" for a b
    using assms
    by (auto dest!: ts_tuple_rel_dest)
  have ts_tuple_rel_auxlist: "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas}"
    using assms
    by auto
  show ?thesis
    using ts_tuple_rel_in ts_tuple_rel_prev
    by (auto simp del: result_mmsaux.simps simp: res foldr_ts_tuple_rel ts_tuple_rel_auxlist
        ts_tuple_rel_Un image_snd)+
qed

lemma valid_result_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux args aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {}"
  using valid_result_mmsaux_unfolded by (cases aux) fast

definition "result_mmsaux' args aux = eval_args_agg args (result_mmsaux args aux)"

lemma valid_result_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux' args aux =
  eval_args_agg args (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
  by (simp add: result_mmsaux'_def valid_result_mmsaux)

interpretation default_msaux: msaux valid_mmsaux init_mmsaux add_new_ts_mmsaux gc_join_mmsaux
  add_new_table_mmsaux result_mmsaux'
  using valid_init_mmsaux valid_add_new_ts_mmsaux valid_gc_join_mmsaux valid_add_new_table_mmsaux
    valid_result_mmsaux'
  by unfold_locales assumption+

(*<*)
end
(*>*)