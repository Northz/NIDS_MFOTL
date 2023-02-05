(*<*)
theory Optimized_Until
  imports Optimized_Common
begin
(*>*)

subsection \<open>Optimized data structure for Until\<close>

type_synonym tp = nat

type_synonym 'a mmuaux = "tp \<times> ts queue \<times> ('a table \<times> (ts + tp)) queue \<times> nat \<times> bool list \<times> bool list \<times>
  'a table \<times> ('a tuple, tp) mapping \<times> (tp, ('a tuple, ts + tp) mapping) mapping \<times> (tp, ts) mapping \<times> 'a table list"

definition tstp_lt :: "ts + tp \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> bool" where
  "tstp_lt tstp ts tp = case_sum (\<lambda>ts'. ts' \<le> ts) (\<lambda>tp'. tp' < tp) tstp"

definition ts_tp_lt :: " \<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> ts + tp \<Rightarrow> bool" where
  "ts_tp_lt I ts tp tstp = case_sum (\<lambda>ts'. memL I (ts' - ts)) (\<lambda>tp'. tp \<le> tp') tstp"

definition tstp_unpack:: "ts + tp \<Rightarrow> nat" where
  "tstp_unpack tstp = case_sum id id tstp"

fun max_tstp :: "ts + tp \<Rightarrow> ts + tp \<Rightarrow> ts + tp" where
  "max_tstp (Inl ts) (Inl ts') = Inl (max ts ts')"
| "max_tstp (Inr tp) (Inr tp') = Inr (max tp tp')"
| "max_tstp (Inl ts) _ = Inl ts"
| "max_tstp _ (Inl ts) = Inl ts"

lemma max_tstp_idem: "max_tstp (max_tstp x y) y = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_idem': "max_tstp x (max_tstp x y) = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_d_d: "max_tstp d d = d"
  by (cases d) auto

lemma max_cases: "(max a b = a \<Longrightarrow> P) \<Longrightarrow> (max a b = b \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis max_def)

lemma max_tstpE: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> (max_tstp tstp tstp' = tstp \<Longrightarrow> P) \<Longrightarrow>
  (max_tstp tstp tstp' = tstp' \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases tstp; cases tstp') (auto elim: max_cases)

lemma max_tstp_intro: "tstp_lt tstp ts tp \<Longrightarrow> tstp_lt tstp' ts tp \<Longrightarrow> isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  tstp_lt (max_tstp tstp tstp') ts tp"
  by (auto simp add: tstp_lt_def max_def split: sum.splits)

lemma max_tstp_intro': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt I ts' tp' tstp \<Longrightarrow> ts_tp_lt I ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto 0 3 simp add: ts_tp_lt_def max_def split: sum.splits)

lemma max_tstp_intro'': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt I ts' tp' tstp' \<Longrightarrow> ts_tp_lt I ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto 0 3 simp add: ts_tp_lt_def max_def elim: contrapos_np split: sum.splits)

lemma max_tstp_isl: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> isl (max_tstp tstp tstp') \<longleftrightarrow> isl tstp"
  by (cases tstp; cases tstp') auto

definition filter_a1_map :: "bool \<Rightarrow> tp \<Rightarrow> ('a tuple, tp) mapping \<Rightarrow> 'a table" where
  "filter_a1_map pos tp a1_map =
    {xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow>
    (pos \<longrightarrow> tp' \<le> tp) \<and> (\<not>pos \<longrightarrow> tp \<le> tp')}"

definition filter_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow>
  'a table" where
  "filter_a2_map I ts tp a2_map = {xs. \<exists>tp' \<le> tp. (case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
    (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt I ts tp tstp | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)}"

definition ivl_restr_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow> bool" where
  "ivl_restr_a2_map I ts tp a2_map = (case Mapping.lookup a2_map tp of Some m \<Rightarrow>
    (\<forall>xs. (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt I ts tp tstp |
                                                             _ \<Rightarrow> True))
    | _ \<Rightarrow> False)"

definition valid_tstp_map :: "ts \<Rightarrow> tp \<Rightarrow> (tp, ts) mapping \<Rightarrow> bool" where
  "valid_tstp_map ts tp tstp_map = (case Mapping.lookup tstp_map tp of
                                   Some ts' \<Rightarrow> ts = ts' |
                                   None \<Rightarrow> False)"

fun triple_eq_pair :: "('a \<times> 'b \<times> 'c) \<Rightarrow> ('a \<times> 'd) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'd \<Rightarrow> 'c) \<Rightarrow> bool" where
  "triple_eq_pair (t, a1, a2) (ts', tp') f g \<longleftrightarrow> t = ts' \<and> a1 = f tp' \<and> a2 = g ts' tp'"


fun valid_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data muaux \<Rightarrow> bool" where
  "valid_mmuaux' args cur dt (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) auxlist \<longleftrightarrow>
    args_L args \<subseteq> args_R args \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    len \<le> tp \<and>
    length (linearize tss) = len \<and> sorted (linearize tss) \<and>
    (\<forall>t \<in> set (linearize tss). t \<le> cur \<and> memR (args_ivl args) (cur - t)) \<and>
    table (args_n args) (args_L args) (Mapping.keys a1_map) \<and>
    Mapping.keys tstp_map = (if len > 0 then {tp - len..tp - 1} else {}) \<and>
    Mapping.keys a2_map = {tp - len..tp} \<and>
    sorted (map (tstp_unpack \<circ> snd) (linearize tables)) \<and>
    (\<forall>tstp \<in> set (map snd (linearize tables)). case tstp of Inl ts \<Rightarrow> ts \<le> cur |
                                                            Inr tp' \<Rightarrow> tp' \<le> tp ) \<and>
    list_all (\<lambda>k. isl k \<longleftrightarrow> \<not> memL (args_ivl args) 0) (map snd (linearize tables)) \<and>
    (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow> result = Mapping.keys m | _ \<Rightarrow> False) \<and>
    Mapping.lookup a2_map tp = Some Mapping.empty \<and>
    (\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
        \<exists>(table, tstp') \<in> set (linearize tables). tstp = tstp' \<and> xs \<in> table)) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      table (args_n args) (args_R args) (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL (args_ivl args) 0))) \<and>
    length done + len = length auxlist \<and>
    rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist)) \<and>
    (\<forall>x \<in> set (take (length done) auxlist). check_before (args_ivl args) dt x) \<and>
    sorted (map fst auxlist) \<and>
    (list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map (args_pos args) tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map (args_ivl args) ts' tp' a2_map)) (drop (length done) auxlist)
      (zip (linearize tss) [tp - len..<tp])) \<and>
    list_all (\<lambda>(ts', tp'). ivl_restr_a2_map (args_ivl args) ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map) (zip (linearize tss) [tp - len..<tp])"

definition valid_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data muaux \<Rightarrow>
  bool" where
  "valid_mmuaux args cur = valid_mmuaux' args cur cur"

fun eval_step_mmuaux :: "args \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "eval_step_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow>
        let I = args_ivl args;
        T = eval_args_agg args result;
        tss' = tl_queue tss';
        (ts', tss'') = case safe_hd tss' of 
              (Some ts', tss'') \<Rightarrow> (ts', tss'') |
              (None, tss'') \<Rightarrow> (0, tss'');
        (tables, taken) = takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables;
        to_del_approx = \<Union>(set (map fst taken));
        to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx;
        m'' = mapping_delete_set m to_del;
        result' = if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m');
        a2_map = if len = 1 then Mapping.update tp Mapping.empty a2_map
                 else Mapping.update (tp - len + 1)
          (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow>
          Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m') a2_map;
        a2_map = Mapping.delete (tp - len) a2_map;
        tstp_map = Mapping.delete (tp - len) tstp_map in
        (tp, tss'', tables, len - 1, maskL, maskR, result', a1_map, a2_map, tstp_map, T # done)))"

fun lin_ts_mmuaux :: "event_data mmuaux \<Rightarrow> ts list" where
  "lin_ts_mmuaux (tp, tss, len, maskL, maskR, result, a1_map, a2_map, done, done_length) =
    linearize tss"

lemma list_length_eq_split:
  assumes "list = xs @ [x] @ xs'"
  and "length list = length lista"
  shows "\<exists>ys y ys'. lista = ys @ [y] @ ys' \<and> length xs = length ys \<and> length xs' = length ys'"
proof -
  have length_eq: "length xs = length list - length xs' - 1" using assms by auto
  then have s1: "lista = take (length xs) lista @ drop (length list - length xs' - 1) lista" by auto
  have "length lista \<ge> length xs + 1" using assms by auto
  then have "drop (length list - length xs' - 1) lista \<noteq> []" using length_eq assms(2) by auto 
  then obtain b xc where xc_def: "drop (length list - length xs' - 1) lista = [b] @ xc" by (metis append_Cons append_Nil list.exhaust)
  then have "lista = take (length xs) lista @ [b] @ xc" using s1 by auto
  then obtain xb' where split_list_1: "lista = xb' @ [b] @ xc" "length xb' = length xs" "length xc = length xs'"
    using xc_def  by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 add_diff_cancel_left' assms(1) assms(2) diff_add_inverse2 diff_diff_left length_append length_drop length_nth_simps(1) length_nth_simps(2) plus_1_eq_Suc)
  then show ?thesis by metis
qed

lemma tstp_le_aux: 
  assumes "Mapping.lookup tstp_map tpa = Some ts"
  and "Mapping.lookup tstp_map tpa' = Some ts'"
  and "tpa \<in> set lista"
  and "tpa' \<in> set lista"
  and "tpa < tpa'"
  and "sorted list"
  and "sorted lista"
  and "length list = length lista"
  and "list_all (\<lambda>(x, y). valid_tstp_map x y tstp_map) (zip list lista)" 
  shows "ts \<le> ts'"
proof -
  obtain yc yb' where split_lista_1: "lista = yb' @ [tpa'] @ yc" using assms(4) by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then obtain xc b xb' where split_list_1: "list = xb' @ [b] @ xc" "length xb' = length yb'" "length xc = length yc"
    using list_length_eq_split[OF split_lista_1 assms(8)[symmetric]] by auto
  have "\<forall>x \<in> set yc. x \<ge> tpa'" using split_lista_1 assms(7) by (metis list.set_intros(1) sorted_append)
  then have "tpa \<in> set yb'" using assms(3) split_lista_1 assms(5) list_appendE by auto
  then obtain ya yb where split_lista_2: "yb' = ya @ [tpa] @ yb" by (metis append_Cons append_Nil in_set_conv_decomp_first)
  then obtain xa a xb where split_list_2: "xb' = xa @ [a] @ xb" "length xa = length ya" "length xb = length yb"
    using list_length_eq_split[OF split_lista_2 split_list_1(2)[symmetric]] by auto
  have "zip list lista = zip xb' yb' @ [(b, tpa')] @ zip xc yc" using split_lista_1 split_list_1 by auto
  moreover have "zip xb' yb' = zip xa ya @ [(a, tpa)] @ zip xb yb" using split_lista_2 split_list_2 by auto
  ultimately have zip_split: "zip list lista = zip xa ya @ [(a, tpa)] @ zip xb yb @ [(b, tpa')] @ zip xc yc" by auto
  then have "(a, tpa) \<in> set (zip list lista)" "(b, tpa') \<in> set (zip list lista)" by auto
  then have eq: "a = ts" "b = ts'" using assms(1-2) list_all_iff[of "\<lambda>(x, y). valid_tstp_map x y tstp_map" "zip list lista"] assms(9) 
    unfolding valid_tstp_map_def by auto
  then have "list = xa @ [ts] @ xb @ [ts'] @ xc" using split_list_1 split_list_2 by auto 
  have "\<forall>x \<in> set xb'. x \<le> ts'" using split_list_1(1)[unfolded eq(2)] assms(6) by (metis append_Cons list.set_intros(1) sorted_append)
  then show ?thesis using split_list_2(1)[unfolded eq(1)] by auto
qed

lemma valid_eval_step_mmuaux':
  assumes "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = ts # tss''" "\<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmuaux' args cur dt (eval_step_mmuaux args aux) auxlist \<and>
    lin_ts_mmuaux (eval_step_mmuaux args aux) = tss''"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where aux_def:
    "aux = (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases aux) auto
  then obtain tss' where safe_hd_eq: "safe_hd tss = (Some ts, tss')"
    using assms(2) safe_hd_rep case_optionE
    by (cases "safe_hd tss") fastforce
  note valid_before = assms(1)[unfolded aux_def]
  have lin_tss_not_Nil: "linearize tss \<noteq> []"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have ts_hd: "ts = hd (linearize tss)"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have lin_tss': "linearize tss' = linearize tss"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have tss'_not_empty: "\<not>Queue.is_empty tss'"
    using is_empty_alt[of tss'] lin_tss_not_Nil unfolding lin_tss' by auto
  have len_pos: "len > 0"
    using lin_tss_not_Nil valid_before by auto
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_before by auto
  have len_tp: "len \<le> tp"
    using valid_before by auto
  have tp_minus_keys: "tp - len \<in> Mapping.keys a2_map"
    using a2_map_keys by auto
  have tp_minus_keys': "tp - len + 1 \<in> Mapping.keys a2_map"
    using a2_map_keys len_pos len_tp by auto
  obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
    using tp_minus_keys by (auto dest: Mapping.in_keysD)
  have result_def: "result = Mapping.keys m"
    using valid_before
    by (auto simp: m_def)
  have "table n R (Mapping.keys m)"
    "(\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using tp_minus_keys m_def valid_before
    unfolding valid_mmuaux'.simps n_def I_def R_def by fastforce+
  then have m_inst: "table n R (Mapping.keys m)"
    "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    using Mapping_keys_intro by fastforce+
  have m_inst_isl: "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> \<not> memL I 0"
    using m_inst(2) by fastforce
  obtain m' where m'_def: "Mapping.lookup a2_map (tp - len + 1) = Some m'"
    using tp_minus_keys' by (auto dest: Mapping.in_keysD)
  have "table n R (Mapping.keys m')"
    "(\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using tp_minus_keys' m'_def valid_before
    unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce+
  then have m'_inst: "table n R (Mapping.keys m')"
    "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    using Mapping_keys_intro by fastforce+
  have m'_inst_isl: "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> \<not> memL I 0"
    using m'_inst(2) by fastforce
  obtain ts' tss''' where ts'_tss'''_def: "(case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> (ts', tss'') | (None, tss'') \<Rightarrow> (0, tss'')) = (ts', tss''')"
    by fastforce
  then have ts'_def: "ts' = (case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> ts' | (None, tss'') \<Rightarrow> 0)"
    by (auto split: prod.splits option.splits)
  have lin_tss''': "linearize tss''' = linearize (tl_queue tss')"
    using ts'_tss'''_def safe_hd_rep[of "tl_queue tss'"]
    by (auto split: prod.splits option.splits)
  define T where "T = Mapping.keys m"
  define T_agg where "T_agg = eval_args_agg args T"
  have t_agg_eq: "T_agg = eval_args_agg args result"
    using result_def T_def T_agg_def by auto
  define tables' where "tables' = fst (takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables)"
  define taken where "taken = snd (takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables)"
  have tables_split: "linearize tables = taken @ (linearize tables')" 
    unfolding taken_def tables'_def takedropWhile_queue_snd takedropWhile_queue_fst dropWhile_queue_rep by auto
  have "sorted (map (tstp_unpack \<circ> snd) (linearize tables))" using valid_before unfolding I_def valid_mmuaux'.simps by auto
  then have sorted_tables': "sorted (map (tstp_unpack \<circ> snd) (linearize tables'))" unfolding tables_split using sorted_append by auto
  have "list_all (\<lambda>k. isl k = (\<not> memL I 0)) (map snd (linearize tables))" using valid_before unfolding I_def valid_mmuaux'.simps by auto
  then have isl_tables': "list_all (\<lambda>k. isl k = (\<not> memL I 0)) (map snd (linearize tables'))" unfolding tables_split by auto
  have taken_valid: "\<forall>(table, tstp) \<in> set taken. \<not>(ts_tp_lt I ts' (tp - len + 1) tstp)" 
    unfolding taken_def takedropWhile_queue_snd by (meson set_takeWhileD)
  have tables'_valid: "\<forall>(table, tstp) \<in> set (linearize tables'). ts_tp_lt I ts' (tp - len + 1) tstp" 
  proof
    fix x
    assume assm: "x \<in> set (linearize tables')"
    then obtain table_h tstp_h tl where hd_tl: "linearize tables' = (table_h, tstp_h)#tl" by (metis list.set_cases surj_pair)
    obtain table tstp where x_def: "x = (table, tstp)" by fastforce
    have "list_all (\<lambda>k. isl k = (\<not> memL I 0)) (map snd (linearize tables))" using valid_before unfolding I_def by auto
    moreover have "tstp_h \<in> set (map snd (linearize tables))" unfolding tables_split hd_tl by auto
    moreover have "tstp \<in> set (map snd (linearize tables))"  using assm unfolding x_def tables_split by force
    ultimately have isl_eq: "isl tstp_h = isl tstp" by (metis (mono_tags, lifting) list_all_append list_all_simps(1) split_list)
    have "\<forall>x \<in> set (map (tstp_unpack \<circ> snd) (linearize tables')). x \<ge> tstp_unpack tstp_h"
      using sorted_tables' unfolding hd_tl by auto
    moreover have "tstp_unpack tstp \<in> set (map (tstp_unpack \<circ> snd) (linearize tables'))" using assm[unfolded x_def] by force
    ultimately have geq: "tstp_unpack tstp_h \<le> tstp_unpack tstp" by auto
    have "ts_tp_lt I ts' (tp - len + 1) tstp_h" using hd_tl[unfolded tables'_def takedropWhile_queue_fst dropWhile_queue_rep] dropWhile_eq_Cons_conv[of _ "linearize tables"] by auto
    then have "ts_tp_lt I ts' (tp - len + 1) tstp" using isl_eq geq unfolding tstp_unpack_def ts_tp_lt_def by(auto split:sum.splits)
    then show "case x of (table, tstp) \<Rightarrow> ts_tp_lt I ts' (tp - len + 1) tstp" using x_def by auto
  qed
  define to_del_approx where "to_del_approx = \<Union>{x. x \<in> set (map fst taken)}"
  define to_del where "to_del = Set.filter (\<lambda>x. case Mapping.lookup m x of Some tstp \<Rightarrow> (\<not>ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                            None \<Rightarrow> False) to_del_approx"
  define m_del where "m_del = mapping_delete_set m to_del"
  define result' where "result' \<equiv> if len = 1 then {} else (result - to_del) \<union> (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow> Mapping.keys m')"
  define m'' where "m'' = Mapping.filter (\<lambda> _ tstp. ts_tp_lt I ts' (tp - len + 1) tstp) m"
  define mc where "mc = Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m'' m'"
  define a2_map' where "a2_map' = (if len = 1 then Mapping.update tp Mapping.empty a2_map
                                  else Mapping.update (tp - len + 1) mc a2_map)"
  define a2_map'' where "a2_map'' = Mapping.delete (tp - len) a2_map'"
  define tstp_map' where "tstp_map' = Mapping.delete (tp - len) tstp_map"
  have m_upd_lookup: "\<And>xs tstp. Mapping.lookup m'' xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    unfolding m''_def Let_def Mapping.lookup_filter
    using m_inst(2) by (auto split: option.splits if_splits)
  have mc_lookup: "\<And>xs tstp. Mapping.lookup mc xs = Some tstp \<Longrightarrow>
    tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0)"
    unfolding mc_def Mapping.lookup_combine
    using m_upd_lookup m'_inst(2)
    by (auto simp add: combine_options_def max_tstp_isl intro: max_tstp_intro split: option.splits)
  have mc_keys: "Mapping.keys mc \<subseteq> Mapping.keys m \<union> Mapping.keys m'"
    unfolding mc_def m''_def Mapping.keys_combine 
    using Mapping.keys_filter by fastforce
  have tp_len_assoc: "tp - len + 1 = tp - (len - 1)"
    using len_pos len_tp by auto
  have a2_map''_keys: "Mapping.keys a2_map'' = {tp - (len - 1)..tp}"
    unfolding a2_map''_def a2_map'_def Mapping.keys_delete Mapping_update_keys a2_map_keys
    using tp_len_assoc apply(auto split:if_splits) 
      apply (metis a2_map_keys atLeastAtMost_iff le_antisym le_eq_less_or_eq less_Suc_eq_le)
      apply (metis One_nat_def Suc_diff_eq_diff_pred a2_map_keys atLeastAtMost_iff le_antisym len_pos not_less_eq_eq)
    using a2_map_keys atLeastAtMost_iff apply blast
    by (metis Suc_le_mono a2_map_keys atLeastAtMost_iff le_SucI)
  have lin_tss_Cons: "linearize tss = ts # linearize (tl_queue tss')"
    using lin_tss_not_Nil
    by (auto simp add: tl_queue_rep lin_tss' ts_hd)
  have tp_len_tp_unfold: "[tp - len..<tp] = (tp - len) # [tp - (len - 1)..<tp]"
    unfolding tp_len_assoc[symmetric]
    using len_pos len_tp Suc_diff_le upt_conv_Cons by auto
  have id: "\<And>x. x \<in> {tp - (len - 1) + 1..tp} \<Longrightarrow>
    Mapping.lookup a2_map'' x = Mapping.lookup a2_map x"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping.lookup_update' tp_len_assoc
    using len_tp by auto
  have list_all2: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map))
    (drop (length done) auxlist) (zip (linearize tss) [tp - len..<tp])"
    using valid_before unfolding I_def pos_def by auto
  obtain hd_aux tl_aux where aux_split: "drop (length done) auxlist = hd_aux # tl_aux"
    "case hd_aux of (t, a1, a2) \<Rightarrow> (t, a1, a2) =
    (ts, filter_a1_map pos (tp - len) a1_map, filter_a2_map I ts (tp - len) a2_map)"
    and list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using list_all2[unfolded lin_tss_Cons tp_len_tp_unfold zip_Cons_Cons list_all2_Cons2] by auto
  have lookup''_tp_minus: "Mapping.lookup a2_map'' (tp - (len - 1)) = (if len = 1 then Some Mapping.empty
                                                                      else Some mc)"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping.lookup_update'
      tp_len_assoc[symmetric]
    using len_tp Mapping.lookup_update'[of _ _ a2_map] by auto
  have filter_a2_map_cong: "\<And>ts' tp'. ts' \<in> set (linearize (tl_queue tss')) \<Longrightarrow>
    tp' \<in> {tp - (len - 1)..<tp} \<Longrightarrow> filter_a2_map I ts' tp' a2_map =
    filter_a2_map I ts' tp' a2_map''"
  proof (rule set_eqI, rule iffI)
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize (tl_queue tss'))"
      "tp' \<in> {tp - (len - 1)..<tp}" "xs \<in> filter_a2_map I ts' tp' a2_map"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'" "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have not_empty_tl: "\<not>Queue.is_empty (tl_queue tss')" using assms(1) is_empty_alt[of "tl_queue tss'"] by auto
    then obtain ts'' tss'' where hd_tl: "safe_hd (tl_queue tss') = (Some ts'', tss'')" 
      using not_empty_head_q[OF not_empty_tl] by auto
    then have ts''_geq: "ts' \<ge> ts''" 
      using hd_le_set[OF _ _ assms(1)] safe_hd_rep[OF hd_tl] lin_tss_Cons valid_before by force
    have tp_bef_in: "tp_bef \<in> {tp - len..tp}"
      using defs(2) valid_before by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    have len_geq: "len \<ge> 2" using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map''"
    proof (cases "tp_bef \<le> tp - (len - 1)")
      case True
      show ?thesis
      proof (cases "tp_bef = tp - len")
        case True
        have m_bef_m: "m_bef = m"
          using defs(2) m_def
          unfolding True by auto
        have lookup: "Mapping.lookup m xs = Some tstp"
          using defs(3,4) assms(2) unfolding m_bef_m 
          by (auto 0 3 simp add: Mapping.lookup_filter ts_tp_lt_def intro: Mapping_keys_intro
              split: sum.splits elim: contrapos_np)
        then have "ts_tp_lt I (case safe_hd (tl_queue tss') of (Some ts', tss'') \<Rightarrow> ts' |
                                                                _ \<Rightarrow> 0) (tp - len + 1) tstp"
          using defs(4) tp_minus_le tp_len_assoc hd_tl ts''_geq unfolding ts_tp_lt_def 
          by(auto split:sum.splits prod.splits option.splits) 
        then have "Mapping.lookup m'' xs = Some tstp" using lookup unfolding m''_def Let_def Mapping.lookup_filter I_def ts'_def by auto

        then have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt I ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro'
              dest: Mapping.in_keysD split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs len_geq
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      next
        case False
        then have "tp_bef = tp - (len - 1)"
          using True tp_bef_in by auto
        then have m_bef_m: "m_bef = m'"
          using defs(2) m'_def
          unfolding tp_len_assoc by auto
        have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt I ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup defs(3)[unfolded m_bef_m]
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro''
              dest: Mapping.in_keysD split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs len_geq
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in len_tp by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto
    qed
  next
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize (tl_queue tss'))" "tp' \<in> {tp - (len - 1)..<tp}"
      "xs \<in> filter_a2_map I ts' tp' a2_map''"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'"
      "Mapping.lookup a2_map'' tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have len_geq: "len \<ge> 2" using assms(2) by auto
    have tp_bef_in: "tp_bef \<in> {tp - (len - 1)..tp}"
      using defs(2) a2_map''_keys by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - len \<le> tp'" "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map"
    proof (cases "tp_bef = tp - (len - 1)")
      case True
      have m_beg_mc: "m_bef = mc"
        using defs(2) len_geq Mapping.lookup_update[of _ _ a2_map]
        unfolding True a2_map''_def a2_map'_def tp_len_assoc Mapping_lookup_delete
        by (auto split: if_splits)
      show ?thesis
        using defs(3)[unfolded m_beg_mc mc_def]
      proof (rule Mapping_lookup_combineE)
        assume lassm: "Mapping.lookup m'' xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          unfolding m''_def Let_def Mapping.lookup_filter
          using m_def tp_minus_le(1) defs 
          by (auto simp add: filter_a2_map_def split: option.splits if_splits)
      next
        assume lassm: "Mapping.lookup m' xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          using m'_def defs(4) tp_minus_le defs
          unfolding filter_a2_map_def tp_len_assoc
          by auto
      next
        fix v' v''
        assume lassms: "Mapping.lookup m'' xs = Some v'" "Mapping.lookup m' xs = Some v''"
          "max_tstp v' v'' = tstp"
        show "xs \<in> filter_a2_map I ts' tp' a2_map"
        proof (rule max_tstpE)
          show "isl v' = isl v''"
            using lassms(1,2) m_upd_lookup m'_inst(2)
            by auto
        next
          assume "max_tstp v' v'' = v'"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(1,3) m_def defs tp_minus_le(1)
            unfolding m''_def Let_def tp_len_assoc Mapping.lookup_filter
            by (auto simp add: filter_a2_map_def split: option.splits if_splits)
        next
          assume "max_tstp v' v'' = v''"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(2,3) m'_def defs tp_minus_le(2)
            unfolding tp_len_assoc
            by (auto simp add: filter_a2_map_def)
        qed
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto (metis option.simps(5))
    qed
  qed
  have list_all2'': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'')) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using filter_a2_map_cong 
    by (intro list_all2_weaken[OF list_all2']) (auto elim!: in_set_zipE split: prod.splits)
  have lookup'': "\<forall>tp' \<in> Mapping.keys a2_map''. case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
  proof (rule ballI)
    fix tp'
    assume assm: "tp' \<in> Mapping.keys a2_map''"
    then obtain f where f_def: "Mapping.lookup a2_map'' tp' = Some f"
      by (auto dest: Mapping.in_keysD)
    have tp'_in: "tp' \<in> {tp - (len - 1)..tp}"
      using assm unfolding a2_map''_keys .
    then have tp'_in_keys: "tp' \<in> Mapping.keys a2_map"
      using valid_before by auto
    have "table n R (Mapping.keys f) \<and>
      (\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
    proof (cases "tp' = tp - (len - 1)")
      case True
      then have f_mc: "f = (if len = 1 then Mapping.empty else mc)"
        using f_def Mapping.lookup_update'[of _ _ a2_map]
        unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping.lookup_update' tp_len_assoc
        by (auto split: if_splits)
      have "table n R (Mapping.keys f)"
        unfolding f_mc
        using mc_keys m_def m'_def m_inst m'_inst
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
        tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0)"
      proof(cases "len = 1")
        case True
        then have "f = Mapping.empty" using f_mc by auto
        then show ?thesis by auto
      next
        case False
        then have eq: "f = mc" using f_mc by auto
        then have "\<forall>xs \<in> Mapping.keys mc. case Mapping.lookup mc xs of Some tstp \<Rightarrow>
        tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0)" using assm Mapping.keys_filter m_inst(2) m_inst_isl m'_inst(2) m'_inst_isl max_tstp_isl
        unfolding m''_def Let_def f_mc mc_def Mapping.lookup_combine
        by (auto simp add: combine_options_def Mapping.lookup_filter
            intro!: max_tstp_intro Mapping_keys_intro dest!: Mapping.in_keysD
            split: option.splits)
      then show ?thesis using eq by auto
    qed
      ultimately show ?thesis
        by auto
    next
      case False
      have "Mapping.lookup a2_map tp' = Some f"
        using tp'_in id[of tp'] f_def False by auto
      then show ?thesis
        using tp'_in_keys valid_before
        unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce
    qed
    then show "case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
      table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> isl tstp = (\<not> memL I 0))"
      using f_def by auto
  qed
  have tl_aux_def: "tl_aux = drop (length done + 1) auxlist"
    using aux_split(1) by (metis Suc_eq_plus1 add_Suc drop0 drop_Suc_Cons drop_drop)
  have T_eq: "Mapping.keys m = filter_a2_map I ts (tp - len) a2_map"
  proof (rule set_eqI, rule iffI)
    fix xs
    assume "xs \<in> filter_a2_map I ts (tp - len) a2_map"
    then obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp - len"
      "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt I ts (tp - len) tstp"
      by (fastforce simp add: filter_a2_map_def split: option.splits)
    then have tp_bef_minus: "tp_bef = tp - len"
      using valid_before Mapping_keys_intro by force
    have m_bef_m: "m_bef = m"
      using defs(2) m_def
      unfolding tp_bef_minus by auto
    show "xs \<in> Mapping.keys m"
      using defs
      unfolding T_def m_bef_m
      by (auto intro: Mapping_keys_filterI Mapping_keys_intro)
  next
    fix xs
    have "ivl_restr_a2_map I ts (tp - len) a2_map" 
      using valid_before lin_tss_Cons tp_len_tp_unfold I_def by auto
    then have aux: "\<forall>k. case Mapping.lookup m k of Some tstp \<Rightarrow> ts_tp_lt I ts (tp - len) tstp |
                                              None \<Rightarrow> True" 
      unfolding ivl_restr_a2_map_def using m_def by auto
    assume "xs \<in> Mapping.keys m"
    then have "tp - len \<le> tp - len"
       "case Mapping.lookup a2_map (tp - len) of 
          None \<Rightarrow> False | 
          Some m \<Rightarrow> (case Mapping.lookup m xs of None \<Rightarrow> False | Some x \<Rightarrow> ts_tp_lt I ts (tp - len) x)"
      using m_def aux  unfolding T_def by (auto simp add: Mapping.in_keysD split: option.splits)
    then show "xs \<in> filter_a2_map I ts (tp - len) a2_map" unfolding filter_a2_map_def by auto
  qed
  have min_auxlist_done: "min (length auxlist) (length done) = length done"
    using valid_before by auto
  then have "\<forall>x \<in> set (take (length done) auxlist). check_before I dt x"
    "rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist))"
    using valid_before unfolding I_def by auto
  then have list_all': "(\<forall>x \<in> set (take (length (result # done)) auxlist). check_before I dt x)"
    "rev (T_agg # done) = map (eval_args_agg args) (map proj_thd (take (length (T # done)) auxlist))"
    using drop_is_Cons_take[OF aux_split(1)] aux_split(2) assms(3) unfolding T_agg_def
    by (auto simp add: T_def T_eq I_def result_def)
  note list_all_split' = list_all_split[of "\<lambda>ts' tp'. ivl_restr_a2_map I ts' tp' a2_map" "\<lambda>ts' tp'. valid_tstp_map ts' tp' tstp_map"]
  note list_all_split'' = list_all_split[of "\<lambda>ts' tp'. ivl_restr_a2_map I ts' tp' a2_map''" "\<lambda>ts' tp'. valid_tstp_map ts' tp' tstp_map'"]
  have ivl_restr: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map)
     (zip (linearize tss) [tp - len..<tp])" using valid_before lin_tss' I_def by auto
  then have "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map) (zip (tl (linearize tss)) [tp - (len - 1)..<tp])"
    using ivl_restr[unfolded lin_tss_Cons tp_len_tp_unfold] lin_tss_Cons by auto
  then have ivl_restr': 
    "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map) (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
    "list_all (\<lambda>(ts', tp'). valid_tstp_map ts' tp' tstp_map) (zip (tl (linearize tss)) [tp - (len - 1)..<tp])"
    using list_all_split' by auto
  have list_all'': "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map'' \<and> valid_tstp_map ts' tp' tstp_map')
     (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
  proof (cases "tl (linearize tss)")
    case Nil
    then show ?thesis by auto
  next
    case (Cons a list)
    then have "length (tl (linearize tss)) \<ge> 1" by auto
    then have "len \<ge> 2" using valid_before by auto
    then have tp_len_eq: "[tp - (len - 1)..<tp] = (tp - (len - 1)) # [tp - (len - 1) + 1..<tp]" by (metis Suc_1 Suc_le_lessD diff_less len_pos len_tp less_le_trans upt_eq_Cons_conv zero_less_diff)
    have not_empty_tss: "\<not> Queue.is_empty (tl_queue tss')" using Cons is_empty_alt lin_tss_Cons by force
    obtain tss'' where hd_tl: "safe_hd (tl_queue tss') = (Some a, tss'')"
      using not_empty_head_q[OF not_empty_tss] lin_tss_Cons local.Cons safe_hd_rep by fastforce
    have ivl_restr'': "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map)
     (zip list [tp - (len - 1) + 1..<tp])" using ivl_restr'(1) Cons tp_len_eq by auto
    have ivl_restr_impl: "\<And>ts' tp'. ts' \<in> set list \<Longrightarrow>
    tp' \<in> {tp - (len - 1) + 1..<tp} \<Longrightarrow> ivl_restr_a2_map I ts' tp' a2_map \<Longrightarrow>
    ivl_restr_a2_map I ts' tp' a2_map''"
    proof -
      fix tsa tpa
      assume assms: "tsa \<in> set list" "tpa \<in> {tp - (len - 1) + 1..<tp}" 
        "ivl_restr_a2_map I tsa tpa a2_map"
      then have *: "tpa \<in> {tp - (len - 1) + 1..tp}" by auto
      show "ivl_restr_a2_map I tsa tpa a2_map''" 
        using id[OF *] assms(3) unfolding ivl_restr_a2_map_def by auto
    qed
    have list_all_eq_1: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map'') (zip list [tp - (len - 1) + 1..<tp])"
      using ivl_restr_impl
      by(intro list.pred_mono_strong[OF ivl_restr'']) (auto elim!: in_set_zipE split: prod.splits)
    have ivl_restr_old: "ivl_restr_a2_map I a (tp - (len - 1)) a2_map" using ivl_restr' unfolding Cons tp_len_eq by auto
    have "ivl_restr_a2_map I a (tp - (len - 1)) a2_map''" unfolding ivl_restr_a2_map_def lookup''_tp_minus mc_def apply(auto simp:Mapping.lookup_combine)
    proof -
      fix xs
      show "case combine_options max_tstp (Mapping.lookup m'' xs) (Mapping.lookup m' xs) of None \<Rightarrow> True
          | Some x \<Rightarrow> ts_tp_lt I a (tp - (len - 1)) x "
      proof (cases "Mapping.lookup m'' xs")
        case none_m'': None
        then show ?thesis
        proof (cases "Mapping.lookup m' xs")
          case None
          then show ?thesis using none_m'' by auto
        next
          case (Some a')
          then have "ts_tp_lt I a (tp - (len - 1)) a'" using m'_def ivl_restr_old unfolding ivl_restr_a2_map_def tp_len_assoc by(auto split:option.splits)
          then show ?thesis using none_m'' Some by auto
        qed
      next
        case some_m'': (Some a')
        then have aux: "ts_tp_lt I a (tp - (len - 1)) a'" unfolding m''_def Let_def Mapping.lookup_filter I_def hd_tl tp_len_assoc ts'_def by(auto split:if_splits option.splits)
        show ?thesis 
        proof (cases "Mapping.lookup m' xs")
          case None
          then show ?thesis using some_m'' aux by auto
        next
          case (Some a'')
          then have "ts_tp_lt I a (tp - (len - 1)) a''" using m'_def ivl_restr_old unfolding ivl_restr_a2_map_def tp_len_assoc by(auto split:option.splits)
          then show ?thesis using some_m'' aux Some unfolding ts_tp_lt_def by(cases a'; cases a''; auto)
        qed
      qed
    qed
    then have split1: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map'') (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
      using list_all_eq_1 Cons tp_len_eq by auto
    have tstp_map_impl: "\<And>ts' tp'. ts' \<in> set (tl (linearize tss)) \<Longrightarrow> tp' \<in> {tp - (len - 1)..<tp} \<Longrightarrow> valid_tstp_map ts' tp' tstp_map \<Longrightarrow> valid_tstp_map ts' tp' tstp_map'"
    proof -
      fix ts' tp'
      assume assms: "tp' \<in> {tp - (len - 1)..<tp}" "valid_tstp_map ts' tp' tstp_map"
      have "tp' \<noteq> tp - len" using assms(1) by (metis add.right_neutral add_le_cancel_left atLeastLessThan_iff not_one_le_zero tp_len_assoc)
      then show "valid_tstp_map ts' tp' tstp_map'" using assms(2) unfolding tstp_map'_def valid_tstp_map_def 
        by(auto split:option.splits; transfer; auto)
    qed
    then have split2: "list_all (\<lambda>(ts', tp'). valid_tstp_map ts' tp' tstp_map') (zip (tl (linearize tss)) [tp - (len - 1)..<tp])" 
      by(intro list.pred_mono_strong[OF ivl_restr'(2)]) (auto elim!: in_set_zipE split: prod.splits)
    show ?thesis using split1 split2 list_all_split'' by auto
  qed 
  let ?del_set = "{k \<in> Mapping.keys m. (case Mapping.lookup m k of Some tstp \<Rightarrow> \<not>(ts_tp_lt I ts' (tp - len + 1) tstp) |
                                                                   None \<Rightarrow> False)}"
  have "?del_set = to_del" 
  proof (rule set_eqI, rule iffI)
    fix x
    assume assm: "x \<in> ?del_set"
    then obtain tstp where tstp_defs: "Mapping.lookup m x = Some tstp" "\<not> ts_tp_lt I ts' (tp - len + 1) tstp"
      by(auto split:option.splits)
    have "tp - len \<in> Mapping.keys a2_map" using tp_minus_keys by blast
    then have "\<forall>xs\<in>Mapping.keys m.
             case Mapping.lookup m xs of
             Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table" 
      using m_def valid_before unfolding valid_mmuaux'.simps by fastforce
    then have "\<exists>(table, tstp') \<in> set (linearize tables). tstp = tstp' \<and> x \<in> table" using m_def valid_before
      using tstp_defs assm case_prodI2 case_prod_conv mem_Collect_eq option.simps(5) by fastforce
    then obtain table tstp' where defs: "(table, tstp') \<in> set (linearize tables)" "tstp = tstp'" "x \<in> table" by auto
    have "(table, tstp') \<notin> set (linearize tables')" 
    proof(rule ccontr)
      assume "\<not> (table, tstp') \<notin> set (linearize tables')"
      then have "(table, tstp') \<in> set (linearize tables')" by auto
      then have "ts_tp_lt I ts' (tp - len + 1) tstp'" using tables'_valid by auto
      then show "False" using defs(2) tstp_defs(2) by auto
    qed
    then have "(table, tstp') \<in> set taken" using defs(1)[unfolded tables_split] by auto
    then have "x \<in> to_del_approx" unfolding to_del_approx_def using defs(3) by auto force
    then show "x \<in> to_del" unfolding to_del_def using assm by(auto split:option.splits)
  next
    fix x
    assume "x \<in> to_del"
    then have "case Mapping.lookup m x of None \<Rightarrow> False | 
               Some tstp \<Rightarrow> \<not> ts_tp_lt I ts' (tp - len + 1) tstp" 
      unfolding to_del_def by auto
    then show "x \<in> ?del_set" by(auto simp: Mapping_keys_intro split:option.splits)
  qed
  moreover have "Mapping.keys m - Mapping.keys (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m) = ?del_set"
    by transfer auto
  moreover have "Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m = mapping_delete_set m (Mapping.keys m - Mapping.keys (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m))"
  proof(rule mapping_eqI) 
    fix x
    show "Mapping.lookup (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m) x =
          Mapping.lookup (mapping_delete_set m (Mapping.keys m - Mapping.keys (Mapping.filter (\<lambda>_. ts_tp_lt I ts' (tp - len + 1)) m))) x"
      using delete_set_lookup[of m] Mapping.lookup_filter[of _ m] Mapping_keys_filterI[of m] Mapping_keys_filterD[of x _ m]
      by(auto simp add:Mapping_keys_intro split:option.splits) blast
  qed
  ultimately have m_eq: "m'' = m_del" unfolding m''_def m_del_def by auto
  have "takedropWhile_queue (\<lambda>(table, tstp). \<not> ts_tp_lt I ts' (tp - len + 1) tstp) tables = (tables', taken)"
    by (auto simp: tables'_def taken_def)
  then have eval_step_mmuaux_eq: "eval_step_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map,
    done) = (tp, tss''', tables', len - 1,  maskL, maskR, result', a1_map, a2_map'', tstp_map', T_agg # done)"
    using safe_hd_eq m_def m'_def mc_def a2_map'_def a2_map''_def I_def tstp_map'_def m_eq[unfolded m_del_def to_del_def to_del_approx_def taken_def] tables'_def ts'_tss'''_def[symmetric]
    by (auto simp add: t_agg_eq Let_def result'_def to_del_def to_del_approx_def split:prod.splits) fastforce+
  have lin_ts: "lin_ts_mmuaux (eval_step_mmuaux args aux) = tss''"
    using lin_tss_Cons assms(2) lin_tss''' unfolding aux_def eval_step_mmuaux_eq by auto
  have lookup_old: "Mapping.lookup a2_map tp = Some Mapping.empty" using valid_before by auto
  have len_not_0: "len \<noteq> 0" using valid_before using lin_tss_not_Nil by force
  then have still_empty: "Mapping.lookup a2_map'' tp = Some Mapping.empty" 
  proof(cases "len = 1")
    case True
    then show ?thesis using a2_map''_def a2_map'_def lookup''_tp_minus by force
  next
    case False
    then have "Suc (tp - len) \<noteq> tp" by (metis diff_add_inverse2 diff_diff_cancel len_tp plus_1_eq_Suc)
    then have "Mapping.lookup a2_map' tp = Some Mapping.empty" 
      unfolding a2_map'_def using Mapping.lookup_update'[of _ _ a2_map] lookup_old by(auto)
    then show ?thesis unfolding a2_map''_def using len_not_0 by (metis Mapping_lookup_delete Suc_eq_plus1 diff_le_self not_less_eq_eq tp_len_assoc)
  qed
  have valid_tables': "\<forall>tp' \<in> Mapping.keys a2_map''. case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
        \<exists>(table, tstp') \<in> set (linearize tables'). tstp = tstp' \<and> xs \<in> table)"
  proof 
    fix tp'
    assume in_a2: "tp' \<in> Mapping.keys a2_map''"
    then have tp'_in: "tp' \<in> {tp - len + 1..tp}" using a2_map''_keys tp_len_assoc by auto
    then have tp'_in': "tp' \<in> {tp - len..tp}" by auto
    have second_last_in_zip: "len \<ge> 2 \<Longrightarrow> (ts', tp - len + 1) \<in> set (zip (linearize tss) [tp - len..<tp])"
    proof -
      assume geq_2: "len \<ge> 2"
      have auxa: "length (linearize tss) = length [tp - len..<tp]" using tp_len_assoc valid_before by auto
      have auxb: "tp - (len - 1) \<noteq> tp" using geq_2 tp_len_assoc by auto
      then have eq2: "[tp - (len - 1)..<tp] = (tp - (len - 1))#[tp - (len - 1) + 1 ..<tp]"
        by (metis Suc_eq_plus1 antisym_conv1 diff_le_self upt_conv_Cons)
      moreover have "length (linearize (tl_queue tss')) = len - 1" using auxa len_tp lin_tss_Cons by force
      ultimately have tss'_not_empty: "linearize (tl_queue tss') \<noteq> []" by force
      obtain ts4 tss'' where safe_hd_eq: "safe_hd (tl_queue tss') = (ts4, tss'')" by(cases "safe_hd (tl_queue tss')") auto
      then obtain ts''' where ts3_def: "ts4 = Some ts'''" using safe_hd_rep[OF safe_hd_eq] tss'_not_empty case_optionE by blast
      then have "ts''' = ts'" using safe_hd_eq unfolding ts'_def by auto
      then have safe_hd_final: "safe_hd (tl_queue tss') = (Some ts', tss'')" using safe_hd_eq ts3_def by auto
      have rep_defs: "ts' = hd (linearize (tl_queue tss'))" "linearize (tl_queue tss') = linearize tss''" "linearize (tl_queue tss') \<noteq> []" using safe_hd_rep[OF safe_hd_final] by auto
      have lin_tss'_Cons: "linearize (tl_queue tss') = ts' # linearize (tl_queue (tl_queue tss'))"
        using tl_queue_rep[of "tl_queue tss'"] rep_defs(1) by (simp add: tss'_not_empty)
      have  "(ts', tp - len + 1) \<in> set (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])" 
        unfolding eq2 lin_tss'_Cons tp_len_assoc by auto
      then show "(ts', tp - len + 1) \<in> set (zip (linearize tss) [tp - len..<tp])" unfolding lin_tss_Cons tp_len_tp_unfold by auto
    qed
    obtain m_aux where m_aux_def: "Mapping.lookup a2_map'' tp' = Some m_aux" using in_a2 by (meson Mapping.in_keysD)
    show "case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of
                Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
    proof(cases "tp' = tp - len + 1")
      case a: True
      then show ?thesis
      proof(cases "len = 1")
        case True
        then have "Mapping.lookup a2_map'' tp' = Some Mapping.empty" using a len_tp
          unfolding a2_map''_def a2_map'_def Mapping_lookup_delete
          by (auto simp: lookup_update')
        then show ?thesis by auto
      next
        case False
        then have mc: "Mapping.lookup a2_map'' tp' = Some mc" using a Mapping.lookup_update
          unfolding a2_map''_def a2_map'_def Mapping_lookup_delete by(auto)
        have "\<forall>xs\<in>Mapping.keys mc. case Mapping.lookup mc xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
        proof 
          fix xs
          assume "xs \<in> Mapping.keys mc"
          then obtain tstp where tstp_def: "Mapping.lookup mc xs = Some tstp" by (meson Mapping.in_keysD)
          then have tstp_combine_def: "Some tstp = combine_options max_tstp (Mapping.lookup m'' xs) (Mapping.lookup m' xs)" unfolding mc_def Mapping.lookup_combine by auto
          have "tp - len + 1 \<in> Mapping.keys a2_map" using m'_def by transfer auto
          then have m'_restr: "\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
            using valid_before m'_def unfolding valid_mmuaux'.simps by (smt (z3) option.case(2))
          have "tp - len \<in> Mapping.keys a2_map" using m_def by transfer auto
          then have m_restr: "\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
            using valid_before m_def unfolding valid_mmuaux'.simps by (smt (z3) option.case(2))
          have "\<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
          proof(cases "Mapping.lookup m' xs")
            case none_m': None
            
            then show ?thesis
            proof(cases "Mapping.lookup m'' xs")
              case None
              then show ?thesis using none_m' tstp_combine_def by auto
            next
              case (Some a')
              then have eq: "a' = tstp" using tstp_combine_def none_m' by auto
              then have restr_a': "ts_tp_lt I ts' (tp - len + 1) tstp" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have m_lookup: "Mapping.lookup m xs = Some a'" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have "xs \<in> Mapping.keys m" using Some unfolding m''_def by(transfer) (auto split:option.splits)
              then have "\<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
                using m_restr m_lookup eq by fastforce
              then obtain table tstp' where defs: "(table, tstp') \<in> set (linearize tables)" "tstp = tstp'" "xs \<in> table" by auto
              have "(table, tstp') \<notin> set taken" using restr_a' taken_valid defs(2) by auto
              then have "(table, tstp') \<in> set (linearize tables')" using defs(1) unfolding tables_split by auto
              then show ?thesis using defs(2-3) by auto
            qed
          next
            case some_m': (Some a)
            then have in_m': "xs \<in> Mapping.keys m'" by transfer auto
            have "m' \<noteq> Mapping.empty" using in_m' by auto
            then have "len \<noteq> 1" using m'_def valid_before by auto
            then have geq2: "len \<ge> 2" using len_pos by linarith
            have "ivl_restr_a2_map I ts' (tp - len + 1) a2_map" using second_last_in_zip[OF geq2] valid_before list_all_iff[of _ "zip (linearize tss) [tp - len..<tp]"]
              unfolding I_def by(auto) 
            then have restr_a: "ts_tp_lt I ts' (tp - len + 1) a" unfolding ivl_restr_a2_map_def
              using some_m' m'_def by(auto split:option.splits)
            have "\<exists>(table, tstp')\<in>set (linearize tables). a = tstp' \<and> xs \<in> table"
              using m'_restr some_m' in_m' by fastforce
            then obtain table' tstp'' where defs: "(table', tstp'') \<in> set (linearize tables)" "a = tstp''" "xs \<in> table'" by auto
            have "(table', tstp'') \<notin> set taken" using restr_a  taken_valid defs(2) by auto
            then have in_a: "(table', tstp'') \<in> set (linearize tables')" using defs(1) unfolding tables_split by auto
            show ?thesis
            proof(cases "Mapping.lookup m'' xs")
              case None
              then have eq: "a = tstp" using tstp_combine_def some_m' by auto
              then show ?thesis using in_a defs(2-3) by auto
            next
              case (Some a')
              then have "tstp = max_tstp a' a" using tstp_combine_def some_m' by auto
              then have eq: "tstp = a' \<or> tstp = a" by(cases a'; cases a; auto)
              have restr_a': "ts_tp_lt I ts' (tp - len + 1) a'" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have m_lookup: "Mapping.lookup m xs = Some a'" using Some unfolding m''_def by(transfer) (auto split:option.splits if_splits)
              have "xs \<in> Mapping.keys m" using Some unfolding m''_def by(transfer) (auto split:option.splits)
              then have "\<exists>(table, tstp')\<in>set (linearize tables). a' = tstp' \<and> xs \<in> table"
                using m_restr m_lookup eq by fastforce
              then obtain table tstp' where defs': "(table, tstp') \<in> set (linearize tables)" "a' = tstp'" "xs \<in> table" by auto
              have "(table, tstp') \<notin> set taken" using restr_a' restr_a taken_valid defs'(2) by auto
              then have "(table, tstp') \<in> set (linearize tables')" using defs'(1) unfolding tables_split by auto
              then show ?thesis using eq defs'(2-3) in_a defs(2-3) by(auto)
            qed
          qed
          then show "case Mapping.lookup mc xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table" using tstp_def by auto
        qed
        then show ?thesis using mc by auto
      qed
    next
      case a: False
      then show ?thesis
      proof(cases "tp' = tp")
        case True
        then have "Mapping.lookup a2_map'' tp' = Some Mapping.empty" using still_empty by auto
        then show ?thesis by auto
      next
        case False
        then have "Mapping.lookup a2_map'' tp' = Mapping.lookup a2_map tp'" using a unfolding a2_map''_def a2_map'_def
          by (smt (z3) Mapping.lookup_update_neq Mapping_lookup_delete a2_map''_def m_aux_def option.simps(3))
        then have *: "Mapping.lookup a2_map tp' = Some m_aux" using m_aux_def by auto
        have "\<forall>tp'\<in>{tp - len..tp}. case Mapping.lookup a2_map tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table" using valid_before by auto
        then have old_cond: "\<forall>xs\<in>Mapping.keys m_aux. case Mapping.lookup m_aux xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
          using  tp'_in' *  by fastforce
        have "\<forall>xs\<in>Mapping.keys m_aux. case Mapping.lookup m_aux xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
        proof 
          fix x
          assume assm: "x \<in> Mapping.keys m_aux"
          then obtain tstp where tstp_def: "Mapping.lookup m_aux x = Some tstp" by (meson Mapping.in_keysD)
          then have "\<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> x \<in> table" using old_cond assm by fastforce
          then obtain table tstp' where defs: "(table, tstp') \<in> set (linearize tables)" "tstp = tstp'"  "x \<in> table"
            by auto
          have tp': "tp' \<in> set [tp - len..<tp]" using False tp'_in by auto
          moreover have auxa: "length (linearize tss) = length [tp - len..<tp]"
            using tp_len_assoc valid_before by auto
          ultimately obtain ts'' where pair_def: "(ts'', tp') \<in> set (zip (linearize tss) [tp - len..<tp])" 
            by (metis in_set_impl_in_set_zip2)
          have "tp - (len - 1) \<noteq> tp" using False tp'_in by auto
          then have not_1: "len \<noteq> 1" by auto
          have "len \<noteq> 0" using tp' by auto
          then have geq2: "len \<ge> 2" using not_1 by auto
          have in_aux: "(ts', tp - len + 1) \<in> set (zip (linearize tss) [tp - len..<tp])"
            using second_last_in_zip[OF geq2] by auto
          then have "valid_tstp_map ts' (tp - len + 1) tstp_map" using * ivl_restr list_all_iff[of _ "zip (linearize tss) [tp - len..<tp]"] by auto
          then have tstp_lookup: "Mapping.lookup tstp_map (tp - len + 1) = Some ts'" unfolding valid_tstp_map_def by (auto split:option.splits)
          have map2: "ivl_restr_a2_map I ts'' tp' a2_map" "valid_tstp_map ts'' tp' tstp_map" using pair_def * ivl_restr list_all_iff[of _ "zip (linearize tss) [tp - len..<tp]"] by auto
          have tstp_lookup': "Mapping.lookup tstp_map tp' = Some ts''" using map2(2) unfolding valid_tstp_map_def by (auto split:option.splits)
          have list_all_tstp: "list_all (\<lambda>(x, y). valid_tstp_map x y tstp_map) (zip (linearize tss) [tp - len..<tp])"
            using valid_before unfolding I_def[symmetric] valid_mmuaux'.simps list_all_split' by auto
          have in1: "tp - len + 1 \<in> set [tp - len..<tp]" by (meson in_aux in_set_zipE)
          have "ts_tp_lt I ts'' tp' tstp" using map2 unfolding ivl_restr_a2_map_def using * tstp_def by(auto split:option.splits)
          moreover have tp_leq: "tp - len + 1 < tp'" using tp'_in a by auto
          moreover have "ts'' \<ge> ts'" using tstp_le_aux[OF tstp_lookup tstp_lookup' in1 tp' tp_leq _ _ auxa list_all_tstp]
            using valid_before by auto
          ultimately have aux: "ts_tp_lt I ts' (tp - len + 1) tstp" unfolding ts_tp_lt_def by(auto split:sum.splits)
          have "(table, tstp') \<notin> set taken"
          proof(rule ccontr)
            assume "\<not> (table, tstp') \<notin> set taken"
            then have "\<not>(ts_tp_lt I ts' (tp - len + 1) tstp)" using taken_valid using \<open>tstp = tstp'\<close> by fastforce
            then show "False" using aux by auto
          qed
          then have "(table, tstp') \<in> set (linearize tables')" using defs(1) unfolding tables_split by auto
          then show "case Mapping.lookup m_aux x of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> x \<in> table" using tstp_def defs(2-3) by auto
        qed
        then show ?thesis using m_aux_def by auto
      qed
    qed
  qed
  have result': "(case Mapping.lookup a2_map'' (tp - (len - 1)) of Some m \<Rightarrow> result' = Mapping.keys m | _ \<Rightarrow> False)"
    using len_not_0 m'_def Suc_diff_le[OF len_tp]
    by (auto simp: a2_map''_def a2_map'_def result'_def result_def mc_def m_eq m_del_def lookup_old Mapping_lookup_delete lookup_update' split: option.splits)
  have "\<forall> (a, b) \<in> set (linearize tables). case b of Inl ts \<Rightarrow> ts \<le> cur | Inr tp' \<Rightarrow> tp' \<le> tp" using valid_before by auto
  moreover have "set (linearize tables') \<subseteq> set (linearize tables)" unfolding tables_split by auto
  ultimately have valid_table_restr: "\<forall>(a, b) \<in> set (linearize tables'). case b of Inl ts \<Rightarrow> ts \<le> cur | Inr tp' \<Rightarrow> tp' \<le> tp" by auto
  have "Mapping.keys tstp_map = {tp - len..tp - 1}" using valid_before len_not_0 by auto
  then have "Mapping.keys tstp_map' = (if len - 1 > 0 then {tp - (len - 1)..tp - 1} else {})" unfolding tstp_map'_def tp_len_assoc[symmetric] using Suc_diff_le by auto
  moreover have "Suc (length auxlist - Suc 0) = length auxlist"
    using assms(2) valid_before
    by (cases auxlist) (auto simp: aux_def)
  ultimately show ?thesis
    using valid_before a2_map''_keys sorted_tl list_all' lookup'' list_all2'' list_all'' lin_ts still_empty sorted_tables' isl_tables' valid_tables' valid_table_restr
    unfolding eval_step_mmuaux_eq valid_mmuaux'.simps tl_aux_def aux_def I_def n_def R_def pos_def
    using lin_tss_not_Nil safe_hd_eq len_pos Suc_diff_le result'_def result'
    by (auto simp add: list.set_sel(2) lin_tss' lin_tss''' tl_queue_rep[of tss'] min_auxlist_done)
qed

lemma done_empty_valid_mmuaux'_intro:
  assumes "valid_mmuaux' args cur dt
    (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) auxlist"
  shows "valid_mmuaux' args cur dt'
    (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, [])
    (drop (length done) auxlist)"
  using assms sorted_drop by (auto simp add: drop_map[symmetric])

lemma valid_mmuaux'_mono:
  assumes "valid_mmuaux' args cur dt aux auxlist" "dt \<le> dt'"
  shows "valid_mmuaux' args cur dt' aux auxlist"
  using assms less_le_trans by (cases aux) (fastforce simp: memR_antimono)

lemma valid_foldl_eval_step_mmuaux':
  assumes valid_before: "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = tss @ tss'"
    "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmuaux aux)) \<Longrightarrow> \<not> memR (args_ivl args) (dt - ts)"
  shows "valid_mmuaux' args cur dt (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss) auxlist \<and>
    lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux args aux) aux tss) = tss'"
  using assms
proof (induction tss arbitrary: aux)
  case (Cons ts tss)
  have app_ass: "lin_ts_mmuaux aux = ts # (tss @ tss')"
    using Cons(3) by auto
  have "\<not> memR (args_ivl args) (dt - ts)"
    using Cons by auto
  then have valid_step: "valid_mmuaux' args cur dt (eval_step_mmuaux args aux) auxlist"
    "lin_ts_mmuaux (eval_step_mmuaux args aux) = tss @ tss'"
    using valid_eval_step_mmuaux'[OF Cons(2) app_ass] by auto
  show ?case
    using Cons(1)[OF valid_step] valid_step Cons(4) app_ass by auto
qed auto

lemma sorted_dropWhile_filter: "sorted xs \<Longrightarrow> dropWhile (\<lambda>t. \<not> memR I (nt - t)) xs =
  filter (\<lambda>t. memR I (nt - t)) xs"
proof (induction xs)
  case (Cons x xs)
  then show ?case
  proof (cases "\<not> memR I (nt - x)")
    case False
    then have neg: "memR I (nt - x)"
      by auto
    with Cons have "\<And>z. z \<in> set xs \<Longrightarrow> memR I (nt - z)"
      by (auto simp: diff_le_mono2)
    with False show ?thesis
      using filter_empty_conv by auto
  qed auto
qed auto

fun shift_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "shift_mmuaux args nt (tp, tss, len, maskL, maskR, result, a1_map, a2_map, done, done_length) =
    (let (tss_queue, tss') = takeWhile_queue (\<lambda>t. \<not> memR (args_ivl args) (nt - t)) tss in
    foldl (\<lambda>aux _. eval_step_mmuaux args aux) (tp, tss', len, maskL, maskR,
      result, a1_map, a2_map, done, done_length) (linearize tss_queue))"

lemma valid_shift_mmuaux':
  assumes "valid_mmuaux' args cur cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmuaux' args cur nt (shift_mmuaux args nt aux) auxlist \<and>
    (\<forall>ts \<in> set (lin_ts_mmuaux (shift_mmuaux args nt aux)). memR (args_ivl args) (nt - ts))"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where aux_def:
    "aux = (tp, tss, len, tables, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases aux) auto
  note valid_before = valid_folded[unfolded aux_def]
  define tss_list where "tss_list =
    linearize (fst (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss))"
  define tss' where "tss' = snd (takeWhile_queue (\<lambda>t. \<not> memR I (nt - t)) tss)"
  let ?aux = "(tp, tss', len, tables, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
  have tss_list_takeWhile: "tss_list = takeWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    using tss_list_def unfolding takeWhile_queue_rep_fst .
  then obtain tss_list' where tss_list'_def: "linearize tss = tss_list @ tss_list'"
    "tss_list' = dropWhile (\<lambda>t. \<not> memR I (nt - t)) (linearize tss)"
    by auto
  obtain tp' len' tss' tables' maskL' maskR' a1_map' a2_map' "done'" done_length' where
    foldl_aux_def: "(tp', tss', tables', len', maskL', maskR', a1_map', a2_map',
      done', done_length') = foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list"
    by (cases "foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list") auto
  have lin_tss_aux: "lin_ts_mmuaux ?aux = linearize tss"
    unfolding aux_def tss'_def lin_ts_mmuaux.simps takeWhile_queue_rep_snd by auto
  then have valid_aux: "valid_mmuaux' args cur nt ?aux auxlist" using valid_before by(auto)
  have "take (length tss_list) (lin_ts_mmuaux ?aux) = tss_list"
    unfolding lin_tss_aux using tss_list'_def(1) by auto
  then have valid_foldl: "valid_mmuaux' args cur nt
    (foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list) auxlist"
    "lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list) = tss_list'"
    using valid_foldl_eval_step_mmuaux'[OF valid_aux, unfolded lin_tss_aux, OF tss_list'_def(1) ]
       tss_list_takeWhile set_takeWhileD
    unfolding lin_tss_aux I_def by fastforce+
  have shift_mmuaux_eq: "shift_mmuaux args nt aux = foldl (\<lambda>aux _. eval_step_mmuaux args aux) ?aux tss_list"
    using tss_list_def unfolding aux_def I_def tss'_def by (auto split:prod.splits)
  have "\<And>ts. ts \<in> set tss_list' \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using sorted_dropWhile_filter tss_list'_def(2) valid_before unfolding I_def by auto
  then show ?thesis
    using valid_foldl(1)[unfolded shift_mmuaux_eq[symmetric]]
    unfolding valid_foldl(2)[unfolded shift_mmuaux_eq[symmetric]] by auto
qed

lift_definition upd_set' :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m d f X a. (if a \<in> X then (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d)
    else Mapping.lookup m a)" .

lemma upd_set'_lookup: "Mapping.lookup (upd_set' m d f X) a = (if a \<in> X then
  (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set'.rep_eq)

lemma upd_set'_keys: "Mapping.keys (upd_set' m d f X) = Mapping.keys m \<union> X"
  by (auto simp add: upd_set'_lookup intro!: Mapping_keys_intro
      dest!: Mapping.in_keysD split: option.splits)

lift_definition upd_nested :: "('a, ('b, 'c) mapping) mapping \<Rightarrow>
  'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a, ('b, 'c) mapping) mapping" is
  "\<lambda>m d f X a. case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None" .

lemma upd_nested_lookup: "Mapping.lookup (upd_nested m d f X) a =
  (case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None)"
  by (simp add: Mapping.lookup.abs_eq upd_nested.abs_eq)

lemma upd_nested_keys: "Mapping.keys (upd_nested m d f X) = Mapping.keys m \<union> fst ` X"
  by (auto simp add: upd_nested_lookup Domain.DomainI fst_eq_Domain intro!: Mapping_keys_intro
      dest!: Mapping.in_keysD split: option.splits)

definition add_new_mmuaux :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data mmuaux" where
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if memL I 0 then Inr tp else Inl nt);
    tstp_map = Mapping.update tp nt tstp_map;
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {});
    tmp = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp;
    table = snd ` tmp;
    tables = append_queue (table, if memL I 0 then Inr tp else Inl nt) tables;
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, tables, len + 1, maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp), a1_map, a2_map, tstp_map, done))"

lemma fst_case: "(\<lambda>x. fst (case x of (t, a1, a2) \<Rightarrow> (t, y t a1 a2, z t a1 a2))) = fst"
  by auto

lemma list_all2_in_setE: "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<And>y. y \<in> set ys \<Longrightarrow> P x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fastforce simp: list_all2_iff set_zip in_set_conv_nth)

lemma list_all2_zip: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> Q y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> Q (fst x)"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

lemma take_takeWhile: "n \<le> length ys \<Longrightarrow>
  (\<And>y. y \<in> set (take n ys) \<Longrightarrow> P y) \<Longrightarrow>
  (\<And>y. y \<in> set (drop n ys) \<Longrightarrow> \<not>P y) \<Longrightarrow>
  take n ys = takeWhile P ys"
proof (induction ys arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases n) simp_all
qed

lemma valid_add_new_mmuaux:
  assumes valid_before: "valid_mmuaux args cur aux auxlist"
    and tabs: "table (args_n args) (args_L args) rel1" "table (args_n args) (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmuaux args nt (add_new_mmuaux args rel1 rel2 nt aux)
    (update_until args rel1 rel2 nt auxlist)"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,4) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, tables, len, maskL, maskR,
    result, a1_map, a2_map, tstp_map, done) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(4)]
    unfolding shift_aux_def by auto
  define new_tstp where "new_tstp = (if memL I 0 then Inr tp else Inl nt)"
  have new_tstp_lt_isl: "tstp_lt new_tstp nt (tp + 1)"
    "isl new_tstp \<longleftrightarrow> \<not> memL I 0"
    by (auto simp add: new_tstp_def tstp_lt_def)
  define tmp where "tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
    (if \<not>pos then {(tp - len, as)} else {})
    | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
    else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if memL I 0 then {tp} \<times> rel2 else {})"
  define tstp_map' where "tstp_map' = Mapping.update tp nt tstp_map"
  define tmp' where "tmp' = Set.filter (\<lambda>(tp, as). case Mapping.lookup tstp_map' tp of Some ts \<Rightarrow> memL I (nt - ts)) tmp"
  have a1_map_lookup: "\<And>as tp'. Mapping.lookup a1_map as = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux(1) Mapping_keys_intro by force
  then have fst_tmp: "\<And>tp'. tp' \<in> fst ` tmp' \<Longrightarrow> tp - len \<le> tp' \<and> tp' < tp + 1"
    unfolding tmp'_def tmp_def by (auto simp add: less_SucI split: option.splits if_splits)
  have snd_tmp: "\<And>tp'. table n R (snd ` tmp')"
    using tabs(2) unfolding tmp'_def tmp_def n_def R_def
    by(auto simp add: table_def split: if_splits option.splits) blast+
  define a2_map' where "a2_map' = Mapping.update (tp + 1) Mapping.empty
    (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp')"
  define a1_map' where "a1_map' = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
    (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1)"
  define tss' where "tss' = append_queue nt tss"
  define tables' where "tables' = append_queue (snd ` tmp', if memL I 0 then Inr tp else Inl nt) tables"
  have add_new_mmuaux_eq: "add_new_mmuaux args rel1 rel2 nt aux = (tp + 1, tss', tables', len + 1,
    maskL, maskR, result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp'), a1_map', a2_map', tstp_map', done)"
    using shift_aux_def new_tstp_def tmp_def a2_map'_def a1_map'_def tss'_def tmp'_def tables'_def
    unfolding I_def pos_def tstp_map'_def
    by (auto simp only: add_new_mmuaux_def Let_def)
  have update_until_eq: "update_until args rel1 rel2 nt auxlist =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) auxlist) @
    [(nt, rel1, if memL I 0 then rel2 else empty_table)]"
    unfolding update_until_def I_def pos_def by simp
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have auxlist_split: "auxlist = take (length done) auxlist @ drop (length done) auxlist"
    using len_done_auxlist by auto
  have lin_tss': "linearize tss' = linearize tss @ [nt]"
    unfolding tss'_def append_queue_rep by (rule refl)
  have len_lin_tss': "length (linearize tss') = len + 1"
    unfolding lin_tss' using valid_shift_aux by auto
  have tmp: "sorted (linearize tss)" "\<And>t. t \<in> set (linearize tss) \<Longrightarrow> t \<le> cur"
    using valid_shift_aux by auto
  have sorted_lin_tss': "sorted (linearize tss')"
    unfolding lin_tss' using tmp(1) le_trans[OF _ assms(4), OF tmp(2)]
    by (simp add: sorted_append)
  have in_lin_tss: "\<And>t. t \<in> set (linearize tss) \<Longrightarrow>
    t \<le> cur \<and> memR I (cur - t)"
    using valid_shift_aux(1) unfolding I_def by auto
  then have set_lin_tss': "\<forall>t \<in> set (linearize tss'). t \<le> nt \<and> memR I (nt - t)"
    unfolding lin_tss' I_def using le_trans[OF _ assms(4)] valid_shift_aux(2)
    by (auto simp add: not_less)
  have a1_map'_keys: "Mapping.keys a1_map' \<subseteq> Mapping.keys a1_map \<union> rel1"
    unfolding a1_map'_def using Mapping.keys_filter Mapping_upd_set_keys
    by (auto simp add: Mapping_upd_set_keys split: if_splits dest: Mapping_keys_filterD)
  then have tab_a1_map'_keys: "table n L (Mapping.keys a1_map')"
    using valid_shift_aux(1) tabs(1) by (auto simp add: table_def n_def L_def)
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_shift_aux by auto
  have a2_map'_keys: "Mapping.keys a2_map' = {tp - len..tp + 1}"
    unfolding a2_map'_def Mapping.keys_update upd_nested_keys a2_map_keys using fst_tmp
    by fastforce
  then have a2_map'_keys': "Mapping.keys a2_map' = {tp + 1 - (len + 1)..tp + 1}"
    by auto
  have len_upd_until: "length done + (len + 1) = length (update_until args rel1 rel2 nt auxlist)"
    using valid_shift_aux unfolding update_until_eq by auto
  have set_take_auxlist: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have list_all2_triple: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) (drop (length done) auxlist)
    (zip (linearize tss) [tp - len..<tp])"
    using valid_shift_aux unfolding I_def pos_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux(2)[OF list_all2_zip[OF list_all2_triple,
      of "\<lambda>y. y \<in> set (linearize tss)"]]
    unfolding I_def by auto
  have length_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using take_takeWhile[OF length_done_auxlist set_take_auxlist set_drop_auxlist] .
  have "length done = length (takeWhile (check_before I nt) auxlist)"
    by (metis (no_types) add_diff_cancel_right' auxlist_split diff_diff_cancel
        length_append length_done_auxlist length_drop take_auxlist_takeWhile)
  then have set_take_auxlist': "\<And>x. x \<in> set (take (length done)
    (update_until args rel1 rel2 nt auxlist)) \<Longrightarrow> check_before I nt x"
    by (metis I_def length_map map_proj_thd_update_until set_takeWhileD takeWhile_eq_take)
  have rev_done: "rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist))"
    using valid_shift_aux by auto
  moreover have "\<dots> = map (eval_args_agg args) (map proj_thd (takeWhile (check_before I nt)
    (update_until args rel1 rel2 nt auxlist)))"
    by (simp add: take_auxlist_takeWhile I_def) (metis List.map.compositionality map_proj_thd_update_until)
  finally have rev_done': "rev done = map (eval_args_agg args) (map proj_thd (take (length done)
    (update_until args rel1 rel2 nt auxlist)))"
    by (metis length_map length_rev takeWhile_eq_take)
  have map_fst_auxlist_take: "\<And>t. t \<in> set (map fst (take (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using set_take_auxlist linear by fastforce
  have map_fst_auxlist_drop: "\<And>t. t \<in> set (map fst (drop (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using in_lin_tss[OF list_all2_zip[OF list_all2_triple, of "\<lambda>y. y \<in> set (linearize tss)"]]
      assms(4) dual_order.trans by auto blast
  have set_drop_auxlist_cong: "\<And>x t a1 a2. x \<in> set (drop (length done) auxlist) \<Longrightarrow>
    x = (t, a1, a2) \<Longrightarrow> mem I ((nt - t)) \<longleftrightarrow> memL I (nt - t)"
  proof -
    fix x t a1 a2
    assume "x \<in> set (drop (length done) auxlist)" "x = (t, a1, a2)"
    then have "memR I (nt - t)"
      using set_drop_auxlist not_less
      by auto
    then show "mem I (nt - t) \<longleftrightarrow> memL I (nt - t)"
      by auto
  qed
  note list_all_split' = list_all_split[of "\<lambda>ts' tp'. ivl_restr_a2_map I ts' tp' a2_map" "\<lambda>ts' tp'. valid_tstp_map ts' tp' tstp_map"]
  have valid_tstp_map: "list_all (\<lambda>(x, y). valid_tstp_map x y tstp_map) (zip (linearize tss) [tp - len..<tp])" 
    using valid_shift_aux unfolding I_def[symmetric] valid_mmuaux'.simps list_all_split' by auto
  have length_tss: "length (linearize tss) = length [tp - len..<tp]" using valid_shift_aux by auto
  have sorted_fst_auxlist: "sorted (map fst auxlist)"
    using valid_shift_aux by auto
  have set_map_fst_auxlist: "\<And>t. t \<in> set (map fst auxlist) \<Longrightarrow> t \<le> nt"
    using arg_cong[OF auxlist_split, of "map fst", unfolded map_append] map_fst_auxlist_take
      map_fst_auxlist_drop by auto
  have lookup_a1_map_keys: "\<And>xs tp'. Mapping.lookup a1_map xs = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux Mapping_keys_intro by force
  have lookup_a1_map_keys': "\<forall>xs \<in> Mapping.keys a1_map'.
    case Mapping.lookup a1_map' xs of Some tp' \<Rightarrow> tp' < tp + 1"
    using lookup_a1_map_keys unfolding a1_map'_def
    by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set Mapping_upd_set_keys
        split: option.splits dest: Mapping.in_keysD) fastforce+
  have sorted_upd_until: "sorted (map fst (update_until args rel1 rel2 nt auxlist))"
    using sorted_fst_auxlist set_map_fst_auxlist
    unfolding update_until_eq
    by (auto simp add: sorted_append comp_def fst_case)
  have old_tables_restr: "\<forall>(a, b) \<in> set (linearize tables). case b of Inl ts \<Rightarrow> ts \<le> cur |
                                                    Inr tp' \<Rightarrow> tp' \<le> tp" 
    "list_all (\<lambda>k. isl k = (\<not> memL (args_ivl args) 0)) (map snd (linearize tables))"
    "sorted (map (tstp_unpack \<circ> snd) (linearize tables))"
    using valid_shift_aux by auto
  then have sorted_upd_tables: "sorted (map (tstp_unpack \<circ> snd) (linearize tables'))"
  proof(cases "memL I 0")
    case True
    have "\<forall>a \<in> set (map snd (linearize tables)). tstp_unpack a \<le> tp" 
    proof
      fix a
      assume assm: "a \<in> set (map snd (linearize tables))"
      then obtain tp' where "a = Inr tp'" 
        using True old_tables_restr(2) list_all_iff[of _ "map snd (linearize tables)"] I_def 
        by(auto) (metis snd_conv sum.collapse(2))
      then show "tstp_unpack a \<le> tp" using old_tables_restr(1) assm unfolding tstp_unpack_def 
        by(auto split:sum.splits)
    qed
    then show ?thesis unfolding tables'_def append_queue_rep 
      using True sorted_append[of "map (tstp_unpack \<circ> snd) (linearize tables)"] old_tables_restr(3) tstp_unpack_def by auto
  next
    case False
    have "\<forall>a \<in> set (map snd (linearize tables)). tstp_unpack a \<le> cur" 
    proof
      fix a
      assume assm: "a \<in> set (map snd (linearize tables))"
      then obtain ts' where "a = Inl ts'" 
        using False old_tables_restr(2) list_all_iff[of _ "map snd (linearize tables)"] I_def 
        by(auto) (metis snd_conv sum.collapse(1))
      then show "tstp_unpack a \<le> cur" using old_tables_restr(1) assm unfolding tstp_unpack_def 
        by(auto split:sum.splits)
    qed
    then show ?thesis unfolding tables'_def append_queue_rep 
      using nt_mono False sorted_append[of "map (tstp_unpack \<circ> snd) (linearize tables)"] old_tables_restr(3) tstp_unpack_def by auto
  qed
  have new_table_restr1: "\<forall>(a, b) \<in> set (linearize tables'). case b of Inl ts \<Rightarrow> ts \<le> nt |
                                                    Inr tp' \<Rightarrow> tp' \<le> tp + 1" 
    using old_tables_restr(1) nt_mono unfolding tables'_def append_queue_rep 
    by(auto split:prod.splits sum.splits) fastforce+
  have new_table_restr2: "list_all (\<lambda>k. isl k = (\<not> memL (args_ivl args) 0)) (map snd (linearize tables'))" 
    using old_tables_restr(2) unfolding tables'_def append_queue_rep I_def by auto
  have lookup_a2_map: "\<And>tp' m. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp cur tp \<and> (isl tstp \<longleftrightarrow> \<not> memL I 0))"
    using valid_shift_aux(1) Mapping_keys_intro unfolding I_def n_def R_def by force
  then have lookup_a2_map': "\<And>tp' m xs tstp. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    Mapping.lookup m xs = Some tstp \<Longrightarrow> tstp_lt tstp nt tp \<and>
    isl tstp = (\<not> memL I 0)"
    using Mapping_keys_intro assms(4) by (force simp add: tstp_lt_def split: sum.splits)
  have lookup_a2_map'_keys: "\<forall>tp' \<in> Mapping.keys a2_map'.
    case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
    (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
  proof (rule ballI)
    fix tp'
    assume tp'_assm: "tp' \<in> Mapping.keys a2_map'"
    then obtain m' where m'_def: "Mapping.lookup a2_map' tp' = Some m'"
      by (auto dest: Mapping.in_keysD)
    have "table n R (Mapping.keys m') \<and>
      (\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
      tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
    proof (cases "tp' = tp + 1")
      case True
      show ?thesis
        using m'_def unfolding a2_map'_def True Mapping.lookup_update
        by (auto simp add: table_def)
    next
      case False
      then have tp'_in: "tp' \<in> Mapping.keys a2_map"
        using tp'_assm unfolding a2_map_keys a2_map'_keys by auto
      then obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        by (auto dest: Mapping.in_keysD)
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
        using m_def m'_def unfolding a2_map'_def Mapping.lookup_update_neq[OF False[symmetric]]
          upd_nested_lookup
        by auto
      have "table n R (Mapping.keys m')"
        using lookup_a2_map[OF m_def] snd_tmp unfolding m'_alt upd_set'_keys
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
        tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
      proof (rule ballI)
        fix xs
        assume xs_assm: "xs \<in> Mapping.keys m'"
        then obtain tstp where tstp_def: "Mapping.lookup m' xs = Some tstp"
          by (auto dest: Mapping.in_keysD)
        have "tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using tstp_def[unfolded m'_alt upd_set'_lookup] new_tstp_lt_isl
            by (auto split: if_splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp'}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using tstp_def[unfolded m'_alt upd_set'_lookup] Some
              by auto
            show ?thesis
              using lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by (auto simp add: tstp_lt_def tstp_eq max_def split: sum.splits)
          next
            case False
            then show ?thesis
              using tstp_def[unfolded m'_alt upd_set'_lookup] lookup_a2_map'[OF m_def Some] Some
              by (auto simp add: tstp_lt_def split: sum.splits)
          qed
        qed
        then show "case Mapping.lookup m' xs of Some tstp \<Rightarrow>
          tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0)"
          using tstp_def by auto
      qed
      ultimately show ?thesis
        by auto
    qed
    then show "case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp nt (tp + 1) \<and> isl tstp = (\<not> memL I 0))"
      using m'_def by auto
  qed
  have tp_upt_Suc: "[tp + 1 - (len + 1)..<tp + 1] = [tp - len..<tp] @ [tp]"
    using upt_Suc by auto
  have map_eq: "map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist)"
    using set_drop_auxlist_cong by auto
  have "drop (length done) (update_until args rel1 rel2 nt auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem I ((nt - t)) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) @
    [(nt, rel1, if memL I 0 then rel2 else empty_table)]"
    unfolding update_until_eq using len_done_auxlist drop_map by auto
  note drop_update_until = this[unfolded map_eq]
  have list_all2_old: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (map (\<lambda>(t, a1, a2). (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist))
    (zip (linearize tss) [tp - len..<tp])"
    unfolding list_all2_map1
    using list_all2_triple
  proof (rule list.rel_mono_strong)
    fix tri pair
    assume tri_pair_in: "tri \<in> set (drop (length done) auxlist)"
      "pair \<in> set (zip (linearize tss) [tp - len..<tp])"
    obtain t a1 a2 where tri_def: "tri = (t, a1, a2)"
      by (cases tri) auto
    obtain ts' tp' where pair_def: "pair = (ts', tp')"
      by (cases pair) auto
    have "valid_tstp_map ts' tp' tstp_map"
       using valid_tstp_map tri_pair_in(2) list_all_iff[of "\<lambda>(x, y). valid_tstp_map x y tstp_map"] 
       unfolding pair_def by auto
    then have tp'_lookup: "Mapping.lookup tstp_map tp' = Some ts'" 
      unfolding valid_tstp_map_def by (auto split:option.splits)
    assume "triple_eq_pair tri pair (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)"
    then have eqs: "t = ts'" "a1 = filter_a1_map pos tp' a1_map"
      "a2 = filter_a2_map I ts' tp' a2_map"
      unfolding tri_def pair_def by auto
    have tp'_ge: "tp' \<ge> tp - len"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have tp'_lt_tp: "tp' < tp"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have ts'_in_lin_tss: "ts' \<in> set (linearize tss)"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    then have ts'_nt: "ts' \<le> nt"
      using valid_shift_aux(1) assms(4) by auto
    then have t_nt: "t \<le> nt"
      unfolding eqs(1) .
    have tp'_set: "tp' \<in> set [tp - len..<tp]" by (simp add: tp'_ge tp'_lt_tp)
    have "table n L (Mapping.keys a1_map)"
      using valid_shift_aux unfolding n_def L_def by auto
    then have a1_tab: "table n L a1"
      unfolding eqs(2) filter_a1_map_def by (auto simp add: table_def)
    note tabR = tabs(2)[unfolded n_def[symmetric] R_def[symmetric]]
    have join_rel2_assms: "L \<subseteq> R" "maskL = join_mask n L"
      using valid_shift_aux unfolding n_def L_def R_def by auto
    have join_rel2_eq: "join rel2 pos a1 = {xs \<in> rel2. proj_tuple_in_join pos maskL xs a1}"
      using join_sub[OF join_rel2_assms(1) a1_tab tabR] join_rel2_assms(2) by auto
    have filter_sub_a2: "\<And>xs m' tp'' tstp. tp'' \<le> tp' \<Longrightarrow>
      Mapping.lookup a2_map' tp'' = Some m' \<Longrightarrow> Mapping.lookup m' xs = Some tstp \<Longrightarrow>
      ts_tp_lt I ts' tp' tstp \<Longrightarrow> (tstp = new_tstp \<Longrightarrow> False) \<Longrightarrow>
      xs \<in> filter_a2_map I ts' tp' a2_map' \<Longrightarrow> xs \<in> a2"
    proof -
      fix xs m' tp'' tstp
      assume m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using le_less_trans[OF m'_def(1) tp'_lt_tp] by auto
      assume new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
      show "xs \<in> a2"
      proof (cases "Mapping.lookup a2_map tp''")
        case None
        then have m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp)
          {b. (tp'', b) \<in> tmp'}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        then show ?thesis
          using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup Mapping.lookup_empty]
          by (auto split: if_splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp'}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        note lookup_m = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup]
            by (auto split: if_splits)
        next
          case (Some tstp')
          have tstp_ok: "tstp = tstp' \<Longrightarrow> xs \<in> a2"
            using eqs(3) lookup_m Some m'_def unfolding filter_a2_map_def by auto
          show ?thesis
          proof (cases "xs \<in> {b. (tp'', b) \<in> tmp'}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            show ?thesis
              using lookup_a2_map'[OF lookup_m Some] new_tstp_lt_isl(2)
                tstp_eq new_tstp_False tstp_ok
              by (auto intro: max_tstpE[of new_tstp tstp'])
          next
            case False
            then have "tstp = tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            then show ?thesis
              using tstp_ok by auto
          qed
        qed
      qed
    qed
    have a2_sub_filter: "a2 \<subseteq> filter_a2_map I ts' tp' a2_map'"
    proof (rule subsetI)
      fix xs
      assume xs_in: "xs \<in> a2"
      then obtain tp'' m tstp where m_def: "tp'' \<le> tp'" "Mapping.lookup a2_map tp'' = Some m"
        "Mapping.lookup m xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        using eqs(3)[unfolded filter_a2_map_def] by (auto split: option.splits)
      have tp''_in: "tp'' \<in> {tp - len..tp}"
        using m_def(2) a2_map_keys by (auto intro!: Mapping_keys_intro)
      then obtain m' where m'_def: "Mapping.lookup a2_map' tp'' = Some m'"
        using a2_map'_keys
        by (metis Mapping.in_keysD One_nat_def add_Suc_right add_diff_cancel_right'
            atLeastatMost_subset_iff diff_zero le_eq_less_or_eq le_less_Suc_eq subsetD)
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using m_def(1) tp'_lt_tp by auto
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp'}"
        using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq] m_def(2)
          upd_nested_lookup] by (auto split: option.splits if_splits)
      show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (cases "xs \<in> {b. (tp'', b) \<in> tmp'}")
        case True
        then have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp)"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp)"
          using new_tstp_lt_isl(2) lookup_a2_map'[OF m_def(2,3)]
          by (auto intro: max_tstp_intro''[OF _ m_def(4)])
        ultimately show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def(4) by auto
      next
        case False
        then have "Mapping.lookup m' xs = Some tstp"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        then show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def by auto
      qed
    qed
    have "pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = join a1 True rel1"
    proof -
      assume pos: pos
      note tabL = tabs(1)[unfolded n_def[symmetric] L_def[symmetric]]
      have join_eq: "join a1 True rel1 = a1 \<inter> rel1"
        using join_eq[OF tabL a1_tab] by auto
      show "filter_a1_map pos tp' a1_map' = join a1 True rel1"
        using eqs(2) pos tp'_lt_tp unfolding filter_a1_map_def a1_map'_def join_eq
        by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set split: if_splits option.splits
            intro: Mapping_keys_intro dest: Mapping.in_keysD Mapping_keys_filterD)
    qed
    moreover have "\<not>pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = a1 \<union> rel1"
      using eqs(2) tp'_lt_tp unfolding filter_a1_map_def a1_map'_def
      by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set intro: Mapping_keys_intro
          dest: Mapping_keys_filterD Mapping.in_keysD split: option.splits)
    moreover have "memL I (nt - t) \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2 \<union> join rel2 pos a1"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume in_int: "memL I (nt - t)"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      show "xs \<in> a2 \<union> join rel2 pos a1"
      proof (cases "tstp = new_tstp")
        case True
        note tstp_new_tstp = True
        have tp''_neq: "tp + 1 \<noteq> tp''"
          using m'_def(1) tp'_lt_tp by auto
        have tp''_in: "tp'' \<in> {tp - len..tp}"
          using m'_def(1,2) tp'_lt_tp a2_map'_keys
          by (auto intro!: Mapping_keys_intro)
        obtain m where m_def: "Mapping.lookup a2_map tp'' = Some m"
          "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp'}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] tp''_in a2_map_keys
          by (fastforce dest: Mapping.in_keysD split: option.splits if_splits)
        show ?thesis
        proof (cases "Mapping.lookup m xs = Some new_tstp")
          case True
          then show ?thesis
            using eqs(3) m'_def(1) m_def(1) m'_def tstp_new_tstp
            unfolding filter_a2_map_def by auto
        next
          case False
          then have xs_in_snd_tmp: "xs \<in> {b. (tp'', b) \<in> tmp'}"
            using m'_def(3)[unfolded m_def(2) upd_set'_lookup True]
            by (auto split: if_splits)
          then have xs_in_rel2: "xs \<in> rel2"
            unfolding tmp'_def tmp_def
            by (auto split: if_splits option.splits)
          show ?thesis
          proof (cases pos)
            case True
            obtain tp''' where tp'''_def: "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
              "if pos then tp'' = max (tp - len) tp''' else tp'' = max (tp - len) (tp''' + 1)"
              using xs_in_snd_tmp m'_def(1) tp'_lt_tp True
              unfolding tmp'_def tmp_def by (auto split: option.splits if_splits)
            have "proj_tuple maskL xs \<in> a1"
              using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) tp'''_def
              by (auto intro: Mapping_keys_intro)
            then show ?thesis
              using True xs_in_rel2 unfolding proj_tuple_in_join_def join_rel2_eq by auto
          next
            case False
            show ?thesis
            proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
              case None
              then show ?thesis
                using xs_in_rel2 False eqs(2)[unfolded filter_a1_map_def]
                unfolding proj_tuple_in_join_def join_rel2_eq
                by (auto dest: Mapping.in_keysD)
            next
              case (Some tp''')
              then have "tp'' = max (tp - len) (tp''' + 1)"
                using xs_in_snd_tmp m'_def(1) tp'_lt_tp False
                unfolding tmp'_def tmp_def by (auto split: option.splits if_splits)
              then have "tp''' < tp'"
                using m'_def(1) by auto
              then have "proj_tuple maskL xs \<notin> a1"
                using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) Some False
                by (auto intro: Mapping_keys_intro)
              then show ?thesis
                using xs_in_rel2 False unfolding proj_tuple_in_join_def join_rel2_eq by auto
            qed
          qed
        qed
      next
        case False
        then show ?thesis
          using filter_sub_a2[OF m'_def _ xs_in] by auto
      qed
    next
      fix xs
      assume in_int: "memL I (nt - t)"
      assume xs_in: "xs \<in> a2 \<union> join rel2 pos a1"
      then have "xs \<in> a2 \<union> (join rel2 pos a1 - a2)"
        by auto
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (rule UnE)
        assume "xs \<in> a2"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
          using a2_sub_filter by auto
      next
        assume "xs \<in> join rel2 pos a1 - a2"
        then have xs_props: "xs \<in> rel2" "xs \<notin> a2" "proj_tuple_in_join pos maskL xs a1"
          unfolding join_rel2_eq by auto
        have ts_tp_lt_new_tstp: "ts_tp_lt I ts' tp' new_tstp"
          using tp'_lt_tp in_int t_nt eqs(1) unfolding new_tstp_def
          by (auto simp add: ts_tp_lt_def elim: contrapos_np)
        show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        proof (cases pos)
          case True
          then obtain tp''' where tp'''_def: "tp''' \<le> tp'"
            "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
            using eqs(2)[unfolded filter_a1_map_def] xs_props(3)[unfolded proj_tuple_in_join_def]
            by (auto dest: Mapping.in_keysD)
          define wtp where "wtp \<equiv> max (tp - len) tp'''"
          have wtp_xs_in: "(wtp, xs) \<in> tmp"
            unfolding wtp_def using tp'''_def tmp_def xs_props(1) True by fastforce
          have wtp_le: "wtp \<le> tp'"
            using tp'''_def(1) tp'_ge unfolding wtp_def by auto
          have wtp_in: "wtp \<in> {tp - len..tp}"
            using tp'''_def(1) tp'_lt_tp unfolding wtp_def by auto
          then have "wtp \<in> (if len > 0 then {tp - len..tp - 1} else {})" using tp'_lt_tp wtp_le by force
          then obtain ts where ts_def: "Mapping.lookup tstp_map wtp = Some ts" 
            using valid_shift_aux unfolding valid_mmuaux'.simps by (metis Mapping.in_keysD)
          have wtp_in': "wtp \<in> set [tp - len..<tp]" using wtp_in wtp_le tp'_lt_tp by auto
          have inL: "memL I (nt - ts)"
          proof(cases "memL I 0")
            case True
            then show ?thesis by auto
          next
            case False
            then have "new_tstp = Inl nt" unfolding new_tstp_def by auto
            moreover have "ts \<le> ts'" 
            proof(cases "wtp = tp'")
              case True
              then show ?thesis using ts_def tp'_lookup by auto
            next
              case False
              then have wtp_le: "wtp < tp'" using wtp_le by auto
              show ?thesis using tstp_le_aux[OF ts_def tp'_lookup wtp_in' tp'_set wtp_le tmp(1) _ length_tss valid_tstp_map] by auto
            qed 
            ultimately show ?thesis using ts_tp_lt_new_tstp unfolding ts_tp_lt_def by auto
          qed
          have wtp_neq: "tp + 1 \<noteq> wtp"
            using wtp_in by auto
          obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
            using wtp_in a2_map_keys Mapping.in_keysD by fastforce
          obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
            using wtp_in a2_map'_keys Mapping.in_keysD by fastforce
          have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp'}"
            using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
              upd_nested_lookup m_def] by auto
          show ?thesis
          proof (cases "Mapping.lookup m xs")
            case None
            thm ts_tp_lt_new_tstp
            have "Mapping.lookup m' xs = Some new_tstp"
              using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup None tstp_map'_def Mapping.lookup_update'
              apply auto using tp'_lt_tp wtp_le by linarith
            then show ?thesis
              unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt_new_tstp by auto
          next
            case (Some tstp')
            have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
              using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup Some tstp_map'_def Mapping.lookup_update'
              apply auto using leD tp'_lt_tp wtp_le by blast
            moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
              using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by auto
            ultimately show ?thesis
              using lookup_a2_map'[OF m_def Some] wtp_le m'_def
              unfolding filter_a2_map_def by auto
          qed
        next
          case False
          show ?thesis
          proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
            case None
            then have in_tmp: "(tp - len, xs) \<in> tmp"
              using tmp_def False xs_props(1) by fastforce
            obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
              using a2_map_keys by (fastforce dest: Mapping.in_keysD)
            obtain m' where m'_def: "Mapping.lookup a2_map' (tp - len) = Some m'"
              using a2_map'_keys by (fastforce dest: Mapping.in_keysD)
            have "tp - len < tp" using le_less_trans tp'_ge tp'_lt_tp by blast
            then have "tp - len \<in> (if len > 0 then {tp - len..tp - 1} else {})" by auto
            then obtain ts where ts_def: "Mapping.lookup tstp_map (tp - len) = Some ts" 
              using valid_shift_aux unfolding valid_mmuaux'.simps by (metis Mapping.in_keysD)
            have inL: "memL I (nt - ts)"
            proof(cases "memL I 0")
              case True
              then show ?thesis by auto
            next
              case False
              then have "new_tstp = Inl nt" unfolding new_tstp_def by auto
              moreover have "ts \<le> ts'"
              proof(cases "tp - len = tp'")
              case True
              then show ?thesis using ts_def tp'_lookup by auto
            next
              case False
              then have wtp_le: "tp - len < tp'" using le_neq_implies_less tp'_ge by presburger
              moreover have "tp - len < tp" using less_trans tp'_lt_tp wtp_le by blast
              ultimately show ?thesis using tstp_le_aux[OF ts_def tp'_lookup _ tp'_set wtp_le tmp(1) _ length_tss valid_tstp_map] by auto
            qed 
              ultimately show ?thesis using ts_tp_lt_new_tstp unfolding ts_tp_lt_def by auto
            qed
            have tp_neq: "tp + 1 \<noteq> tp - len"
              by auto
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp - len, b) \<in> tmp'}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                unfolding tmp'_def m'_alt upd_set'_lookup None tstp_map'_def Mapping.lookup_update' 
                using in_tmp inL ts_def apply auto using \<open>tp - len < tp\<close> nat_neq_iff by blast
              then show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def ts_tp_lt_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                unfolding tmp'_def m'_alt upd_set'_lookup Some tstp_map'_def Mapping.lookup_update'
                using in_tmp ts_def inL using \<open>tp - len < tp\<close> by force
              moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def by auto
            qed
          next
            case (Some tp''')
            then have tp'_gt: "tp' > tp'''"
              using xs_props(3)[unfolded proj_tuple_in_join_def] eqs(2)[unfolded filter_a1_map_def]
                False by (auto intro: Mapping_keys_intro)
            define wtp where "wtp \<equiv> max (tp - len) (tp''' + 1)"
            have wtp_xs_in: "(wtp, xs) \<in> tmp"
              unfolding wtp_def tmp_def using xs_props(1) Some False by fastforce
            have wtp_le: "wtp \<le> tp'"
              using tp'_ge tp'_gt unfolding wtp_def by auto
            have wtp_in: "wtp \<in> {tp - len..tp}"
              using tp'_lt_tp tp'_gt unfolding wtp_def by auto
            then have "wtp \<in> (if len > 0 then {tp - len..tp - 1} else {})"
              using tp'_lt_tp wtp_le by force
            then obtain ts where ts_def: "Mapping.lookup tstp_map wtp = Some ts" 
              using valid_shift_aux unfolding valid_mmuaux'.simps by (metis Mapping.in_keysD)
            have wtp_in': "wtp \<in> set [tp - len..<tp]" using wtp_in wtp_le tp'_lt_tp by auto
            have inL: "memL I (nt - ts)"
            proof(cases "memL I 0")
              case True
              then show ?thesis by auto
            next
              case False
              then have "new_tstp = Inl nt" unfolding new_tstp_def by auto
              moreover have "ts \<le> ts'" 
              proof(cases "wtp = tp'")
                case True
                then show ?thesis using ts_def tp'_lookup by auto
              next
                case False
                then have wtp_le: "wtp < tp'" using wtp_le by auto
                show ?thesis using tstp_le_aux[OF ts_def tp'_lookup wtp_in' tp'_set wtp_le tmp(1) _ length_tss valid_tstp_map] by auto
              qed 
              ultimately show ?thesis using ts_tp_lt_new_tstp unfolding ts_tp_lt_def by auto
            qed
            have wtp_neq: "tp + 1 \<noteq> wtp"
              using wtp_in by auto
            obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
              using wtp_in a2_map_keys Mapping.in_keysD by fastforce
            obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
              using wtp_in a2_map'_keys Mapping.in_keysD by fastforce
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp'}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup None tstp_map'_def Mapping.lookup_update'
                apply auto using leD tp'_lt_tp wtp_le by blast
              then show ?thesis
                unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                using wtp_xs_in ts_def inL unfolding tmp'_def m'_alt upd_set'_lookup Some tstp_map'_def Mapping.lookup_update'
                apply auto using leD tp'_lt_tp wtp_le by blast
              moreover have "ts_tp_lt I ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro' ts_tp_lt_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                using lookup_a2_map'[OF m_def Some] wtp_le m'_def
                unfolding filter_a2_map_def by auto
            qed
          qed
        qed
      qed
    qed
    moreover have "\<not> memL I (nt - t) \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume out: "\<not> memL I (nt - t)"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      have new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
        using m'_def t_nt out tp'_lt_tp unfolding eqs(1)
        by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits elim: contrapos_np)
      show "xs \<in> a2"
        using filter_sub_a2[OF m'_def new_tstp_False xs_in] .
    next
      fix xs
      assume "xs \<in> a2"
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        using a2_sub_filter by auto
    qed
    ultimately show "triple_eq_pair (case tri of (t, a1, a2) \<Rightarrow>
      (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if memL I (nt - t) then a2 \<union> join rel2 pos a1 else a2))
      pair (\<lambda>tp'. filter_a1_map pos tp' a1_map') (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map')"
      using eqs unfolding tri_def pair_def by auto
  qed
  have filter_a1_map_rel1: "filter_a1_map pos tp a1_map' = rel1"
    unfolding filter_a1_map_def a1_map'_def using leD lookup_a1_map_keys
    by (force simp add: a1_map_lookup less_imp_le_nat Mapping.lookup_filter
        Mapping_lookup_upd_set keys_is_none_rep dest: Mapping_keys_filterD
        intro: Mapping_keys_intro split: option.splits)
  have filter_a1_map_rel2: "filter_a2_map I nt tp a2_map' =
    (if memL I 0 then rel2 else empty_table)"
  proof (cases "memL I 0")
    case True
    note left_I_zero = True
    have "\<And>tp' m' xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m' \<Longrightarrow>
      Mapping.lookup m' xs = Some tstp \<Longrightarrow> ts_tp_lt I nt tp tstp \<Longrightarrow> xs \<in> rel2"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt I nt tp tstp"
      have tp'_neq: "tp + 1 \<noteq> tp'"
        using lassms(1) by auto
      have tp'_in: "tp' \<in> {tp - len..tp}"
        using lassms(1,2) a2_map'_keys tp'_neq by (auto intro!: Mapping_keys_intro)
      obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
        using lassms(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp'_neq]
          upd_nested_lookup] tp'_in a2_map_keys
        by (fastforce dest: Mapping.in_keysD intro: Mapping_keys_intro split: option.splits)
      have "xs \<in> {b. (tp', b) \<in> tmp'}"
      proof (rule ccontr)
        assume "xs \<notin> {b. (tp', b) \<in> tmp'}"
        then have Some: "Mapping.lookup m xs = Some tstp"
          using lassms(3)[unfolded m_def(2) upd_set'_lookup] by auto
        show "False"
          using lookup_a2_map'[OF m_def(1) Some] lassms(4) left_I_zero
          by (auto simp add: tstp_lt_def ts_tp_lt_def split: sum.splits)
      qed
      then show "xs \<in> rel2"
        unfolding tmp'_def tmp_def by (auto split: option.splits if_splits)
    qed
    moreover have "\<And>xs. xs \<in> rel2 \<Longrightarrow> \<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
      Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt I nt tp tstp"
    proof -
      fix xs
      assume lassms: "xs \<in> rel2"
      obtain m' where m'_def: "Mapping.lookup a2_map' tp = Some m'"
        using a2_map'_keys by (fastforce dest: Mapping.in_keysD)
      have tp_neq: "tp + 1 \<noteq> tp"
        by auto
      obtain m where m_def: "Mapping.lookup a2_map tp = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}"
        using m'_def a2_map_keys unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
          upd_nested_lookup
        by (auto dest: Mapping.in_keysD split: option.splits if_splits)
           (metis Mapping.in_keysD atLeastAtMost_iff diff_le_self le_eq_less_or_eq
            option.simps(3))
      have "tp \<in> Mapping.keys tstp_map'" using valid_shift_aux unfolding valid_mmuaux'.simps
        by (simp add: \<open>\<And>tsa. tsa \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - tsa)\<close> Mapping.lookup_update' keys_is_none_rep tstp_map'_def)
      then obtain ts where ts_def: "Mapping.lookup tstp_map' tp = Some ts" 
        using valid_shift_aux unfolding valid_mmuaux'.simps by (meson Mapping.in_keysD)
      have xs_in_tmp: "xs \<in> {b. (tp, b) \<in> tmp'}"
        using lassms left_I_zero ts_def unfolding tstp_map'_def tmp'_def tmp_def by auto
      show "\<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
        Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt I nt tp tstp"
      proof (cases "Mapping.lookup m xs")
        case None
        moreover have "Mapping.lookup m' xs = Some new_tstp"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup None by auto
        moreover have "ts_tp_lt I nt tp new_tstp"
          using left_I_zero new_tstp_def by (auto simp add: ts_tp_lt_def)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      next
        case (Some tstp')
        moreover have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup Some by auto
        moreover have "ts_tp_lt I nt tp (max_tstp new_tstp tstp')"
          using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF m_def(1) Some] new_tstp_lt_isl left_I_zero
          by (auto simp add: sum.discI(1) new_tstp_def ts_tp_lt_def tstp_lt_def split: sum.splits)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      qed
    qed
    ultimately show ?thesis
      unfolding filter_a2_map_def
      using True by (fastforce split: option.splits)
  next
    case False
    note left_I_pos = False
    have "\<And>tp' m xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m \<Longrightarrow>
      Mapping.lookup m xs = Some tstp \<Longrightarrow> \<not>(ts_tp_lt I nt tp tstp)"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp"
      from lassms(1) have tp'_neq_Suc_tp: "tp + 1 \<noteq> tp'"
        by auto
      show "\<not>(ts_tp_lt I nt tp tstp)"
      proof (cases "Mapping.lookup a2_map tp'")
        case None
        then have tp'_in_tmp: "tp' \<in> fst ` tmp'" and
          m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by (auto split: if_splits)
        then have "tstp = new_tstp"
          using lassms(3)[unfolded m'_alt upd_set'_lookup]
          by (auto split: if_splits)
        then show ?thesis
          using False by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits sum.splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by auto
        note lookup_a2_map_tp' = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then have "tstp = new_tstp"
            using lassms(3) unfolding m'_alt upd_set'_lookup by (auto split: if_splits)
          then show ?thesis
            using False by (auto simp add: ts_tp_lt_def new_tstp_def split: if_splits sum.splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp'}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using lassms(3)
              unfolding m'_alt upd_set'_lookup Some by auto
            show ?thesis
              using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF lookup_a2_map_tp' Some] new_tstp_lt_isl left_I_pos
              by (auto simp add: tstp_eq tstp_lt_def ts_tp_lt_def new_tstp_def split: sum.splits)
          next
            case False
            then show ?thesis
              using lassms(3) lookup_a2_map'[OF lookup_a2_map_tp' Some]
                nat_le_linear[of nt "case tstp of Inl ts \<Rightarrow> ts"]
              unfolding m'_alt upd_set'_lookup Some
              by (auto simp add: ts_tp_lt_def tstp_lt_def split: sum.splits)
          qed
        qed
      qed
    qed
    then show ?thesis
      using False by (auto simp add: filter_a2_map_def empty_table_def split: option.splits)
  qed
  have zip_dist: "zip (linearize tss @ [nt]) ([tp - len..<tp] @ [tp]) =
    zip (linearize tss) [tp - len..<tp] @ [(nt, tp)]"
    using valid_shift_aux(1) by auto
  have list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (drop (length done) (update_until args rel1 rel2 nt auxlist))
    (zip (linearize tss') [tp + 1 - (len + 1)..<tp + 1])"
    unfolding lin_tss' tp_upt_Suc drop_update_until zip_dist
    using filter_a1_map_rel1 filter_a1_map_rel2 list_all2_appendI[OF list_all2_old]
    by auto
  have "Mapping.keys tstp_map = (if len > 0 then {tp - len..tp - 1} else {})" using valid_shift_aux by auto
  then have tstp_map'_keys: "Mapping.keys tstp_map' = (if len + 1 > 0 then {tp + 1 - (len + 1)..tp} else {})" 
    unfolding tstp_map'_def Mapping.keys_update using atLeastAtMost_insertL by auto
  have list_all_old: "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map) (zip (linearize tss) [tp - len..<tp])"
   using valid_shift_aux unfolding I_def by auto
  then have list_all_old': "list_all (\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map' \<and> valid_tstp_map ts' tp' tstp_map') (zip (linearize tss) [tp - len..<tp])"
  proof (rule list.pred_mono_strong[of "\<lambda>(ts', tp'). ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map"])
    fix z
    assume assms: "z \<in> set (zip (linearize tss) [tp - len..<tp])" "case z of (ts', tp') \<Rightarrow> ivl_restr_a2_map I ts' tp' a2_map \<and> valid_tstp_map ts' tp' tstp_map"
    then obtain ts' tp' where defs: "z = (ts', tp')" "ts' \<in> set (linearize tss)" "tp' \<in> set [tp - len..<tp]"
      by (metis in_set_zipE prod_decode_aux.cases)
    then have restr: "ivl_restr_a2_map I ts' tp' a2_map" "valid_tstp_map ts' tp' tstp_map" using assms(2) by auto
    have "Mapping.keys tstp_map = set [tp - len..<tp]" using valid_shift_aux by(auto) (metis Suc_pred le_0_eq le_imp_less_Suc length_0_conv neq0_conv)
    then obtain ts where ts_def: "Mapping.lookup tstp_map tp' = Some ts" using defs(3) by (metis Mapping.in_keysD)
    then have ts_eq: "ts = ts'" using restr(2) unfolding valid_tstp_map_def by auto
    have neq: "(tp + 1 = tp') = False" using defs(3) by auto
    have tp'_lt_tp: "tp' < tp"
      using defs(3) by auto
    have valid_ivl_restr: "ivl_restr_a2_map I ts' tp' a2_map'"
    proof(cases "Mapping.lookup a2_map tp'")
      case None
      then show ?thesis unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
        using ts_def restr(1) by(auto simp: ivl_restr_a2_map_def split:option.splits) 
    next
      case (Some a)
      fix a'
      assume l: "Mapping.lookup a2_map tp' = Some a'"
      show "ivl_restr_a2_map I ts' tp' a2_map'" 
      proof(cases "tp' \<in> fst ` tmp")
        case True
        then show ?thesis 
        proof(cases "memL I (nt - ts)")
          case True
          then have "ts_tp_lt I ts' tp' new_tstp" 
            using tp'_lt_tp defs(3) ts_eq unfolding new_tstp_def
            by (auto simp add: ts_tp_lt_def elim: contrapos_np)
          then show ?thesis using l ts_def unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
            using restr(1) upd_set'_lookup[of a'] lookup_a2_map' max_tstp_intro' new_tstp_lt_isl(2)
            by(auto simp: ivl_restr_a2_map_def rev_image_eqI split:option.splits) 
        next
          case False
          then show ?thesis using l ts_def unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
          using restr(1) upd_set'_lookup[of a'] by(auto simp: ivl_restr_a2_map_def rev_image_eqI) (metis Mapping.lookup_update' nat_less_le option.simps(5) tp'_lt_tp tstp_map'_def)
        qed
      next
        case False
        then show ?thesis using l unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' neq upd_nested_lookup tmp'_def
          using restr(1) upd_set'_lookup[of a'] by(auto simp: ivl_restr_a2_map_def rev_image_eqI) 
      qed 
    qed
    have valid_tstp_map: "valid_tstp_map ts' tp' tstp_map'" 
      using restr(2) neq unfolding tstp_map'_def valid_tstp_map_def Mapping.lookup_update'
      apply(auto) using tp'_lt_tp by fastforce
    show "case z of (ts', tp') \<Rightarrow> ivl_restr_a2_map I ts' tp' a2_map' \<and> valid_tstp_map ts' tp' tstp_map'"
      using valid_tstp_map valid_ivl_restr defs(1) by auto
  qed
  obtain m' where m'_def: "Mapping.lookup a2_map' tp = Some m'"
    using a2_map'_keys by (fastforce dest: Mapping.in_keysD)
  have tp_neq: "tp + 1 \<noteq> tp" by auto
  obtain m where m_def: "Mapping.lookup a2_map tp = Some m" "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}"
    using m'_def a2_map_keys unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup
    by (auto dest: Mapping.in_keysD split: option.splits if_splits) (metis Mapping.in_keysD atLeastAtMost_iff diff_le_self le_eq_less_or_eq option.simps(3))
  have m_empty: "m = Mapping.empty" using m_def valid_shift_aux by auto
  have "ivl_restr_a2_map I nt tp a2_map'" 
  proof (cases "memL I 0")
    case True
    show ?thesis unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' upd_nested_lookup 
      using m_def apply(auto)
    proof -
      fix xs
      show "case Mapping.lookup (upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}) xs of
          None \<Rightarrow> True | Some x \<Rightarrow> ts_tp_lt I nt tp x"
        unfolding upd_set'_lookup new_tstp_def ts_tp_lt_def using True m_empty by(auto split:option.splits)
    qed
  next
    case False
     show ?thesis unfolding a2_map'_def ivl_restr_a2_map_def Mapping.lookup_update' upd_nested_lookup 
       using m_def apply(auto)
     proof -
       fix xs
       have "Mapping.lookup tstp_map' tp = Some nt" unfolding tstp_map'_def by transfer auto
       then show "case Mapping.lookup (upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp'}) xs of
          None \<Rightarrow> True | Some x \<Rightarrow> ts_tp_lt I nt tp x"
         unfolding upd_set'_lookup new_tstp_def ts_tp_lt_def tmp'_def 
         using False m_empty by auto
     qed
  qed
  moreover have "valid_tstp_map nt tp tstp_map'"
    unfolding tstp_map'_def valid_tstp_map_def Mapping.lookup_update' by auto
  ultimately have list_all': "list_all
     (\<lambda>(ts', tp').
         ivl_restr_a2_map I ts' tp' a2_map' \<and> valid_tstp_map ts' tp' tstp_map')
     (zip (linearize tss') [tp + 1 - (len + 1)..<tp + 1])" 
    unfolding lin_tss' tp_upt_Suc zip_dist using list_all_old' by auto
  have valid_table_restr: "\<forall>tp' \<in> Mapping.keys a2_map'. case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
  proof 
    fix tp'
    assume tp'_in: "tp' \<in> Mapping.keys a2_map'"
    then obtain m where m_def: "Mapping.lookup a2_map' tp' = Some m" by (meson Mapping.in_keysD)
    have "\<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
    proof(cases "tp' = tp + 1")
      case True
      then have "m = Mapping.empty" using m_def unfolding a2_map'_def Mapping.lookup_update' by auto
      then show ?thesis by auto
    next
      case not_eq: False
      then show ?thesis 
      proof(cases "Mapping.lookup a2_map tp'")
        case None
        then show ?thesis 
        proof(cases "tp' \<in> fst ` tmp'")
          case True
          then have m_def: "m = upd_set' Mapping.empty new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}"
            using m_def not_eq None unfolding a2_map'_def Mapping.lookup_update' upd_nested_lookup by auto
          show ?thesis unfolding m_def upd_set'_lookup upd_set'_keys Mapping.lookup_empty tables'_def append_queue_rep new_tstp_def 
            by(simp) (meson image_snd)
        next
          case False
          then have "m = Mapping.empty" using m_def None not_eq unfolding a2_map'_def Mapping.lookup_update' upd_nested_lookup by auto
          then show ?thesis by auto
        qed
      next
        case (Some a)
        have "(\<forall>tp'\<in>Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table)"
          using valid_shift_aux by auto
        then have a_restr: "\<forall>xs \<in> Mapping.keys a. case Mapping.lookup a xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables). tstp = tstp' \<and> xs \<in> table"
            using Some tp'_in Mapping_keys_intro by fastforce
        have m_def: "m = upd_set' a new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp'}" using Some m_def not_eq unfolding a2_map'_def Mapping.lookup_update' upd_nested_lookup by auto
        show ?thesis
        proof 
          fix xs
          assume in_m: "xs \<in> Mapping.keys m"
          show "case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp'}")
            case True
            then show ?thesis
            proof(cases "Mapping.lookup a xs")
              case None
              then show ?thesis using True unfolding m_def upd_set'_lookup tables'_def append_queue_rep new_tstp_def by(cases "memL I 0"; simp; meson image_snd)
            next
              case (Some a')
              then have "xs \<in> Mapping.keys a" by transfer auto
              then have "\<exists>x\<in>set (linearize tables). case x of (tablea, tstp') \<Rightarrow> a' = tstp' \<and> xs \<in> tablea"
                using a_restr Some by fastforce
              then show ?thesis using Some True unfolding m_def upd_set'_lookup tables'_def append_queue_rep new_tstp_def 
                by(cases "memL I 0"; cases a'; simp; meson image_snd; linarith)
            qed
          next
            case False
            then have in_a: "xs \<in> Mapping.keys a" using in_m unfolding m_def upd_set'_keys False by auto
            then obtain tstp where tstp_def: "Mapping.lookup a xs = Some tstp" by (meson Mapping.in_keysD)
            then have "\<exists>x\<in>set (linearize tables). case x of (tablea, tstp') \<Rightarrow> tstp = tstp' \<and> xs \<in> tablea"
              using a_restr in_a by fastforce
            then show ?thesis using False tstp_def unfolding m_def upd_set'_lookup tables'_def append_queue_rep by(cases "memL I 0") simp+
          qed
        qed
      qed
    qed
    then show "case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> \<forall>xs\<in>Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow> \<exists>(table, tstp')\<in>set (linearize tables'). tstp = tstp' \<and> xs \<in> table"
      using m_def by auto
  qed
  have "Mapping.lookup a2_map' (tp + 1) = Some Mapping.empty" 
    unfolding a2_map'_def using Mapping.lookup_update[of "tp + 1" Mapping.empty "upd_nested a2_map new_tstp (max_tstp new_tstp) tmp'"] by auto
  moreover have "(case Mapping.lookup a2_map' (tp - len) of None \<Rightarrow> False | Some m \<Rightarrow>
     result \<union> snd ` (Set.filter (\<lambda>(t, x). t = tp - len) tmp') = Mapping.keys m)"
  proof -
    have "(case Mapping.lookup a2_map (tp - len) of None \<Rightarrow> False | Some m \<Rightarrow> result = Mapping.keys m)"
      using valid_shift_aux
      by auto
    then show ?thesis
      by (force simp: a2_map'_def lookup_update' upd_nested_lookup upd_set'_keys split: option.splits)
  qed
  ultimately show ?thesis
    using valid_shift_aux len_lin_tss' sorted_lin_tss' set_lin_tss' tab_a1_map'_keys a2_map'_keys'
      len_upd_until sorted_upd_until lookup_a1_map_keys' rev_done' set_take_auxlist'
      lookup_a2_map'_keys list_all2' tstp_map'_keys list_all' new_table_restr1 new_table_restr2 sorted_upd_tables valid_table_restr
    unfolding valid_mmuaux_def add_new_mmuaux_eq valid_mmuaux'.simps
      I_def n_def L_def R_def pos_def by auto
qed

lemma list_all2_check_before: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> memR I (nt - y)) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<not>check_before I nt x"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

fun eval_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow> event_data table list \<times> event_data mmuaux" where
  "eval_mmuaux' args nt aux =
    (let (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    shift_mmuaux args nt aux in
    (rev done, (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, [])))"

lemma valid_eval_mmuaux':
  assumes "valid_mmuaux args cur aux auxlist" "nt \<ge> cur"
    "eval_mmuaux' args nt aux = (res, aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "valid_mmuaux args cur aux' auxlist' \<and> res = map (eval_args_agg args) res'"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss tables maskL maskR result a1_map a2_map tstp_map "done" where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, tables, len, maskL, maskR,
    result, a1_map, a2_map, tstp_map, done) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> memR (args_ivl args) (nt - ts)"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(2)]
    unfolding shift_aux_def by auto
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have list_all: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux[unfolded valid_mmuaux'.simps]
      list_all2_check_before[OF _ valid_shift_aux(2)] unfolding I_def by fast
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using len_done_auxlist list_all set_drop_auxlist
    by (rule take_takeWhile) assumption+
  have rev_done: "rev done = map (eval_args_agg args) (map proj_thd (take (length done) auxlist))"
    using valid_shift_aux by auto
  then have res'_def: "map (eval_args_agg args) res' = rev done"
    using eval_until_res[OF assms(4)] unfolding take_auxlist_takeWhile I_def by auto
  then have auxlist'_def: "auxlist' = drop (length done) auxlist"
    using eval_until_auxlist'[OF assms(4)] by (metis length_map length_rev)
  have eval_mmuaux_eq: "eval_mmuaux' args nt aux = (rev done, (tp, tss, tables, len, maskL, maskR,
    result, a1_map, a2_map, tstp_map, []))"
    using shift_aux_def by auto
  show ?thesis
    using assms(3) done_empty_valid_mmuaux'_intro[OF valid_shift_aux(1)]
    unfolding shift_aux_def eval_mmuaux_eq pos_def auxlist'_def res'_def valid_mmuaux_def by auto
qed

definition init_mmuaux :: "args \<Rightarrow> event_data mmuaux" where
  "init_mmuaux args = (0, empty_queue, empty_queue, 0,
  join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
  {}, Mapping.empty, Mapping.update 0 Mapping.empty Mapping.empty, Mapping.empty, [])"

lemma valid_init_mmuaux: "L \<subseteq> R \<Longrightarrow> valid_mmuaux (init_args I n L R b agg) 0
  (init_mmuaux (init_args I n L R b agg)) []"
  unfolding init_mmuaux_def valid_mmuaux_def
  by (auto simp add: init_args_def empty_queue_rep table_def)

fun length_mmuaux :: "args \<Rightarrow> event_data mmuaux \<Rightarrow> nat" where
  "length_mmuaux args (tp, tss, tables, len, maskL, maskR, result, a1_map, a2_map, tstp_map, done) =
    length done + len"

lemma valid_length_mmuaux:
  assumes "valid_mmuaux args cur aux auxlist"
  shows "length_mmuaux args aux = length auxlist"
  using assms by (cases aux) (auto simp add: valid_mmuaux_def dest: list_all2_lengthD)

interpretation default_muaux: muaux valid_mmuaux init_mmuaux add_new_mmuaux length_mmuaux eval_mmuaux'
  using valid_init_mmuaux valid_add_new_mmuaux valid_length_mmuaux valid_eval_mmuaux'
  by unfold_locales assumption+

(*<*)
end
(*>*)