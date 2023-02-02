(*<*)
theory Correct_Since
  imports
    Correct_Agg
begin
(*>*)


subsubsection \<open> Since \<close>

definition "Sincep pos \<phi> I \<psi> \<equiv> Formula.Since (if pos then \<phi> else Formula.Neg \<phi>) I \<psi>"

lemma fv_sinceP: "fv (Sincep pos \<phi> I \<psi>) = fv \<phi> \<union> fv \<psi>"
  by (auto simp:Sincep_def)

lemma progress_Sincep: "progress \<sigma> P (Sincep pos \<phi> I \<psi>) j = progress \<sigma> P (Formula.Since \<phi> I \<psi>) j"
  by (simp add: Sincep_def)

fun wf_mbuf2S :: "Formula.trace \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> event_data list set \<Rightarrow>
  ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula \<Rightarrow> event_data mbuf2S \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_mbuf2S \<sigma> P V j n R \<phi> I \<psi> (buf\<phi>, buf\<psi>, ts, skew) pIn pOut \<longleftrightarrow>
    list_all2 (\<lambda>i. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
      [pOut ..< progress \<sigma> P \<phi> j] buf\<phi> \<and>
    list_all2 (\<lambda>i. qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>))
      [pIn ..< progress \<sigma> P \<psi> j] buf\<psi> \<and>
    list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [pOut ..< j] ts \<and>
    pOut = (if skew then Suc pIn else pIn)"

definition "sat_since_point pos \<sigma> V \<phi> \<psi> pIn i t x \<longleftrightarrow>
  (\<exists>j<pIn. \<tau> \<sigma> j = t \<and> Formula.sat \<sigma> V x j \<psi> \<and>
    (\<forall>k\<in>{j<..i}. if pos then Formula.sat \<sigma> V x k \<phi> else \<not> Formula.sat \<sigma> V x k \<phi>))"

definition (in msaux) wf_since_aux :: "Formula.trace \<Rightarrow> _ \<Rightarrow> event_data list set \<Rightarrow> args \<Rightarrow>
  ty Formula.formula \<Rightarrow> ty Formula.formula \<Rightarrow> 'msaux \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_since_aux \<sigma> V R args \<phi> \<psi> aux pIn pOut \<longleftrightarrow> pIn \<le> pOut \<and>
    valid_aggargs (args_n args) (Formula.fv \<psi>) (args_agg args) \<and> 
    (\<exists>auxlist. valid_msaux args (if pOut = 0 then 0 else \<tau> \<sigma> (pOut-1)) aux auxlist \<and>
      sorted_wrt (\<lambda>x y. fst x > fst y) auxlist \<and>
      (\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow>
        (\<exists>i<pIn. \<tau> \<sigma> i = t) \<and> memR (args_ivl args) (\<tau> \<sigma> (pOut-1) - t) \<and>
        qtable (args_n args) (fv \<psi>) (mem_restr R)
          (\<lambda>x. sat_since_point (args_pos args) \<sigma> V \<phi> \<psi> pIn (pOut-1) t (map the x)) X) \<and>
      (\<forall>i<pIn. memR (args_ivl args) (\<tau> \<sigma> (pOut-1) - \<tau> \<sigma> i) \<longrightarrow> (\<exists>X. (\<tau> \<sigma> i, X) \<in> set auxlist)))"

lemma (in msaux) wf_since_aux_UNIV_alt:
  "wf_since_aux \<sigma> V UNIV args \<phi> \<psi> aux pIn pOut \<longleftrightarrow> pIn \<le> pOut \<and>
    valid_aggargs (args_n args) (Formula.fv \<psi>) (args_agg args) \<and>
    (\<exists>auxlist. valid_msaux args (if pOut = 0 then 0 else \<tau> \<sigma> (pOut-1)) aux auxlist \<and>
      sorted_wrt (\<lambda>x y. fst x > fst y) auxlist \<and>
      (\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow>
        (\<exists>i<pIn. \<tau> \<sigma> i = t) \<and> memR (args_ivl args) (\<tau> \<sigma> (pOut-1) - t) \<and>
        wf_table (args_n args) (fv \<psi>)
          (\<lambda>x. sat_since_point (args_pos args) \<sigma> V \<phi> \<psi> pIn (pOut-1) t (map the x)) X) \<and>
      (\<forall>i<pIn. memR (args_ivl args) (\<tau> \<sigma> (pOut-1) - \<tau> \<sigma> i) \<longrightarrow> (\<exists>X. (\<tau> \<sigma> i, X) \<in> set auxlist)))"
  unfolding wf_since_aux_def qtable_mem_restr_UNIV ..

lemma wf_mbuf2S_add:
  assumes wf: "wf_mbuf2S \<sigma> P V j n R \<phi> I \<psi> buf (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) (progress \<sigma> P (Sincep pos \<phi> I \<psi>) j)"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'"
    and rm: "rel_mapping (\<le>) P P'"
    and xs: "list_all2 (\<lambda>i. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>))
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> (j + \<delta>)] ys"
  shows "wf_mbuf2S \<sigma> P' V (j + \<delta>) n R \<phi> I \<psi> (mbuf2S_add xs ys (map (\<tau> \<sigma>) [j..<j + \<delta>]) buf)
    (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) (progress \<sigma> P (Sincep pos \<phi> I \<psi>) j)"
proof -
  let ?nts = "map (\<tau> \<sigma>) [j..<j + \<delta>]"
  let ?pIn = "min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
  let ?pOut = "progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
  obtain buf\<phi> buf\<psi> ts skew where buf_eq: "buf = (buf\<phi>, buf\<psi>, ts, skew)"
    by (metis surj_pair)
  then have result_eq: "mbuf2S_add xs ys ?nts buf = (buf\<phi> @ xs, buf\<psi> @ ys, ts @ ?nts, skew)"
    by simp
  show ?thesis
    unfolding result_eq wf_mbuf2S.simps
  proof (intro conjI)
    show "list_all2 (\<lambda>i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
        [?pOut..<progress \<sigma> P' \<phi> (j + \<delta>)] (buf\<phi> @ xs)" (is "?P [?pOut..<?p\<phi>'] (buf\<phi> @ xs)")
      unfolding list_all2_append2
    proof (intro exI)
      let ?p\<phi> = "progress \<sigma> P \<phi> j"
      show "[?pOut..<?p\<phi>'] = [?pOut..<?p\<phi>] @ [?p\<phi>..<?p\<phi>'] \<and>
          length [?pOut..<?p\<phi>] = length buf\<phi> \<and> length [?p\<phi>..<?p\<phi>'] = length xs \<and>
          ?P [?pOut..<?p\<phi>] buf\<phi> \<and> ?P [?p\<phi>..<?p\<phi>'] xs"
        using wf xs by (auto simp: buf_eq progress_Sincep upt_add_eq_append' 
            progress_mono_gen[OF _ bounded rm] dest: list_all2_lengthD)
    qed
    show "list_all2 (\<lambda>i. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>))
        [?pIn..<progress \<sigma> P' \<psi> (j + \<delta>)] (buf\<psi> @ ys)" (is "?P [?pIn..<?p\<psi>'] (buf\<psi> @ ys)")
      unfolding list_all2_append2
    proof (intro exI)
      let ?p\<psi> = "progress \<sigma> P \<psi> j"
      show "[?pIn..<?p\<psi>'] = [?pIn..<?p\<psi>] @ [?p\<psi>..<?p\<psi>'] \<and>
          length [?pIn..<?p\<psi>] = length buf\<psi> \<and> length [?p\<psi>..<?p\<psi>'] = length ys \<and>
          ?P [?pIn..<?p\<psi>] buf\<psi> \<and> ?P [?p\<psi>..<?p\<psi>'] ys"
        using wf ys by (auto simp: buf_eq progress_Sincep upt_add_eq_append' progress_mono_gen[OF _ bounded rm]
            dest: list_all2_lengthD)
    qed
    show "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?pOut..<j + \<delta>] (ts @ ?nts)"
      unfolding list_all2_append2
    proof (intro exI)
      have "?pOut \<le> j"
        by (rule progress_le_gen[OF bounded(1)])
      then show "[?pOut..<j + \<delta>] = [?pOut..<j] @ [j..<j + \<delta>] \<and>
          length [?pOut..<j] = length ts \<and> length [j..<j + \<delta>] = length ?nts \<and>
          list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [?pOut..<j] ts \<and> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [j..<j + \<delta>] ?nts"
        using wf by (auto simp add: buf_eq list.rel_map list.rel_refl simp flip: upt_add_eq_append'
              dest: list_all2_lengthD)
    qed
    show "?pOut = (if skew then Suc ?pIn else ?pIn)"
      using wf by (simp add: buf_eq)
  qed
qed

lemma (in msaux) wf_since_aux_update1:
  assumes wf: "wf_since_aux \<sigma> V R args \<phi> \<psi> aux pIn pOut"
    and t_eq: "t = \<tau> \<sigma> pOut"
    and rel1: "qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) pOut \<phi>) rel1"
    and args_n: "args_n args = n"
    and args_L: "args_L args = fv \<phi>"
    and safe: "fv \<phi> \<subseteq> fv \<psi>"
  shows "wf_since_aux \<sigma> V R args \<phi> \<psi> (join_msaux args rel1 (add_new_ts_msaux args t aux)) pIn (Suc pOut)"
  using wf unfolding t_eq wf_since_aux_def
  apply (clarsimp split del: if_split)
  subgoal for auxlist
    apply (rule exI[where x="map (\<lambda>(t', rel). (t', join rel (args_pos args) rel1)) (filter (\<lambda>(t', rel). memR (args_ivl args) (\<tau> \<sigma> pOut - t')) auxlist)"])
    apply (intro conjI)
    subgoal
      using rel1 by (auto simp add: args_n args_L qtable_def
        intro!: valid_join_msaux valid_add_new_ts_msaux)
    subgoal
      by (simp add: sorted_wrt_map sorted_wrt_filter split_beta)
    subgoal
      apply (clarsimp simp add: args_n args_L)
      subgoal for a b
        apply (drule spec2[of _ a b])
        apply clarify
        apply (erule qtable_join[OF _ rel1])
        using safe apply blast
        using safe apply blast
          apply simp
         apply (simp add: sat_since_point_def sat_the_restrict safe; safe)
           apply (meson diff_le_self order_trans greaterThanAtMost_iff)
          apply (meson greaterThanAtMost_iff less_le_trans order_refl)
         apply (metis greaterThanAtMost_iff Suc_pred bot_nat_0.extremum_uniqueI le_antisym not_le not_less_eq_eq)
        apply (simp add: sat_since_point_def sat_the_restrict safe; safe)
          apply (meson diff_le_self order_trans greaterThanAtMost_iff)
         apply (meson greaterThanAtMost_iff less_le_trans order_refl)
        apply (metis greaterThanAtMost_iff Suc_pred bot_nat_0.extremum_uniqueI le_antisym not_le not_less_eq_eq)
        done
      done
    subgoal
      by (clarsimp simp add: split_beta image_iff)
        (meson memR_antimono \<tau>_mono diff_le_mono diff_le_self)
    done
  done

lemma sat_since_point_Suc: "sat_since_point pos \<sigma> V \<phi> \<psi> (Suc i) i (\<tau> \<sigma> i) x =
    (sat_since_point pos \<sigma> V \<phi> \<psi> i i (\<tau> \<sigma> i) x \<or> Formula.sat \<sigma> V x i \<psi>)"
  unfolding sat_since_point_def
  apply auto
  using less_antisym apply blast
  by (meson less_Suc_eq)

lemma sat_since_point_Suc': "t < \<tau> \<sigma> i \<Longrightarrow>
    sat_since_point pos \<sigma> V \<phi> \<psi> (Suc i) i t x = sat_since_point pos \<sigma> V \<phi> \<psi> i i t x"
  unfolding sat_since_point_def
  apply auto
  using less_\<tau>D apply blast
  by (metis less_Suc_eq)

lemma (in msaux) wf_since_aux_update2:
  assumes wf: "wf_since_aux \<sigma> V R args \<phi> \<psi> aux pIn pOut"
    and rel2: "qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) pIn \<psi>) rel2"
    and pOut_pIn: "pOut = Suc pIn"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_R: "args_R args = fv \<psi>"
    and safe: "fv \<phi> \<subseteq> fv \<psi>"
  shows "wf_since_aux \<sigma> V R args \<phi> \<psi> (add_new_table_msaux args rel2 aux) (Suc pIn) pOut"
  using wf unfolding pOut_pIn wf_since_aux_def
  apply clarsimp
  subgoal for auxlist
    apply (rule exI[where x="(case auxlist of
        [] => [(\<tau> \<sigma> pIn, rel2)]
      | ((t, y) # ts) \<Rightarrow> if t = \<tau> \<sigma> pIn then (t, y \<union> rel2) # ts else (\<tau> \<sigma> pIn, rel2) # auxlist)"])
    apply (intro conjI)
    subgoal
      using rel2 by (auto simp add: args_n args_R qtable_def
        intro!: valid_add_new_table_msaux)
    subgoal
      apply (clarsimp split: list.split if_split)
      apply (intro conjI impI; simp)
       apply (metis \<tau>_mono le_neq_implies_less less_imp_le_nat)
      by (metis order.strict_trans less_\<tau>D less_imp_not_less linorder_neqE_nat)
     apply (clarsimp simp only: args_ivl args_n)
    subgoal for t X
      apply (cases auxlist)
      subgoal
        apply simp
        apply (intro conjI, auto)
        apply (subst qtable_cong_strong[where Q'="\<lambda>v. Formula.sat \<sigma> V (map the v) pIn \<psi>", OF refl])
         apply (simp add: sat_since_point_def)
         apply (metis diff_self_eq_0 greaterThanAtMost_iff lessI less_antisym memR_zero not_le)
        by (rule rel2)
      apply clarsimp
      subgoal for a b auxlist'
        apply (cases "a = \<tau> \<sigma> pIn")
         apply clarsimp
         apply (elim disjE)
          apply clarsimp
          apply (intro conjI)
           apply (metis lessI)
          apply (rule qtable_union[where ?Q1.0="\<lambda>x. sat_since_point (args_pos args) \<sigma>
                  V \<phi> \<psi> pIn pIn (\<tau> \<sigma> pIn)
                  (map the x)", OF _ rel2])
           apply simp
          apply (rule sat_since_point_Suc)
         apply (drule spec2)
         apply (drule conjunct2)
         apply (drule (1) mp)
         apply (elim conjE, intro conjI)
           apply (metis less_Suc_eq)
          apply assumption
         apply (erule qtable_cong[OF _ refl])
         apply (auto simp: sat_since_point_Suc')[]
        apply clarsimp
        apply (elim disjE)
          apply clarsimp
          apply (intro conjI, metis lessI)
          apply (rule qtable_cong[OF rel2 refl])
          apply (metis diff_self_eq_0 fst_conv less_\<tau>D less_imp_not_less memR_zero sat_since_point_Suc sat_since_point_def)
         apply (drule spec2)
         apply (drule conjunct1[of "_ \<longrightarrow> _"])
         apply (drule (1) mp)
         apply (elim conjE, intro conjI)
           apply (metis less_Suc_eq)
          apply simp
        apply simp
        apply (erule qtable_cong[OF _ refl])
         apply (rule sat_since_point_Suc'[symmetric])
        apply (meson less_\<tau>D less_imp_not_less linorder_neqE_nat)
        apply (frule spec2)
         apply (drule conjunct2[of "_ \<longrightarrow> _"])
         apply (drule (1) mp)
         apply (elim conjE, intro conjI)
           apply (metis less_Suc_eq)
          apply assumption
        apply (erule qtable_cong[OF _ refl])
        apply (rule sat_since_point_Suc'[symmetric])
        by (metis fst_conv less_\<tau>D less_imp_not_less linorder_neqE_nat)
      done
    apply clarsimp
    subgoal for i
      apply (cases "i = pIn")
       apply (auto split: list.split)[]
      apply (subgoal_tac "i < pIn")
       apply (drule spec[of "\<lambda>i. _ i \<longrightarrow> _ i"])
       apply (drule (1) mp)+
       apply (auto split: list.split)
       apply blast
      apply blast
      done
    done
  done

lemma sat_Sincep_alt: "pIn = Suc i \<or> \<not> memL I (\<tau> \<sigma> i - \<tau> \<sigma> pIn) \<Longrightarrow>
  Formula.sat \<sigma> V x i (Sincep pos \<phi> I \<psi>) \<longleftrightarrow>
  (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat_since_point pos \<sigma> V \<phi> \<psi> pIn i (\<tau> \<sigma> j) x)"
  unfolding Sincep_def sat_since_point_def
  apply (auto simp add: less_Suc_eq_le)
  apply blast
      apply blast
     apply (metis (no_types, lifting) diff_le_mono2 less_\<tau>D memL_mono not_le)
    apply (metis (no_types, lifting) \<tau>_mono diff_is_0_eq dual_order.strict_trans le_eq_less_or_eq not_le_imp_less)
   apply (metis (no_types, lifting) diff_le_mono2 less_\<tau>D memL_mono not_le)
  by (metis (no_types, lifting) \<tau>_mono diff_is_0_eq dual_order.strict_trans le_eq_less_or_eq linear)

lemma (in msaux) wf_since_aux_result':
  assumes valid_msaux: 
    "pIn \<le> Suc pOut"
    "sorted_wrt (\<lambda>x y. fst x > fst y) auxlist"
      "\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow> (\<exists>i<pIn. \<tau> \<sigma> i = t) \<and> memR (args_ivl args) (\<tau> \<sigma> (Suc pOut-1) - t)
      \<and> qtable (args_n args) (fv \<psi>) (mem_restr R)
          (\<lambda>x. sat_since_point (args_pos args) \<sigma> V \<phi> \<psi> pIn (Suc pOut-1) t (map the x)) X"
      "\<forall>i<pIn. memR (args_ivl args) (\<tau> \<sigma> (Suc pOut-1) - \<tau> \<sigma> i) \<longrightarrow> (\<exists>X. (\<tau> \<sigma> i, X) \<in> set auxlist)"
      "cur = (if Suc pOut = 0 then 0 else \<tau> \<sigma> (Suc pOut-1))"
    and subs: "fv \<phi> \<subseteq> fv \<psi>"
    and complete: "pIn = Suc pOut \<or> \<not> memL I (\<tau> \<sigma> pOut - \<tau> \<sigma> pIn)"
    and args_ivl: "args_ivl args = I"
    and agg_n: "agg_n args = n'"
    and args_n: "args_n args = n"
    and args_pos: "args_pos args = pos"
  shows "qtable n (fv (Sincep pos \<phi> I \<psi>)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) pOut (Sincep pos \<phi> I \<psi>)) (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
  using valid_msaux(1-4) subs using valid_msaux(5)
  apply (clarsimp simp add: foldr_union)
    apply (rule qtableI)
    subgoal
      apply (auto simp add: args_n table_def Sincep_def dest!: qtable_wf_tupleD) by (metis Un_absorb1 qtable_wf_tupleD)
    subgoal for x
      apply clarsimp
      subgoal for a b
        apply (drule spec2[of _ a b])
        apply (clarsimp simp add: sat_Sincep_alt[OF complete] args_ivl args_n args_pos)
        by (meson Suc_leI Suc_le_mono le_trans qtable_def)
      done
    subgoal for x
      apply (clarsimp simp add: sat_Sincep_alt[OF complete] args_ivl args_n args_pos)
      subgoal for j
        apply (erule allE[of "\<lambda>i. i < pIn \<longrightarrow> _ i" j])
        apply (erule impE)
         apply (metis complete less_Suc_eq_le less_\<tau>D less_imp_not_less linorder_neqE_nat sat_since_point_def)
        apply(auto simp add: fv_sinceP)
        by (metis (no_types, lifting) Un_commute qtable_def sup.orderE)
      done
    done

lemma (in msaux) wf_since_aux_result:
  assumes wf: "wf_since_aux \<sigma> V R args \<phi> \<psi> aux pIn (Suc pOut)"
    and complete: "pIn = Suc pOut \<or> \<not> memL I (\<tau> \<sigma> pOut - \<tau> \<sigma> pIn)"
    and args_ivl: "args_ivl args = I"
    and agg_n: "agg_n args = n'"
    and args_n: "args_n args = n"
    and args_pos: "args_pos args = pos"
    and subs: "fv \<phi> \<subseteq> fv \<psi>"
    and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
  shows "qtable n' (fv (packagg args (Sincep pos \<phi> I \<psi>))) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) pOut (packagg args (Sincep pos \<phi> I \<psi>))) (result_msaux args aux)"
proof -
  obtain cur auxlist where *:
    "pIn \<le> Suc pOut"
    "sorted_wrt (\<lambda>x y. fst x > fst y) auxlist"
      "\<forall>t X. (t, X) \<in> set auxlist \<longrightarrow> (\<exists>i<pIn. \<tau> \<sigma> i = t) \<and> memR (args_ivl args) (\<tau> \<sigma> (Suc pOut-1) - t)
      \<and> qtable (args_n args) (fv \<psi>) (mem_restr R)
          (\<lambda>x. sat_since_point (args_pos args) \<sigma> V \<phi> \<psi> pIn (Suc pOut-1) t (map the x)) X"
      "\<forall>i<pIn. memR (args_ivl args) (\<tau> \<sigma> (Suc pOut-1) - \<tau> \<sigma> i) \<longrightarrow> (\<exists>X. (\<tau> \<sigma> i, X) \<in> set auxlist)"
      "cur = (if Suc pOut = 0 then 0 else \<tau> \<sigma> (Suc pOut-1))" and
    valid_aggargs: "valid_aggargs (args_n args) (fv \<psi>) (args_agg args)" and
    valid_ms: "valid_msaux args cur aux auxlist"
    using wf unfolding wf_since_aux_def by auto
  have valid_aggargs': "valid_aggargs (args_n args) (fv (Sincep pos \<phi> I \<psi>)) (args_agg args)"
    using valid_aggargs subs by(auto simp: Sincep_def sup.absorb_iff2)
  have **: "qtable (args_n args) (fv (Sincep pos \<phi> I \<psi>)) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) pOut (Sincep pos \<phi> I \<psi>)) (foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, memL (args_ivl args) (cur - t)] {})"
    using wf_since_aux_result'[OF * subs complete args_ivl agg_n args_n args_pos] args_n by auto
  show ?thesis using qtable_eval_args_agg[OF ** mr valid_aggargs'] valid_result_msaux[OF valid_ms] agg_n
    by auto
qed 

lemma (in maux) eval_since_gen:
  assumes pre:
      "list_all2 (\<lambda>i. qtable n' (Formula.fv (packagg args (Sincep pos \<phi> I \<psi>))) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (Sincep pos \<phi> I \<psi>))))
        [start..<pOut] (rev zs)" (is "?A pOut (rev zs)")
      "wf_mbuf2S \<sigma> P V j n R \<phi> I \<psi> buf pIn pOut" (is "?B buf pIn pOut")
      "wf_since_aux \<sigma> V R args \<phi> \<psi> aux pIn pOut" (is "?C aux pIn pOut")
      "pIn \<le> progress \<sigma> P \<phi> j" "pIn \<le> progress \<sigma> P \<psi> j"
      "pOut \<le> progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
      "start \<le> pOut"
      "(zs', buf', aux') = eval_since args zs buf aux"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P"
    and fvi_subset: "fv \<phi> \<subseteq> fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>"
    and args_R: "args_R args = Formula.fv \<psi>"
    and args_pos: "args_pos args = pos"
    and agg_n: "agg_n args = n'"
    and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
  shows
      "?A (progress \<sigma> P (Sincep pos \<phi> I \<psi>) j) zs' \<and>
      wf_mbuf2S \<sigma> P V j n R \<phi> I \<psi> buf' (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) (progress \<sigma> P (Sincep pos \<phi> I \<psi>) j) \<and>
      ?C aux' (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) (progress \<sigma> P (Sincep pos \<phi> I \<psi>) j)"
  using pre
proof (induction zs buf aux arbitrary: pIn pOut zs' buf' aux' taking: args rule: eval_since.induct)
  case (1 zs x xs t ts skew aux)
  note wf_result = "1.prems"(1)
  note wf_buf = "1.prems"(2)
  note wf_aux = "1.prems"(3)
  note leqs = "1.prems"(4-7)
  note result_eq = "1.prems"(8)
  have pIn_eq: "pIn = progress \<sigma> P \<psi> j" and \<psi>_before_\<phi>: "progress \<sigma> P \<psi> j \<le> progress \<sigma> P \<phi> j"
    using wf_buf leqs by (auto dest: list_all2_lengthD)
  show ?case proof (cases "skew \<or> memL (args_ivl args) 0")
    case True
    then have eqs: "zs' = rev zs" "buf' = (x # xs, [], t # ts, skew)" "aux' = aux"
      using result_eq by simp_all
    have pOut_eq: "pOut = progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
      using wf_buf leqs True
      by (auto simp add: progress_Sincep args_ivl)
    show ?thesis
      using wf_result wf_buf wf_aux \<psi>_before_\<phi>
      by (simp add: eqs pIn_eq pOut_eq split: if_splits)
  next
    case False
    then have eqs: "zs' = rev (result_msaux args aux' # zs)" "buf' = (xs, [], ts, True)"
        "aux' = join_msaux args x (add_new_ts_msaux args t aux)"
      using result_eq by (simp_all add: Let_def)
    have pOut_eq: "Suc pOut = progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
      using wf_buf leqs False
      by (auto simp add: progress_Sincep args_ivl list_all2_Cons2 upt_eq_Cons_conv)
    have C: "?C aux' pIn (Suc pOut)"
      unfolding eqs using wf_buf
      by (intro wf_since_aux_update1[OF wf_aux _ _ args_n args_L fvi_subset])
        (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
    then have "qtable n' (fv (packagg args (Sincep pos \<phi> I \<psi>))) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) pOut (packagg args (Sincep pos \<phi> I \<psi>)))
        (result_msaux args aux')"
      using wf_buf False
      by (intro wf_since_aux_result[OF C _ args_ivl agg_n args_n args_pos fvi_subset mr]) (auto simp:args_ivl)
    then have "?A (Suc pOut) zs'"
      unfolding eqs using wf_result leqs
      by (simp add: list_all2_appendI)
    moreover have "?B buf' pIn (Suc pOut)"
      unfolding eqs using wf_buf False
      by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
    moreover note C
    ultimately show ?thesis
      using \<psi>_before_\<phi>
      by (simp add: eqs pIn_eq pOut_eq split: if_splits)
  qed
next
  case (2 zs xs y ys ts aux)
  note wf_result = "2.prems"(1)
  note wf_buf = "2.prems"(2)
  note wf_aux = "2.prems"(3)
  note leqs = "2.prems"(4-7)
  note result_eq = "2.prems"(8)
  let ?arg_aux = "add_new_table_msaux args y aux"
  show ?case proof (rule "2.IH")
    show "(zs', buf', aux') = eval_since args zs (xs, ys, ts, False) ?arg_aux"
      using result_eq by (simp add: Let_def)
    show "?A pOut (rev zs)" by fact
    show "?B (xs, ys, ts, False) (Suc pIn) pOut"
      using wf_buf by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
    show "?C ?arg_aux (Suc pIn) pOut"
      using wf_buf
      by (intro wf_since_aux_update2[OF wf_aux _ _ args_ivl args_n args_R fvi_subset])
        (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
    show "Suc pIn \<le> progress \<sigma> P \<phi> j"
      using wf_buf leqs by (simp add: progress_Sincep)
    show "Suc pIn \<le> progress \<sigma> P \<psi> j"
      using wf_buf by (simp add: list_all2_Cons2 upt_eq_Cons_conv)
  qed fact+
next
  case (3 zs x xs y ys t ts aux)
  note wf_result = "3.prems"(1)
  note wf_buf = "3.prems"(2)
  note wf_aux = "3.prems"(3)
  note leqs = "3.prems"(4-7)
  note result_eq = "3.prems"(8)
  let ?arg_aux = "add_new_table_msaux args y (join_msaux args x (add_new_ts_msaux args t aux))"
  show ?case proof (rule "3.IH"[OF refl])
    show s: "?C ?arg_aux (Suc pIn) (Suc pOut)"
      using wf_buf
      by (intro wf_since_aux_update2[OF _ _ _ args_ivl args_n args_R fvi_subset]
          wf_since_aux_update1[OF wf_aux _ _ args_n args_L fvi_subset])
        (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
    then have "qtable n' (fv (packagg args (Sincep pos \<phi> I \<psi>))) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) pOut (packagg args (Sincep pos \<phi> I \<psi>)))
        (result_msaux args ?arg_aux)"
      using wf_buf
      by (intro wf_since_aux_result[OF s _ args_ivl agg_n args_n args_pos fvi_subset mr])
        (auto simp add: args_ivl)
    then show "?A (Suc pOut) (rev (result_msaux args ?arg_aux # zs))"
      using wf_result leqs
      by (simp add: list_all2_appendI)
    show "?B (xs, ys, ts, False) (Suc pIn) (Suc pOut)"
      using wf_buf
      by (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
    show "Suc pIn \<le> progress \<sigma> P \<phi> j"
      using wf_buf by (simp add: list_all2_Cons2 upt_eq_Cons_conv)
    moreover show "Suc pIn \<le> progress \<sigma> P \<psi> j"
      using wf_buf by (simp add: list_all2_Cons2 upt_eq_Cons_conv)
    ultimately show "Suc pOut \<le> progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
      using wf_buf by (simp add: progress_Sincep)
    show "start \<le> Suc pOut" using leqs by simp
    show "(zs', buf', aux') = eval_since args (result_msaux args ?arg_aux # zs)
         (xs, ys, ts, False) ?arg_aux"
      using result_eq by (simp add: Let_def)
  qed
next
  case ("4_1" zs vb aux)
  then have "pIn = min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
    by (cases vb) auto
  moreover have "pOut = progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
    using "4_1" by (cases vb) (auto simp add: progress_Sincep)
  ultimately show ?case
    using "4_1" by simp
next
  case ("4_2" zs v vc aux)
  then show ?case by (auto simp add: progress_Sincep)
next
  case ("4_3" zs vd ve va aux)
  then show ?case by (auto simp add: progress_Sincep)
next
  case ("4_4" zs v vd ve aux)
  then have "pIn = min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
    apply simp
    by (metis bounded diff_diff_cancel length_upt min.absorb2 min.bounded_iff progress_le_gen upt_eq_Nil_conv)
  moreover have "pOut = progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
    using "4_4"
    apply (simp add: progress_Sincep)
    by (smt (z3) calculation list.rel_distinct(1) min_def upt_eq_Nil_conv)
  ultimately show ?case
    using "4_4" by (simp only: eval_since.simps prod.inject)
next
  case ("4_5" zs v ve aux)
  then have "pIn = min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
    by (simp) (metis le_antisym le_zero_eq min.absorb2)
  moreover have "pOut = progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
    using "4_5"
    apply (simp add: progress_Sincep)
    by (smt (z3) bot_nat_0.extremum_uniqueI bounded dual_order.trans min.commute min_def pred_mapping_mono_strong progress_le_gen)
  ultimately show ?case
    using "4_5" by (simp only: eval_since.simps prod.inject)
next
  case ("4_6" zs v vb aux)
  then have "pIn = min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)"
    apply simp
    by (metis bounded diff_diff_cancel diff_is_0_eq dual_order.refl dual_order.trans min.commute min_def progress_le_gen)
  moreover have "pOut = progress \<sigma> P (Sincep pos \<phi> I \<psi>) j"
    using "4_6"
    apply (simp add: progress_Sincep)
    by (smt (z3) bot_nat_0.extremum_uniqueI bounded dual_order.trans min.commute min_def pred_mapping_mono_strong progress_le_gen)
  ultimately show ?case
    using "4_6" by (simp only: eval_since.simps prod.inject)
qed

lemma (in maux) eval_since:
  assumes
    eq: "(zs, buf', aux') = eval_since args [] (mbuf2S_add xs ys (map (\<tau> \<sigma>) [j..<j + \<delta>]) buf) aux"
    and pre:
      "wf_mbuf2S \<sigma> P V j n R \<phi> I \<psi> buf (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) (progress \<sigma> P (Sincep pos \<phi> I \<psi>) j)"
        (is "?wf_buf P j buf")
      "wf_since_aux \<sigma> V R args \<phi> \<psi> aux (min (progress \<sigma> P \<phi> j) (progress \<sigma> P \<psi> j)) (progress \<sigma> P (Sincep pos \<phi> I \<psi>) j)"
        (is "?wf_aux P j aux")
    and xs: "list_all2 (\<lambda>i. qtable n (Formula.fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>))
      [progress \<sigma> P \<phi> j..<progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    and ys: "list_all2 (\<lambda>i. qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>))
      [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> (j + \<delta>)] ys"
    and bounded: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'"
    and rm: "rel_mapping (\<le>) P P'"
    and fvi_subset: "fv \<phi> \<subseteq> fv \<psi>"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>"
    and args_R: "args_R args = Formula.fv \<psi>"
    and args_pos: "args_pos args = pos"
    and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')" 
    and agg_n: "agg_n args = n'"
  shows
      "list_all2 (\<lambda>i. qtable n' (Formula.fv (packagg args (Sincep pos \<phi> I \<psi>))) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (Sincep pos \<phi> I \<psi>))))
        [progress \<sigma> P (Sincep pos \<phi> I \<psi>) j..<progress \<sigma> P' (Sincep pos \<phi> I \<psi>) (j + \<delta>)] zs \<and>
      ?wf_buf P' (j + \<delta>) buf' \<and>
      ?wf_aux P' (j + \<delta>) aux'"
  apply (rule eval_since_gen[OF _ _ pre(2)])
  apply simp
              apply (rule wf_mbuf2S_add[OF pre(1) bounded rm xs ys])
             apply (simp add: min.coboundedI1 progress_mono_gen[OF _ bounded rm])
            apply (simp add: min.coboundedI2 progress_mono_gen[OF _ bounded rm])
           apply (simp add: progress_mono_gen[OF _ bounded rm])
          apply simp
  by fact+

(*<*)
end
(*>*)