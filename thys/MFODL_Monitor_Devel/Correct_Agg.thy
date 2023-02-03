(*<*)
theory Correct_Agg
  imports
    Monitor 
    Progress
begin
(*>*)


subsection \<open> Lift envs \<close>

definition lift_envs' :: "nat \<Rightarrow> event_data list set \<Rightarrow> event_data list set" where
  "lift_envs' b R = (\<lambda>(xs,ys). xs @ ys) ` ({xs. length xs = b} \<times> R)"

lemma mem_restr_lift_envs'_append[simp]:
  "length xs = b \<Longrightarrow> mem_restr (lift_envs' b R) (xs @ ys) = mem_restr R ys"
  unfolding mem_restr_def lift_envs'_def
  by (auto simp: list_all2_append list.rel_map intro!: exI[where x="map the xs"] list.rel_refl)

lemma mem_restr_lift_envs'_zero[simp]: "mem_restr (lift_envs' 0 R) = mem_restr R"
  using mem_restr_lift_envs'_append[of "[]" 0]
  by auto

lemma mem_restr_dropI: "mem_restr (lift_envs' b R) xs \<Longrightarrow> mem_restr R (drop b xs)"
  unfolding mem_restr_def lift_envs'_def
  by (auto simp: append_eq_conv_conj list_all2_append2)

lemma mem_restr_dropD:
  assumes "b \<le> length xs" and "mem_restr R (drop b xs)"
  shows "mem_restr (lift_envs' b R) xs"
proof -
  let ?R = "\<lambda>a b. a \<noteq> None \<longrightarrow> a = Some b"
  from assms(2) obtain v where "v \<in> R" and "list_all2 ?R (drop b xs) v"
    unfolding mem_restr_def ..
  show ?thesis unfolding mem_restr_def proof
    have "list_all2 ?R (take b xs) (map the (take b xs))"
      by (auto simp: list.rel_map intro!: list.rel_refl)
    moreover note \<open>list_all2 ?R (drop b xs) v\<close>
    ultimately have "list_all2 ?R (take b xs @ drop b xs) (map the (take b xs) @ v)"
      by (rule list_all2_appendI)
    then show "list_all2 ?R xs (map the (take b xs) @ v)" by simp
    show "map the (take b xs) @ v \<in> lift_envs' b R"
      unfolding lift_envs'_def using assms(1) \<open>v \<in> R\<close> by auto
  qed
qed


subsection \<open> Aggregators' qtable \<close>

definition "agg_n args = (case args_agg args of None \<Rightarrow> args_n args | Some aggargs \<Rightarrow> aggargs_n aggargs)"

definition "agg_tys args = (case args_agg args of None \<Rightarrow> []           | Some aggargs \<Rightarrow> aggargs_tys aggargs)"

lemma progress_packagg[simp]: "Progress.progress \<sigma> P (packagg args \<phi>) j = Progress.progress \<sigma> P \<phi> j"
  by (auto simp: packagg_def split: option.splits)

lemma qtable_eval_agg:
  assumes inner: "qtable (length tys + n) (Formula.fv \<phi>) (mem_restr (lift_envs' (length tys) R))
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) rel"
    and n: "\<forall>x\<in>Formula.fv (Formula.Agg y \<omega> tys f \<phi>). x < n"
    and fresh: "y + length tys \<notin> Formula.fv \<phi>"
    and b_fv: "{0..<length tys} \<subseteq> Formula.fv \<phi>"
    and f_fv: "Formula.fv_trm f \<subseteq> Formula.fv \<phi>"
    and g0: "g0 = (Formula.fv \<phi> \<subseteq> {0..<length tys})"
  shows "qtable n (Formula.fv (Formula.Agg y \<omega> tys f \<phi>)) (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)) (eval_agg n g0 y \<omega> tys f rel)"
    (is "qtable _ ?fv _ ?Q ?rel'")
proof -
  let ?b = "length tys"
  define M where "M = (\<lambda>v. {(x, ecard Zs) | x Zs.
      Zs = {zs. length zs = ?b \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and>
      Zs \<noteq> {}})"
  
  have f_fvi: "Formula.fvi_trm ?b f \<subseteq> Formula.fvi ?b \<phi>"
    using f_fv by (auto simp: fvi_trm_iff_fv_trm[where b= ?b] fvi_iff_fv[where b= ?b])
  show ?thesis proof (cases "g0 \<and> rel = empty_table")
    case True
    then have [simp]: "Formula.fvi ?b \<phi> = {}"
      by (auto simp: g0 fvi_iff_fv(1)[where b= ?b])
    then have [simp]: "Formula.fvi_trm ?b f = {}"
      using f_fvi by auto
    show ?thesis proof (rule qtableI)
      show "table n ?fv ?rel'" by (simp add: eval_agg_def True)
    next
      fix v
      assume "wf_tuple n ?fv v" "mem_restr R v"
      have "\<not> Formula.sat \<sigma> V (zs @ map the v) i \<phi>" if [simp]: "length zs = ?b" for zs
      proof -
        let ?zs = "map2 (\<lambda>z i. if i \<in> Formula.fv \<phi> then Some z else None) zs [0..<?b]"
        have "wf_tuple ?b {x \<in> fv \<phi>. x < ?b} ?zs"
          by (simp add: wf_tuple_def)
        then have "wf_tuple (?b + n) (Formula.fv \<phi>) (?zs @ v[y:=None])"
          using \<open>wf_tuple n ?fv v\<close> True
          by (auto simp: g0 intro!: wf_tuple_append wf_tuple_upd_None)
        then have "\<not> Formula.sat \<sigma> V (map the (?zs @ v[y:=None])) i \<phi>"
          using True \<open>mem_restr R v\<close>
          by (auto simp del: map_append dest!: in_qtableI[OF inner, rotated -1]
              intro!: mem_restr_upd_None)
        also have "Formula.sat \<sigma> V (map the (?zs @ v[y:=None])) i \<phi> \<longleftrightarrow> Formula.sat \<sigma> V (zs @ map the v) i \<phi>"
          using True by (auto simp: g0 nth_append intro!: sat_fv_cong)
        finally show ?thesis .
      qed
      then have M_empty: "M (map the v) = {}"
        unfolding M_def by blast
      show "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)"
        if "v \<in> eval_agg n g0 y \<omega> tys f rel"
        using M_empty True that n
        by (simp add: M_def eval_agg_def g0 singleton_table_def)
      have "v \<in> singleton_table n y (the (v ! y))" "length v = n"
        using \<open>wf_tuple n ?fv v\<close> unfolding wf_tuple_def singleton_table_def
        by (auto simp add: tabulate_alt map_nth
            intro!: trans[OF map_cong[where g="(!) v", simplified nth_map, OF refl], symmetric])
      then show "v \<in> eval_agg n g0 y \<omega> tys f rel"
        if "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)"
        using M_empty True that n
        by (simp add: M_def eval_agg_def g0)
    qed
  next
    case non_default_case: False
    have union_fv: "{0..<?b} \<union> (\<lambda>x. x + ?b) ` Formula.fvi ?b \<phi> = fv \<phi>"
      using b_fv
      by (auto simp: fvi_iff_fv(1)[where b= ?b] intro!: image_eqI[where b=x and x="x - ?b" for x])
    have b_n: "\<forall>x\<in>fv \<phi>. x < ?b + n"
    proof
      fix x assume "x \<in> fv \<phi>"
      show "x < ?b + n" proof (cases "x \<ge> ?b")
        case True
        with \<open>x \<in> fv \<phi>\<close> have "x - ?b \<in> ?fv"
          by (simp add: fvi_iff_fv(1)[where b= ?b])
        then show ?thesis using n f_fvi by (auto simp: Un_absorb2)
      qed simp
    qed

    define M' where "M' = (\<lambda>k. let group = Set.filter (\<lambda>x. drop ?b x = k) rel;
        images = meval_trm f ` group
      in (\<lambda>y. (y, ecard (Set.filter (\<lambda>x. meval_trm f x = y) group))) ` images)"
    have M'_M: "M' (drop ?b x) = M (map the (drop ?b x))" if "x \<in> rel" "mem_restr (lift_envs' ?b R) x" for x
    proof -
      from that have wf_x: "wf_tuple (?b + n) (fv \<phi>) x"
        by (auto elim!: in_qtableE[OF inner])
      then have wf_zs_x: "wf_tuple (?b + n) (fv \<phi>) (map Some zs @ drop ?b x)"
        if "length zs = ?b" for zs
        using that b_fv
        by (auto intro!: wf_tuple_append wf_tuple_map_Some wf_tuple_drop)
      have 1: "(length zs = ?b \<and> Formula.sat \<sigma> V (zs @ map the (drop ?b x)) i \<phi> \<and>
          Formula.eval_trm (zs @ map the (drop ?b x)) f = y) \<longleftrightarrow>
        (\<exists>a. a \<in> rel \<and> take ?b a = map Some zs \<and> drop ?b a = drop ?b x \<and> meval_trm f a = y)"
        (is "?A \<longleftrightarrow> (\<exists>a. ?B a)") for y zs
      proof (intro iffI conjI)
        assume ?A
        then have "?B (map Some zs @ drop (length zs) x)"
          using in_qtableI[OF inner wf_zs_x] \<open>mem_restr (lift_envs' ?b R) x\<close>
            meval_trm_eval_trm[OF wf_zs_x f_fv b_n]
          by (auto intro!: mem_restr_dropI)
        then show "\<exists>a. ?B a" ..
      next
        assume "\<exists>a. ?B a"
        then obtain a where "?B a" ..
        then have "a \<in> rel" and a_eq: "a = map Some zs @ drop ?b x"
          using append_take_drop_id[of ?b a] by auto
        then have "length a = ?b + n"
          using inner unfolding qtable_def table_def
          by (blast intro!: wf_tuple_length)
        then show "length zs = ?b"
          using wf_tuple_length[OF wf_x] unfolding a_eq by simp
        then have "mem_restr (lift_envs' ?b R) a"
          using \<open>mem_restr _ x\<close> unfolding a_eq by (auto intro!: mem_restr_dropI)
        then show "Formula.sat \<sigma> V (zs @ map the (drop ?b x)) i \<phi>"
          using in_qtableE[OF inner \<open>a \<in> rel\<close>]
          by (auto simp: a_eq sat_fv_cong[THEN iffD1, rotated -1])
        from \<open>?B a\<close> show "Formula.eval_trm (zs @ map the (drop ?b x)) f = y"
          using meval_trm_eval_trm[OF wf_zs_x f_fv b_n, OF \<open>length zs = ?b\<close>]
          unfolding a_eq by simp
      qed
      have 2: "map Some (map the (take ?b a)) = take ?b a" if "a \<in> rel" for a
        using that b_fv inner[THEN qtable_wf_tupleD]  
        unfolding table_def wf_tuple_def
        using list_eq_iff_nth_eq[of "map Some (map the (take ?b a))" "take ?b a"]
        by auto
      have 3: "ecard {zs. \<exists>a. a \<in> rel \<and> take ?b a = map Some zs \<and> drop ?b a = drop ?b x \<and> P a} =
        ecard {a. a \<in> rel \<and> drop ?b a = drop ?b x \<and> P a}" (is "ecard ?A = ecard ?B") for P
      proof -
        have "ecard ?A = ecard ((\<lambda>zs. map Some zs @ drop ?b x) ` ?A)"
          by (auto intro!: ecard_image[symmetric] inj_onI)
        also have "(\<lambda>zs. map Some zs @ drop ?b x) ` ?A = ?B"
          by (subst (1 2) eq_commute) (auto simp: image_iff, metis "2" append_take_drop_id)
        finally show ?thesis .
      qed
      show ?thesis
        unfolding M_def M'_def
        by (auto simp: non_default_case Let_def image_def Set.filter_def 1 3, metis "2")
    qed
    have drop_lift: "mem_restr (lift_envs' ?b R) x" if "x \<in> rel" "mem_restr R ((drop ?b x)[y:=z])" for x z
    proof -
      have "(drop ?b x)[y:=None] = (drop ?b x)[y:=drop ?b x ! y]" proof -
        from \<open>x \<in> rel\<close> have "drop ?b x ! y = None"
          using fresh n inner[THEN qtable_wf_tupleD]
          by (simp add: add.commute wf_tuple_def)
        then show ?thesis by simp
      qed
      then have "(drop ?b x)[y:=None] = drop ?b x" by simp
      moreover from \<open>x \<in> rel\<close> have "length x = ?b + n"
        using inner[THEN qtable_wf_tupleD]
        by (simp add: wf_tuple_def)
      moreover from that(2) have "mem_restr R ((drop ?b x)[y:=z, y:=None])"
        by (rule mem_restr_upd_None)
      ultimately show ?thesis
        by (auto intro!: mem_restr_dropD)
    qed

    {
      fix v
      assume "mem_restr R v"
      have "v \<in> (\<lambda>k. k[y:=Some (eval_agg_op \<omega> (M' k))]) ` drop ?b ` rel \<longleftrightarrow>
          v \<in> (\<lambda>k. k[y:=Some (eval_agg_op \<omega> (M (map the k)))]) ` drop ?b ` rel"
        (is "v \<in> ?A \<longleftrightarrow> v \<in> ?B")
      proof
        assume "v \<in> ?A"
        then obtain v' where *: "v' \<in> rel" "v = (drop ?b v')[y:=Some (eval_agg_op \<omega> (M' (drop ?b v')))]"
          by auto
        then have "M' (drop ?b v') = M (map the (drop ?b v'))"
          using \<open>mem_restr R v\<close> by (auto intro!: M'_M drop_lift)
        with * show "v \<in> ?B" by simp
      next
        assume "v \<in> ?B"
        then obtain v' where *: "v' \<in> rel" "v = (drop ?b v')[y:=Some (eval_agg_op \<omega> (M (map the (drop ?b v'))))]"
          by auto
        then have "M (map the (drop ?b v')) = M' (drop ?b v')"
          using \<open>mem_restr R v\<close> by (auto intro!: M'_M[symmetric] drop_lift)
        with * show "v \<in> ?A" by simp
      qed
      then have "v \<in> eval_agg n g0 y \<omega> tys f rel \<longleftrightarrow> v \<in> (\<lambda>k. k[y:=Some (eval_agg_op \<omega> (M (map the k)))]) ` drop ?b ` rel"
        by (simp add: non_default_case eval_agg_def M'_def Let_def)
    }
    note alt = this

    show ?thesis proof (rule qtableI)
      show "table n ?fv ?rel'"
        using inner[THEN qtable_wf_tupleD] n f_fvi
        by (auto simp: eval_agg_def non_default_case table_def wf_tuple_def Let_def nth_list_update
            fvi_iff_fv[where b= ?b] add.commute)
    next
      fix v
      assume "wf_tuple n ?fv v" "mem_restr R v"
      then have length_v: "length v = n" by (simp add: wf_tuple_def)

      show "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)"
        if "v \<in> eval_agg n g0 y \<omega> tys f rel"
      proof -
        from that obtain v' where "v' \<in> rel"
          "v = (drop ?b v')[y:=Some (eval_agg_op \<omega> (M (map the (drop ?b v'))))]"
          using alt[OF \<open>mem_restr R v\<close>] by blast
        then have length_v': "length v' = ?b + n"
          using inner[THEN qtable_wf_tupleD]
          by (simp add: wf_tuple_def)
        have "Formula.sat \<sigma> V (map the v') i \<phi>"
          using \<open>v' \<in> rel\<close> \<open>mem_restr R v\<close>
          by (auto simp: \<open>v = _\<close> elim!: in_qtableE[OF inner] intro!: drop_lift \<open>v' \<in> rel\<close>)
        then have "Formula.sat \<sigma> V (map the (take ?b v') @ map the v) i \<phi>"
        proof (rule sat_fv_cong[THEN iffD1, rotated], intro ballI)
          fix x
          assume "x \<in> fv \<phi>"
          then have "x \<noteq> y + ?b" using fresh by blast
          moreover have "x < length v'"
            using \<open>x \<in> fv \<phi>\<close> b_n by (simp add: length_v')
          ultimately show "map the v' ! x = (map the (take ?b v') @ map the v) ! x"
            by (auto simp: \<open>v = _\<close> nth_append)
        qed
        then have 1: "M (map the v) \<noteq> {}" by (force simp: M_def length_v')

        have "y < length (drop ?b v')" using n by (simp add: length_v')
        moreover have "Formula.sat \<sigma> V (zs @ map the v) i \<phi> \<longleftrightarrow>
          Formula.sat \<sigma> V (zs @ map the (drop ?b v')) i \<phi>" if "length zs = ?b" for zs
        proof (intro sat_fv_cong ballI)
          fix x
          assume "x \<in> fv \<phi>"
          then have "x \<noteq> y + ?b" using fresh by blast
          moreover have "x < length v'"
            using \<open>x \<in> fv \<phi>\<close> b_n by (simp add: length_v')
          ultimately show "(zs @ map the v) ! x = (zs @ map the (drop ?b v')) ! x"
            by (auto simp: \<open>v = _\<close> that nth_append)
        qed
        moreover have "Formula.eval_trm (zs @ map the v) f =
          Formula.eval_trm (zs @ map the (drop ?b v')) f" if "length zs = ?b" for zs
        proof (intro eval_trm_fv_cong ballI)
          fix x
          assume "x \<in> fv_trm f"
          then have "x \<noteq> y + ?b" using f_fv fresh by blast
          moreover have "x < length v'"
            using \<open>x \<in> fv_trm f\<close> f_fv b_n by (auto simp: length_v')
          ultimately show "(zs @ map the v) ! x = (zs @ map the (drop ?b v')) ! x"
            by (auto simp: \<open>v = _\<close> that nth_append)
        qed
        ultimately have "map the v ! y = eval_agg_op \<omega> (M (map the v))"
          by (simp add: M_def \<open>v = _\<close> conj_commute cong: conj_cong)
        with 1 show ?thesis by (auto simp: M_def)
      qed

      show "v \<in> eval_agg n g0 y \<omega> tys f rel"
        if sat_Agg: "Formula.sat \<sigma> V (map the v) i (Formula.Agg y \<omega> tys f \<phi>)"
      proof -
        obtain zs where "length zs = ?b" and "map Some zs @ v[y:=None] \<in> rel"
        proof (cases "fv \<phi> \<subseteq> {0..<?b}")
          case True
          with non_default_case have "rel \<noteq> empty_table" by (simp add: g0)
          then obtain x where "x \<in> rel" by auto
          have "(\<forall>i < n. (v[y:=None]) ! i = None)"
            using True \<open>wf_tuple n ?fv v\<close> f_fv
            by (fastforce simp: wf_tuple_def fvi_iff_fv[where b= ?b] fvi_trm_iff_fv_trm[where b= ?b])
          moreover have x: "(\<forall>i < n. drop ?b x ! i = None) \<and> length x = ?b + n"
            using True \<open>x \<in> rel\<close> inner[THEN qtable_wf_tupleD] f_fv
            by (auto simp: wf_tuple_def)
          ultimately have "v[y:=None] = drop ?b x"
            unfolding list_eq_iff_nth_eq by (auto simp: length_v)
          with \<open>x \<in> rel\<close> have "take ?b x @ v[y:=None] \<in> rel" by simp
          moreover have "map (Some \<circ> the) (take ?b x) = take ?b x"
            using True \<open>x \<in> rel\<close> inner[THEN qtable_wf_tupleD] b_fv
            by (subst map_cong[where g=id, OF refl]) (auto simp: wf_tuple_def in_set_conv_nth)
          ultimately have "map Some (map the (take ?b x)) @ v[y:=None] \<in> rel" by simp
          then show thesis using x[THEN conjunct2] by (fastforce intro!: that[rotated])
        next
          case False
          with sat_Agg obtain zs where "length zs = ?b" and "Formula.sat \<sigma> V (zs @ map the v) i \<phi>"
            by auto
          then have "Formula.sat \<sigma> V (zs @ map the (v[y:=None])) i \<phi>"
            using fresh
            by (auto simp: map_update not_less nth_append elim!: sat_fv_cong[THEN iffD1, rotated]
                intro!: nth_list_update_neq[symmetric])
          then have "map Some zs @ v[y:=None] \<in> rel"
            using b_fv f_fv fresh
            by (auto intro!: in_qtableI[OF inner] wf_tuple_append wf_tuple_map_Some
                wf_tuple_upd_None \<open>wf_tuple n ?fv v\<close> mem_restr_upd_None \<open>mem_restr R v\<close>
                simp: \<open>length zs = ?b\<close> set_eq_iff fvi_iff_fv[where b= ?b] fvi_trm_iff_fv_trm[where b= ?b])
              force+
          with that \<open>length zs = ?b\<close> show thesis by blast
        qed
        then have 1: "v[y:=None] \<in> drop ?b ` rel" by (intro image_eqI) auto

        have y_length: "y < length v" using n by (simp add: length_v)
        moreover have "Formula.sat \<sigma> V (zs @ map the (v[y:=None])) i \<phi> \<longleftrightarrow>
          Formula.sat \<sigma> V (zs @ map the v) i \<phi>" if "length zs = ?b" for zs
        proof (intro sat_fv_cong ballI)
          fix x
          assume "x \<in> fv \<phi>"
          then have "x \<noteq> y + ?b" using fresh by blast
          moreover have "x < ?b + length v"
            using \<open>x \<in> fv \<phi>\<close> b_n by (simp add: length_v)
          ultimately show "(zs @ map the (v[y:=None])) ! x = (zs @ map the v) ! x"
            by (auto simp: that nth_append)
        qed
        moreover have "Formula.eval_trm (zs @ map the (v[y:=None])) f =
          Formula.eval_trm (zs @ map the v) f" if "length zs = ?b" for zs
        proof (intro eval_trm_fv_cong ballI)
          fix x
          assume "x \<in> fv_trm f"
          then have "x \<noteq> y + ?b" using f_fv fresh by blast
          moreover have "x < ?b + length v"
            using \<open>x \<in> fv_trm f\<close> f_fv b_n by (auto simp: length_v)
          ultimately show "(zs @ map the (v[y:=None])) ! x = (zs @ map the v) ! x"
            by (auto simp: that nth_append)
        qed
        ultimately have "map the v ! y = eval_agg_op \<omega> (M (map the (v[y:=None])))"
          using sat_Agg by (simp add: M_def cong: conj_cong) (simp cong: rev_conj_cong)
        then have 2: "v ! y = Some (eval_agg_op \<omega> (M (map the (v[y:=None]))))"
          using \<open>wf_tuple n ?fv v\<close> y_length by (auto simp add: wf_tuple_def)
        show ?thesis
          unfolding alt[OF \<open>mem_restr R v\<close>]
          by (rule image_eqI[where x="v[y:=None]"]) 
            (use 1 2 in \<open>auto simp: y_length list_update_id2\<close>)
      qed
    qed
  qed
qed

lemma qtable_eval_args_agg:
  "qtable (agg_n args) (fv (packagg args \<psi>)) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) ne (packagg args \<psi>)) (eval_args_agg args rel)"
  if q: "qtable (args_n args) (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) ne \<psi>) rel"
    and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
    and valid_aggargs: "valid_aggargs (args_n args) (fv \<psi>) (args_agg args)"
proof (cases "args_agg args")
  case None
  have pack: "packagg args \<psi> = \<psi>"
    by (auto simp add: packagg_def None)
  have "mem_restr R' = mem_restr R"
    using mr mem_restr_lift_envs'_append[of "[]" 0]
    by (auto simp: agg_tys_def None)
  then show ?thesis
    using q
    unfolding pack
    by (auto simp: eval_args_agg_def agg_n_def None)
next
  case (Some aggargs)
  have n_def: "agg_n args = aggargs_n aggargs" "args_n args = length (aggargs_tys aggargs) + aggargs_n aggargs"
    using valid_aggargs
    by (auto simp: agg_n_def Some valid_aggargs_def)
  have x_in_colsD: "x + length (aggargs_tys aggargs) \<in> aggargs_cols aggargs \<Longrightarrow> x < aggargs_n aggargs" for x
    using valid_aggargs
    by (auto simp: valid_aggargs_def Some safe_aggargs_def)
  show ?thesis
    unfolding packagg_def Some eval_args_agg_def
    apply (auto simp del: sat.simps fvi.simps simp: eval_aggargs_def n_def)
    apply (rule qtable_eval_agg)
    using q valid_aggargs mr
    by (auto simp: n_def agg_tys_def Some valid_aggargs_def safe_aggargs_def
        fvi_iff_fv[where ?b="length (aggargs_tys aggargs)"] fvi_trm_iff_fv_trm[where ?b="length (aggargs_tys aggargs)"]
        dest!: x_in_colsD)
qed


(*<*)
end
(*>*)