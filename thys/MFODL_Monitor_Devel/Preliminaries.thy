(*<*)
theory Preliminaries
  imports 
    Main
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
begin
(*>*)


section \<open> Preliminary lemmas \<close>

unbundle lattice_syntax \<comment> \<open> enable notation \<close>


subsection \<open> Lists \<close>

lemma foldr_union: "foldr (\<union>) Xs {} = \<Union>(set Xs)"
  by (induction Xs) auto

lemma zip_map_el: "(i, x) \<in> set (zip xs (map f xs)) \<Longrightarrow> x = f i"
  by (metis fst_conv in_set_zip nth_map snd_conv)

lemma zip_P: "\<And>xs P. (\<forall>(i,x) \<in> set (zip [0..<length xs] xs). P x) = (\<forall>x \<in> set xs. P x)"
  by (metis case_prodD case_prodI2 diff_zero in_set_impl_in_set_zip2 length_upt set_zip_rightD)

lemma zip_idx: "\<And>xs P. \<forall>(i,x) \<in> set (zip [0..<length xs] xs). x = xs!i"
  by (metis (mono_tags, lifting) case_prodI2 map_nth zip_map_el)

lemma upt_append: "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> [a..<b] @ [b..<c] = [a..<c]"
  by (metis le_Suc_ex upt_add_eq_append)

lemma hd_app: "hd (xs @ ys) = (case xs of [] \<Rightarrow> hd ys | x # _ \<Rightarrow> x)"
  by (cases xs) auto

lemma list_update_id2: "xs ! i = z \<Longrightarrow> xs[i:=z] = xs"
  by (induction xs arbitrary: i) (auto split: nat.split)

lemma nth_list_update_alt: "xs[i := x] ! j = (if i < length xs \<and> i = j then x else xs ! j)"
  by auto

lemma nth_filter: "i < length (filter P xs) \<Longrightarrow>
  (\<And>i'. i' < length xs \<Longrightarrow> P (xs ! i') \<Longrightarrow> Q (xs ! i')) \<Longrightarrow> Q (filter P xs ! i)"
  by (metis (lifting) in_set_conv_nth set_filter mem_Collect_eq)

lemma nth_partition: "i < length xs \<Longrightarrow>
  (\<And>i'. i' < length (filter P xs) \<Longrightarrow> Q (filter P xs ! i')) \<Longrightarrow>
  (\<And>i'. i' < length (filter (Not \<circ> P) xs) \<Longrightarrow> Q (filter (Not \<circ> P) xs ! i')) \<Longrightarrow> Q (xs ! i)"
  by (metis (no_types, lifting) in_set_conv_nth set_filter mem_Collect_eq comp_apply)

lemma list_all2_upt_Cons: "P a x \<Longrightarrow> list_all2 P [Suc a..<b] xs \<Longrightarrow> Suc a \<le> b \<Longrightarrow>
  list_all2 P [a..<b] (x # xs)"
  by (simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all2_upt_append: "list_all2 P [a..<b] xs \<Longrightarrow> list_all2 P [b..<c] ys \<Longrightarrow>
  a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> list_all2 P [a..<c] (xs @ ys)"
  by (induction xs arbitrary: a) (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)

lemma list_all2_hdD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P i (hd xs)" "i < j"
  using assms unfolding list_all2_conv_all_nth
  by (auto simp: hd_conv_nth intro: zero_less_diff[THEN iffD1] dest!: spec[of _ 0])

lemma list_all2_lastD:
  assumes "list_all2 P [i..<j] xs" "xs \<noteq> []"
  shows "P (j - 1) (last xs)"
  using assms list_all2_hdD(2)[OF assms, THEN less_imp_add_positive] unfolding list_all2_conv_all_nth
  by (auto dest!: spec[of _ "length xs - 1"] simp: last_conv_nth Suc_le_eq)

lemma rel_mono_zip:
  assumes before: "list_all2 P1 x y"
  assumes impl: "(\<And>a b. (a, b) \<in> set (zip x y) \<Longrightarrow> P1 a b \<Longrightarrow> P2 a b)"
  shows "list_all2 P2 x y"
proof -
  have eq_len: "length x = length y"
    using before
    unfolding list_all2_iff
    by auto
  moreover have "\<And>a b. (a, b)\<in>set (zip x y) \<Longrightarrow> P2 a b"
  proof -
    fix a b
    assume "(a, b)\<in>set (zip x y)"
    then show "P2 a b"
      using before impl
      unfolding list_all2_iff
      by auto
  qed

  ultimately show ?thesis
    unfolding list_all2_iff
    by auto
qed

inductive list_all3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool" 
  for P :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool)" 
  where "list_all3 P [] [] []"
  | "P a1 a2 a3 \<Longrightarrow> list_all3 P q1 q2 q3 \<Longrightarrow> list_all3 P (a1 # q1) (a2 # q2) (a3 # q3)"

lemma list_all3_list_all2D: "list_all3 P xs ys zs \<Longrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  by (induct xs ys zs rule: list_all3.induct) auto

lemma list_all2_list_all3I: "length xs = length ys \<Longrightarrow> list_all2 (case_prod P) (zip xs ys) zs \<Longrightarrow>
  list_all3 P xs ys zs"
  by (induct xs ys arbitrary: zs rule: list_induct2)
    (auto simp: list_all2_Cons1 intro: list_all3.intros)

lemma list_all3_list_all2_eq: "list_all3 P xs ys zs \<longleftrightarrow>
  (length xs = length ys \<and> list_all2 (case_prod P) (zip xs ys) zs)"
  using list_all2_list_all3I list_all3_list_all2D by blast

lemma list_all3_mapD: "list_all3 P (map f xs) (map g ys) (map h zs) \<Longrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  by (induct "map f xs" "map g ys" "map h zs" arbitrary: xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_mapI: "list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs \<Longrightarrow>
  list_all3 P (map f xs) (map g ys) (map h zs)"
  by (induct xs ys zs rule: list_all3.induct)
    (auto intro: list_all3.intros)

lemma list_all3_map_iff: "list_all3 P (map f xs) (map g ys) (map h zs) \<longleftrightarrow>
  list_all3 (\<lambda>x y z. P (f x) (g y) (h z)) xs ys zs"
  using list_all3_mapD list_all3_mapI by blast

lemmas list_all3_map =
  list_all3_map_iff[where g=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and h=id, unfolded list.map_id id_apply]
  list_all3_map_iff[where f=id and g=id, unfolded list.map_id id_apply]

lemma list_all3_conv_all_nth:
  "list_all3 P xs ys zs =
  (length xs = length ys \<and> length ys = length zs \<and> (\<forall>i < length xs. P (xs!i) (ys!i) (zs!i)))"
  by (auto simp add: list_all3_list_all2_eq list_all2_conv_all_nth)

lemma list_all3_refl [intro?]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x x x) \<Longrightarrow> list_all3 P xs xs xs"
  by (simp add: list_all3_conv_all_nth)

lemma list_all3_list_all2_conv: "list_all3 R xs xs ys = list_all2 (\<lambda>x. R x x) xs ys"
  by (auto simp: list_all3_conv_all_nth list_all2_conv_all_nth)

lemma list_all3_Nil[simp]:
  "list_all3 P xs ys [] \<longleftrightarrow> xs = [] \<and> ys = []"
  "list_all3 P xs [] zs \<longleftrightarrow> xs = [] \<and> zs = []"
  "list_all3 P [] ys zs \<longleftrightarrow> ys = [] \<and> zs = []"
  unfolding list_all3_conv_all_nth by auto

lemma list_all3_Cons:
  "list_all3 P xs ys (z # zs) \<longleftrightarrow> (\<exists>x xs' y ys'. xs = x # xs' \<and> ys = y # ys' \<and> P x y z \<and> list_all3 P xs' ys' zs)"
  "list_all3 P xs (y # ys) zs \<longleftrightarrow> (\<exists>x xs' z zs'. xs = x # xs' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs' ys zs')"
  "list_all3 P (x # xs) ys zs \<longleftrightarrow> (\<exists>y ys' z zs'. ys = y # ys' \<and> zs = z # zs' \<and> P x y z \<and> list_all3 P xs ys' zs')"
  unfolding list_all3_conv_all_nth
  by (auto simp: length_Suc_conv Suc_length_conv nth_Cons split: nat.splits)

lemma list_all3_mono_strong: "list_all3 P xs ys zs \<Longrightarrow>
  (\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> P x y z \<Longrightarrow> Q x y z) \<Longrightarrow>
  list_all3 Q xs ys zs"
  by (induct xs ys zs rule: list_all3.induct) (auto intro: list_all3.intros)

lemma list_all3_list_all2I: "list_all3 (\<lambda>x y z. Q x z) xs ys zs \<Longrightarrow> list_all2 Q xs zs"
  by (induct xs ys zs rule: list_all3.induct) auto


subsection \<open> Logic and sets \<close>

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma image_eqD: "f ` A = B \<Longrightarrow> \<forall>x\<in>A. f x \<in> B"
  by blast

lemma set_eqI2: "(\<And>x. x\<in>A \<Longrightarrow> x\<in>B) \<Longrightarrow> (\<And>x. x\<in>B \<Longrightarrow> x\<in>A) \<Longrightarrow> A = B"
  by auto

lemma eq_singleton_iff: "A = {a} \<longleftrightarrow> a \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> x = a)"
  by auto

lemma sub_pair_unfold: "A \<subseteq> {{}, X} \<longleftrightarrow> A = {} \<or> A = {{}} \<or> A = {X} \<or> A = {{},X}"
  by blast


subsection \<open> Finiteness and cardinality \<close>

lemma finite_Union_image_Collect: 
  "finite A \<Longrightarrow> (\<And>X. X \<in> A \<Longrightarrow> finite (f X)) \<Longrightarrow> finite (\<Union>{f X|X. X \<in> A})"
  by (rule finite_Union, auto)

lemma finite_image_Collect: "finite A \<Longrightarrow> finite {f k |k. k \<in> A}"
  apply (subst Collect_mem_eq[where A=A, symmetric])
  by (rule finite_image_set) simp

lemma finite_bounded_\<I>: "bounded I \<Longrightarrow> finite {i |i. memL I i \<and> memR I i}"
  by (transfer, clarsimp simp: upclosed_def downclosed_def)
    (metis (lifting) infinite_nat_iff_unbounded_le mem_Collect_eq)

lemma finite_bounded_\<I>2: "bounded I \<Longrightarrow> finite {f i |i. memL I (f i) \<and> memR I (f i)}"
  apply (transfer, clarsimp simp: upclosed_def downclosed_def)
  by (smt (verit, best) infinite_nat_iff_unbounded_le mem_Collect_eq)

lemma finite_vimage_set: "finite {x. P x} \<Longrightarrow> inj f \<Longrightarrow> finite {x. P (f x)}"
  using finite_vimageI
  unfolding vimage_def by force

lemma finite_vimage_\<tau>_nat: "finite {k. \<tau> \<sigma> k - c = n}"
proof (transfer, clarsimp)
  fix \<sigma> :: "('a \<times> nat) stream" 
    and c :: nat 
    and n :: nat
  assume h1: "ssorted (smap snd \<sigma>)"
    and h2: "sincreasing (smap snd \<sigma>)"
  have "\<exists>k. n < snd (\<sigma> !! k) - c"
    using h2 sincreasing_grD less_diff_conv 
    by (metis smap_alt)
  moreover have "\<forall>i j. i \<le> j \<longrightarrow> snd (\<sigma> !! i) \<le> snd (\<sigma> !! j)"
    using iffD1[OF ssorted_iff_mono h1] smap_alt by auto
  ultimately show "finite {k. snd (\<sigma> !! k) - c = n}"
    unfolding finite_nat_set_iff_bounded_le
    by (smt (verit, del_insts) add_less_cancel_left diff_le_mono linorder_le_cases 
        mem_Collect_eq nat_arith.rule0 order_less_le_trans zero_order(3))
qed

lemma finite_vimage_\<I>_Until:
  assumes "bounded I"
  shows "finite {k. mem I (\<tau> \<sigma> k - \<tau> \<sigma> \<iota>)}"
proof-
  let ?A = "{{k. \<tau> \<sigma> k - \<tau> \<sigma> \<iota> = n}|n. mem I n}"
  have "?A = (\<lambda>n. {k. \<tau> \<sigma> k - \<tau> \<sigma> \<iota> = n}) ` {i |i. mem I i}"
    by auto
  hence "finite ?A"
    using finite_bounded_\<I>[OF assms] 
    by simp
  moreover have "{k. mem I (\<tau> \<sigma> k - \<tau> \<sigma> \<iota>)} = \<Union>?A"
    by auto
  ultimately show ?thesis
    using finite_Union[of ?A] 
      finite_vimage_\<tau>_nat[of \<sigma> \<open>\<tau> \<sigma> \<iota>\<close>]
    by auto
qed


subsection \<open> Orders \<close>

lemma bounded_fixpoint_ex:
  fixes f :: "nat \<Rightarrow> nat"
  shows "mono_on {..j} f \<Longrightarrow> (\<forall>x \<le> j. f x \<le> j) \<Longrightarrow> \<exists>y \<le> j. y = f y"
  apply (induct j)
   apply simp
  apply (simp add: mono_on_def)
  by (metis eq_iff le_Suc_eq)

lemma bounded_fixpoint_ex_above:
  fixes f :: "nat \<Rightarrow> nat"
  shows "mono_on {i..j} f \<Longrightarrow> (\<forall>x \<in> {i .. j}. f x \<in> {i .. j}) \<Longrightarrow> i \<le> j \<Longrightarrow> \<exists>y \<in> {i .. j}. y = f y"
  apply (induct j)
   apply simp
   apply (simp add: mono_on_def)
  by (metis atLeastAtMost_iff le_Suc_eq order_antisym_conv)

lemma Inf_leq:
  fixes X::"nat set"
  shows "X \<noteq> {} \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Inf Y \<le> Inf X"
  by (simp add: cInf_superset_mono)

lemma min_Inf:
  fixes X :: "nat set"
  assumes "X \<noteq> {}" "Y \<noteq> {}"
  shows "min (Inf X) (Inf Y) = Inf (X \<union> Y)"
proof -
  obtain x where x_def: "x = Inf X" "x \<in> X" "\<And>z. z \<in> X \<Longrightarrow> x \<le> z"
    using assms(1) cInf_lower
    by (auto simp add: Inf_nat_def1)
  obtain y where y_def: "y = Inf Y" "y \<in> Y" "\<And>z. z \<in> Y \<Longrightarrow> y \<le> z"
    using assms(2) cInf_lower
    by (auto simp add: Inf_nat_def1)
  have "min x y \<in> X \<union> Y" "\<And>z. z \<in> X \<union> Y \<Longrightarrow> min x y \<le> z"
    using x_def(2,3) y_def(2,3)
    by (fastforce simp: min_def)+
  then have "Inf (X \<union> Y) = min x y"
    unfolding Inf_nat_def
    by (rule Least_equality)
  then show ?thesis
    by (auto simp: x_def(1) y_def(1))
qed

lemma cInf_restrict_nat:
  fixes x :: nat
  assumes "x \<in> A"
  shows "Inf A = Inf {y \<in> A. y \<le> x}"
  using assms by (auto intro!: antisym intro: cInf_greatest cInf_lower Inf_nat_def1)

lemma Inf_UNIV_nat: "(Inf UNIV :: nat) = 0"
  by (simp add: cInf_eq_minimum)

lemma bounded_rtranclp_mono:
  fixes n :: "'x :: linorder"
  assumes "\<And>i j. R i j \<Longrightarrow> j < n \<Longrightarrow> S i j" "\<And>i j. R i j \<Longrightarrow> i \<le> j"
  shows "rtranclp R i j \<Longrightarrow> j < n \<Longrightarrow> rtranclp S i j"
proof (induct rule: rtranclp_induct)
  case (step y z)
  then show ?case
    using assms(1,2)[of y z]
    by (auto elim!: rtrancl_into_rtrancl[to_pred, rotated])
qed auto

lemma max_memR:
  assumes A_def: "A = {j. j\<le>k \<and> memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> j)}"
  shows "k = Max A"
proof -
  have "k \<in> A"
    unfolding A_def
    by auto
  moreover {
    assume "\<exists>k' \<in> A. k' > k"
    then obtain k' where k'_props: "k' \<in> A" "k' > k"
      by auto
    then have "False"
      unfolding A_def
      by auto
  }
  ultimately show k_eq: "k = Max A"
    unfolding A_def
    by (metis (no_types, lifting) Max_eqI finite_nat_set_iff_bounded_le le_less_linear)
qed

lemma eq_memR:
  assumes non_empty: "A \<noteq> {}"
  assumes A_def: "A = {j. j<k \<and> memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> j)}"
  shows "A = {Min A..Max A}"
proof -
  have A_props: "finite A" "A \<noteq> {}"
    using non_empty
    unfolding A_def
    by auto

  define j where "j = Min A"

  have "j \<in> A"
    using A_props
    unfolding j_def
    by auto
  then have j_props: "j \<le> k" "memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> j)"
    unfolding A_def
    by auto

  have "\<And>x. x \<in> {Min A..Max A} \<Longrightarrow> x \<in> A"
  proof -
    fix x
    assume assm: "x \<in> {Min A..Max A}"
    then have "x \<le> Max A" by auto
    moreover have "Max A \<in> A" using A_props by auto
    ultimately have "x < k"
      unfolding A_def
      by auto
    moreover have "memR (args_ivl args) (\<tau> \<sigma> k - \<tau> \<sigma> x)"
    proof -
      have "x \<ge> j"
        using j_def assm
        by auto
      then have "\<tau> \<sigma> j \<le> \<tau> \<sigma> x"
        by auto
      then have "\<tau> \<sigma> k - \<tau> \<sigma> j \<ge> \<tau> \<sigma> k - \<tau> \<sigma> x"
        by linarith
      then show ?thesis
        using j_props memR_antimono
        by auto
    qed
    ultimately show "x \<in> A"
      unfolding A_def
      by auto
  qed
  moreover have "\<And>x. x < Min A \<Longrightarrow> x \<notin> A"
    using A_props
    by auto
  moreover have "\<And>x. x > Max A \<Longrightarrow> x \<notin> A"
    using A_props
    by auto
  ultimately have A_mem: "\<And>x. (x \<in> {Min A..Max A}) = (x \<in> A)"
    by (meson A_props Min_eq_iff atLeastAtMost_iff eq_Max_iff)
  then show "A = {Min A..Max A}"
    by blast
qed

lemma drop_filter_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). memR I (mt - t)) xs = drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). memR I (mt - t)) xs = drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
    using Cons
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). memR I (mt - t)) xs)"
      by auto
    moreover have "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = (drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case mem: False
    then have filter_IH: "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). memR I (mt - t)) xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)")
      case 0
      then show ?thesis using IH by auto
    next
      case (Suc nat)
      then have drop_IH: "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = drop nat xs"
        using filter_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR I (mt - t)) db")
        case True
        then have "(length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) = 0"
          using True mem
          by (simp add: prod.case_eq_if)
        then have "drop (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x#xs"
          using mem
          by auto
        moreover have "filter (\<lambda>(t, _). memR I (mt - t)) (x#xs) = x#xs"
          using True mem
          by auto
        ultimately show ?thesis
          by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). \<not>memR I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). \<not>memR I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(2) j_props
          by auto
        ultimately have "((\<lambda>(t, _). \<not>memR I (mt - t)) x)" using memR_antimono by auto
        then show ?thesis using mem by auto
      qed
    qed
  qed
qed

lemma take_filter_not_memR:
  assumes "sorted (map fst xs)"
  shows "filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have IH: "filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs"
    using Cons
    by auto
  show ?case
  proof (cases "(\<lambda>(t, _). \<not>memR I (mt - t)) x")
    case True
    then have "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = x#(filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)"
      by auto
    moreover have "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x#(take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) xs)"
      using True
      by auto
    ultimately show ?thesis using IH by auto
  next
    case not_mem: False
    then have filter_IH: "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)"
      by auto
    then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)) (x#xs)"
      by auto
    show ?thesis
    proof (cases "length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) xs)")
      case 0
      then show ?thesis by auto
    next
      case (Suc nat)
      then have takeWhile_IH: "take (length (filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs))) (x#xs) = x # (take nat xs)"
        using takeWhile_IH
        by auto
      then show ?thesis
      proof (cases "\<forall>db \<in> set xs. (\<lambda>(t, _). memR I (mt - t)) db")
        case True
        then have "filter (\<lambda>(t, _). \<not>memR I (mt - t)) (x#xs) = []"
          using filter_IH
          by (simp add: case_prod_beta')
        then show ?thesis using takeWhile_IH by auto
      next
        case False
        then obtain j where j_props: "((\<lambda>(t, _). \<not>memR I (mt - t)) (xs!j))" "j \<in> {0..<length xs}"
          by (metis (mono_tags, lifting) atLeastLessThan_iff case_prod_beta' in_set_conv_nth leI not_less_zero)
        then have "((\<lambda>(t, _). \<not>memR I (mt - t)) ((x#xs)!(Suc j)))"
          by auto
        moreover have "fst ((x#xs)!0) \<le> fst ((x#xs)!(Suc j))"
          using Cons(2) j_props
          by auto
        ultimately have "((\<lambda>(t, _). \<not>memR I (mt - t)) x)" using memR_antimono by auto
        then show ?thesis using not_mem by auto
      qed
    qed
  qed
qed

lemma memR_impl_pred:
  shows "memR (args_ivl args) (\<tau> \<sigma> k - j) \<Longrightarrow> memR (args_ivl args) (\<tau> \<sigma> (k - 1) - j)"
proof -
  have "\<tau> \<sigma> (k - 1) \<le> \<tau> \<sigma> k"
    by auto
  then have "\<tau> \<sigma> (k - 1) - j \<le> \<tau> \<sigma> k - j"
    by linarith
  then show memR_impl: "memR (args_ivl args) (\<tau> \<sigma> k - j) \<Longrightarrow> memR (args_ivl args) (\<tau> \<sigma> (k - 1) - j)"
    using memR_antimono[of "args_ivl args"]
    by auto
qed


subsection \<open> Intervals and traces \<close>

lemma nth_pts_prefix_cong: "\<pi> \<le> \<pi>' \<Longrightarrow> i < plen \<pi> \<Longrightarrow> pts \<pi> ! i = pts \<pi>' ! i"
  by transfer (auto simp add: nth_append)

lemma Inf_memR_conv: 
  "\<Sqinter> {i. \<forall>k. k < j \<and> k \<le> n \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)} =
  (case j of 0 \<Rightarrow> 0 | Suc x \<Rightarrow> Inf {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)})"
  using memR_antimono[OF _ diff_le_mono[OF \<tau>_mono]]
  by (fastforce simp: cInf_eq_minimum less_Suc_eq_le 
      split: nat.splits intro!: arg_cong[where ?f=Inf])

lemma min_x_Inf: 
  "min x (\<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}) 
  = \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
proof -
  {
    assume assm: "x < \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
    then have "x \<in> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
      by auto
    then have "x \<ge> \<Sqinter> {i. memR I (\<tau> \<sigma> (min x n) - \<tau> \<sigma> i)}"
      by (simp add: cInf_lower)
    then have "False" using assm by auto
  }
  then show ?thesis
    by (meson min.absorb2 not_le_imp_less)
qed

unbundle no_lattice_syntax \<comment> \<open> disable notation \<close>

(*<*)
end
(*>*)