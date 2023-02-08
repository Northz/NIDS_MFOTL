theory Type_Soundness
  imports Typing
begin


subsection \<open> Type soundness \<close>

context sat_general
begin

lemma safe_neg_eq: 
  "safe_formula (Formula.Neg (Formula.Eq x1 x2)) \<Longrightarrow> safe_formula  (Formula.Eq x1 x2) \<or>
  (Formula.sat \<sigma> V v i  (Formula.Neg (Formula.Eq x1 x2)) \<longleftrightarrow> sat' \<sigma> V v i  (Formula.Neg (Formula.Eq x1 x2))) "
  by (cases x1; cases x2) auto

lemma foldl_sound:
  assumes  " \<forall>x\<in>set (x22). ty_of x = t" "ty_of x21 = t" 
  shows
    "foldl undef_min x21 x22 = foldl min x21 x22"
    "foldl undef_max x21 x22 = foldl max x21 x22"
    "t \<in> numeric_ty \<Longrightarrow> foldl undef_plus x21 x22 = foldl (+) x21 x22 \<and> ty_of (foldl (+) x21 x22 ) = t"
  
proof -
  from assms(1-2) 
  have minmax:"foldl undef_min x21 x22 = foldl min x21 x22 \<and> foldl undef_max x21 x22 = foldl max x21 x22"
  proof (induction x22 arbitrary: x21 t)
    case (Cons a x22)
    then show ?case using undef_less_eq_sound   
      by (cases x21; cases a; simp add: min_def undef_min_def max_def undef_max_def) fastforce+ 
  qed auto
  from this show "foldl undef_min x21 x22 = foldl min x21 x22" by auto
  from minmax show "foldl undef_max x21 x22 = foldl max x21 x22" by auto
next
  assume "t \<in> numeric_ty"
  from this assms show "foldl undef_plus x21 x22 = foldl (+) x21 x22 \<and> ty_of (foldl (+) x21 x22 ) = t"
  proof (induction x22 arbitrary: x21 t)
  case (Cons a x22)
  then show ?case using undef_plus_sound 
    apply (cases x21; cases a; auto simp add: numeric_ty_def)
    using ty_of.simps by presburger+
  qed auto
qed

lemma eval_agg_op_sound: 
  assumes 
    "M={(x, ecard Zs) | x Zs. Zs =
      {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}"
    "S, E \<turnstile> formula.Agg y (agg_op,d) tys f \<phi> " 
    "wty_envs S \<sigma> V"
    "fv_trm f \<subseteq> fv \<phi>"
    "safe_formula \<phi>" 
  shows "eval_agg_op (agg_op,d) M = eval_agg_op' (agg_op,d) M"
proof -
  from assms(2) obtain t where t_def: "agg_env E tys  \<turnstile> f :: t" and t_wty:"t \<in> agg_trm_type agg_op" by cases auto
  have fv_wty: "y\<in>fv_trm f \<Longrightarrow> length zs = length tys \<Longrightarrow> Formula.sat \<sigma> V (zs @ v) i \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y zs
    apply (rule ty_of_sat_safe)
    using assms by (auto elim: wty_formula.cases)
  then have wty_M: "\<forall>(x,card) \<in>  M . ty_of x = t" 
    using assms(1) t_def by (auto dest!: ty_of_eval_trm)
  have "finite_multiset M \<Longrightarrow>set (flatten_multiset M) \<subseteq> fst ` M" 
    apply (rule set_of_flatten_multiset)
    using finite_set apply (auto simp add: assms(1)) 
    using finite_fst by (auto simp add: finite_multiset_def assms(1)) 
  then have wty_flatten: "finite_multiset M \<Longrightarrow> \<forall>x \<in> set (flatten_multiset M). ty_of x = t" 
    using wty_M by fastforce
  have avg: "finite_multiset M \<Longrightarrow> flatten_multiset M = x21 # x22 \<Longrightarrow> agg_op = Formula.Agg_Avg \<Longrightarrow>
          double_of_event_data_agg (foldl (+) x21 x22) = undef_double_of_event_data_agg (foldl undef_plus x21 x22)" for x21 x22
  proof -
    assume assm: "finite_multiset M" "flatten_multiset M = x21 # x22" "agg_op = Formula.Agg_Avg" 
    have foldl_plus: "foldl undef_plus x21 x22 = foldl (+) x21 x22" 
      apply (rule  conjE[OF foldl_sound(3)]) using wty_flatten t_wty assm by auto
    have foldl_ty: "ty_of (foldl (+) x21 x22) \<in> numeric_ty " 
      apply (rule conjE[OF  foldl_sound(3)]) using assm wty_flatten t_wty by auto
    show ?thesis apply (auto simp: foldl_plus) apply (cases "foldl (+) x21 x22") using  undef_double_of_event_data_agg_sound foldl_ty by (auto simp add: numeric_ty_def)
  qed
  have med:"finite_multiset M \<Longrightarrow> flatten_multiset M = xs \<Longrightarrow> agg_op = Formula.Agg_Med \<Longrightarrow> i< length xs \<Longrightarrow>
    double_of_event_data_agg (xs!i) = undef_double_of_event_data_agg (xs!i) " for xs i 
    using t_wty wty_flatten undef_double_of_event_data_agg_sound nth_mem[where ?n=i and ?xs=xs] by (cases "xs!i")  (auto simp add: numeric_ty_def split:ty.splits) 
  then show ?thesis
    apply (cases agg_op) using wty_flatten t_wty avg apply (auto simp:Let_def split: list.splits bool.splits) 
    using foldl_sound  apply presburger+ 
    by (metis div2_less_self in_set_conv_nth list.set_intros(2))
qed 

(* TODO: move to formula *)
lemma sat_trigger_mem0_iff: "mem I 0 \<Longrightarrow> Formula.sat \<sigma> V v i (formula.Trigger \<phi> I \<psi>) 
  \<longleftrightarrow> (\<forall>j \<le> i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k\<in>{j<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (formula.And \<phi> \<psi>)))"
  using sat_trigger_rewrite_0_mem[of I _ _ _ i \<phi> \<psi>]
  by auto

lemma sat_release_mem0_iff: "mem I 0 \<Longrightarrow> Formula.sat \<sigma> V v i (formula.Release \<phi> I \<psi>) 
  \<longleftrightarrow> (\<forall>j \<ge> i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k\<in>{i..<j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (formula.And \<phi> \<psi>)))"
  using sat_release_rewrite_0_mem[of I _ _ _ i \<phi> \<psi>]
  by auto


subsubsection \<open> Results for sat' from sat \<close>

lemma sat'_until_true:
  assumes "\<not>mem I 0"
  shows "sat' \<sigma> V v i (Formula.Until \<phi> I Formula.TT) = sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.Prev all \<phi>))"
proof (rule iffI)
  assume "sat' \<sigma> V v i (Formula.Until \<phi> I Formula.TT)"
  then obtain j where j_props: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>" by auto
  {
    assume "j=i"
    then have "False" using j_props assms by auto
  }
  then have "j>i" using j_props(1) using le_eq_less_or_eq by blast
  then show "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.Prev all \<phi>))"
    using j_props interval_all
    by (auto split: nat.split intro!: exI[of _ j])
next
  assume "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.Prev all \<phi>))"
  then show "sat' \<sigma> V v i (Formula.Until \<phi> I Formula.TT)" by auto
qed

lemma sat'_always_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "bounded I1" (* [a, b] *)
  shows "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>)) = sat' \<sigma> V v i (always_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
  then show "sat' \<sigma> V v i (always_safe_bounded I1 \<phi>)"
    using assms always_safe_bounded_def
    by (simp add: always_safe_bounded_def)
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "sat' \<sigma> V v i (always_safe_bounded I1 \<phi>)"
  then have rewrite: "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Neg (eventually I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def always_safe_bounded_def
    by (simp add: always_safe_bounded_def)
  then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j \<phi>" by auto
  have j_geq_i_sat: "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> (sat' \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> sat' \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> sat' \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<ge>i" "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
    then have "(sat' \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> sat' \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> sat' \<sigma> V v k \<phi>"
      using j_geq_i_sat by auto
    moreover {
      assume assm: "(sat' \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> sat' \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>sat' \<sigma> V v j \<phi>" 
        by (auto simp: once_def)
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>sat' \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)"
          using j_props assms
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" "memR I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
          using k_props assms
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def interval_geq j_props(1)
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms I2_def j_props(1) k_props(1) interval_geq
          by (metis forall_finite(1) int_remove_lower_bound.rep_eq memL.rep_eq memR.rep_eq not_le_imp_less prod.sel(1-2))
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "sat' \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j \<phi>" by auto
  then show "sat' \<sigma> V v i (Formula.And (eventually I1 \<phi>) (always I1 \<phi>))"
    using rewrite
    by auto
qed

lemma sat'_release_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
shows "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>)) = sat' \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume release: "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
  {
    assume "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j \<psi>"
    then have all: "sat' \<sigma> V v i (always I1 \<psi>)" by auto
    obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using release by auto
    then have "sat' \<sigma> V v i (always_safe_bounded I1 \<psi>)"
      using assms sat'_always_rewrite_bounded[of I1 \<sigma> V v i \<psi>] all
      by auto
    then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      by auto
  }
  moreover {
    assume "\<exists>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> \<not>sat' \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<not>sat' \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{i ..< j} \<and> sat' \<sigma> V v k \<phi>}"
    define k where k_def: "k = Min A"
    have "(\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" using j_props release by auto
    then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{i ..< j}" "sat' \<sigma> V v k \<phi>" using A_def by auto
    {
      fix x
      assume x_props: "x\<le>j" "\<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume k_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
        have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" using x_props by auto
        then have "\<tau> \<sigma> x - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by linarith
        moreover have "memR I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using assms j_props by auto 
        ultimately have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using memR_antimono by blast
        moreover have "memL I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          using k_not_mem_1 x_props assms I2_def
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    }
    then have geq_j_mem: "\<forall>x\<le>j. \<not>mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have k_mem: "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
      then have "sat' \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {i ..< k}. sat' \<sigma> V v k \<phi>)" using release k_props by auto
      moreover {
        assume "(\<exists>k \<in> {i ..< k}. sat' \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {i ..< k}" "sat' \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "sat' \<sigma> V v k \<psi>" by auto
      then have k_sat: "sat' \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_until: "sat' \<sigma> V v k (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using assms int_remove_lower_bound.rep_eq memL.rep_eq prod.sel(1)
        by auto
      {
        assume "k=i"
        then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] using assms k_mem by auto
      }
      moreover {
        assume k_neq_i: "\<not>(k=i)"
        then have k_pred_geq_i: "k-1\<ge>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {i..<k}" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          then have "sat' \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. sat' \<sigma> V v k \<phi>)" using release by auto
          moreover {
            assume "\<exists>k \<in> {i ..< x}. sat' \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {i ..< x}" "sat' \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<ge> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "sat' \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{i..<k}. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          moreover have "sat' \<sigma> V v (k-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_pred_geq_i k_until interval_all k_neq_i
            by auto
          ultimately have "(\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_pred_geq_i
            by blast
          then have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{i..<k} \<and> mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<and> sat' \<sigma> V v l \<psi>}"
          define c where "c = Min B"
          assume "\<not>mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
          then have "sat' \<sigma> V v (k-1) \<psi> \<or> (\<exists>x \<in> {i ..< k-1}. sat' \<sigma> V v x \<phi>)"
            using release k_pred_geq_i
            by auto
          moreover {
            assume "\<exists>x \<in> {i ..< k-1}. sat' \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {i ..< k-1} \<and> sat' \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<ge> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "sat' \<sigma> V v (k-1) \<psi>" by auto
          then have B_props: "B \<noteq> {} \<and> finite B"
            using B_def k_pred_geq_i k_suc_mem k_props k_neq_i
            by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{i..<k}" "mem I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" "sat' \<sigma> V v c \<psi>" using B_def by auto
          then have k_cond: "k\<ge>c" "sat' \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
          {
            assume "c=0"
            then have "False" using c_props assms by auto
          }
          then have c_pos: "c\<noteq>0" by auto
          {
            fix x
            assume x_props: "x\<in>{c..<k}"
            then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> c" by auto
            then have lower: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> c - \<tau> \<sigma> i)" by auto
            have "\<tau> \<sigma> x \<le> \<tau> \<sigma> k" using x_props by auto
            then have upper: "(\<tau> \<sigma> x - \<tau> \<sigma> i) \<le> (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
            then have "memR I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
              using k_mem memR_antimono by blast
            then have "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using assms c_props lower by auto
            then have "sat' \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{c..<k}. sat' \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> k - \<tau> \<sigma> c)"
            using k_mem c_props
            by (metis atLeastLessThan_iff int_remove_lower_bound.rep_eq interval_geq less_or_eq_imp_le memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
          ultimately have c_sat: "sat' \<sigma> V v c (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using assms k_cond
            by auto
          {
            assume "(c-1) \<in> B"
            then have "c-1\<ge>c" using c_def B_props by auto
            moreover have "c-1 < c" using c_pos by auto
            ultimately have "False" by auto
          }
          then have "(c-1) \<notin> B" by blast
          then have disj: "(c-1)\<notin>{i..<k} \<or> \<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>sat' \<sigma> V v (c-1) \<psi>" using B_def by blast
          {
            assume "(c-1)\<notin>{i..<k}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c-1)\<notin>{i..<k})"
            then have c_pred_geq_i: "(c-1)\<in>{i..<k}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>sat' \<sigma> V v (c-1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              then have "\<not>sat' \<sigma> V v (c-1) \<psi>" using disj by blast
              then have "False"
                using k_greater_sat c_pred_geq_i c_suc_mem
                by auto
            }
            moreover {
              assume c_pred_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              {
                assume "\<not>mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                then have upper: "\<not> memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
                  using c_pred_not_mem_1 assms geq_j_mem k_cond k_props
                  by auto
                have "\<tau> \<sigma> c \<ge> \<tau> \<sigma> (c-1)" by auto
                then have "\<tau> \<sigma> c - \<tau> \<sigma> i \<ge> \<tau> \<sigma> (c-1) - \<tau> \<sigma> i" using diff_le_mono by blast
                moreover have "memR I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" using c_props assms by auto
                ultimately have "memR I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using memR_antimono by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
              then have "(c-1)\<ge>i" "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" "sat' \<sigma> V v (c-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_pred_geq_i c_sat interval_all c_pos
                by auto
              then have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat'_eventually
                by blast
            }
            ultimately have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately have "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using release
    by auto
  then show "sat' \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
    using assms I2_def
    by (simp add: release_safe_bounded_def) blast
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "sat' \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def
    by (auto simp: release_safe_bounded_def)
  then have eventually: "sat' \<sigma> V v i (eventually I1 Formula.TT)" by auto
  then have "sat' \<sigma> V v i (always_safe_bounded I1 \<psi>) \<or> sat' \<sigma> V v i (eventually I2 \<phi>) \<or> sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    using assm
    by auto
  moreover {
    assume "sat' \<sigma> V v i (always_safe_bounded I1 \<psi>)"
    then have "sat' \<sigma> V v i (always I1 \<psi>)"
      using assms sat'_always_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
      by auto
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "sat' \<sigma> V v i (eventually I2 \<phi>)"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<ge>i" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
      {
        assume "x\<le>j"
        then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> x - \<tau> \<sigma> i)" using j_props assms I2_def flip_int_less_lower_props
          by (meson diff_le_mono memL_mono memR_antimono memR_zero zero_le)
        then have "False" using x_props assms I2_def
          using flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<le>j)" by blast
      then have "x>j" by auto
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> x>j" by auto
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume until: "sat' \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    then have j_pred_sat: "sat' \<sigma> V v (j+1) (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))" by auto
    then have "\<exists>x\<ge>(j+1). sat' \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{(j+1)..<x}. sat' \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<ge>(j+1)" "sat' \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{(j+1)..<x}. sat' \<sigma> V v k \<psi>" by blast
    {
      fix l
      assume l_props: "l\<ge>i"
      {
        assume "l>x"
        then have "\<exists>k \<in> {i ..< l}. sat' \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l>x)" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        then have l_props: "x\<ge>l" "l\<ge>i" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using l_props by auto
        {
          assume "l\<ge>(j+1)"
          then have "sat' \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<ge>(j+1)"
          then have l_geq: "l\<le>(j+1)" by auto
          have j_suc_psi: "sat' \<sigma> V v (j+1) \<psi>" using j_pred_sat by auto
          {
            assume "l<(j+1)"
            then have "\<tau> \<sigma> l \<le> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using assms I2_def j_props flip_int_less_lower_props
            by (meson diff_le_mono le0 memL_mono memR_antimono memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
              using assms I2_def flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j+1)" using l_geq le_eq_less_or_eq by blast
          then have "sat' \<sigma> V v l \<psi>" using j_suc_psi by blast
        }
        ultimately have "sat' \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {i ..< l}. sat' \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. sat' \<sigma> V v k \<phi>)" by auto
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  ultimately have "sat' \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by blast
  then show "sat' \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
    using assm
    by auto
qed

lemma sat'_and_release_rewrite:
  assumes "bounded I" "\<not>mem I 0" (* [a, b] *)
  shows "sat' \<sigma> V v i (Formula.And \<phi> (Formula.Release \<phi>' I \<psi>')) = sat' \<sigma> V v i (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
proof (cases "\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)")
  case True
  then have eventually: "sat' \<sigma> V v i (eventually I Formula.TT)"
    by auto
  then have "sat' \<sigma> V v i (Formula.Release \<phi>' I \<psi>') = sat' \<sigma> V v i (release_safe_bounded \<phi>' I \<psi>')"
    using sat'_release_rewrite[OF assms, of \<sigma> V v i \<phi>' \<psi>']
    by auto
  moreover have "
    Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<phi> (Formula.Neg (eventually I Formula.TT))) (Formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>'))) =
    Formula.sat \<sigma> V v i (Formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>'))"
    using eventually
    by auto
  ultimately show ?thesis
    unfolding and_release_safe_bounded_def
    by auto
qed (auto simp add: and_release_safe_bounded_def)

lemma sat'_release_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  assumes geq: "j\<ge>i"
  assumes mem_j: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  shows "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> sat' \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {i..<j}. sat' \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {i..<j}. sat' \<sigma> V v x \<phi>}"
  define k where "k = Min A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {i..<j}" "sat' \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "(\<forall>l<k. l \<notin> A)"
    using Min_le[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using mem mem_j k_props interval_leq[of I 0 \<sigma> j i k] by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat'_always_rewrite_0:
  fixes I :: \<I>
  assumes "mem I 0" "bounded I"
  shows "sat' \<sigma> V v i (always I \<phi>) = sat' \<sigma> V v i (always_safe_0 I \<phi>)"
proof (rule iffI)
  assume all: "sat' \<sigma> V v i (always I \<phi>)"
  {
    define A where "A = {j. j\<ge>i \<and> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)}"
    define j where "j = Inf A"
    assume "\<exists>j\<ge>i. mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then have "A \<noteq> {}" using A_def by auto
    then have "j \<in> A" using j_def by (simp add: Inf_nat_def1)
    then have j_props: "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" using A_def by auto
    {
      fix k
      assume k_props: "k \<in> {i..<j}"
      then have ineq: "\<tau> \<sigma> k - \<tau> \<sigma> i \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" by (simp add: diff_le_mono)
      {
        assume "mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        then have "k \<in> A" using A_def k_props by auto
        then have "k \<ge> j" using j_def cInf_lower by auto
        then have "False" using k_props by auto
      }
      then have "\<not>mem (flip_int_double_upper I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using j_props ineq assms(1) flip_int_double_upper_leq[of I "(\<tau> \<sigma> j - \<tau> \<sigma> i)" "(\<tau> \<sigma> k - \<tau> \<sigma> i)"]
        by auto 
      then have "sat' \<sigma> V v k \<phi>" using k_props all by auto
    }
    then have until_j: "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>" by blast
    have "\<not> mem (flip_int_double_upper I) 0"
      using assms
      by (simp add: flip_int_double_upper.rep_eq memL.rep_eq)
    then have "sat' \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>))"
      using j_props until_j sat'_until_true[of "(flip_int_double_upper I)" \<sigma> V v i \<phi>]
      by auto
  }
  moreover {
    define B where "B = {b. \<not>memR I b}"
    define b where "b = Inf B"
    define C where "C = {k. k\<ge>i \<and> b \<le> \<tau> \<sigma> k - \<tau> \<sigma> i}"
    define c where "c = Inf C"
    assume empty_int: "\<forall>j\<ge>i. \<not> mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" (* [b+1, 2b] *)
    from assms(2) have "B \<noteq> {}" using B_def bounded_memR by auto
    then have "b \<in> B" using b_def by (simp add: Inf_nat_def1)
    then have b_props: "\<not>memR I b" using B_def by auto
   
    have exists_db: "\<And>x. \<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
    proof -
      fix x
      show "\<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i"
        using ex_le_\<tau>[of i "x + \<tau> \<sigma> i" \<sigma>]
        by auto
    qed
    then have "C \<noteq> {}" using C_def by auto
    then have "c \<in> C" using c_def by (simp add: Inf_nat_def1)
    then have c_props: "c\<ge>i" "b \<le> \<tau> \<sigma> c - \<tau> \<sigma> i" using C_def by auto
    {
      assume "b = 0"
      then have "False" using b_props by auto
    }
    then have b_pos: "b>0" by blast
    {
      assume "c = i"
      then have "False" using c_props b_pos by auto
    }
    then have c_ge_i: "c>i" using c_props using le_less by blast
    {
      assume "\<not>mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
      then have "\<not>memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" using assms(1) memL_mono by blast
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<in> B" using B_def by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<ge> b" using b_def cInf_lower by auto
      then have "(c-1) \<in> C" using C_def c_ge_i by auto
      then have "c-1 \<ge> c" using c_def cInf_lower by auto
      then have "False" using c_ge_i by auto
    }
    then have c_pred_mem: "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by blast
    then have c_pred_sat: "sat' \<sigma> V v (c-1) \<phi>" using all c_ge_i by auto
    {
      assume "\<not>mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" (* [b+1, \<infinity>] but attention, here 'b' = b+1 *)
      then have "memR I (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" using assms(1) bounded_memR int_flip_mem by blast
      then have c_dist: "(\<tau> \<sigma> c - \<tau> \<sigma> (c-1)) < b" using b_props memR_antimono not_le by blast
      from c_pred_mem have "memR I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" by auto
      then have "(\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) < b" using b_props memR_antimono not_le by blast
      then have b_ineq: "b \<le> (\<tau> \<sigma> c - \<tau> \<sigma> i)" "(\<tau> \<sigma> c - \<tau> \<sigma> i) \<le> 2 * (b-1)"
        using c_props c_dist
        by auto
      {
        assume "\<not>memR I (b-1)"
        then have "(b-1) \<in> B" using B_def by auto
        then have "(b-1) \<ge> b" using b_def cInf_lower by auto
        then have "False" using b_pos by linarith
      }
      then have "memR I (b-1)" by blast
      then have "(\<lambda>i. memR I ((div) i 2)) (2*(b-1))" by auto
      then have "(\<lambda>i. memR I ((div) i 2)) (\<tau> \<sigma> c - \<tau> \<sigma> i)" using b_ineq by auto
      then have "memR (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        by (simp add: flip_int_double_upper.rep_eq memR.rep_eq)
      moreover have "memL (flip_int_double_upper I) (\<tau> \<sigma> c - \<tau> \<sigma> i)"
        using b_ineq b_props flip_int_double_upper.rep_eq memL.rep_eq memR_antimono
        by auto
      ultimately have "False" using empty_int c_props by auto
    }
    then have "mem (flip_int I) (\<tau> \<sigma> c - \<tau> \<sigma> (c-1))" by blast
    then have c_pred_sat: "sat' \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      using c_pred_sat c_ge_i
      by auto
    have "\<forall>j\<in>{i..<(c-1)}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
      by (meson \<tau>_mono assms(1) atLeastLessThan_iff c_pred_mem diff_le_mono le_eq_less_or_eq memL_mono memR_antimono zero_le)
    then have "\<forall>j\<in>{i..<(c-1)}. sat' \<sigma> V v j \<phi>" using all by auto
    then have
        "(c-1)\<ge>i"
        "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
        "sat' \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
        "(\<forall>k \<in> {i ..< (c-1)}. sat' \<sigma> V v k \<phi>)"
      using c_ge_i c_pred_mem c_pred_sat
      by auto
    then have "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
      by auto
  }
  ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    by auto
  then show "sat' \<sigma> V v i (always_safe_0 I \<phi>)" using always_safe_0_def by metis
next
  assume "sat' \<sigma> V v i (always_safe_0 I \<phi>)"
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    using always_safe_0_def
    by metis
  then have "sat' \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT) \<or> sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))" by auto
  moreover {
    assume "sat' \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT)"
    then obtain j where j_props:
      "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>"
      by auto
    then have "\<forall>k\<ge>i. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<longrightarrow> k<j"
      by (metis (no_types, lifting) assms flip_int_double_upper.rep_eq forall_finite(1) interval_leq leI memL.rep_eq prod.sel(1))
    then have "sat' \<sigma> V v i (always I \<phi>)" using j_props by auto
  }
  moreover {
    assume "sat' \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
    then obtain j where j_props:
      "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "sat' \<sigma> V v j (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      "\<forall>k\<in>{i..<j}. sat' \<sigma> V v k \<phi>"
      by auto
    then have phi_sat: "\<forall>k\<in>{i..j}. sat' \<sigma> V v k \<phi>" by auto
    {
      fix k
      assume k_props: "k>j" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have t_geq: "(\<tau> \<sigma> k - \<tau> \<sigma> i) \<ge> (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using diff_le_mono by auto
      from j_props have "mem (flip_int I) (\<tau> \<sigma> (j+1) - \<tau> \<sigma> j)" by auto
      then have "\<not>mem I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)"
        by (metis \<tau>_mono assms(2) diff_le_mono2 flip_int.rep_eq j_props(1) memL.rep_eq memL_mono prod.sel(1))
      then have "\<not>memR I (\<tau> \<sigma> (j+1) - \<tau> \<sigma> i)" using assms memL_mono by blast
      then have "\<not>memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using t_geq memR_antimono by blast
      then have "False" using k_props by auto
    }
    then have "\<forall>k>j. \<not>mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" by auto
    then have "sat' \<sigma> V v i (always I \<phi>)" using phi_sat by auto
  }
  ultimately show "sat' \<sigma> V v i (always I \<phi>)" by blast
qed

lemma sat'_release_rewrite_0:
  assumes mem: "mem I 0" "bounded I"
shows "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>) = sat' \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume release: "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  {
    assume "\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  moreover {
    assume "\<not>(\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat' \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<ge> i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "\<not>sat' \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    define A where "A = {j. j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Min A"
    from j'_props have "\<not>sat' \<sigma> V v j' \<psi> \<or> sat' \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>sat' \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {i..<j'}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> sat' \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms release sat'_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {i..<j}. sat' \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {i..<j} \<and> \<not> sat' \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using assms j_props interval_leq[of I 0 \<sigma> j i k]
        by auto
      then have "\<exists>x \<in> {i..<k}. mem I (\<tau> \<sigma> x - \<tau> \<sigma> i) \<and> sat' \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms release k_props sat'_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {i..<k}" "mem I (\<tau> \<sigma> x - \<tau> \<sigma> i)" "sat' \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<ge> Min A"
        using A_def A_props k_props j_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {i..<j}. sat' \<sigma> V v k \<psi>" by blast
    then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<in>{i..j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat' \<sigma> V v j \<phi>}"
      define k where "k = Min B"
      assume "sat' \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<in>{i..j'}" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "sat' \<sigma> V v k \<phi>" using B_def by auto
      have "\<forall>l<k. l \<notin> B"
        using Min_le[OF B_props(2)]
        by (fastforce simp: k_def)
      {
        fix l
        assume l_props: "l \<in> {i..<k}"
        then have l_mem: "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using assms k_props interval_leq[of I 0 \<sigma> k i l]
          by auto
        {
          assume "sat' \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem k_props by auto
          then have "l\<ge>k" "l<k"
            using k_def l_props B_props(2) Min_le[of B l]
            by auto
        }
        then have "\<not>sat' \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{i..<k}. \<not>sat' \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "sat' \<sigma> V v k \<psi>" using k_props release B_def by auto
      {
        fix l
        assume l_props: "l\<in>{i..<k}"
        then have "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using k_props assms interval_leq[of I 0 \<sigma> k i l]
          by auto
        then have "sat' \<sigma> V v l \<psi>"
          using l_props release not_phi
          by auto
      }
      then have "\<forall>l\<in>{i..<k}. sat' \<sigma> V v l \<psi>"
        using not_phi assms release
        by auto
      then have "sat' \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by auto
  }
  ultimately have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))" by blast
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms sat'_always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  then show "sat' \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
next
  assume "sat' \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I \<psi>))"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
  then have "sat' \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always I \<psi>))"
    using assms sat'_always_rewrite_0[of I \<sigma> V v i "\<psi>"]
    by auto
  moreover {
    assume "sat' \<sigma> V v i (always I \<psi>)"
    then have "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
  }
  moreover {
    fix j
    assume until_and_j_props: "sat' \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))" "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then obtain "j'" where j'_props: "j'\<ge>i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "sat' \<sigma> V v j' (Formula.And \<phi> \<psi>)" "(\<forall>k \<in> {i ..< j'}. sat' \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume ge: "j' > j"
      then have "\<forall>k \<in> {i ..< j'}. sat' \<sigma> V v k \<psi>" using j'_props by auto
      then have "sat' \<sigma> V v j \<psi>" using until_and_j_props ge by auto
      then have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" by auto
    }
    moreover {
      assume leq: "\<not> j' > j"
      moreover {
        assume "j = j'"
        then have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)"
          using leq j'_props
          by auto
      }
      ultimately have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "sat' \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat' \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "sat' \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
qed


subsubsection \<open> Soundness proof \<close>

lemma soundness: (*Theorem 3.12 helper*)
  assumes
    "safe_formula \<phi>" 
    "S,E \<turnstile> \<phi>"
    "\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y"
    "wty_envs S \<sigma> V"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" 
  using assms 
proof (induction arbitrary: v V i S E rule: safe_formula_induct)
  case (Pred e tms)
  from Pred(2) obtain p tys where obt: "S p = Some tys \<and> list_all2 (\<lambda>tm ty. E \<turnstile> tm :: ty) tms tys" by cases auto
  from this Pred have tms_wty: "x \<in> set tms \<Longrightarrow> \<exists>t \<in> set tys. E \<turnstile> x :: t " for x 
    by (metis in_set_conv_nth list_all2_conv_all_nth) 
  have eval_tms_eq: "map (Formula.eval_trm v) tms = map (eval_trm' v) tms" using tms_wty Pred(3) by (auto dest!: eval_trm_sound)
  then show ?case using Pred(1) apply (auto simp add: trm.is_Var_def trm.is_Const_def)
    by (metis eval_tms_eq )+
next 
  case (Let p \<phi> \<psi>) 
  obtain E' where 
    psi_wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>" and
    phi_wty: "S, E' \<turnstile> \<phi>" using Let.prems(1) by cases auto
  have wtyenv: "x \<in> \<Gamma> \<sigma> i \<Longrightarrow> (case x of (p, xs) \<Rightarrow> (p, length xs) \<notin> dom V \<longrightarrow> (case S (p, length xs) of None \<Rightarrow> False | Some ts \<Rightarrow> wty_tuple ts xs))" for x i
    using Let.prems(3) by (auto simp add: wty_envs_def wty_event_def wty_tuple_def) 
  have ty_of_phi: "x \<in> Formula.fv \<phi> \<Longrightarrow>  Formula.sat \<sigma> V xs i \<phi> \<Longrightarrow> length xs = Formula.nfv \<phi> \<Longrightarrow> ty_of (xs!x) = E' x" for x xs
    apply (rule ty_of_sat_safe) using Let phi_wty by auto 
  have "x \<in> Formula.fv \<phi> \<Longrightarrow>  Formula.sat \<sigma> V xs i \<phi> \<Longrightarrow> length xs = Formula.nfv \<phi> \<Longrightarrow> (tabulate E' 0 (Formula.nfv \<phi>)!x) = ty_of (xs!x)" for x xs 
    using ty_of_phi[of x xs] apply(auto simp add: Formula.nfv_def split: nat.splits)
    by (metis Formula.nfv_def add.left_neutral fvi_less_nfv nth_tabulate)
  then  have list_all_tab:"length xs = Formula.nfv \<phi> \<Longrightarrow>
    Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi> \<Longrightarrow> list_all2 (\<lambda>t x. ty_of x = t) (tabulate E' 0 (Formula.nfv \<phi>)) xs " for xs i 
  proof -
    assume a1: "Formula.sat \<sigma> V xs i \<phi> \<or> sat' \<sigma> V xs i \<phi>"
    assume a2: "length xs = Formula.nfv \<phi>"
    obtain nn :: "event_data list \<Rightarrow> ty list \<Rightarrow> (ty \<Rightarrow> event_data \<Rightarrow> bool) \<Rightarrow> nat" where
      "\<forall>x0 x1 x2. (\<exists>v3<length x1. \<not> x2 (x1 ! v3) (x0 ! v3)) = (nn x0 x1 x2 < length x1 \<and> \<not> x2 (x1 ! nn x0 x1 x2) (x0 ! nn x0 x1 x2))" by moura
    then have "\<forall>p ts es. (\<not> list_all2 p ts es \<or> length ts = length es \<and> (\<forall>n. \<not> n < length ts \<or> p (ts ! n) (es ! n))) \<and> (list_all2 p ts es \<or> length ts \<noteq> length es \<or> nn es ts p < length ts \<and> \<not> p (ts ! nn es ts p) (es ! nn es ts p))"
      by (metis (no_types) list_all2_conv_all_nth)
    then show ?thesis
      using a2 a1 by (smt (z3) Let.hyps(1) Let.hyps(2) Let.prems(3) add.left_neutral atLeastLessThan_iff dual_order.refl length_tabulate less_nat_zero_code not_less nth_tabulate phi_wty subset_eq ty_of_sat'_safe ty_of_sat_safe)
  qed
  have phi_case: "sat' \<sigma> V v5 i5 \<phi> = Formula.sat \<sigma> V v5 i5 \<phi> " for v5 i5
  proof -
    {
      assume sat: " Formula.sat \<sigma> V v5 i5 \<phi>"
      have "y \<in> fv \<phi> \<Longrightarrow> ty_of (v5 ! y) = E' y" for y 
        thm ty_of_sat_safe
        apply (rule ty_of_sat_safe) using Let sat phi_wty by auto
      then have " Formula.sat \<sigma> V v5 i5 \<phi> = sat' \<sigma> V v5 i5 \<phi> " 
        using phi_wty Let by auto
    } moreover {
      assume sat': "sat' \<sigma> V v5 i5 \<phi>"
      have "y \<in> fv \<phi> \<Longrightarrow> ty_of (v5 ! y) = E' y" for y 
        apply (rule ty_of_sat'_safe) using Let sat' phi_wty by auto
      then have " Formula.sat \<sigma> V v5 i5 \<phi> = sat' \<sigma> V v5 i5 \<phi> "   
        using phi_wty Let by auto
    } ultimately show ?thesis by auto
  qed
  have V_eq: "V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v i. Formula.sat \<sigma> V v i \<phi>)) = V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v i. sat' \<sigma> V v i \<phi>))"
    using phi_case by auto
  have "Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v i. Formula.sat \<sigma> V v i \<phi>))) v i \<psi> = sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> (\<lambda>v i. sat' \<sigma> V v i \<phi>))) v i \<psi>"  
    unfolding V_eq
    apply (rule Let.IH(2))
    using psi_wty phi_wty Let.prems apply (auto simp add: wty_envs_def wty_event_def wty_tuple_def domIff)
    subgoal for i a b apply (cases "a = p") by auto
    subgoal for i xs using list_all_tab by auto
    subgoal for i xs using list_all_tab by presburger
    done
  then show ?case by auto
next
  case (And_assign \<phi> \<psi>)
  obtain t1 t2 where eq: "\<psi> = formula.Eq t1 t2" using And_assign(2) by (auto simp add: safe_assignment_def split: formula.splits)
  obtain t where t_def: "E \<turnstile> t1 :: t \<and> E \<turnstile> t2 :: t" using  And_assign(4) by (auto simp add: eq  elim: wty_formula.cases)
  have " Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" using  t_def And_assign(4,5) by (auto simp add: eq dest: poly_value_of )
  then show ?case using And_assign by (auto elim: wty_formula.cases)
next
  case (And_constraint \<phi> \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" using And_constraint by (auto elim: wty_formula.cases)
  have psi_wty: "S, E \<turnstile> \<psi>" using And_constraint(7) by (auto elim: wty_formula.cases)
  show ?case using phi_eq And_constraint(5,8) psi_wty
    by (cases \<psi> rule: is_constraint.cases) 
      (auto simp add: undef_less_eq_sound undef_less_def less_event_data_def 
        dest: poly_value_of  elim!: wty_formula.cases)
next
  case (And_Not \<phi> \<psi>)
  have "S, E \<turnstile> \<psi>" using And_Not.prems(1) by (auto elim: wty_formula.cases)
  then show ?case using And_Not by (auto elim: wty_formula.cases)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  have "S, E \<turnstile> \<psi>'" 
    using And_Trigger.prems(1)
    by (auto elim: wty_formula.cases)
  then show ?case
    using And_Trigger wty_formula_AndD(2)[of S E \<phi>] 
      wty_formula_TriggerD(1)[of S E \<phi>' I \<psi>']
    by (auto elim: wty_formula.cases)
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  have "S, E \<turnstile> and_release_safe_bounded \<phi> \<phi>' I \<psi>'"
    using \<open>S, E \<turnstile> formula.And \<phi> (formula.Release \<phi>' I \<psi>')\<close> 
      wty_formulaD(16,17)[of _ _ \<phi>' I  \<psi>']
      wty_formulaD(4,5)[of S E \<phi>]
    by (auto simp: and_release_safe_bounded_def always_safe_bounded_def
      release_safe_bounded_def Formula.eventually_def once_def 
      intro!: wty_formula.intros)
  thus ?case
    using And_Release.IH
    unfolding sat_and_release_rewrite[OF \<open>bounded I\<close> \<open> \<not> mem I 0 \<close> ]
    unfolding sat'_and_release_rewrite[OF \<open>bounded I\<close> \<open> \<not> mem I 0 \<close> ]
    using \<open>\<forall>y\<in>fv (formula.And \<phi> (formula.Release \<phi>' I \<psi>')). ty_of (v ! y) = E y\<close>
    by (auto intro!: And_Release.IH[OF _ _ \<open>wty_envs S \<sigma> V\<close>])
next
  case (Ands l pos neg)
  have pos_IH: "\<phi> \<in> set pos \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)  \<Longrightarrow>  wty_envs S \<sigma> V
\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> using Ands.IH(1) Ball_set_list_all   by (smt (verit, best))
  have pos_case: "\<phi> \<in> set pos \<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> " for \<phi> using Ands pos_IH by (auto elim: wty_formula.cases)
  have neg_IH: "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y) \<Longrightarrow>  wty_envs S \<sigma> V
\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> using Ands.IH(2) Ball_set_list_all 
    by (smt (verit, best))
  have "\<phi> \<in> set ( neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<and> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> using Ands by (auto elim: wty_formula.cases)
  then have "\<phi> \<in> set ( map remove_neg neg) \<Longrightarrow> S, E \<turnstile> \<phi> \<and> (\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> 
    apply (auto simp add: Formula.nfv_def )
    subgoal for x by (cases x) (auto elim: wty_formula.cases) done
  then have remove_neg_case: "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> " for \<phi> using Ands.prems(3) neg_IH by auto
  have remove_neg_sat: " (Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi> )= ( Formula.sat \<sigma> V v i (remove_neg \<phi>) = sat' \<sigma> V v i (remove_neg \<phi>))  " 
    for \<phi>  by (cases \<phi>)  auto
   have neg_case: "\<phi> \<in> set neg\<Longrightarrow>  Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for \<phi> 
    using  remove_neg_case[of "remove_neg \<phi>"]  by ( auto simp add:  remove_neg_sat[of \<phi>] )    
  then show ?case using pos_case neg_case Ands(1) by auto
next
  case (Exists t \<phi>)
  {
    fix za
    assume assm: "Formula.sat \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,6) assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )
    from this  have "local.sat' \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(6) wty assm by auto
  } moreover {
    fix za
    assume assm: "sat' \<sigma> V (za # v) i \<phi>" 
    from Exists.prems(1) have wty: "S, case_nat t E \<turnstile> \<phi>" by cases
    have "0 \<in> fv \<phi> \<Longrightarrow> ty_of za = t" 
      using ty_of_sat'_safe[where ?E="case_nat t E" and ?S=S and ?\<phi>=\<phi> and ?v="za#v" and ?V=V and ?i=i and ?\<sigma>=\<sigma> and ?x=0]  
      Exists(1,6) assm wty by auto 
    then have "\<forall>y\<in>fv \<phi>. ty_of ((za # v) ! y) = (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> E x)" using  Exists.prems(2)   by (auto simp add:  fvi_Suc split: nat.splits )
    from this  have "Formula.sat \<sigma> V (za # v) i \<phi>" using Exists.IH[of S "case_nat t E" "za#v" V i] Exists(6) wty assm by auto
  }
  ultimately show ?case by auto 
next
  case (Agg y \<omega> tys f \<phi>) 
  have phi_wty: "S, agg_env E tys \<turnstile> \<phi>" using Agg.prems(1) by (auto elim: wty_formula.cases)
  have phi_case: "length zs = length tys \<Longrightarrow> Formula.sat \<sigma> V (zs @ v) i \<phi> =  sat' \<sigma> V (zs @ v) i \<phi>" for zs 
  proof -
    assume len_zs:"length zs = length tys"
    {
      assume sat: " Formula.sat \<sigma> V (zs @ v) i \<phi>"
      have fv_wty: "y \<in> fv \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y
        using ty_of_sat_safe Agg(4,8) sat len_zs phi_wty  by  (auto simp add: Formula.nfv_def)
      have " Formula.sat \<sigma> V (zs @ v) i \<phi> = sat' \<sigma> V (zs @ v) i \<phi> " 
        using phi_wty Agg(4,5,8) len_zs fv_wty by auto 
    } moreover{
      assume sat':"sat' \<sigma> V (zs @ v) i \<phi>"
      have fv_wty: "y \<in> fv \<phi> \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y 
        using ty_of_sat'_safe Agg(4,8) sat' len_zs phi_wty by  (auto simp add: Formula.nfv_def)
      have " Formula.sat \<sigma> V (zs @ v) i \<phi> = sat' \<sigma> V (zs @ v) i \<phi> " 
        using phi_wty Agg(4,5,8) len_zs fv_wty by auto 
    }
    ultimately show ?thesis by auto
  qed
  have "Formula.eval_trm (zs @ v) f = eval_trm' (zs @ v) f"  if a1:"Formula.sat \<sigma> V (zs @ v) i \<phi>" and a2:"length zs = length tys" for zs
  proof -
    have fv_wty: "y\<in>fv_trm f \<Longrightarrow> ty_of ((zs @ v) ! y) = agg_env E tys y" for y 
      using ty_of_sat_safe  Agg(3,4,8) a1 a2 phi_wty by auto 
    show ?thesis using Agg.prems(1) fv_wty by (auto dest: eval_trm_sound elim: wty_formula.cases) 
  qed
  then have 
 "{(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
= {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat' \<sigma> V (zs @ v) i \<phi> \<and> eval_trm' (zs @ v) f = x} \<and> Zs \<noteq> {}}"
    using phi_case  by (smt (z3) Collect_cong) 
  moreover obtain agg_op d where omega_def:"\<omega> = (agg_op,d)" using Agg.prems(1) by cases auto
  moreover have eval_agg_op_case: "M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> Formula.sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
 \<Longrightarrow> eval_agg_op (agg_op,d) M = eval_agg_op' (agg_op,d) M" for M
    apply (rule eval_agg_op_sound) using omega_def Agg(3,4,6,8) by auto 
  ultimately show ?case by auto
next
  case (Since \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i using Since by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Since by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq) 
next
  case (Not_Since \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i apply (rule Not_Since.IH(1)) using Not_Since by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Not_Since by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq)
next
  case (Until \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i using Until by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Until by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq)
next
  case (Not_Until \<phi> I \<psi>)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i apply (rule Not_Until.IH(1)) using Not_Until by (auto elim: wty_formula.cases)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  using Not_Until by (auto elim: wty_formula.cases)
  show ?case by (auto simp add: phi_eq psi_eq) 
next
  case (Trigger_0 \<phi> I \<psi>)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  
    using Trigger_0 by (auto elim: wty_formula.cases)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i 
    using Trigger_0
    apply (cases "\<exists>\<phi>'. \<phi> = Formula.Neg \<phi>'"; clarsimp simp: case_Neg_iff)
    by (smt (verit, ccfv_SIG) ty_of_sat'_safe ty_of_sat_safe wty_formula_NegD wty_formula_TriggerD(1))
      (meson ty_of_sat'_safe ty_of_sat_safe wty_formula_TriggerD(1))
  show ?case
    by (auto simp: phi_eq psi_eq)
next
  case (Trigger \<phi> I \<psi>)
  have psi_eq: "Formula.sat \<sigma> V v i \<psi> = sat' \<sigma> V v i \<psi>" for i  
    using Trigger by (auto elim: wty_formula.cases)
  have phi_eq: "Formula.sat \<sigma> V v i \<phi> = sat' \<sigma> V v i \<phi>" for i 
    using Trigger
    by (clarsimp simp: case_Neg_iff)
  show ?case
    by (auto simp: phi_eq psi_eq)
next
  case (Release_0 \<phi> I \<psi>)
  have "S, E \<turnstile> release_safe_0 \<phi> I \<psi>"
    unfolding release_safe_0_def always_safe_0_def
    using \<open>S, E \<turnstile> formula.Release \<phi> I \<psi>\<close> 
      wty_formulaD(16,17)[of _ _ \<phi> I  \<psi>]
    by (auto intro!: wty_formula.intros)
  thus ?case
    unfolding sat_release_rewrite_0[OF \<open> mem I 0 \<close> \<open>bounded I\<close>]
    unfolding sat'_release_rewrite_0[OF \<open> mem I 0 \<close> \<open>bounded I\<close>]
    using \<open>\<forall>y\<in>fv (formula.Release \<phi> I \<psi>). ty_of (v ! y) = E y\<close>
    by (auto intro!: Release_0.IH[OF _ _ \<open>wty_envs S \<sigma> V\<close>])
next
  case (Release \<phi> I \<psi>)
  then show ?case 
    by clarsimp
next
  case (MatchP I r)
  from  MatchP(1) have "Regex.safe_regex fv rgx_safe_pred Past Strict r \<or> Regex.safe_regex fv rgx_safe_pred Past Lax r " by auto
  from this have atms_safe: " \<phi> \<in> regex.atms r \<Longrightarrow> safe_formula \<phi> \<or> (\<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and> safe_formula \<psi>)" for \<phi>
    using case_NegE  by (induction r) auto
  have atms_regex_atms: " \<phi> \<in> safe_atms r \<or> ( \<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and>  \<psi>\<in> safe_atms r)" if assm: " \<phi> \<in> regex.atms r" for \<phi> 
    using assm atms_safe apply (induction r) by auto
  from MatchP(4) have  " (\<phi> \<in> safe_atms r \<Longrightarrow>\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> 
    apply auto apply (induction r) 
        apply (auto) subgoal for x y apply (cases "safe_formula x") by (auto split: formula.splits  ) done
  from this  MatchP have IH: "\<phi> \<in> safe_atms r \<Longrightarrow>Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5
    using match_safe_wty_nfv[of \<phi> r I S E] by auto
  have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5 
    using atms_regex_atms[of \<phi>] IH by auto 
  then show ?case  using match_cong[OF refl other_IH, where ?r=r] by auto 
next
  case (MatchF I r)
  from  MatchF(1) have "Regex.safe_regex fv rgx_safe_pred Futu Strict r 
  \<or> Regex.safe_regex fv rgx_safe_pred Futu Lax r " by auto
  from this have atms_safe: " \<phi> \<in> regex.atms r \<Longrightarrow> safe_formula \<phi> \<or> (\<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and> safe_formula \<psi>)" for \<phi>
    using case_NegE  by (induction r) auto
  have atms_regex_atms: " \<phi> \<in> safe_atms r \<or> ( \<exists> \<psi>. \<phi> = Formula.Neg \<psi> \<and>  \<psi>\<in> safe_atms r)" 
    if assm: " \<phi> \<in> regex.atms r" for \<phi> 
    using assm atms_safe apply (induction r) by auto
  from MatchF(4) have  " (\<phi> \<in> safe_atms r \<Longrightarrow>\<forall>y\<in>fv \<phi>. ty_of (v ! y) = E y)" for \<phi> 
    apply auto apply (induction r ) 
        apply (auto) subgoal for x y apply (cases "safe_formula x") by (auto split: formula.splits  ) done
  from this  MatchF have IH: "\<phi> \<in> safe_atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5
    using match_safe_wty_nfv[of \<phi> r I S E] by auto
  have other_IH: "\<phi> \<in> regex.atms r \<Longrightarrow> Formula.sat \<sigma> V v i5 \<phi> = sat' \<sigma> V v i5 \<phi>" for \<phi> i5 
    using atms_regex_atms[of \<phi>] IH by auto 
  then show ?case using match_cong[OF refl other_IH, where ?r=r] by auto 
next
  case (LetPast p \<phi> \<psi>)
  obtain E' where 
    psi_wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E \<turnstile> \<psi>" and
    phi_wty: "S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>)), E' \<turnstile> \<phi>" using LetPast.prems(1) by cases auto
  have wtyenv: "x \<in> \<Gamma> \<sigma> i \<Longrightarrow> (case x of (p, xs) \<Rightarrow> (p, length xs) \<notin> dom V \<longrightarrow> (case S (p, length xs) of None \<Rightarrow> False | Some ts \<Rightarrow> wty_tuple ts xs))" for x i
    using LetPast.prems(3) by (auto simp add: wty_envs_def wty_event_def wty_tuple_def) 
  let ?V' = "(V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)))"
  let ?V'' = "(V((p, Formula.nfv \<phi>) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)))"
  have wty_envs: "wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>))) \<sigma> ?V'"
    using wty_envs_update[OF LetPast(3) LetPast(9) phi_wty LetPast(2)] ty_of_sat'_safe[OF LetPast(3)] by blast
  then have wty_envs': "wty_envs (S((p, Formula.nfv \<phi>) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>))) \<sigma>
 (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. j < i \<and> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j))" for i
    unfolding wty_envs_def by(auto simp:domI) 
  have "(letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v i =
        (letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v i" for v i
  proof(induction i arbitrary: v rule:less_induct)
    case (less x)
    then show ?case
    proof -
      assume "(\<And>y v. y < x \<Longrightarrow>
          letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v y =
          letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v y)"
      then have eq: "(\<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j) =
             (\<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j)"
        by auto
      {
        assume sat: "(letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v x"
        have *: "Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j)) v x \<phi>"
          using iffD1[OF letpast_sat.simps sat] LetPast(5)[OF phi_wty _ wty_envs', of v x x]
          ty_of_sat'_safe[OF LetPast(3) phi_wty wty_envs' iffD1[OF letpast_sat.simps sat]] unfolding eq by blast
        have "letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v x" 
          using iffD1[OF letpast_sat.simps[of "(\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)", symmetric], OF *] by auto
      } moreover {
        assume sat: "letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) v x"
        have *: "sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> \<lambda>w j. j < x \<and> letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>) w j)) v x \<phi>"
          using ty_of_sat_safe[OF LetPast(3) phi_wty wty_envs', of x, unfolded eq, OF iffD1[OF letpast_sat.simps sat]]
            iffD1[OF letpast_sat.simps sat] LetPast(5)[OF phi_wty _ wty_envs', of v x x]  unfolding eq by blast
        have "(letpast_sat (\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)) v x" 
          using iffD1[OF letpast_sat.simps[of "(\<lambda>X v i. sat' \<sigma> (V((p, Formula.nfv \<phi>) \<mapsto> X)) v i \<phi>)", symmetric], OF *] by auto
      } ultimately show ?thesis by fastforce
    qed
  qed
  then have V_eq: "?V' = ?V''" by force
  have "Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>" unfolding V_eq[symmetric] 
  proof -
    {
      assume sat: " Formula.sat \<sigma> ?V' v i \<psi>"
      have "Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>" 
        using ty_of_sat_safe[OF LetPast(4) psi_wty wty_envs sat] LetPast(6)[OF psi_wty _ wty_envs] by blast
    } moreover {
      assume sat': "sat' \<sigma> ?V' v i \<psi>"
      have " Formula.sat \<sigma> ?V' v i \<psi> = sat' \<sigma> ?V' v i \<psi>"   
        using ty_of_sat'_safe[OF LetPast(4) psi_wty wty_envs sat'] LetPast(6)[OF psi_wty _ wty_envs] by blast
    } ultimately show ?thesis by auto
  qed
  then have "Formula.sat \<sigma> ?V'' v i \<psi> = sat' \<sigma> ?V' v i \<psi>" unfolding V_eq[symmetric] by auto
  then show ?case by(auto simp:Let_def)
next
  case (TP t)
  then show ?case by(auto simp:trm.is_Var_def trm.is_Const_def) 
next
  case (TS t)
  then show ?case by(auto simp:trm.is_Var_def trm.is_Const_def)
qed (auto elim: wty_formula.cases split: nat.splits)

lemma soundness2: (*Theorem 3.12*)
  assumes 
    "safe_formula \<phi>"
    "S,E \<turnstile> \<phi>"
    "wty_envs S \<sigma> V"
  shows "Formula.sat \<sigma> V v i \<phi> \<longleftrightarrow> sat' \<sigma> V v i \<phi>" 
  using  soundness[OF assms(1-2) _ assms(3)]
    ty_of_sat_safe[OF assms(1-3), of v i]
    ty_of_sat'_safe[OF assms(1-3), of v i] 
  by auto

end
end