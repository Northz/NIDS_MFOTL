(*<*)
theory Trigger_Release_Rewrites
  imports
    Event_Data
    Formula
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
begin
(*>*)

lemma interval_unbounded_leq:
  assumes "j \<le> i" "k \<le> j"
  assumes "\<not> bounded I" (* [a, \<infinity>] *)
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" (* if j\<le>i is part of the interval, then so is k\<le>j\<le>i *)
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  have "\<tau> \<sigma> j \<ge> \<tau> \<sigma> k" using assms by auto
  then have "\<tau> \<sigma> i - \<tau> \<sigma> j \<le> \<tau> \<sigma> i - \<tau> \<sigma> k" by linarith
  then have "memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms
    by auto
  then show ?thesis using bounded_memR assms by auto
qed

lemma interval_unbounded_geq:
  assumes "i \<le> j" "j \<le> k"
  assumes "\<not> bounded I" (* [a, \<infinity>] *)
  assumes "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" (* if j\<le>i is part of the interval, then so is k\<le>j\<le>i *)
  shows "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" using assms by auto
  then have "\<tau> \<sigma> j - \<tau> \<sigma> i \<le> \<tau> \<sigma> k - \<tau> \<sigma> i" by linarith
  then have "memL I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using assms
    by auto
  then show ?thesis using bounded_memR assms by auto
qed

lemma interval_0_bounded_geq:
  assumes "j \<le> i" "j \<le> k"
  assumes "mem I 0" "bounded I" (* [0, a] *)
  assumes "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" (* if j\<le>i is part of the interval, then so is j\<le>k\<le>i *)
  shows "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
proof -
  have "\<tau> \<sigma> j \<le> \<tau> \<sigma> k" using assms by auto
  then have ineq: "\<tau> \<sigma> i - \<tau> \<sigma> j \<ge> \<tau> \<sigma> i - \<tau> \<sigma> k" by linarith
  then have "memR I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms
    by (transfer' fixing: \<sigma>) (auto split: if_splits)
  moreover have "memL I (\<tau> \<sigma> i - \<tau> \<sigma> k)" using ineq assms
    by (transfer' fixing: \<sigma>) (auto split: if_splits)
  ultimately show ?thesis by auto
qed

lemma flip_int_props:
  assumes "bounded I"
  assumes "I' = flip_int I"
  shows "\<not>bounded I' \<and> \<not>mem I' 0"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_props:
  assumes "\<not>memL I 0" (* [a, b] *)
  assumes "I' = flip_int_less_lower I" (* [0, a] *)
  shows "mem I' 0 \<and> bounded I'"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_mem:
  assumes "\<not>bounded I" "\<not>mem I x" (* [a, \<infinity>], x < a *)
  shows "mem (flip_int_less_lower I) x" (* x \<in> [0, a] *)
  using assms
  by (transfer') (simp add: bounded_memR)

lemma int_flip_mem:
  assumes "bounded I" "mem I 0" "\<not>mem I x" (* [0, a], a<x *)
  shows "mem (flip_int I) x" (* [a, \<infinity>] *)
  using assms memL_mono
  by (transfer') (auto split: if_splits)

lemma flip_int_double_upper_leq:
  assumes "mem (flip_int_double_upper I) x" (* x \<in> [b+1, 2b] *)
  assumes "\<not> mem (flip_int_double_upper I) y" "y\<le>x" (* y \<notin> [b+1, 2b] and y \<le> x *)
  assumes "mem I 0"
  shows "mem I y"
proof -
  from assms(2) have "\<not>memL (flip_int_double_upper I) y \<or> \<not>memR (flip_int_double_upper I) y" by auto
  moreover have "\<forall>m. m \<le> x \<longrightarrow> memR (flip_int_double_upper I) m" using assms(1) by auto
  ultimately have "\<not>memL (flip_int_double_upper I) y" using assms(3) by auto
  then show "mem I y" using assms(4) by (transfer') (auto split: if_splits)
qed

lemma historically_rewrite_0:
  fixes I1 :: \<I>
  assumes "mem I1 0"
  shows "Formula.sat \<sigma> V v i (Formula.Historically I1 \<phi>) = Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int I1"
  assume hist: "Formula.sat \<sigma> V v i (Formula.Historically I1 \<phi>)"
  {
    define A where "A = {j. j\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
    define j where "j = Max A"
    assume int_bound: "bounded I1" "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using A_def by auto
    {
      fix k
      assume k_props: "j<k" "k\<le>i" 
      {
        assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        then have "False" using A_props k_props j_def A_def by auto
      }
      then have "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" by blast
      then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using assms I2_def
        by (transfer' fixing: \<sigma>) (auto split: if_splits)
    }
    then have "\<forall>k\<in>{j<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" by auto
    then have "\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<phi>" using hist by auto
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 Formula.TT)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>))"
      using since_true int_bound I2_def flip_int_props
      by simp
  }
  moreover {
    assume unbounded: "\<not>bounded I1"
    then have mem_leq_j: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms
      using bounded_memR memL_mono
      by blast
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using mem_leq_j hist
      by auto
  }
  moreover {
    assume "\<forall>j\<le>i. \<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then have mem_leq_j: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms I2_def
      by (transfer' fixing: \<sigma>) (auto split: if_splits)
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using mem_leq_j hist
      by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
    using I2_def historically_safe_0_def
    by auto
next
  define I2 where "I2 = flip_int I1"
  assume hist: "Formula.sat \<sigma> V v i (historically_safe_0 I1 \<phi>)"
  {
    assume int_bounded: "bounded I1"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<phi> I2 (Formula.Next all \<phi>)) (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>)))"
      using I2_def historically_safe_0_def hist
      by simp
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>)) \<or> Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))" by auto
    moreover {
      assume since: "Formula.sat \<sigma> V v i (Formula.Since \<phi> I2 (Formula.Next all \<phi>))"
      then have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>))" by auto
      then obtain j where j_props: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> (\<forall>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
      {
        fix k
        assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        {
          assume "k\<le>j"
          then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j" by simp
          then have "\<tau> \<sigma> i - \<tau> \<sigma> k \<ge> \<tau> \<sigma> i - \<tau> \<sigma> j" by auto
          then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using j_props I2_def
            by (transfer' fixing: \<sigma>) (auto split: if_splits dest: memR_antimono)
          then have "False" using int_bounded k_props I2_def
            by (transfer' fixing: \<sigma>) (auto split: if_splits)
        }
        then have "\<not>(k\<le>j)" by blast
        then have "Formula.sat \<sigma> V v k \<phi>" using k_props j_props by auto
      }
      then have "Formula.sat \<sigma> V v i (Formula.Historically I1 \<phi>)" by auto
    }
    moreover {
      assume "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      then have "Formula.sat \<sigma> V v i (Formula.Historically I1 \<phi>)" by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Historically I1 \<phi>)" by blast
  }
  moreover {
    assume "\<not>bounded I1"
    then have "Formula.sat \<sigma> V v i (Formula.Since \<phi> I1 (Formula.And Formula.first \<phi>))"
      using historically_safe_0_def hist
      by simp
    then have "Formula.sat \<sigma> V v i (Formula.Historically I1 \<phi>)" by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Historically I1 \<phi>)" by blast
qed

lemma historically_rewrite_unbounded:
  assumes "\<not> mem I1 0" "\<not> bounded I1" (* [a, \<infinity>] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Historically I1 \<phi>)) = Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1"
  assume historically: "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Historically I1 \<phi>))"
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>}"
  define j where "j = Max A"
  have "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>" using historically by auto
  then have A_props: "finite A" "A \<noteq> {}" using A_def by auto
  then have "j \<in> A" using j_def by auto
  then have j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" using A_def by auto
  {
    fix k
    assume k_props: "k\<le>j"
    then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      using assms(2) j_props(1-2) interval_unbounded_leq[of j i k I1 \<sigma>]
      by auto
    then have first_sat: "Formula.sat \<sigma> V v k \<phi>" 
      using j_props k_props historically assms(1-2) 
      by auto
  }
  then have leq_j: "\<forall>k\<le>j. Formula.sat \<sigma> V v k \<phi>" by auto
  define B where "B = {k. k\<le>i \<and> mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)}"
  define k where "k = Min B"
  have "mem I2 0"
    using assms I2_def
    by (transfer') (auto split: if_splits)
  then have B_props: "B \<noteq> {}" "finite B" using B_def by auto
  then have k_in_B: "k \<in> B" using k_def by auto
  then have k_props: "k\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using B_def by auto
  {
    assume "k=0"
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
      using k_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of k i j I2 \<sigma>] I2_def
      by auto
    then have "False"
      using assms j_props I2_def
      by (transfer') (auto split: if_splits)
  }
  then have k_pos: "k>0" by blast
  {
    assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))"
    then have "(k-1) \<in> B" using B_def k_props by auto
    then have "(k-1) \<ge> k" using B_props k_def by auto
    then have "False" using k_pos by auto
  }
  then have "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))" by blast
  then have k_pre: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (k-1))"
    using assms flip_int_less_lower_mem I2_def
    by auto
  then have "Formula.sat \<sigma> V v (k-1) \<phi>" using historically k_props by auto
  then have "(k-1) \<in> A" using A_def k_pre k_props by auto
  then have "(k-1) \<le> j" using j_def A_props by auto
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))))"
    using interval_all k_pos leq_j k_props
    by (auto split: nat.split)
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) \<and> Formula.sat \<sigma> V v i (once I1 \<phi>)"
    using historically
    by auto
  then show "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
    using assms historically_safe_unbounded_def I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1"
  define A where "A = {j. j\<le>i \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)}"
  assume "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) (once I1 \<phi>))"
    using assms historically_safe_unbounded_def I2_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.And (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))) (once I1 \<phi>))"
    by auto
  then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))))" by auto
  then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))"
    by auto
  then obtain j where j_props:
    "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))"
    by blast
  {
    assume "j = 0"
    then have "\<not>Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<phi> all (Formula.And \<phi> Formula.first)))" by auto
    then have "False" using j_props by auto
  }
  then have j_pos: "j \<noteq> 0" by auto
  then have j_pred_sat: "Formula.sat \<sigma> V v (j-1) (Formula.Since \<phi> all (Formula.And \<phi> Formula.first))"
    using j_pos j_props
    by (simp add: Nitpick.case_nat_unfold)
  {
    fix x
    assume x_props: "x>j-1"
    then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" using x_props by auto
    then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using j_props assms flip_int_less_lower_props[of I1 I2] interval_0_bounded_geq[of j i x I2] I2_def
      by auto
    then have "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      using assms I2_def
      by (transfer') (auto split: if_splits)
  }
  then have x_greater: "\<forall>x>(j-1). \<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by blast
  {
    fix x
    assume x_props: "x\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
    {
      assume "x>(j-1)"
      then have "False" using x_props x_greater by auto
    }
    then have "\<not>(x>j-1)" by blast
    then have "x\<le>(j-1)" by auto
  }
  then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> x\<le>j-1" by blast
  then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<phi>" using j_pred_sat by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Historically I1 \<phi>))" using rewrite by auto
qed

lemma historically_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b], a>0 *)
  (*
    [0, b-a] would be more efficient but this interval can
    (probably) not be constructed using the current
    implementation of intervals.
  *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Historically I1 \<phi>)) = Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Historically I1 \<phi>))"
  then show "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
    using assms historically_safe_bounded_def
    by auto
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Neg (once I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def historically_safe_bounded_def
    by auto
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" by auto
  have j_leq_i_sat: "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> (Formula.sat \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    then have "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v k \<phi>"
      using j_leq_i_sat by auto
    moreover {
      assume assm: "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" using assm by auto
      have j_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)"
          using j_props assms(1-2)
          by auto
      have k_int: "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
          using k_props assms(1-2)
          by auto
      {
        assume k_geq_j: "k\<ge>j"
        then have "memR I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j)"
          using j_int k_int assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms leq_k_sat j_props k_geq_j by auto
      }
      moreover {
        assume k_less_j: "\<not>(k\<ge>j)"
        then have "memR I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)"
          using j_int k_int assms I2_def
          by (metis diff_le_mono int_remove_lower_bound.rep_eq le_eq_less_or_eq memR.rep_eq memR_antimono neq0_conv prod.sel(1) prod.sel(2) zero_less_diff)
        then have "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k)" using assms I2_def
          by (simp add: int_remove_lower_bound.rep_eq memL.rep_eq)
        then have "False" using assms geq_k_sat j_props k_less_j by auto
      }
      ultimately have "False" by blast
    }
    ultimately have "Formula.sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<phi>" by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 \<phi>) (Formula.Historically I1 \<phi>))" using rewrite by auto
qed

lemma sat_trigger_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
  assumes leq: "j\<le>i"
  assumes mem_j: "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
  shows "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {j<..i}. Formula.sat \<sigma> V v x \<phi>}"
  define k where "k = Max A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {j<..i}" "Formula.sat \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "\<forall>l>k. l \<notin> A"
    using Max_ge[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
    using mem mem_j k_props interval_geq[of I 0 \<sigma> i j k]
    by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat_trigger_rewrite_0:
  assumes "mem I 0"
shows "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>) = Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  moreover {
    define A where "A = {j. j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Max A"
    assume "\<not>(\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "\<not>Formula.sat \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    then have "\<not>Formula.sat \<sigma> V v j' \<psi> \<or> Formula.sat \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>Formula.sat \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {j'<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> k) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms trigger sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {j<..i} \<and> \<not> Formula.sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)"
        using assms j_props interval_geq[of I 0 \<sigma> i j k]
        by auto
      then have "\<exists>x \<in> {k<..i}. mem I (\<tau> \<sigma> i - \<tau> \<sigma> x) \<and> Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms trigger k_props sat_trigger_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {k<..i}" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> x)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<le> Max A"
        using A_def A_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {j<..i}. Formula.sat \<sigma> V v k \<psi>" by blast
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Historically I (Formula.And \<psi> (Formula.Neg \<phi>))))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<le> i \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>}"
      define k where "k = Max B"
      assume "Formula.sat \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> k)" "Formula.sat \<sigma> V v k \<phi>" using B_def by auto
      have "\<forall>l>k. l \<notin> B"
        using Max_ge[OF B_props(2)]
        by (fastforce simp: k_def)
      {
        fix l
        assume l_props: "l \<in> {k<..i}"
        then have l_mem: "mem I (\<tau> \<sigma> i - \<tau> \<sigma> l)"
          using assms k_props interval_geq[of I 0 \<sigma> i k l]
          by auto
        {
          assume "Formula.sat \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem by auto
          then have "l\<le>k" "l>k"
            using k_def l_props B_props(2) Max_ge[of B l]
            by auto
        }
        then have "\<not>Formula.sat \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{k<..i}. \<not>Formula.sat \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "Formula.sat \<sigma> V v k \<psi>" using k_props trigger B_def by auto
      {
        fix l
        assume l_props: "l\<in>{k<..i}"
        then have "mem I (\<tau> \<sigma> i - \<tau> \<sigma> l)"
          using k_props assms interval_geq[of I 0 \<sigma> i k l]
          by auto
        then have "Formula.sat \<sigma> V v l \<psi>"
          using l_props trigger not_phi
          by auto
      }
      then have "\<forall>l\<in>{k<..i}. Formula.sat \<sigma> V v l \<psi>"
        using not_phi assms trigger
        by auto
      then have "Formula.sat \<sigma> V v i (Formula.Since \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Historically I (Formula.And \<psi> (Formula.Neg \<phi>))))" by blast
  then show "Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
    using assms historically_rewrite_0[of I \<sigma> V v i "(Formula.And \<psi> (Formula.Neg \<phi>))"] trigger_safe_0_def
    by auto
next
  assume "Formula.sat \<sigma> V v i (trigger_safe_0 \<phi> I \<psi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Since \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Historically I (Formula.And \<psi> (Formula.Neg \<phi>))))"
    using trigger_safe_0_def assms historically_rewrite_0[of I \<sigma> V v i "(Formula.And \<psi> (Formula.Neg \<phi>))"]
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Historically I (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)"
      by auto
  }
  moreover {
    fix j
    assume since_and_j_props: "Formula.sat \<sigma> V v i (Formula.Since \<psi> I (Formula.And \<phi> \<psi>))" "j \<le> i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)"
    then obtain "j'" where j'_props:
      "j'\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j')" "Formula.sat \<sigma> V v j' (Formula.And \<phi> \<psi>)"
      "(\<forall>k \<in> {j' <.. i}. Formula.sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume le: "j' < j"
      then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
        using j'_props since_and_j_props le
        by auto
    }
    moreover {
      assume geq: "\<not> j' < j"
      moreover {
        assume "j = j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)"
          using geq j'_props
          by auto
      }
      ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I \<psi>)" by auto
qed

lemma sat_trigger_rewrite:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" (* [a, b] *)
  assumes "I2 = flip_int_less_lower I1" (* [0, a-1] *)
shows "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>) = Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
proof (rule iffI)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)"
  {
    assume "\<forall>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> all (Formula.And \<phi> \<psi>)))))" by auto
  }
  moreover {
    assume "\<exists>j\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> \<not>Formula.sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "\<not>Formula.sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{j <.. i} \<and> Formula.sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Max A"
    have "(\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" using j_props trigger by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{j <.. i}" "Formula.sat \<sigma> V v k \<phi>" using A_def by auto
    {
      fix x
      assume x_props: "x\<ge>j" "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      {
        assume k_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
        have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" using x_props by auto
        then have "\<tau> \<sigma> i - \<tau> \<sigma> x \<le> \<tau> \<sigma> i - \<tau> \<sigma> j" by auto
        moreover have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" using assms j_props by auto 
        ultimately have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using memR_antimono by blast
        moreover have "memL I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
          using x_props assms
          by (metis flip_int_less_lower.rep_eq memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
        ultimately have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using assms by auto
        then have "False" using k_not_mem_1 by auto
      }
      then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by auto
    }
    then have geq_j_mem: "\<forall>x\<ge>j. \<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" by auto
    {
      assume "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> k)"
      then have k_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> k)" using geq_j_mem k_props by auto
      then have "Formula.sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {k <.. i}. Formula.sat \<sigma> V v k \<phi>)" using trigger k_props by auto
      moreover {
        assume "(\<exists>k \<in> {k <.. i}. Formula.sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {k <.. i}" "Formula.sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "Formula.sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_since: "Formula.sat \<sigma> V v k (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using int_remove_lower_bound.rep_eq memL.rep_eq by auto
      {
        assume "k=i"
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] assms k_mem
          by auto
      }
      moreover {
        assume "\<not>(k=i)"
        then have k_suc_leq_i: "k+1\<le>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
          then have "Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>)" using trigger by auto
          moreover {
            assume "\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {x <.. i}" "Formula.sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<le> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{k<..i}. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          moreover have "Formula.sat \<sigma> V v (k+1) (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_suc_leq_i k_since interval_all
            by auto
          ultimately have "(\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_suc_leq_i
            by blast
          then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{k<..i} \<and> mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<and> Formula.sat \<sigma> V v l \<psi>}"
          define c where "c = Max B"
          assume "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (k+1))" using geq_j_mem k_props by auto
          then have "Formula.sat \<sigma> V v (k+1) \<psi> \<or> (\<exists>x \<in> {k+1 <.. i}. Formula.sat \<sigma> V v x \<phi>)" using trigger k_suc_leq_i by auto
          moreover {
            assume "\<exists>x \<in> {k+1 <.. i}. Formula.sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {k+1 <.. i} \<and> Formula.sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<le> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v (k+1) \<psi>" by auto
          then have B_props: "B \<noteq> {}" "finite B" using B_def k_suc_leq_i k_suc_mem k_props by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{k<..i}" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> c)" "Formula.sat \<sigma> V v c \<psi>"
            using B_def
            by auto
          then have k_cond: "k\<le>c" "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
          {
            fix x
            assume x_props: "x\<in>{k<..c}"
            then have "\<tau> \<sigma> x \<le> \<tau> \<sigma> c" by auto
            then have lower: "(\<tau> \<sigma> i - \<tau> \<sigma> x) \<ge> (\<tau> \<sigma> i - \<tau> \<sigma> c)" by linarith
            have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> k" using x_props by auto
            then have upper: "(\<tau> \<sigma> i - \<tau> \<sigma> x) \<le> (\<tau> \<sigma> i - \<tau> \<sigma> k)" by linarith
            then have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
              using k_mem memR_antimono by blast
            then have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using assms c_props lower by auto
            then have "Formula.sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{k<..c}. Formula.sat \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> c - \<tau> \<sigma> k)"
            using k_mem c_props
          by (metis diff_is_0_eq diff_self_eq_0 greaterThanAtMost_iff int_remove_lower_bound.rep_eq interval_leq memL.rep_eq memR.rep_eq prod.sel(1-2))
          ultimately have c_sat: "Formula.sat \<sigma> V v c (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using k_cond
            by auto
          {
            assume "(c+1) \<in> B"
            then have "c+1\<le>c" using c_def B_props by auto
            then have "False" by auto
          }
          then have "(c+1) \<notin> B" by blast
          then have disj: "(c+1)\<notin>{k<..i} \<or> \<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>Formula.sat \<sigma> V v (c+1) \<psi>" using B_def by blast
          {
            assume "(c+1)\<notin>{k<..i}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c+1)\<notin>{k<..i})"
            then have c_suc_leq_i: "(c+1)\<in>{k<..i}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1)) \<or> \<not>Formula.sat \<sigma> V v (c+1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
              then have "\<not>Formula.sat \<sigma> V v (c+1) \<psi>" using disj by blast
              then have "False"
                using k_greater_sat c_suc_leq_i c_suc_mem
                by auto
            }
            moreover {
              assume c_suc_not_mem_1: "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
              {
                assume not_mem2: "\<not>mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                then have upper: "\<not>memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                  using c_suc_not_mem_1 assms geq_j_mem k_cond k_props
                  by auto
                have "\<tau> \<sigma> c \<le> \<tau> \<sigma> (c+1)" by auto
                then have "\<tau> \<sigma> i - \<tau> \<sigma> c \<ge> \<tau> \<sigma> i - \<tau> \<sigma> (c+1)" using diff_le_mono2 by blast
                moreover have "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> c)" using c_props assms by auto
                ultimately have "memR I1 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))"
                  using not_mem2 memR_antimono
                  by blast
                then have "False" using upper by auto
              }
              then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" by blast
              then have "(c+1)\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> (c+1))" "Formula.sat \<sigma> V v (c+1) (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_suc_leq_i c_sat interval_all
                by auto
              then have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat_once
                by blast
            }
            ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by auto
next
  assume "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
  then have "Formula.sat \<sigma> V v i (Formula.Historically I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Historically I1 \<psi>)"
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (once I2 \<phi>)"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<phi>" by blast
    {
      fix x
      assume x_props: "x\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x)"
      {
        assume j_leq_x: "x\<ge>j"
        then have "\<tau> \<sigma> x \<ge> \<tau> \<sigma> j" by auto
        then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> x)" using j_leq_x j_props assms
          using flip_int_less_lower_props interval_0_bounded_geq memR_zero
          by blast
        then have "False"
          using x_props assms flip_int_less_lower.rep_eq memR.rep_eq memR_zero
          by auto
      }
      then have "\<not>(x\<ge>j)" by blast
      then have "x<j" by auto
    }
    then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> x<j" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume since: "Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<le>i. mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<le>i" "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    {
      assume "j = 0"
      then have "\<not>Formula.sat \<sigma> V v j (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
      then have "False" using j_props by auto
    }
    then have j_pos: "j>0" by auto
    then have j_pred_sat: "Formula.sat \<sigma> V v (j-1) (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
      using j_pos j_props
      by (simp add: Nitpick.case_nat_unfold)
    then have "\<exists>x\<le>(j-1). Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{x<..(j-1)}. Formula.sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<le>(j-1)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{x<..(j-1)}. Formula.sat \<sigma> V v k \<psi>"
      by blast
    {
      fix l
      assume l_props: "l\<le>i"
      {
        assume "l<x"
        then have "\<exists>k \<in> {l <.. i}. Formula.sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l<x)" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
        then have l_props: "x\<le>l" "l\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)" using l_props by auto
        {
          assume "l\<le>(j-1)"
          then have "Formula.sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<le>(j-1)"
          then have l_geq: "l\<ge>(j-1)" by auto
          have j_pred_psi: "Formula.sat \<sigma> V v (j-1) \<psi>" using j_pred_sat by auto
          {
            assume l_greater: "l>(j-1)"
            then have "\<tau> \<sigma> l \<ge> \<tau> \<sigma> j" by auto
            then have "mem I2 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
              using assms j_props j_pos l_greater flip_int_less_lower_props interval_0_bounded_geq
              by (metis One_nat_def Suc_pred le_simps(3) memR_zero)
            then have "\<not>mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l)"
              using assms flip_int_less_lower.rep_eq memR.rep_eq memR_zero
              by auto
            then have "False" using l_assms by auto
          }
          then have "l=(j-1)" using l_geq le_eq_less_or_eq by blast
          then have "Formula.sat \<sigma> V v l \<psi>" using j_pred_psi by blast
        }
        ultimately have "Formula.sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> l) \<longrightarrow> Formula.sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {l <.. i}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<le>i. mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> x) \<longrightarrow> Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {x <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Trigger \<phi> I1 \<psi>)" by blast
qed

lemma sat_trigger_rewrite_unbounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "\<not>bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
  have disj: "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using trigger assms I2_def sat_trigger_rewrite
      by auto
  {
    assume "Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (once I1 \<psi>)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      using disj assms historically_rewrite_unbounded[of I1 \<sigma> V v i \<psi>]
    by simp
  }
  moreover {
    assume "\<not>Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (once I2 \<phi>) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using disj j_props
      by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_unbounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      by simp
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_unbounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using trigger
    by auto
  then show "Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
    using trigger_safe_unbounded_def[of \<phi> I1 \<psi>] assms I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (trigger_safe_unbounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_unbounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def trigger_safe_unbounded_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
    using assms historically_rewrite_unbounded[of I1 \<sigma> V v i \<psi>]
    by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
    using assms I2_def sat_trigger_rewrite assm
    by auto
qed

lemma sat_trigger_rewrite_bounded:
  fixes I1 I2 :: \<I>
  assumes "\<not>mem I1 0" "bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume trigger: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
  then obtain j where j_props: "j\<le>i" "mem I1 (\<tau> \<sigma> i - \<tau> \<sigma> j)" "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. Formula.sat \<sigma> V v k \<phi>)" by auto
  have disj: "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using trigger assms I2_def sat_trigger_rewrite
      by auto
  {
    assume "Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (once I1 \<psi>)" using j_props by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      using disj assms historically_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
    by simp
  }
  moreover {
    assume "\<not>Formula.sat \<sigma> V v j \<psi>"
    then have "Formula.sat \<sigma> V v i (Formula.Or (once I2 \<phi>) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      using disj j_props
      by auto
    then have "Formula.sat \<sigma> V v i (historically_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (once I2 \<phi>) \<or> Formula.sat \<sigma> V v i (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
      by simp
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_bounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using trigger
    by auto
  then show "Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
    using trigger_safe_bounded_def[of \<phi> I1 \<psi>] assms I2_def
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (trigger_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Or (Formula.Or (historically_safe_bounded I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def trigger_safe_bounded_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (Formula.Historically I1 \<psi>) (once I2 \<phi>)) (once I2 (Formula.Prev all (Formula.Since \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
    using assms historically_rewrite_bounded[of I1 \<sigma> V v i]
    by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (once I1 Formula.TT) (Formula.Trigger \<phi> I1 \<psi>))"
    using assms I2_def sat_trigger_rewrite assm
    by auto
qed

lemma always_rewrite_0:
  fixes I :: \<I>
  assumes "mem I 0" "bounded I"
  shows "Formula.sat \<sigma> V v i (Formula.Always I \<phi>) = Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)"
proof (rule iffI)
  assume all: "Formula.sat \<sigma> V v i (Formula.Always I \<phi>)"
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
      then have "Formula.sat \<sigma> V v k \<phi>" using k_props all by auto
    }
    then have until_j: "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>" by blast
    have "\<not> mem (flip_int_double_upper I) 0"
      using assms
      by (simp add: flip_int_double_upper.rep_eq memL.rep_eq)
    then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>))"
      using j_props until_j until_true[of "(flip_int_double_upper I)" \<sigma> V v i \<phi>]
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
    have "\<forall>x. \<exists>j\<ge>i. x \<le> \<tau> \<sigma> j" using Suc_le_lessD ex_le_\<tau> by blast
    then have exists_db: "\<forall>x. \<exists>j\<ge>i. x \<le> \<tau> \<sigma> j - \<tau> \<sigma> i" using nat_move_sub_le by blast
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
    then have c_pred_sat: "Formula.sat \<sigma> V v (c-1) \<phi>" using all c_ge_i by auto
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
    then have c_pred_sat: "Formula.sat \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      using c_pred_sat c_ge_i
      by auto
    have "\<forall>j\<in>{i..<(c-1)}. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
      by (meson \<tau>_mono assms(1) atLeastLessThan_iff c_pred_mem diff_le_mono le_eq_less_or_eq memL_mono memR_antimono zero_le)
    then have "\<forall>j\<in>{i..<(c-1)}. Formula.sat \<sigma> V v j \<phi>" using all by auto
    then have
        "(c-1)\<ge>i"
        "mem I (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
        "Formula.sat \<sigma> V v (c-1) (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
        "(\<forall>k \<in> {i ..< (c-1)}. Formula.sat \<sigma> V v k \<phi>)"
      using c_ge_i c_pred_mem c_pred_sat
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
      by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    by auto
  then show "Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)" using always_safe_0_def by auto
next
  assume "Formula.sat \<sigma> V v i (always_safe_0 I \<phi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<phi> (flip_int_double_upper I) (Formula.Prev all \<phi>)) (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))))"
    using always_safe_0_def
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT) \<or> Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))" by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Until \<phi> (flip_int_double_upper I) Formula.TT)"
    then obtain j where j_props:
      "j\<ge>i" "mem (flip_int_double_upper I) (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>"
      by auto
    then have "\<forall>k\<ge>i. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<longrightarrow> k<j"
      by (metis (no_types, lifting) assms flip_int_double_upper.rep_eq forall_finite(1) interval_leq leI memL.rep_eq prod.sel(1))
    then have "Formula.sat \<sigma> V v i (Formula.Always I \<phi>)" using j_props by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Until \<phi> I (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT)))"
    then obtain j where j_props:
      "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j (Formula.And \<phi> (Formula.Next (flip_int I) Formula.TT))"
      "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<phi>"
      by auto
    then have phi_sat: "\<forall>k\<in>{i..j}. Formula.sat \<sigma> V v k \<phi>" by auto
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
    then have "Formula.sat \<sigma> V v i (Formula.Always I \<phi>)" using phi_sat by auto
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Always I \<phi>)" by blast
qed

lemma always_rewrite_bounded:
  fixes I1 :: \<I>
  assumes "bounded I1" (* [a, b] *)
  shows "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Always I1 \<phi>)) = Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
proof (rule iffI)
  assume "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Always I1 \<phi>))"
  then show "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
    using assms always_safe_bounded_def
    by auto
next
  define I2 where "I2 = int_remove_lower_bound I1"
  assume "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<phi>)"
  then have rewrite: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Neg (eventually I1 (Formula.And (Formula.Or (once I2 \<phi>) (eventually I2 \<phi>)) (Formula.Neg \<phi>)))))"
    using assms I2_def always_safe_bounded_def
    by auto
  then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<phi>" by auto
  have j_geq_i_sat: "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> (Formula.sat \<sigma> V v j (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v j (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v j \<phi>"
    using rewrite
    by auto
  {
    fix k
    assume k_props: "k\<ge>i" "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
    then have "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>))) \<or> Formula.sat \<sigma> V v k \<phi>"
      using j_geq_i_sat by auto
    moreover {
      assume assm: "(Formula.sat \<sigma> V v k (Formula.Neg (once I2 \<phi>)) \<and> Formula.sat \<sigma> V v k (Formula.Neg (eventually I2 \<phi>)))"
      then have leq_k_sat: "\<forall>j\<le>k. mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> j) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" by auto
      have geq_k_sat: "\<forall>j\<ge>k. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> k) \<longrightarrow> \<not>Formula.sat \<sigma> V v j \<phi>" using assm by auto
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
    ultimately have "Formula.sat \<sigma> V v k \<phi>" by auto
  }
  then have "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<phi>" by auto
  then show "Formula.sat \<sigma> V v i (Formula.And (eventually I1 \<phi>) (Formula.Always I1 \<phi>))"
    using rewrite
    by auto
qed

lemma sat_release_rewrite_0_mem:
  fixes i j :: nat
  assumes mem: "mem I 0"
  assumes trigger: "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  assumes geq: "j\<ge>i"
  assumes mem_j: "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  shows "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>))"
proof (cases "\<exists>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<phi>")
  case True
  define A where "A = {x \<in> {i..<j}. Formula.sat \<sigma> V v x \<phi>}"
  define k where "k = Min A"
  have A_props: "A \<noteq> {}" "finite A" using True A_def by auto
  then have k_in_A: "k \<in> A" using k_def by auto
  then have k_props: "k \<in> {i..<j}" "Formula.sat \<sigma> V v k \<phi>" by (auto simp: A_def)
  have "(\<forall>l<k. l \<notin> A)"
    using Min_le[OF A_props(2)]
    by (fastforce simp: k_def)
  moreover have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" using mem mem_j k_props interval_leq[of I 0 \<sigma> j i k] by auto
  ultimately show ?thesis using k_props mem trigger by (auto simp: A_def)
next
  case False
  then show ?thesis using assms by auto
qed

lemma sat_release_rewrite_0:
  assumes mem: "mem I 0" "bounded I"
shows "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>) = Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume release: "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)"
  {
    assume "\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>))"
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Always I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  moreover {
    assume "\<not>(\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j (Formula.And \<psi> (Formula.Neg \<phi>)))"
    then obtain j' where j'_props: "j' \<ge> i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "\<not>Formula.sat \<sigma> V v j' (Formula.And \<psi> (Formula.Neg \<phi>))" by blast
    define A where "A = {j. j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)}"
    define j where "j = Min A"
    from j'_props have "\<not>Formula.sat \<sigma> V v j' \<psi> \<or> Formula.sat \<sigma> V v j' \<phi>" by simp
    moreover {
      assume "\<not>Formula.sat \<sigma> V v j' \<psi>"
      then have "\<exists>k \<in> {i..<j'}. mem I (\<tau> \<sigma> k - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)"
      using j'_props assms release sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> j']
      by auto
    then have A_props: "A \<noteq> {} \<and> finite A" using A_def by auto
    then have "j \<in> A" using j_def by auto
    then have j_props: "j \<in> {i..<j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.And \<phi> \<psi>)"
      using A_def
      by auto
    {
      assume "\<not>(\<forall>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<psi>)"
      then obtain k where k_props: "k \<in> {i..<j} \<and> \<not> Formula.sat \<sigma> V v k \<psi>" by blast
      then have "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)"
        using assms j_props interval_leq[of I 0 \<sigma> j i k]
        by auto
      then have "\<exists>x \<in> {i..<k}. mem I (\<tau> \<sigma> x - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        using assms release k_props sat_release_rewrite_0_mem[of I \<sigma> V v i \<phi> \<psi> k]
        by auto
      then obtain x where x_props: "x \<in> {i..<k}" "mem I (\<tau> \<sigma> x - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)"
        by blast
      then have "x \<ge> Min A"
        using A_def A_props k_props j_props
        by auto
      then have "False"
        using j_def k_props x_props
        by auto
    }
    then have "\<forall>k \<in> {i..<j}. Formula.sat \<sigma> V v k \<psi>" by blast
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Always I (Formula.And \<psi> (Formula.Neg \<phi>))))"
      using j_props
      by auto
    }
    moreover {
      define B where "B = {j. j\<in>{i..j'} \<and> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j \<phi>}"
      define k where "k = Min B"
      assume "Formula.sat \<sigma> V v j' \<phi>"
      then have B_props: "B \<noteq> {}" "finite B" using B_def j'_props by auto
      then have "k \<in> B" using k_def by auto
      then have k_props: "k\<in>{i..j'}" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v k \<phi>" using B_def by auto
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
          assume "Formula.sat \<sigma> V v l \<phi>"
          then have "l \<in> B" using B_def l_props l_mem k_props by auto
          then have "l\<ge>k" "l<k"
            using k_def l_props B_props(2) Min_le[of B l]
            by auto
        }
        then have "\<not>Formula.sat \<sigma> V v l \<phi>" by auto
      }
      then have not_phi: "\<forall>l\<in>{i..<k}. \<not>Formula.sat \<sigma> V v l \<phi>" using assms B_def by auto
      
      then have k_sat_psi: "Formula.sat \<sigma> V v k \<psi>" using k_props release B_def by auto
      {
        fix l
        assume l_props: "l\<in>{i..<k}"
        then have "mem I (\<tau> \<sigma> l - \<tau> \<sigma> i)"
          using k_props assms interval_leq[of I 0 \<sigma> k i l]
          by auto
        then have "Formula.sat \<sigma> V v l \<psi>"
          using l_props release not_phi
          by auto
      }
      then have "\<forall>l\<in>{i..<k}. Formula.sat \<sigma> V v l \<psi>"
        using not_phi assms release
        by auto
      then have "Formula.sat \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))"
        using k_props k_sat_psi
        by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Always I (Formula.And \<psi> (Formula.Neg \<phi>))))" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Always I (Formula.And \<psi> (Formula.Neg \<phi>))))" by blast
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I (Formula.And \<psi> (Formula.Neg \<phi>))))"
    using assms always_rewrite_0[of I \<sigma> V v i "(Formula.And \<psi> (Formula.Neg \<phi>))"]
    by auto
  then show "Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
next
  assume "Formula.sat \<sigma> V v i (release_safe_0 \<phi> I \<psi>)"
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (always_safe_0 I (Formula.And \<psi> (Formula.Neg \<phi>))))"
    using assms release_safe_0_def[of \<phi> I \<psi>]
    by auto
  then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Until \<psi> I (Formula.And \<phi> \<psi>)) (Formula.Always I (Formula.And \<psi> (Formula.Neg \<phi>))))"
    using assms always_rewrite_0[of I \<sigma> V v i "(Formula.And \<psi> (Formula.Neg \<phi>))"]
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (Formula.Always I \<psi>)"
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
  }
  moreover {
    fix j
    assume until_and_j_props: "Formula.sat \<sigma> V v i (Formula.Until \<psi> I (Formula.And \<phi> \<psi>))" "j \<ge> i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
    then obtain "j'" where j'_props: "j'\<ge>i" "mem I (\<tau> \<sigma> j' - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j' (Formula.And \<phi> \<psi>)" "(\<forall>k \<in> {i ..< j'}. Formula.sat \<sigma> V v k \<psi>)"
      by fastforce
    moreover {
      assume ge: "j' > j"
      then have "\<forall>k \<in> {i ..< j'}. Formula.sat \<sigma> V v k \<psi>" using j'_props by auto
      then have "Formula.sat \<sigma> V v j \<psi>" using until_and_j_props ge by auto
      then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by auto
    }
    moreover {
      assume leq: "\<not> j' > j"
      moreover {
        assume "j = j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using j'_props
          by auto
      }
      moreover {
        assume neq: "j \<noteq> j'"
        then have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)"
          using leq j'_props
          by auto
      }
      ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    ultimately have "Formula.sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" by blast
  }
  ultimately show "Formula.sat \<sigma> V v i (Formula.Release \<phi> I \<psi>)" by auto
qed

lemma sat_release_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
shows "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume release: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
  {
    assume "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<psi>"
    then have all: "Formula.sat \<sigma> V v i (Formula.Always I1 \<psi>)" by auto
    obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" using release by auto
    then have "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>)"
      using assms always_rewrite_bounded[of I1 \<sigma> V v i \<psi>] all
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
      by auto
  }
  moreover {
    assume "\<exists>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> \<not>Formula.sat \<sigma> V v j \<psi>"
    then obtain j where j_props: "j\<ge>i" "mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "\<not>Formula.sat \<sigma> V v j \<psi>" by auto
    define A where "A = {k. k \<in>{i ..< j} \<and> Formula.sat \<sigma> V v k \<phi>}"
    define k where k_def: "k = Min A"
    have "(\<exists>k \<in> {i ..< j}. Formula.sat \<sigma> V v k \<phi>)" using j_props release by auto
    then have A_props: "A \<noteq> {}" "finite A" using A_def by auto
    then have "k \<in> A" using k_def by auto
    then have k_props: "k \<in>{i ..< j}" "Formula.sat \<sigma> V v k \<phi>" using A_def by auto
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
      then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
        using k_props
        by auto
    }
    moreover {
      assume k_not_mem_2: "\<not>mem I2 (\<tau> \<sigma> k - \<tau> \<sigma> i)"
      then have k_mem: "mem I1 (\<tau> \<sigma> k - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
      then have "Formula.sat \<sigma> V v k \<psi> \<or> (\<exists>k \<in> {i ..< k}. Formula.sat \<sigma> V v k \<phi>)" using release k_props by auto
      moreover {
        assume "(\<exists>k \<in> {i ..< k}. Formula.sat \<sigma> V v k \<phi>)"
        then obtain l where l_props: "l \<in> {i ..< k}" "Formula.sat \<sigma> V v l \<phi>" by blast
        then have "l \<in> A" using A_def k_props l_props by auto
        then have "False" using A_props l_props k_def by auto
      }
      ultimately have "Formula.sat \<sigma> V v k \<psi>" by auto
      then have k_sat: "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_props by auto
      then have k_until: "Formula.sat \<sigma> V v k (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
        using assms int_remove_lower_bound.rep_eq memL.rep_eq prod.sel(1)
        by auto
      {
        assume "k=i"
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          using k_sat sat_once[of \<sigma> V v i I2 \<phi>] using assms k_mem by auto
      }
      moreover {
        assume k_neq_i: "\<not>(k=i)"
        then have k_pred_geq_i: "k-1\<ge>i" using k_props by auto
        {
          fix x
          assume x_props: "x \<in> {i..<k}" "mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i)"
          then have "Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>)" using release by auto
          moreover {
            assume "\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>"
            then obtain l where l_props: "l \<in> {i ..< x}" "Formula.sat \<sigma> V v l \<phi>" by blast
            then have "l \<in> A" using A_def x_props k_props by auto
            then have "l \<ge> k" using k_def A_props by auto
            then have "False" using l_props x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v x \<psi>" by auto
        }
        then have k_greater_sat: "\<forall>x\<in>{i..<k}. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v x \<psi>" by auto
        {
          assume k_suc_mem: "mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          moreover have "Formula.sat \<sigma> V v (k-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
            using k_pred_geq_i k_until interval_all k_neq_i
            by auto
          ultimately have "(\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            using k_pred_geq_i
            by blast
          then have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
            by auto
        }
        moreover {
          define B where "B = {l. l\<in>{i..<k} \<and> mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v l \<psi>}"
          define c where "c = Min B"
          assume "\<not>mem I2 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)"
          then have k_suc_mem: "mem I1 (\<tau> \<sigma> (k-1) - \<tau> \<sigma> i)" using geq_j_mem k_props by auto
          then have "Formula.sat \<sigma> V v (k-1) \<psi> \<or> (\<exists>x \<in> {i ..< k-1}. Formula.sat \<sigma> V v x \<phi>)"
            using release k_pred_geq_i
            by auto
          moreover {
            assume "\<exists>x \<in> {i ..< k-1}. Formula.sat \<sigma> V v x \<phi>"
            then obtain x where x_props: "x \<in> {i ..< k-1} \<and> Formula.sat \<sigma> V v x \<phi>" by blast
            then have "x \<in> A" using A_def k_props by auto
            then have "x \<ge> k" using A_props k_def by auto
            then have "False" using x_props by auto
          }
          ultimately have "Formula.sat \<sigma> V v (k-1) \<psi>" by auto
          then have B_props: "B \<noteq> {} \<and> finite B"
            using B_def k_pred_geq_i k_suc_mem k_props k_neq_i
            by auto
          then have "c \<in> B" using c_def by auto
          then have c_props: "c\<in>{i..<k}" "mem I1 (\<tau> \<sigma> c - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v c \<psi>" using B_def by auto
          then have k_cond: "k\<ge>c" "Formula.sat \<sigma> V v k (Formula.And \<phi> \<psi>)" using k_sat by auto
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
            then have "Formula.sat \<sigma> V v x \<psi>" using k_greater_sat x_props c_props by auto
          }
          then have "\<forall>x\<in>{c..<k}. Formula.sat \<sigma> V v x \<psi>" by auto
          moreover have "mem (int_remove_lower_bound I1) (\<tau> \<sigma> k - \<tau> \<sigma> c)"
            using k_mem c_props
            by (metis atLeastLessThan_iff int_remove_lower_bound.rep_eq interval_geq less_or_eq_imp_le memL.rep_eq memR.rep_eq prod.sel(1) prod.sel(2))
          ultimately have c_sat: "Formula.sat \<sigma> V v c (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))"
            using assms k_cond
            by auto
          {
            assume "(c-1) \<in> B"
            then have "c-1\<ge>c" using c_def B_props by auto
            moreover have "c-1 < c" using c_pos by auto
            ultimately have "False" by auto
          }
          then have "(c-1) \<notin> B" by blast
          then have disj: "(c-1)\<notin>{i..<k} \<or> \<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>Formula.sat \<sigma> V v (c-1) \<psi>" using B_def by blast
          {
            assume "(c-1)\<notin>{i..<k}"
            then have "False" using assms c_props by auto
          }
          moreover {
            assume "\<not>((c-1)\<notin>{i..<k})"
            then have c_pred_geq_i: "(c-1)\<in>{i..<k}" by auto
            then have disj: "\<not>mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i) \<or> \<not>Formula.sat \<sigma> V v (c-1) \<psi>" using disj by auto
            {
              assume c_suc_mem: "mem I1 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)"
              then have "\<not>Formula.sat \<sigma> V v (c-1) \<psi>" using disj by blast
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
              then have "(c-1)\<ge>i" "mem I2 (\<tau> \<sigma> (c-1) - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v (c-1) (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))"
                using c_pred_geq_i c_sat interval_all c_pos
                by auto
              then have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
                using interval_all sat_eventually
                by blast
            }
            ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by auto
          }
          ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))" by blast
        }
        ultimately have "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
          by blast
        then have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by simp
      }
      ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))"
          by blast
    }
    ultimately have "Formula.sat \<sigma> V v i (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))))" by blast
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using release
    by auto
  then show "Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
    using assms I2_def release_safe_bounded_def
    by simp
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def release_safe_bounded_def
    by simp
  then have eventually: "Formula.sat \<sigma> V v i (eventually I1 Formula.TT)" by auto
  then have "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (eventually I2 \<phi>) \<or> Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    using assm
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>)"
    then have "Formula.sat \<sigma> V v i (Formula.Always I1 \<psi>)"
      using assms always_rewrite_bounded[of I1 \<sigma> V v i \<psi>]
      by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  moreover {
    assume "Formula.sat \<sigma> V v i (eventually I2 \<phi>)"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j \<phi>" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j \<phi>" by blast
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
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" using j_props by auto
  }
  moreover {
    assume until: "Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    then have "\<exists>j\<ge>i. mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by auto
    then obtain j where j_props: "j\<ge>i" "mem I2 (\<tau> \<sigma> j - \<tau> \<sigma> i)" "Formula.sat \<sigma> V v j (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>)))" by blast
    then have j_pred_sat: "Formula.sat \<sigma> V v (j+1) (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))" by auto
    then have "\<exists>x\<ge>(j+1). Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>) \<and> (\<forall>k\<in>{(j+1)..<x}. Formula.sat \<sigma> V v k \<psi>)" by auto
    then obtain x where x_props: "x\<ge>(j+1)" "Formula.sat \<sigma> V v x (Formula.And \<phi> \<psi>)" "\<forall>k\<in>{(j+1)..<x}. Formula.sat \<sigma> V v k \<psi>" by blast
    {
      fix l
      assume l_props: "l\<ge>i"
      {
        assume "l>x"
        then have "\<exists>k \<in> {i ..< l}. Formula.sat \<sigma> V v k \<phi>" using x_props j_props by auto
      }
      moreover {
        assume l_assms: "\<not>(l>x)" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)"
        then have l_props: "x\<ge>l" "l\<ge>i" "mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i)" using l_props by auto
        {
          assume "l\<ge>(j+1)"
          then have "Formula.sat \<sigma> V v l \<psi>" using x_props l_props by auto
        }
        moreover {
          assume "\<not>l\<ge>(j+1)"
          then have l_geq: "l\<le>(j+1)" by auto
          have j_suc_psi: "Formula.sat \<sigma> V v (j+1) \<psi>" using j_pred_sat by auto
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
          then have "Formula.sat \<sigma> V v l \<psi>" using j_suc_psi by blast
        }
        ultimately have "Formula.sat \<sigma> V v l \<psi>" by blast
      }
      ultimately have "(mem I1 (\<tau> \<sigma> l - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v l \<psi>) \<or> (\<exists>k \<in> {i ..< l}. Formula.sat \<sigma> V v k \<phi>)" by blast
    }
    then have "\<forall>x\<ge>i. mem I1 (\<tau> \<sigma> x - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v x \<psi> \<or> (\<exists>k \<in> {i ..< x}. Formula.sat \<sigma> V v k \<phi>)" by auto
    then have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by auto
  }
  ultimately have "Formula.sat \<sigma> V v i (Formula.Release \<phi> I1 \<psi>)" by blast
  then show "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
    using assm
    by auto
qed

(* verify that the derived rewrite formulas are safe *)

(* trigger *)

(* [0, b] *)
lemma
  assumes "safe_formula \<psi>"
  assumes "fv \<phi> \<subseteq> fv \<psi>"
  assumes "safe_formula \<phi> \<or> (is_constraint (Formula.Neg \<phi>) \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"
  shows "safe_formula (trigger_safe_0 \<phi> I \<psi>)"
  using assms by (auto simp add: trigger_safe_0_def)

lemma trigger_safe_0_conditions: "safe_formula (trigger_safe_0 \<phi> I \<psi>) = (safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>)))"
proof (rule iffI)
  define \<alpha> where "\<alpha> = Formula.Since \<psi> I (Formula.And \<psi> \<phi>)"
  define \<beta> where "\<beta> = historically_safe_0 I (Formula.And \<psi> (Formula.Neg \<phi>))"
  assume "safe_formula (trigger_safe_0 \<phi> I \<psi>)"
  then have safe: "safe_formula \<alpha>" "safe_formula \<beta>"
    using \<alpha>_def \<beta>_def
    by (auto simp add: trigger_safe_0_def)
  from safe(1) have a: "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
  )" using \<alpha>_def by auto
  moreover from safe(2) have b: "safe_formula \<psi> \<and>
    (safe_formula (Formula.Neg \<phi>) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    using \<beta>_def by (auto simp add: safe_assignment_def)
  ultimately have "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (safe_formula (Formula.Neg \<phi>) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    by auto
  then show "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    using safe_formula_Neg
    by blast
next
  assume assm: "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
  then have "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (safe_formula (Formula.Neg \<phi>) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    using safe_formula_Neg
    by blast
  then show "safe_formula (trigger_safe_0 \<phi> I \<psi>)"
    by (simp add: trigger_safe_0_def)
qed

lemma neg_phi_and_constraint: "(case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False) \<Longrightarrow> is_constraint (Formula.Neg \<phi>) \<Longrightarrow> False"
proof (cases \<phi>)
  case phi: (Neg \<phi>')
  assume "is_constraint (Formula.Neg \<phi>)"
  then show ?thesis using phi by auto
qed (auto)

lemma safe_formula_constraint_simp: "((case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False) \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>))) =
       ((case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False) \<and> (safe_formula \<phi>))"
  using neg_phi_and_constraint
  by auto

lemma trigger_release_conditions_simp:
  "(safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>)))
  =
  (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>) \<and> (
      (safe_assignment (fv \<psi>) \<phi>) \<or>
      (\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or>
      is_constraint \<phi>
    )))"
proof -
  have "(safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>)))
    =
    (safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<and> ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> \<subseteq> fv \<psi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))) \<or>
      safe_formula \<phi> \<and> ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> \<subseteq> fv \<psi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))) \<or>
      fv \<phi> \<subseteq> fv \<psi> \<and> ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<and> is_constraint \<phi> \<or> (is_constraint \<phi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>)) \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False) \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>))))
    ))
" by auto
  moreover have "(safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<and> ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> \<subseteq> fv \<psi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))) \<or>
      safe_formula \<phi> \<and> ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> \<subseteq> fv \<psi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))) \<or>
      fv \<phi> \<subseteq> fv \<psi> \<and> ((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<and> is_constraint \<phi> \<or> (is_constraint \<phi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>)) \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False) \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>))))
    ))
= 
      (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> (safe_formula \<phi> \<or> is_constraint (Formula.Neg \<phi>) \<and> (
        (safe_assignment (fv \<psi>) \<phi>) \<or>
        (\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or>
        is_constraint \<phi>
      )))
"
    by (auto simp add: safe_formula_constraint_simp safe_assignment_def)
  ultimately show ?thesis by auto
qed

lemma 
  assumes "mem I 0"
  shows "safe_formula (Formula.Trigger \<phi> I \<psi>) = safe_formula (trigger_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume "safe_formula (Formula.Trigger \<phi> I \<psi>)"
  then show "safe_formula (trigger_safe_0 \<phi> I \<psi>)"
    using assms
    by (auto simp add: trigger_safe_0_def restricted_formula_def)
next
  assume assm: "safe_formula (trigger_safe_0 \<phi> I \<psi>)"
  then show "safe_formula (Formula.Trigger \<phi> I \<psi>)" using
      trigger_safe_0_conditions[of \<phi> I \<psi>] assms trigger_release_conditions_simp restricted_formula_def
    by auto
qed

lemma "Formula.future_bounded (trigger_safe_0 \<phi> I \<psi>) = (Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: trigger_safe_0_def)

(* [a, \<infinity>] *)

lemma
  assumes "safe_formula \<psi>"
  assumes "safe_formula \<phi>"
  assumes "fv \<phi> = fv \<psi>"
  (* can this be improved? probably not. if \<psi> holds everywhere, \<phi> can be assigned anything *)
  (* vice versa, if \<phi> holds at i, everything can be assigned to \<psi> *)
  shows "safe_formula (trigger_safe_unbounded \<phi> I \<psi>)"
  using assms
  by (auto simp add: trigger_safe_unbounded_def once_def historically_safe_unbounded_def)

lemma "Formula.future_bounded (trigger_safe_unbounded \<phi> I \<psi>) = (Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: trigger_safe_unbounded_def)

(* [a, b] *)

lemma 
  assumes "\<not>mem I 0"
  shows "safe_formula (Formula.Trigger \<phi> I \<psi>) = safe_formula (trigger_safe_bounded \<phi> I \<psi>)"
proof (rule iffI)
  assume "safe_formula (Formula.Trigger \<phi> I \<psi>)"
  then show "safe_formula (trigger_safe_bounded \<phi> I \<psi>)"
    using assms
    by (simp add: trigger_safe_bounded_def)
next
  assume "safe_formula (trigger_safe_bounded \<phi> I \<psi>)"
  then show "safe_formula (Formula.Trigger \<phi> I \<psi>)"
  by (simp add: trigger_safe_bounded_def safe_assignment_def)
qed

lemma "Formula.future_bounded (trigger_safe_bounded \<phi> I \<psi>) = (bounded I \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: trigger_safe_bounded_def)

(* release *)

(* [0, b] *)

lemma release_safe_0_conditions: "safe_formula (release_safe_0 \<phi> I \<psi>) = (safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>)))"
proof (rule iffI)
  define \<alpha> where "\<alpha> = Formula.Since \<psi> I (Formula.And \<psi> \<phi>)"
  define \<beta> where "\<beta> = always_safe_0 I (Formula.And \<psi> (Formula.Neg \<phi>))"
  assume "safe_formula (release_safe_0 \<phi> I \<psi>)"
  then have safe: "safe_formula \<alpha>" "safe_formula \<beta>"
    using \<alpha>_def \<beta>_def
    by (auto simp add: release_safe_0_def)
  from safe(1) have a: "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
  )" using \<alpha>_def by auto
  moreover from safe(2) have b: "safe_formula \<psi> \<and>
    (safe_formula (Formula.Neg \<phi>) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    using \<beta>_def by (auto simp add: safe_assignment_def)
  ultimately have "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (safe_formula (Formula.Neg \<phi>) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    by auto
  then show "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    using safe_formula_Neg
    by blast
next
  assume assm: "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (((\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x)) \<or> (fv \<phi> = {} \<and> safe_formula \<phi>)) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
  then have "safe_formula \<psi> \<and> (
      safe_assignment (fv \<psi>) \<phi> \<or> safe_formula \<phi> \<or>
        fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint \<phi> \<or> (case \<phi> of Formula.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))
    ) \<and> (safe_formula (Formula.Neg \<phi>) \<or> fv \<phi> \<subseteq> fv \<psi> \<and> (is_constraint (Formula.Neg \<phi>) \<or> safe_formula \<phi>))"
    using safe_formula_Neg
    by blast
  then show "safe_formula (release_safe_0 \<phi> I \<psi>)"
    by (simp add: release_safe_0_def)
qed

lemma 
  assumes "mem I 0"
  shows "safe_formula (Formula.Release \<phi> I \<psi>) = safe_formula (release_safe_0 \<phi> I \<psi>)"
proof (rule iffI)
  assume "safe_formula (Formula.Release \<phi> I \<psi>)"
  then show "safe_formula (release_safe_0 \<phi> I \<psi>)"
    using assms
    by (auto simp add: release_safe_0_def restricted_formula_def)
next
  assume assm: "safe_formula (release_safe_0 \<phi> I \<psi>)"
  then show "safe_formula (Formula.Release \<phi> I \<psi>)"
    using release_safe_0_conditions[of \<phi> I \<psi>] assms trigger_release_conditions_simp restricted_formula_def
    by auto
qed

lemma "Formula.future_bounded (release_safe_0 \<phi> I \<psi>) = (bounded I \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: release_safe_0_def)

(* [a, b] *)

lemma
  assumes "\<not>mem I 0"
  shows "safe_formula (Formula.Release \<phi> I \<psi>) = safe_formula (release_safe_bounded \<phi> I \<psi>)"
proof (rule iffI)
  assume "safe_formula (Formula.Release \<phi> I \<psi>)"
  then show "safe_formula (release_safe_bounded \<phi> I \<psi>)"
    using assms
    by (simp add: release_safe_bounded_def)
next
  assume "safe_formula (release_safe_bounded \<phi> I \<psi>)"
  then show "safe_formula (Formula.Release \<phi> I \<psi>)"
  by (simp add: release_safe_bounded_def safe_assignment_def)
qed

lemma "Formula.future_bounded (release_safe_bounded \<phi> I \<psi>) = (bounded I \<and> \<not>mem I 0 \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
proof (rule iffI)
  assume "Formula.future_bounded (release_safe_bounded \<phi> I \<psi>)"
  then show "bounded I \<and> \<not>mem I 0 \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>"
    by (auto simp add: release_safe_bounded_def eventually_def bounded.rep_eq flip_int_less_lower.rep_eq)
next
  assume "bounded I \<and> \<not>mem I 0 \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>"
  then show "Formula.future_bounded (release_safe_bounded \<phi> I \<psi>)"
    using flip_int_less_lower_props[of I "flip_int_less_lower I"] int_remove_lower_bound_bounded
  by (auto simp add: release_safe_bounded_def eventually_def)
qed

fun map_formula :: "(Formula.formula \<Rightarrow> Formula.formula) \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula" where
  "map_formula f (Formula.Pred r ts) = f (Formula.Pred r ts)"
| "map_formula f (Formula.Let p \<phi> \<psi>) = f (
    Formula.Let p (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Eq t1 t2) = f (Formula.Eq t1 t2)"
| "map_formula f (Formula.Less t1 t2) = f (Formula.Less t1 t2)"
| "map_formula f (Formula.LessEq t1 t2) = f (Formula.LessEq t1 t2)"
| "map_formula f (Formula.Neg \<phi>) = f (Formula.Neg (map_formula f \<phi>))"
| "map_formula f (Formula.Or \<phi> \<psi>) = f (
    Formula.Or (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.And \<phi> \<psi>) = f (
    Formula.And (map_formula f \<phi>) (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Ands \<phi>s) = f (
    Formula.Ands (map (map_formula f) \<phi>s)
  )"
| "map_formula f (Formula.Exists \<phi>) = f (Formula.Exists (map_formula f \<phi>))"
| "map_formula f (Formula.Agg y \<omega> b f' \<phi>) = f (
    Formula.Agg y \<omega> b f' (map_formula f \<phi>)
  )"
| "map_formula f (Formula.Prev I \<phi>) = f (Formula.Prev I (map_formula f \<phi>))"
| "map_formula f (Formula.Next I \<phi>) = f (Formula.Next I (map_formula f \<phi>))"
| "map_formula f (Formula.Historically I \<phi>) = f (Formula.Historically I (map_formula f \<phi>))"
| "map_formula f (Formula.Always I \<phi>) = f (Formula.Always I (map_formula f \<phi>))"
| "map_formula f (Formula.Since \<phi> I \<psi>) = f (
    Formula.Since (map_formula f \<phi>) I ( map_formula f \<psi>)
  )"
| "map_formula f (Formula.Until \<phi> I \<psi>) = f (
    Formula.Until (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Trigger \<phi> I \<psi>) = f (
    Formula.Trigger (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.Release \<phi> I \<psi>) = f (
    Formula.Release (map_formula f \<phi>) I (map_formula f \<psi>)
  )"
| "map_formula f (Formula.MatchF I r) = f (Formula.MatchF I r)"
| "map_formula f (Formula.MatchP I r) = f (Formula.MatchP I r)"

lemma map_formula_fvi:
  assumes "\<forall>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  shows "\<forall>b. Formula.fvi b (map_formula f \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi>) qed (auto simp add: assms)


lemma map_formula_sat:
  assumes "\<forall>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  assumes "\<forall>\<sigma> V v i \<phi>. Formula.sat \<sigma> V v i (f \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  shows "\<forall>\<sigma> V v i. Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (map_formula f \<phi>)"
using assms proof (induction \<phi>)
  case assm: (Let p \<phi>' \<psi>')
  from assms have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
    using Formula.nfv_def map_formula_fvi
    by auto
  {
    fix \<sigma> V v i
    have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi>' \<and> Formula.sat \<sigma> V v i \<phi>'})) v i \<psi>'"
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = Formula.nfv \<phi>' \<and> Formula.sat \<sigma> V v i \<phi>'})) v i (map_formula f \<psi>')"
      using assm
      by blast
    then have "Formula.sat \<sigma> V v i (formula.Let p \<phi>' \<psi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Let p \<phi>' \<psi>'))"
      using assm nfv_eq assms
      by auto
  }
  then show ?case by blast
next
  case assm: (Agg y \<omega> b f' \<phi>')
  {
    fix \<sigma> V v i
    define M where "M = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = b \<and>
        Formula.sat \<sigma> V (zs @ v) i \<phi>' \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    define M' where "M' = {(x, ecard Zs) |
        x Zs. Zs = {zs. length zs = b \<and>
        Formula.sat \<sigma> V (zs @ v) i (map_formula f \<phi>') \<and>
        Formula.eval_trm (zs @ v) f' = x} \<and> Zs \<noteq> {}
    }"
    have M_eq: "M = M'" using M_def M'_def assm by auto
    have nfv_eq: "\<forall>\<phi>. Formula.nfv (map_formula f \<phi>) = Formula.nfv \<phi>"
      using assms Formula.nfv_def map_formula_fvi
      by auto
    have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = (
      (M = {} \<longrightarrow> fv \<phi>' \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M
    )"
      using M_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = (
      (M' = {} \<longrightarrow> fv (map_formula f \<phi>') \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M')"
      using assms assm M_eq nfv_eq map_formula_fvi
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' (map_formula f \<phi>'))"
      using M'_def
      by auto
    then have "Formula.sat \<sigma> V v i (formula.Agg y \<omega> b f' \<phi>') = Formula.sat \<sigma> V v i (map_formula f (formula.Agg y \<omega> b f' \<phi>'))"
      using assms by auto
  }
  then show ?case by blast
qed (auto split: nat.split)

fun rewrite_historically :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite_historically (Formula.Historically I \<phi>) = (
    if (mem I 0) then
      historically_safe_0 I (rewrite_historically \<phi>)
    else (
      if (bounded I) then
        historically_safe_bounded I (rewrite_historically \<phi>)
      else
        historically_safe_unbounded I (rewrite_historically \<phi>)
    )
  )"
| "rewrite_historically f = f"

lemma historically_safe_0_fvi[simp]: "Formula.fvi b (historically_safe_0 I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_0_def split: if_splits)

lemma historically_safe_unbounded_fvi[simp]: "Formula.fvi b (historically_safe_unbounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_bounded_fvi[simp]: "Formula.fvi b (historically_safe_bounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma rewrite_historically_fvi[simp]: "Formula.fvi b (rewrite_historically \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi>) qed (auto)

lemma rewrite_historically_sat[simp]: "\<forall>\<sigma> V v i. Formula.sat \<sigma> V v i (rewrite_historically \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (induction \<phi>)
  case assm: (Historically I \<phi>')
  {
    fix \<sigma> V v i
    {
      assume mem: "mem I 0"
      then have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (historically_safe_0 I (rewrite_historically \<phi>'))"
        by auto
      then have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (formula.Historically I (rewrite_historically \<phi>'))"
        using mem historically_rewrite_0[of I \<sigma> V v i "(rewrite_historically \<phi>')"]
        by auto
    }
    moreover {
      assume mem: "\<not> mem I 0"
      {
        assume b: "bounded I"
        then have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (historically_safe_bounded I (rewrite_historically \<phi>'))"
          using mem by auto
        then have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (formula.Historically I (rewrite_historically \<phi>'))"
          using mem b historically_rewrite_bounded[of I \<sigma> V v i "(rewrite_historically \<phi>')"]
          by auto
      }
      moreover {
        assume b: "\<not> bounded I"
        then have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (historically_safe_unbounded I (rewrite_historically \<phi>'))"
          using mem by auto
        then have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (formula.Historically I (rewrite_historically \<phi>'))"
          using mem b historically_rewrite_unbounded[of I \<sigma> V v i "(rewrite_historically \<phi>')"]
          by auto
      }
      ultimately have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (formula.Historically I (rewrite_historically \<phi>'))"
        by auto
    }
    ultimately have "Formula.sat \<sigma> V v i (rewrite_historically (Formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (formula.Historically I (rewrite_historically \<phi>'))"
        by auto
      then have "Formula.sat \<sigma> V v i (rewrite_historically (formula.Historically I \<phi>')) = Formula.sat \<sigma> V v i (formula.Historically I \<phi>')"
        using assm
        by auto
  }
  then show ?case by blast
qed (auto)

fun rewrite_always :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite_always (Formula.Always I \<phi>) = (
    if (mem I 0) then
      always_safe_0 I (rewrite_always \<phi>)
    else (
      if (bounded I) then
        always_safe_bounded I (rewrite_always \<phi>)
      else
        undefined
    )
  )"
| "rewrite_always f = f"

lemma always_safe_0_fvi[simp]: "Formula.fvi b (always_safe_0 I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: always_safe_0_def split: if_splits)

lemma always_safe_bounded_fvi[simp]: "Formula.fvi b (always_safe_bounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: always_safe_bounded_def)

lemma rewrite_always_fvi[simp]: "Formula.future_bounded \<phi> \<Longrightarrow> Formula.fvi b (rewrite_always \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi>) qed (auto)

fun rewrite_trigger :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite_trigger (Formula.Trigger \<phi> I \<psi>) = (
    if (mem I 0) then
      trigger_safe_0 (rewrite_trigger \<phi>) I (rewrite_trigger \<psi>)
    else (
      if (bounded I) then
        trigger_safe_bounded (rewrite_trigger \<phi>) I (rewrite_trigger \<psi>)
      else
        trigger_safe_unbounded (rewrite_trigger \<phi>) I (rewrite_trigger \<psi>)
    )
  )"
| "rewrite_trigger f = f"

lemma trigger_safe_0_fvi[simp]: "Formula.fvi b (trigger_safe_0 \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_0_def)

lemma trigger_safe_unbounded_fvi[simp]: "Formula.fvi b (trigger_safe_unbounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_unbounded_def)

lemma trigger_safe_bounded_fvi[simp]: "Formula.fvi b (trigger_safe_bounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_bounded_def)

lemma rewrite_trigger_fvi[simp]: "Formula.fvi b (rewrite_trigger \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi>) qed (auto)

fun rewrite_release :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite_release (Formula.Release \<phi> I \<psi>) = (
    if (mem I 0) then
      release_safe_0 (rewrite_release \<phi>) I (rewrite_release \<psi>)
    else (
      if (bounded I) then
        release_safe_bounded (rewrite_release \<phi>) I (rewrite_release \<psi>)
      else
        undefined
    )
  )"
| "rewrite_release f = f"

lemma release_safe_0_fvi[simp]: "Formula.fvi b (release_safe_0 \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: release_safe_0_def)

lemma release_safe_bounded_fvi[simp]: "Formula.fvi b (release_safe_bounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: release_safe_bounded_def)

lemma rewrite_release_fvi[simp]: "Formula.future_bounded \<phi> \<Longrightarrow> Formula.fvi b (rewrite_release \<phi>) = Formula.fvi b \<phi>"
proof (induction \<phi>) qed (auto)
