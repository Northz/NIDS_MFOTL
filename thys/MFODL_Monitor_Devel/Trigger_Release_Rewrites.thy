(*<*)
theory Trigger_Release_Rewrites
  imports
    Event_Data
    Formula
    "MFOTL_Monitor_Devel.Interval"
    "MFOTL_Monitor_Devel.Trace"
begin
(*>*)



lemma sat_release_rewrite:
  fixes I1 I2 :: \<I>
  assumes "bounded I1" "\<not>mem I1 0" (* [a, b] *)
shows "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>)) = Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
proof (rule iffI)
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume release: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Release \<phi> I1 \<psi>))"
  {
    assume "\<forall>j\<ge>i. mem I1 (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> Formula.sat \<sigma> V v j \<psi>"
    then have all: "Formula.sat \<sigma> V v i (always I1 \<psi>)" by auto
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
    by auto
next
  define I2 where "I2 = flip_int_less_lower I1" (* [0, a-1] *)
  assume "Formula.sat \<sigma> V v i (release_safe_bounded \<phi> I1 \<psi>)"
  then have assm: "Formula.sat \<sigma> V v i (Formula.And (eventually I1 Formula.TT) (Formula.Or (Formula.Or (always_safe_bounded I1 \<psi>) (eventually I2 \<phi>)) (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))))"
    using assms I2_def release_safe_bounded_def
    by auto
  then have eventually: "Formula.sat \<sigma> V v i (eventually I1 Formula.TT)" by auto
  then have "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>) \<or> Formula.sat \<sigma> V v i (eventually I2 \<phi>) \<or> Formula.sat \<sigma> V v i (eventually I2 (Formula.Next all (Formula.Until \<psi> (int_remove_lower_bound I1) (Formula.And \<phi> \<psi>))))"
    using assm
    by auto
  moreover {
    assume "Formula.sat \<sigma> V v i (always_safe_bounded I1 \<psi>)"
    then have "Formula.sat \<sigma> V v i (always I1 \<psi>)"
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

(* this would be the safety in full generality (for the current implementation).
  for simplicity safe_assignment, is_contraint and nested triggers
   are currently disallowed
*)
definition safe_formula_dual' where "
  safe_formula_dual' b \<phi> I \<psi> = (if (mem I 0) then
    (safe_formula \<psi> \<and> fv \<phi> \<subseteq> fv \<psi> \<and> (
      safe_formula \<phi> \<or> safe_assignment (fv \<psi>) \<phi> \<or> is_constraint \<phi> \<or>
      (case \<phi> of formula.Neg x \<Rightarrow> safe_formula x | formula.Trigger x xa xb \<Rightarrow> safe_formula_dual True safe_formula x xa xb
        | _ \<Rightarrow> False)
    ))
      else
    b \<and> (safe_formula \<phi> \<and> safe_formula \<psi> \<and> fv \<phi> = fv \<psi>))
"

(* trigger *)

(* [0, b] *)
lemma
  assumes "safe_formula (Formula.Trigger \<phi> I \<psi>)"
  shows "safe_formula (trigger_safe_0 \<phi> I \<psi>)"
  using assms
  by (auto simp add: trigger_safe_0_def safe_formula_dual_def split: if_splits)
     (auto split: formula.splits)

lemma "mem I 0 \<Longrightarrow>
  safe_formula_dual' False \<phi> I \<psi> = safe_formula (trigger_safe_0 \<phi> I \<psi>)"
  by (auto simp add: trigger_safe_0_def safe_formula_dual'_def split: if_splits)


lemma "Formula.future_bounded (trigger_safe_0 \<phi> I \<psi>) = (Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: trigger_safe_0_def)

(* [a, \<infinity>] *)

lemma
  assumes "safe_formula_dual True safe_formula \<phi> I \<psi>"
  assumes "\<not> mem I 0"
  shows "safe_formula (trigger_safe_unbounded \<phi> I \<psi>)"
  using assms
  by (auto simp add: trigger_safe_unbounded_def once_def historically_safe_unbounded_def safe_formula_dual_def)

lemma "Formula.future_bounded (trigger_safe_unbounded \<phi> I \<psi>) = (Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: trigger_safe_unbounded_def)

(* release *)

(* [0, b] *)

lemma "mem I 0 \<Longrightarrow>
  safe_formula_dual' False \<phi> I \<psi> = safe_formula (release_safe_0 \<phi> I \<psi>)"
  by (auto simp add: release_safe_0_def safe_formula_dual'_def split: if_splits)

lemma "Formula.future_bounded (release_safe_0 \<phi> I \<psi>) = (bounded I \<and> Formula.future_bounded \<psi> \<and> Formula.future_bounded \<phi>)"
  by (auto simp add: release_safe_0_def)

(* [a, b] *)

lemma
  assumes "safe_formula_dual True safe_formula \<phi> I \<psi>"
  assumes "\<not> mem I 0"
  shows "safe_formula (release_safe_bounded \<phi> I \<psi>)"
  using assms
  by (auto simp add: release_safe_bounded_def once_def historically_safe_unbounded_def safe_formula_dual_def)

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
proof (induction \<phi>) qed (auto simp add: assms release_safe_0_def always_safe_0_def)


lemma map_formula_sat:
  assumes "\<And>b \<phi>. Formula.fvi b (f \<phi>) = Formula.fvi b \<phi>"
  assumes "\<And>\<sigma> V v i \<phi>. Formula.sat \<sigma> V v i (f \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  shows "\<And>\<sigma> V v i. Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (map_formula f \<phi>)"
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


fun rewrite_trigger :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite_trigger (Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)) = (
    if (mem I 0) then
      \<comment> \<open>the rewrite function already was applied recursively, hence the trigger should already be rewritten\<close>
      Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)
    else (
      case \<phi> of (Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))) \<Rightarrow> (
        if I = I' \<and> v1 = 0 \<and> v2 = 0 \<and> v3 = 0 \<and> v4 = 0 then
          if (bounded I) then
            trigger_safe_bounded \<alpha> I \<beta>
          else
            trigger_safe_unbounded \<alpha> I \<beta>
        else
          Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)
        )
      | _ \<Rightarrow> Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)
    )
  )"
| "rewrite_trigger (Formula.Trigger \<alpha> I \<beta>) = (
    if (mem I 0) then
      trigger_safe_0 \<alpha> I \<beta>
    else (
      Formula.Trigger \<alpha> I \<beta>
    )
  )"
| "rewrite_trigger f = f"

lemma historically_safe_0_fvi[simp]: "Formula.fvi b (historically_safe_0 I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_0_def split: if_splits)

lemma historically_safe_unbounded_fvi[simp]: "Formula.fvi b (historically_safe_unbounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_unbounded_def)

lemma historically_safe_bounded_fvi[simp]: "Formula.fvi b (historically_safe_bounded I \<phi>) = Formula.fvi b \<phi>"
  by (auto simp add: historically_safe_bounded_def)

lemma trigger_safe_0_fvi[simp]: "Formula.fvi b (trigger_safe_0 \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_0_def split: if_splits)

lemma trigger_safe_unbounded_fvi[simp]: "Formula.fvi b (trigger_safe_unbounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_unbounded_def)

lemma trigger_safe_bounded_fvi[simp]: "Formula.fvi b (trigger_safe_bounded \<phi> I \<psi>) = Formula.fvi b \<phi> \<union> Formula.fvi b \<psi>"
  by (auto simp add: trigger_safe_bounded_def)

lemma rewrite_trigger_fvi[simp]: "Formula.fvi b (rewrite_trigger \<phi>) = Formula.fvi b \<phi>"
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And
        using Trigger
        by auto
    next
      case not_mem: False
      then show ?thesis
        proof (cases "case \<phi> of (Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))) \<Rightarrow> True | _ \<Rightarrow> False")
          case True
          then obtain v1 v2 v3 v4 I' where \<phi>_eq:
            "\<phi> = Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))"
            by (auto split: formula.splits trm.splits)
          show ?thesis
          proof (cases "I = I' \<and> v1 = 0 \<and> v2 = 0 \<and> v3 = 0 \<and> v4 = 0")
            case var_eqs: True
            then have \<phi>_eq': "\<phi> = once I Formula.TT"
              unfolding \<phi>_eq once_def Formula.TT_def Formula.FF_def
              by auto
            show ?thesis
            proof (cases "bounded I")
              case True
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_bounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                by auto
            next
              case False
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_unbounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                by auto
            qed
          next
            case False
            then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
              using not_mem
              unfolding Trigger \<phi>_eq rewrite_trigger.simps
              by auto
            then show ?thesis
              unfolding And Trigger
              by auto
          qed
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
          using not_mem
          unfolding Trigger rewrite_trigger.simps
          by (auto split: formula.splits trm.splits)
        then show ?thesis
          unfolding And Trigger
          by auto
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      unfolding Trigger rewrite
      using trigger_safe_0_fvi[of b \<alpha> I \<beta>]
      by auto
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis unfolding Trigger by auto
  qed
qed (auto)

lemma rewrite_trigger_sat[simp]: "Formula.sat \<sigma> V v i (rewrite_trigger \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (cases \<phi>)
  case (And \<phi> \<psi>)
  then show ?thesis
  proof (cases \<psi>)
    case (Trigger \<alpha> I \<beta>)
    then show ?thesis
    proof (cases "mem I 0")
      case True
      then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
        unfolding Trigger
        by auto
      then show ?thesis
        unfolding And Trigger
        by auto
    next
      case not_mem: False
      then show ?thesis
        proof (cases "case \<phi> of (Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))) \<Rightarrow> True | _ \<Rightarrow> False")
          case True
          then obtain v1 v2 v3 v4 I' where \<phi>_eq:
            "\<phi> = Formula.Since (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v1) (Formula.Var v2))))) I' (Formula.Neg (Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var v3) (Formula.Var v4)))))"
            by (auto split: formula.splits trm.splits)
          show ?thesis
          proof (cases "I = I' \<and> v1 = 0 \<and> v2 = 0 \<and> v3 = 0 \<and> v4 = 0")
            case var_eqs: True
            then have \<phi>_eq': "\<phi> = once I Formula.TT"
              unfolding \<phi>_eq once_def Formula.TT_def Formula.FF_def
              by auto
            show ?thesis
            proof (cases "bounded I")
              case True
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_bounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                using sat_trigger_rewrite_bounded[OF not_mem True]
                by auto
            next
              case False
              then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = trigger_safe_unbounded \<alpha> I \<beta>"
                using not_mem var_eqs
                unfolding Trigger \<phi>_eq rewrite_trigger.simps
                by auto
              then show ?thesis
                unfolding And Trigger \<phi>_eq'
                using sat_trigger_rewrite_unbounded[OF not_mem False]
                by auto
            qed
          next
            case False
            then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
              using not_mem
              unfolding Trigger \<phi>_eq rewrite_trigger.simps
              by auto
            then show ?thesis
              unfolding And Trigger
              by auto
          qed
      next
        case False
        then have "(rewrite_trigger (formula.And \<phi> \<psi>)) = Formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
          using not_mem
          unfolding Trigger rewrite_trigger.simps
          by (auto split: formula.splits trm.splits)
        then show ?thesis
          unfolding And Trigger
          by auto
      qed
    qed
  qed (auto)
next
  case (Trigger \<alpha> I \<beta>)
  show ?thesis
  proof (cases "mem I 0")
    case True
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = trigger_safe_0 \<alpha> I \<beta>"
      by auto
    show ?thesis
      unfolding Trigger rewrite
      using sat_trigger_rewrite_0[OF True]
      by auto
  next
    case False
    then have rewrite: "rewrite_trigger (formula.Trigger \<alpha> I \<beta>) = formula.Trigger \<alpha> I \<beta>"
      by auto
    then show ?thesis unfolding Trigger by auto
  qed
qed (auto)


thm map_formula_sat[OF rewrite_trigger_fvi rewrite_trigger_sat]