(*<*)
theory Interval
  imports 
    "HOL-Library.Extended_Nat" 
    "HOL-Library.Product_Lexorder"
begin
(*>*)

section \<open>Intervals\<close>

definition upclosed :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "upclosed mem = (\<forall>l m. mem l \<longrightarrow> l \<le> m \<longrightarrow> mem m)"

definition downclosed :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "downclosed mem = (\<forall>m r. mem r \<longrightarrow> m \<le> r \<longrightarrow> mem m)"

typedef \<I> = "{(memL, memR, bounded).
  (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> (bounded \<longleftrightarrow> (\<exists>m. \<not> memR m))}"
  by (intro exI[of _ "(\<lambda>_. True, \<lambda>_. True, False)"]) (auto simp: upclosed_def downclosed_def)

setup_lifting type_definition_\<I>

lift_definition memL :: "\<I> \<Rightarrow> nat \<Rightarrow> bool" is fst .
lift_definition memR :: "\<I> \<Rightarrow> nat \<Rightarrow> bool" is "fst o snd" .
lift_definition bounded :: "\<I> \<Rightarrow> bool" is "snd o snd" .
abbreviation mem :: "\<I> \<Rightarrow> nat \<Rightarrow> bool" where "mem \<I> n \<equiv> memL \<I> n \<and> memR \<I> n"

lemma memL_mono[elim]: "memL I l \<Longrightarrow> l \<le> m \<Longrightarrow> memL I m"
  by transfer (auto simp: upclosed_def)
lemma memR_antimono[elim]: "memR I r \<Longrightarrow> m \<le> r \<Longrightarrow> memR I m"
  by transfer (auto simp: downclosed_def)
lemma memR_zero[simp]: "memR I 0"
  by transfer (auto simp: downclosed_def)
lemma memR_nonzeroD: "\<not> memR I t \<Longrightarrow> t > 0"
  by (erule contrapos_np) simp

lemma bounded_memR: "bounded I \<longleftrightarrow> (\<exists>m. \<not> memR I m)"
  by transfer auto

lift_definition all :: \<I> is "(\<lambda>_. True, \<lambda>_. True, False)" by (auto simp: upclosed_def downclosed_def)
lift_definition point :: "nat \<Rightarrow> \<I>" is "\<lambda>n. ((\<le>) n, (\<ge>) n, True)"
  by (auto simp: upclosed_def downclosed_def not_le)
lift_definition subtract :: "nat \<Rightarrow> \<I> \<Rightarrow> \<I>" is
  "\<lambda>n (memL, memR, b). (\<lambda>i. memL (i + n), \<lambda>i. i = 0 \<or> memR (i + n), b)"
    apply (auto simp: upclosed_def downclosed_def)
   apply (metis add.commute le_iff_add linear)
  by (metis le0 linorder_neqE_nat nat_le_iff_add not_less0)

lemma point_simps[simp]:
  "memL (point n) = (\<le>) n"
  "memR (point n) = (\<ge>) n"
  "bounded (point n) = True"
  by (transfer; auto)+

lemma subtract_simps[simp]:
  "subtract 0 I = I"
  "subtract x (point y) = point (y - x)"
  "memL (subtract x I) n = memL I (n + x)"
  "memR (subtract x I) n = (n = 0 \<or> memR I (n + x))"
  "bounded (subtract x I) = bounded I"
  by (transfer; auto simp: downclosed_def)+

lift_definition interval :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" is
  "\<lambda>l. \<lambda>r. (if enat l \<le> r then (\<lambda>i. l \<le> i, \<lambda>i. enat i \<le> r, r \<noteq> \<infinity>) else (\<lambda>_. True, \<lambda>_. True, False))"
  using enat_iless
  by (auto simp: upclosed_def downclosed_def not_le order_subst2)

lift_definition clopen_ivlR :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" is
  "\<lambda>l. \<lambda>r. (if enat l < r then (\<lambda>i. l \<le> i, \<lambda>i. enat i < r, r \<noteq> \<infinity>) else (\<lambda>_. True, \<lambda>_. True, False))"
  using enat_iless 
  apply (auto simp: upclosed_def downclosed_def not_le order_subst2)
  apply (meson enat_ord_simps(1) order_le_less_trans)
  using not_less_iff_gr_or_eq by blast

lift_definition clopen_ivlL :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" is
  "\<lambda>l. \<lambda>r. (if enat l < r then (\<lambda>i. l < i, \<lambda>i. enat i \<le> r, r \<noteq> \<infinity>) else (\<lambda>_. True, \<lambda>_. True, False))"
  using enat_iless Suc_ile_eq
  by (auto simp: upclosed_def downclosed_def not_le order_subst2)

lemma interval_bounds:
  fixes a:: nat
  fixes b:: enat
  fixes I::\<I>
  assumes "a \<le> b"
  assumes "I = interval a b"
  shows "memL I = (\<lambda>i. a \<le> i) \<and> memR I = (\<lambda>i. enat i \<le> b) \<and> (bounded I = (b \<noteq> \<infinity>))"
  using assms
  by transfer auto

(* [a, b] \<Rightarrow> [b+1, \<infinity>] *)
lift_definition flip_int :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if bounded I then ((\<lambda>i. \<not>memR I i), (\<lambda>i. True), False) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

(* [a, b] \<Rightarrow> [b+1, 2b]. nonempty if b+1\<le>2b \<Leftrightarrow> 1\<le>b *)
lift_definition flip_int_double_upper :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if (bounded I) then ((\<lambda>i. \<not>memR I i), (\<lambda>i. memR I ((div) i 2)), True) else ((\<lambda>i. True), (\<lambda>i. True), False)"
proof -
  define A where "A = {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
  {
    fix I :: \<I>
    assume I_props: "bounded I"
    define B where "B = {x. \<not> memR I x}"
    define b where "b = Inf B"
    define x where "x = 2 * b"
    have up: "upclosed (\<lambda>i. \<not> memR I i)"
      using memR_antimono upclosed_def
      by blast
    {
      fix r m
      assume assumptions: "(\<lambda>i. memR I ((div) i 2)) r" "m\<le>r"
      then have "(\<lambda>i. memR I ((div) i 2)) m" by auto
    }
    then have "\<forall>m r. (\<lambda>i. memR I ((div) i 2)) r \<longrightarrow> m \<le> r \<longrightarrow> (\<lambda>i. memR I ((div) i 2)) m" by auto
    then have down: "downclosed (\<lambda>i. memR I ((div) i 2))" using downclosed_def by auto
    have "\<exists>b. \<not>memR I b" using I_props bounded_memR by auto
    then have B_props: "B \<noteq> {}" using B_def by auto
    then have "b \<in> B" using b_def by (simp add: Inf_nat_def1)
    then have b_props: "\<not> memR I b" using B_def by auto
    then have "0 < b" using memR_nonzeroD by blast
    then have b_half_props: "(b div 2) < b" by auto
    {
      assume "\<not> memR I (b div 2)"
      then have "(b div 2) \<in> B" using B_def by blast
      then have "(b div 2) \<ge> b" using cInf_lower b_def by auto
      then have "False" using b_half_props by auto
    }
    then have "memR I (b div 2)" by blast
    moreover have "\<not>memR I (x div 2)" using x_def b_props by auto
    ultimately have "(\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) \<in> A"
      using b_props A_def up down
      by auto
  }
  then have "\<forall>I. bounded I \<longrightarrow> (\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) \<in> A" by auto
  moreover have "\<forall>I. \<not>bounded I \<longrightarrow> (\<lambda>i. True, \<lambda>i. True, False) \<in> A"
    using A_def
    by (metis Interval.all.rep_eq Rep_\<I>)
  ultimately have "\<forall>I. (if bounded I then (\<lambda>i. \<not> memR I i, \<lambda>i. memR I (i div 2), True) else (\<lambda>i. True, \<lambda>i. True, False)) \<in> A"
    by (auto split: if_splits)
  then show "\<And>\<I>. (if bounded \<I> then (\<lambda>i. \<not> memR \<I> i, \<lambda>i. memR \<I> (i div 2), True) else (\<lambda>i. True, \<lambda>i. True, False))
         \<in> {(memL, memR, bounded). (\<exists>m. memL m \<and> memR m) \<and> upclosed memL \<and> downclosed memR \<and> bounded = (\<exists>m. \<not> memR m)}"
    using A_def
    by auto
qed

(* [a, b] \<Rightarrow> [0, a-1] *)
lift_definition flip_int_less_lower :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. if \<not>memL I 0 then ((\<lambda>i. True), (\<lambda>i. \<not>memL I i), True) else ((\<lambda>i. True), (\<lambda>i. True), False)"
  by transfer (auto simp: upclosed_def downclosed_def)

(* [a, b] \<Rightarrow> [0, b] *)
lift_definition int_remove_lower_bound :: "\<I> \<Rightarrow> \<I>" is
  "\<lambda>I. ((\<lambda>i. True), (\<lambda>i. memR I i), bounded I)"
  by transfer (auto simp: upclosed_def downclosed_def)

lemma flip_int_props:
  assumes "bounded I"
  assumes "I' = flip_int I"
  shows "\<not>bounded I' \<and> \<not>mem I' 0"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_props:
  assumes "\<not>memL I 0" (* [a, b] *)
  assumes "I' = flip_int_less_lower I" (* [0, a-1] *)
  shows "mem I' 0 \<and> bounded I'"
  using assms by (transfer') (auto split: if_splits)

lemma flip_int_less_lower_memL:
  assumes "\<not>memL I x" (* [a, b], x < a *)
  shows "memL (flip_int_less_lower I) x" (* x \<in> [0, a-1] *)
  using assms
  by (transfer') (simp)

lemma flip_int_less_lower_memR:
  assumes "\<not>memL I 0" (* I = [a, b], I' = [0, a-1]. x \<le> a-1 *)
  shows "(memR (flip_int_less_lower I) x) = (\<not>memL I x)" (* x \<notin> [a, b] *)
  using assms
  by (transfer') (simp)

lemma flip_int_less_lower_mem:
  assumes "\<not>bounded I" "\<not>mem I x" (* [a, \<infinity>], x < a *)
  shows "mem (flip_int_less_lower I) x" (* x \<in> [0, a-1] *)
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

lemma flip_int_double_upper_bounded[simp]: "bounded (flip_int_double_upper I) = bounded I"
  by (transfer') (auto)

lemma int_remove_lower_bound_bounded[simp]: "bounded (int_remove_lower_bound I) = bounded I"
  by (transfer') (auto)

lemma int_remove_lower_bound_mem: "mem I x \<Longrightarrow> mem (int_remove_lower_bound I) x"
  by (transfer') (auto)

lemma memR_flip_int_double_upper: "memR I t \<Longrightarrow> memR (flip_int_double_upper I) t"
  by transfer auto

lemma int_remove_lower_bound_simps [simp]: 
  "memL (int_remove_lower_bound I) 0"
  "mem (int_remove_lower_bound I) 0"
  by (transfer, clarsimp)+

bundle ivl_no_notation
begin

(* use bold with \bold (warning: hard to copy-paste) *)
no_notation clopen_ivlR ("\<^bold>[_,_\<^bold>\<rangle>")
    and clopen_ivlL ("\<^bold>\<langle>_,_\<^bold>]")
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end

bundle ivl_notation
begin

(* use bold with \bold (warning: hard to copy-paste) *)
notation clopen_ivlR ("\<^bold>[_,_\<^bold>\<rangle>")
    and clopen_ivlL ("\<^bold>\<langle>_,_\<^bold>]")
     and Interval.interval ("\<^bold>[_,_\<^bold>]")

end

unbundle ivl_notation \<comment> \<open> enable notation \<close>

lemma memL_interval_simp[simp]: "memL \<^bold>[a,b\<^bold>] x \<longleftrightarrow> (a \<le> b \<and> a \<le> x) \<or> (a > b)"
  by transfer auto

lemma memL_clopen_ivlR_simp[simp]: "memL \<^bold>[a,b\<^bold>\<rangle> x \<longleftrightarrow> (a < b \<and> a \<le> x) \<or> (a \<ge> b)"
  by transfer auto

lemma memL_clopen_ivlL_simp[simp]: "memL \<^bold>\<langle>a,b\<^bold>] x \<longleftrightarrow> (a < b \<and> a < x) \<or> (a \<ge> b)"
  by transfer auto

lemma memR_interval_simp[simp]: "memR \<^bold>[a,b\<^bold>] x \<longleftrightarrow> (x \<le> b \<and> a \<le> b) \<or> (a > b)"
  by transfer auto

lemma memR_clopen_ivlR_simp[simp]: "memR \<^bold>[a,b\<^bold>\<rangle> x \<longleftrightarrow> (a < b \<and> x < b) \<or> (a \<ge> b)"
  by transfer auto

lemma memR_clopen_ivlL_simp[simp]: "memR \<^bold>\<langle>a,b\<^bold>] x \<longleftrightarrow> (a < b \<and> x \<le> b) \<or> (a \<ge> b)"
  by transfer auto

lemma mem_interval_simp[simp]: "mem \<^bold>[a,b\<^bold>] x \<longleftrightarrow> (a \<le> b \<and> a \<le> x \<and> x \<le> b) \<or> (a > b)"
  by transfer auto

lemma mem_clopen_ivlR_simp[simp]: "mem \<^bold>[a,b\<^bold>\<rangle> x \<longleftrightarrow> (a \<le> x \<and> x < b) \<or> (a \<ge> b)"
  by transfer auto

lemma mem_clopen_ivlL_simp[simp]: "mem \<^bold>\<langle>a,b\<^bold>] x \<longleftrightarrow> (a < x \<and> x \<le> b) \<or> (a \<ge> b)"
  by transfer auto

unbundle ivl_no_notation \<comment> \<open> disable notation \<close>


(*<*)
end
(*>*)