(*  Copyright 2021 Dawit Legesse Tirore, Dmitriy Traytel, Martin Raszyk
    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation; either version 2.1 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
    *)
theory Rewriting
  imports Formula
begin


subsection \<open> Rewriting \<close>

text \<open> For rewriting, we define a larger formula datatype and its semantics. 
We prove it consistent with the previous one, i.e. we add canonical projection 
@{text "project :: 'a formula \<Rightarrow> 'a Formula.formula"} and embedding 
@{text "embed :: 'a Formula.formula \<Rightarrow> 'a formula"} functions and show them 
correct (lemmas @{text "sat_project"} and @{text "sat_embed"}) with respect
to the previous semantics. In this new formula datatype, we define our rewriting 
and show its correctness (lemma @{text "final_sat"}). \<close>

(* Formula.sat           Rewriting.sat
      \<F> ------ embed ------> \<F>\<^sup>+
                              |
                              v
                           rewrite
                              |
                              v
      \<F> <----- project ----- \<F>\<^sup>+ *)


subsubsection \<open> New syntax and semantics \<close>

(* defining a larger formula datatype and its semantics *)
datatype (discs_sels) 'a formula = 
    Pred Formula.name "Formula.trm list"
  | Let Formula.name "'a formula" "'a formula"
  | LetPast Formula.name "'a formula" "'a formula"
  | Eq Formula.trm Formula.trm
  | Less Formula.trm Formula.trm
  | LessEq Formula.trm Formula.trm
  | Neg "'a formula"
  | Or "'a formula" "'a formula"
  | And "'a formula" "'a formula"
  | Ands "'a formula list"
  | Exists 'a "'a formula"
  | Agg nat "'a Formula.agg_op" "'a list" Formula.trm "'a formula"
  | Prev \<I> "'a formula" 
  | Next \<I> "'a formula"
  | Once \<I> "'a formula" 
  | Eventually \<I> "'a formula"
  | Historically \<I> "'a formula"
  | Always \<I> "'a formula"
  | Since "'a formula" \<I> "'a formula"
  | Until "'a formula" \<I> "'a formula"
  | Trigger "'a formula" \<I> "'a formula"
  | Release "'a formula" \<I> "'a formula"
  | MatchF \<I> "'a formula Regex.regex"
  | MatchP \<I> "'a formula Regex.regex"
  | TP Formula.trm
  | TS Formula.trm

bundle rewrite_no_notation
begin

no_notation Pred ("_ \<dagger>\<^sub>R _" [85, 85] 85)
     and Eq (infixl "=\<^sub>R" 75)
     and LessEq ("(_/ \<le>\<^sub>R _)" [76,76] 75)
     and Less ("(_/ <\<^sub>R _)" [76,76] 75)
     and Neg ("\<not>\<^sub>R _" [82] 82)
     and And (infixr "\<and>\<^sub>R" 80)
     and Or (infixr "\<or>\<^sub>R" 80)
     and Exists ("\<exists>\<^sub>R:_. _" [70,70] 70)
     and Ands ("\<And>\<^sub>R _" [70] 70)
     and Prev ("\<^bold>Y\<^sub>R _ _" [55, 65] 65)
     and Next ("\<^bold>X\<^sub>R _ _" [55, 65] 65)
     and Since ("_ \<^bold>S\<^sub>R _ _" [60,55,60] 60)
     and Until ("_ \<^bold>U\<^sub>R _ _" [60,55,60] 60)
     and Trigger ("_ \<^bold>T\<^sub>R _ _" [60,55,60] 60)
     and Release ("_ \<^bold>R\<^sub>R _ _" [60,55,60] 60)
     and Once ("\<^bold>P\<^sub>R _ _" [55, 65] 65)
     and Historically ("\<^bold>H\<^sub>R _ _" [55, 65] 65)
     and Eventually ("\<^bold>F\<^sub>R _ _" [55, 65] 65)
     and Always ("\<^bold>G\<^sub>R _ _" [55, 65] 65)

end

bundle rewrite_notation
begin

notation Pred ("_ \<dagger>\<^sub>R _" [85, 85] 85)
     and Eq (infixl "=\<^sub>R" 75)
     and LessEq ("(_/ \<le>\<^sub>R _)" [76,76] 75)
     and Less ("(_/ <\<^sub>R _)" [76,76] 75)
     and Neg ("\<not>\<^sub>R _" [82] 82)
     and And (infixr "\<and>\<^sub>R" 80)
     and Or (infixr "\<or>\<^sub>R" 80)
     and Exists ("\<exists>\<^sub>R:_. _" [70,70] 70)
     and Ands ("\<And>\<^sub>R _" [70] 70)
     and Prev ("\<^bold>Y\<^sub>R _ _" [55, 65] 65)
     and Next ("\<^bold>X\<^sub>R _ _" [55, 65] 65)
     and Since ("_ \<^bold>S\<^sub>R _ _" [60,55,60] 60)
     and Until ("_ \<^bold>U\<^sub>R _ _" [60,55,60] 60)
     and Trigger ("_ \<^bold>T\<^sub>R _ _" [60,55,60] 60)
     and Release ("_ \<^bold>R\<^sub>R _ _" [60,55,60] 60)
     and Once ("\<^bold>P\<^sub>R _ _" [55, 65] 65)
     and Historically ("\<^bold>H\<^sub>R _ _" [55, 65] 65)
     and Eventually ("\<^bold>F\<^sub>R _ _" [55, 65] 65)
     and Always ("\<^bold>G\<^sub>R _ _" [55, 65] 65)

end

unbundle MFODL_notation
unbundle rewrite_notation

primrec project :: "'a formula \<Rightarrow> 'a Formula.formula"
  where "project (p \<dagger>\<^sub>R ts) = p \<dagger> ts"
  | "project (Let p \<phi> \<psi>) = Formula.Let p (project \<phi>) (project \<psi>)"
  | "project (LetPast p \<phi> \<psi>) = Formula.LetPast p (project \<phi>) (project \<psi>)"
  | "project (t1 =\<^sub>R t2) = (t1 =\<^sub>F t2)"
  | "project (t1 \<le>\<^sub>R t2) = (t1 \<le>\<^sub>F t2)"
  | "project (t1 <\<^sub>R t2) = (t1 <\<^sub>F t2)"
  | "project (\<not>\<^sub>R \<phi>) = \<not>\<^sub>F (project \<phi>)"
  | "project (\<phi> \<or>\<^sub>R \<psi>) = (project \<phi>) \<or>\<^sub>F (project \<psi>)"
  | "project (\<phi> \<and>\<^sub>R \<psi>) = (project \<phi>) \<and>\<^sub>F (project \<psi>)"
  | "project (\<And>\<^sub>R \<phi>s) = \<And>\<^sub>F (map project \<phi>s)"
  | "project (\<exists>\<^sub>R:t. \<phi>) = \<exists>\<^sub>F:t. (project \<phi>)"
  | "project (Agg y \<omega> b' f \<phi>) = Formula.Agg y \<omega> b' f (project \<phi>)"
  | "project (\<^bold>Y\<^sub>R I \<phi>) = \<^bold>Y I (project \<phi>)"
  | "project (\<^bold>X\<^sub>R I \<phi>) = \<^bold>X I (project \<phi>)"
  | "project (\<^bold>P\<^sub>R I \<phi>) = once I (project \<phi>)"
  | "project (\<^bold>F\<^sub>R I \<phi>) = eventually I (project \<phi>)"
  | "project (\<^bold>H\<^sub>R I \<phi>) = historically I (project \<phi>)"
  | "project (\<^bold>G\<^sub>R I \<phi>) = always I (project \<phi>)"
  | "project (\<phi> \<^bold>S\<^sub>R I \<psi>) = (project \<phi>) \<^bold>S I (project \<psi>)"
  | "project (\<phi> \<^bold>U\<^sub>R I \<psi>) = (project \<phi>) \<^bold>U I (project \<psi>)"
  | "project (\<phi> \<^bold>T\<^sub>R I \<psi>) = (project \<phi>) \<^bold>T I (project \<psi>)"
  | "project (\<phi> \<^bold>R\<^sub>R I \<psi>) = (project \<phi>) \<^bold>R I (project \<psi>)"
  | "project (MatchF I r) = Formula.MatchF I (regex.map_regex project r)"
  | "project (MatchP I r) = Formula.MatchP I (regex.map_regex project r)"
  | "project (TP t) = Formula.TP t"
  | "project (TS t) = Formula.TS t"

primrec embed :: "'a Formula.formula \<Rightarrow> 'a formula"
  where "embed (p \<dagger> ts) = p \<dagger>\<^sub>R ts"
  | "embed (Formula.Let p \<phi> \<psi>) = Let p (embed \<phi>) (embed \<psi>)"
  | "embed (Formula.LetPast p \<phi> \<psi>) = LetPast p (embed \<phi>) (embed \<psi>)"
  | "embed (t1 =\<^sub>F t2) = (t1 =\<^sub>R t2)"
  | "embed (t1 \<le>\<^sub>F t2) = (t1 \<le>\<^sub>R t2)"
  | "embed (t1 <\<^sub>F t2) = (t1 <\<^sub>R t2)"
  | "embed (\<not>\<^sub>F \<phi>) = \<not>\<^sub>R (embed \<phi>)"
  | "embed (\<phi> \<or>\<^sub>F \<psi>) = (embed \<phi>) \<or>\<^sub>R (embed \<psi>)"
  | "embed (\<phi> \<and>\<^sub>F \<psi>) = (embed \<phi>) \<and>\<^sub>R (embed \<psi>)"
  | "embed (\<And>\<^sub>F \<phi>s) = \<And>\<^sub>R (map embed \<phi>s)"
  | "embed (\<exists>\<^sub>F:t. \<phi>) = \<exists>\<^sub>R:t. (embed \<phi>)"
  | "embed (Formula.Agg y \<omega> b' f \<phi>) = Agg y \<omega> b' f (embed \<phi>)"
  | "embed (\<^bold>Y I \<phi>) = \<^bold>Y\<^sub>R I (embed \<phi>)"
  | "embed (\<^bold>X I \<phi>) = \<^bold>X\<^sub>R I (embed \<phi>)"
  | "embed (\<phi> \<^bold>S I \<psi>) = (embed \<phi>) \<^bold>S\<^sub>R I (embed \<psi>)"
  | "embed (\<phi> \<^bold>U I \<psi>) = (embed \<phi>) \<^bold>U\<^sub>R I (embed \<psi>)"
  | "embed (\<phi> \<^bold>T I \<psi>) = (embed \<phi>) \<^bold>T\<^sub>R I (embed \<psi>)"
  | "embed (\<phi> \<^bold>R I \<psi>) = (embed \<phi>) \<^bold>R\<^sub>R I (embed \<psi>)"
  | "embed (Formula.MatchF I r) = MatchF I (regex.map_regex embed r)"
  | "embed (Formula.MatchP I r) = MatchP I (regex.map_regex embed r)"
  | "embed (Formula.TP t) = TP t"
  | "embed (Formula.TS t) = TS t"

lemma project_embed: "project (embed \<phi>) = \<phi>"
  by (induct \<phi>)
    (auto simp: list.map_ident_strong 
      regex.map_comp regex.map_ident_strong)

fun fvi :: "nat \<Rightarrow> 't formula \<Rightarrow> nat set" 
  where "fvi b (Pred r ts) = (\<Union>t\<in>set ts. Formula.fvi_trm b t)"
  | "fvi b (Let p \<phi> \<psi>) = fvi b \<psi>"
  | "fvi b (LetPast p \<phi> \<psi>) = fvi b \<psi>"
  | "fvi b (Eq t1 t2) = Formula.fvi_trm b t1 \<union> Formula.fvi_trm b t2"
  | "fvi b (Less t1 t2) = Formula.fvi_trm b t1 \<union> Formula.fvi_trm b t2"
  | "fvi b (LessEq t1 t2) = Formula.fvi_trm b t1 \<union> Formula.fvi_trm b t2"
  | "fvi b (Neg \<phi>) = fvi b \<phi>"
  | "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  | "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  | "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
  | "fvi b (Exists t \<phi>) = fvi (Suc b) \<phi>"
  | "fvi b (Agg y \<omega> tys f \<phi>) = fvi (b + length tys) \<phi> 
      \<union> Formula.fvi_trm (b + length tys) f \<union> (if b \<le> y then {y - b} else {})"
  | "fvi b (Prev I \<phi>) = fvi b \<phi>"
  | "fvi b (Next I \<phi>) = fvi b \<phi>"
  | "fvi b (\<^bold>P\<^sub>R I \<phi>) = fvi b \<phi>"
  | "fvi b (\<^bold>F\<^sub>R I \<phi>) = fvi b \<phi>"
  | "fvi b (\<^bold>H\<^sub>R I \<phi>) = fvi b \<phi>"
  | "fvi b (\<^bold>G\<^sub>R I \<phi>) = fvi b \<phi>"
  | "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  | "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  | "fvi b (Trigger \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  | "fvi b (Release \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  | "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
  | "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"
  | "fvi b (TP t) = Formula.fvi_trm b t"
  | "fvi b (TS t) = Formula.fvi_trm b t"

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> tys f \<phi>)
  let ?b' = "length tys"
  have *: "b + c + ?b' = b + ?b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  using fvi_plus[where c=1] by simp

lemma fvi_iff_fv: "x \<in> fvi b \<phi> \<longleftrightarrow> x + b \<in> fvi 0 \<phi>"
  using fvi_plus[where b=0 and c=b] by simp_all

definition nfv :: "'t formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fvi 0 \<phi>))"

lemma nfv_simps[simp]:
  "nfv (Let p \<phi> \<psi>) = nfv \<psi>"
  "nfv (LetPast p \<phi> \<psi>) = nfv \<psi>"
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = Regex.nfv_regex (fvi 0) r"
  "nfv (MatchF I r) = Regex.nfv_regex (fvi 0) r"
  unfolding nfv_def Regex.nfv_regex_def 
  by (simp_all add: image_Un Max_Un[symmetric])

lemma fv_project: "FV (project \<phi>) = fvi 0 \<phi>"
proof (induct \<phi>)
next
  case (Exists t \<phi>)
  thus ?case
    by (auto simp: fvi_Suc Formula.fvi_Suc)
next
  case (Agg y \<omega> b' f \<phi>)
  hence "Formula.fvi (length b') (project \<phi>) \<subseteq> fvi (length b') \<phi>"
    apply (clarsimp simp: subset_eq)
    by (subst (asm) Formula.fvi_iff_fv, subst fvi_iff_fv) simp
  moreover have "fvi (length b') \<phi> \<subseteq> Formula.fvi (length b') (project \<phi>)"
    using Agg apply (clarsimp simp: subset_eq)
    by (subst (asm) fvi_iff_fv, subst Formula.fvi_iff_fv, simp)
  ultimately show ?case
    by auto
next
  case (MatchP I r)
  thus ?case
    by (induct r; clarsimp)
next
  case (MatchF I r)
  thus ?case
    by (induct r; clarsimp)
qed auto

lemma nfv_project: "Formula.nfv (project \<phi>) = nfv \<phi>"
  by (simp add: nfv_def Formula.nfv_def fv_project)

lemma fvi_embed[simp]: "fvi 0 (embed \<phi>) = FV \<phi>"
proof (induct \<phi>)
next
  case (Exists t \<phi>)
  thus ?case
    by (auto simp: fvi_Suc Formula.fvi_Suc)
next
  case (Agg y \<omega> b' f \<phi>)
  hence "Formula.fvi (length b') \<phi> \<subseteq> fvi (length b') (embed \<phi>)"
    apply (clarsimp simp: subset_eq)
    by (subst (asm) Formula.fvi_iff_fv, subst fvi_iff_fv) simp
  moreover have "fvi (length b') (embed \<phi>) \<subseteq> Formula.fvi (length b') \<phi>"
    using Agg apply (clarsimp simp: subset_eq)
    by (subst (asm) fvi_iff_fv, subst Formula.fvi_iff_fv, simp)
  ultimately show ?case
    by auto
next
  case (MatchP I r)
  thus ?case
    by (induct r; clarsimp)
next
  case (MatchF I r)
  thus ?case
    by (induct r; clarsimp)
qed auto

lemma nfv_embed[simp]: "nfv (embed \<phi>) = Formula.nfv \<phi>"
  by (simp add: nfv_def Formula.nfv_def)

fun sat :: "Formula.trace \<Rightarrow> (Formula.name \<times> nat \<rightharpoonup> Formula.env \<Rightarrow> nat \<Rightarrow> bool) 
  \<Rightarrow> Formula.env \<Rightarrow> nat \<Rightarrow> ty formula \<Rightarrow> bool" 
  where "sat \<sigma> V v i (Pred r ts) = (case V (r, length ts) of
       None \<Rightarrow> (r, map (Formula.eval_trm v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> X (map (Formula.eval_trm v) ts) i)"
  | "sat \<sigma> V v i (Let p \<phi> \<psi>) = sat \<sigma> (V((p, nfv \<phi>) \<mapsto> \<lambda>w j. sat \<sigma> V w j \<phi>)) v i \<psi>"
  | "sat \<sigma> V v i (LetPast p \<phi> \<psi>) =
      (let pn = (p, nfv \<phi>) in
      sat \<sigma> (V(pn \<mapsto> letpast_sat (\<lambda>X u k. sat \<sigma> (V(pn \<mapsto> X)) u k \<phi>))) v i \<psi>)"
  | "sat \<sigma> V v i (Eq t1 t2) = (Formula.eval_trm v t1 = Formula.eval_trm v t2)"
  | "sat \<sigma> V v i (Less t1 t2) = (Formula.eval_trm v t1 < Formula.eval_trm v t2)"
  | "sat \<sigma> V v i (LessEq t1 t2) = (Formula.eval_trm v t1 \<le> Formula.eval_trm v t2)"
  | "sat \<sigma> V v i (Neg \<phi>) = (\<not> sat \<sigma> V v i \<phi>)"
  | "sat \<sigma> V v i (Or \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<or> sat \<sigma> V v i \<psi>)"
  | "sat \<sigma> V v i (And \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v i \<psi>)"
  | "sat \<sigma> V v i (Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>)"
  | "sat \<sigma> V v i (Exists t \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
  | "sat \<sigma> V v i (Agg y \<omega> tys f \<phi>) =
      (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = length tys \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> Formula.eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
      in (M = {} \<longrightarrow> fvi 0 \<phi> \<subseteq> {0..<length tys}) \<and> v ! y = eval_agg_op \<omega> M)"
  | "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
  | "sat \<sigma> V v i (Next I \<phi>) = (mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) \<and> sat \<sigma> V v (Suc i) \<phi>)"
  | "sat \<sigma> V v i (Once I \<phi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<phi>)"
  | "sat \<sigma> V v i (Eventually I \<phi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<phi>)"
  | "sat \<sigma> V v i (Historically I \<phi>) = (\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  | "sat \<sigma> V v i (Always I \<phi>) = (\<forall>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<longrightarrow> sat \<sigma> V v j \<phi>)"
  | "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
  | "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
  | "sat \<sigma> V v i (Trigger \<phi> I \<psi>) = (\<forall>j\<le>i. (mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>)))"
  | "sat \<sigma> V v i (Release \<phi> I \<psi>) = (\<forall>j\<ge>i. (mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)) \<longrightarrow> (sat \<sigma> V v j \<psi> \<or> (\<exists>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>)))"
  | "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<and> Regex.match (sat \<sigma> V v) r j i)"
  | "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<and> Regex.match (sat \<sigma> V v) r i j)"
  | "sat \<sigma> V v i (TP t) = (Formula.eval_trm v t = EInt (integer_of_nat i))"
  | "sat \<sigma> V v i (TS t) = (Formula.eval_trm v t = EInt (integer_of_nat (\<tau> \<sigma> i)))"

lemma sat_project: "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> project \<phi> \<longleftrightarrow> sat \<sigma> V v i \<phi>"
proof (induct \<phi> arbitrary: \<sigma> V v i)
next
  case (MatchP I r)
  then show ?case 
    apply (induct r; clarsimp)
    by blast
      (smt (verit) match_cong match_map_regex)+
next
  case (MatchF I r)
  then show ?case
    apply (induct r; clarsimp)
    by blast
      (smt (verit) match_cong match_map_regex)+
qed (auto simp: fv_project nfv_project 
    simp del: fun_upd_apply 
    split: nat.splits)

lemma sat_embed: "sat \<sigma> V v i (embed \<phi>) \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
proof (induct \<phi> arbitrary: \<sigma> V v i)
next
  case (MatchP I r)
  then show ?case 
    apply (induct r; clarsimp)
    by blast
      (smt (verit) match_cong match_map_regex)+
next
  case (MatchF I r)
  then show ?case
    apply (induct r; clarsimp)
    by blast
      (smt (verit) match_cong match_map_regex)+
qed (auto simp del: fun_upd_apply 
    split: nat.splits)


subsubsection \<open> Definition of rewriting function \<close>

primrec rr_regex 
  where "rr_regex rr (Regex.Skip n) = {}"
  | "rr_regex rr (Regex.Test \<phi>) = rr \<phi>"
  | "rr_regex rr (Regex.Plus r s) = rr_regex rr r \<inter> rr_regex rr s"
  | "rr_regex rr (Regex.Times r s) = rr_regex rr r \<union> rr_regex rr s"
  | "rr_regex rr (Regex.Star r) = {}"

primrec tvars 
  where "tvars (Formula.Var v) = [v]"
  |"tvars (Formula.Const c) = []"
  |"tvars (Formula.F2i t) = tvars t"
  |"tvars (Formula.I2f t) = tvars t"
  |"tvars (Formula.UMinus t) = tvars t"
  |"tvars (Formula.Plus t1 t2) =  (tvars t1)@ (tvars t2)"
  |"tvars (Formula.Minus t1 t2) =  (tvars t1)@ (tvars t2)"
  |"tvars (Formula.Mult t1 t2) =  (tvars t1)@ (tvars t2)"
  |"tvars (Formula.Div t1 t2) =  (tvars t1)@ (tvars t2)"
  |"tvars (Formula.Mod t1 t2) =  (tvars t1)@ (tvars t2)"

primrec rr :: "nat \<Rightarrow> 'a formula \<Rightarrow> nat set" 
  where "rr b (Pred r ts) = (\<Union>t\<in>set ts. Formula.fvi_trm b t)"
  | "rr b (Let p \<phi> \<psi>) = rr b \<psi>"
  | "rr b (LetPast p \<phi> \<psi>) = rr b \<psi>"
  | "rr  b(Eq t1 t2) = (case (t1,t2) of
                               (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                              |(Formula.Const _,Formula.Var x) \<Rightarrow> {x-b}
                              | _ \<Rightarrow> {})"
  | "rr b (Less t1 t2) = (case (t1,t2) of
                        (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                        |_ \<Rightarrow> {})"
  | "rr b (LessEq t1 t2) = (case (t1,t2) of
                                              (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                                             |_ \<Rightarrow> {})"
  | "rr b (Or \<phi> \<psi>) =  (rr b \<phi>) \<inter> (rr b \<psi>)"
  | "rr b (And \<phi> \<psi>) = rr b \<psi> \<union> (rr b \<phi>)"
  | "rr b (Ands \<phi>s) = (let xs = map (rr b) \<phi>s in \<Union>x\<in>set xs. x)"
  | "rr b (Exists t \<phi>) = (if (0 \<in> (rr 0 \<phi>)) then rr (Suc b) \<phi> else {})"
  | "rr b (Agg y \<omega> b' f \<phi>) = (if {0..<length b'} \<subseteq> rr 0 \<phi> 
      then {y} \<union> rr (b + length b') \<phi> else {})" (*How?*)
  | "rr b (Prev I \<phi>) = rr b \<phi>"
  | "rr b (Next I \<phi>) = rr b \<phi>"
  | "rr b (Since \<phi> I \<psi>) = rr b \<psi>"
  | "rr b (Until \<phi> I \<psi>) = rr b \<psi>"
  | "rr b (Release \<phi> I \<psi>) = (if \<not> (mem I 0) then {} else rr b \<psi>)"
  | "rr b (Trigger \<phi> I \<psi>) = (if \<not> (mem I 0) then {} else rr b \<psi>)"
  | "rr b (MatchF I r) = {}" (*rr_regex should have been used here*)
  | "rr b (MatchP I r) = {}" (*and here*)
  | "rr b (Neg \<alpha>) = {}"
  | "rr b (Eventually I \<alpha>) = rr b \<alpha>"
  | "rr b (Once I \<alpha>) = rr b \<alpha>"
  | "rr b (Always I \<alpha>) = (if \<not> (mem I 0) then {} else rr b \<alpha>)"
  | "rr b (Historically I \<alpha>) = (if \<not> (mem I 0) then {} else rr b \<alpha>)"
  | "rr b (TP t) = Formula.fvi_trm b t"
  | "rr b (TS t) = Formula.fvi_trm b t"

abbreviation "fvi_r b r \<equiv> Formula.fvi b (project r)"

definition prop_cond :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool"
  where "prop_cond f1 f2 =
       (let rr1 = rr 0 f1;
            rr2 = rr 0 f2;
            fv2 = fvi_r 0 f2
        in (rr1 \<inter> (fv2-rr2))\<noteq> {})"

(*------------setup and lemmas about shifting valuation list----------------------------*)

fun shiftTI :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" 
  where "shiftTI k (Formula.Var i) = (if i < k then Formula.Var i
                                               else Formula.Var (i + 1))"
  | "shiftTI k (Formula.Plus t u) = Formula.Plus (shiftTI k t) (shiftTI k u)"
  | "shiftTI k (Formula.Minus t u) = Formula.Minus (shiftTI k t) (shiftTI k u)"
  | "shiftTI k (Formula.UMinus t) = Formula.UMinus (shiftTI k t)"
  | "shiftTI k (Formula.Mult t u) = Formula.Mult (shiftTI k t) (shiftTI k u)"
  | "shiftTI k (Formula.Div t u) = Formula.Div (shiftTI k t) (shiftTI k u)"
  | "shiftTI k (Formula.Mod t u) = Formula.Mod (shiftTI k t) (shiftTI k u)"
  | "shiftTI k (Formula.F2i t) = Formula.F2i (shiftTI k t)"
  | "shiftTI k (Formula.I2f t) = Formula.I2f (shiftTI k t)"
  | "shiftTI k (Formula.Const n) = (Formula.Const n)"

lemma eval_trm_shiftTI: "length xs = b \<Longrightarrow>
  Formula.eval_trm (xs @ z # v) (shiftTI b t) = Formula.eval_trm (xs @ v) t"
  by (induct b t rule: shiftTI.induct) (auto simp: nth_append split: trm.splits)

lemma shift_fv_in_t: "x+1 \<in> Formula.fvi_trm b (shiftTI b t) \<longleftrightarrow> x  \<in> Formula.fvi_trm b t"
   by (induction t;auto)

primrec shiftI :: "nat \<Rightarrow> 'a Formula.formula \<Rightarrow> 'a Formula.formula" 
  where "shiftI k (Formula.Pred r ts) = Formula.Pred r (map (shiftTI k) ts)"
  | "shiftI k (Formula.Exists t a) = Formula.Exists t (shiftI (Suc k) a)"
  | "shiftI k (Formula.Let nm a b) = Formula.Let nm a (shiftI k b)" (*fixed error, a is not shifted*)
  | "shiftI k (Formula.LetPast nm a b) = Formula.LetPast nm a (shiftI k b)"
  | "shiftI k (Formula.Eq t1 t2) = Formula.Eq (shiftTI k t1) (shiftTI k t2)"
  | "shiftI k (Formula.Less t1 t2) =  Formula.Less (shiftTI k t1) (shiftTI k t2)"
  | "shiftI k (Formula.LessEq t1 t2) = Formula.LessEq (shiftTI k t1) (shiftTI k t2)"
  | "shiftI k (Formula.Neg a) = Formula.Neg (shiftI k a)"
  | "shiftI k (Formula.Or a b) = Formula.Or (shiftI k a) (shiftI k b)"
  | "shiftI k (Formula.And a b) = Formula.And (shiftI k a) (shiftI k b)"
  | "shiftI k (Formula.Ands as) = Formula.Ands (map (shiftI k) as)"
  | "shiftI k (Formula.Agg y op b t a) = Formula.Agg (if y < k then y else y + 1)
                                              op b (shiftTI (k + length b) t) (shiftI (k + length b) a)"
  | "shiftI k (Formula.Prev \<I> a) = Formula.Prev \<I> (shiftI k a)"
  | "shiftI k (Formula.Next \<I> a) = Formula.Next \<I> (shiftI k a)"
  | "shiftI k (Formula.Since a1 \<I> a2) = Formula.Since (shiftI k a1) \<I> (shiftI k a2)"
  | "shiftI k (Formula.Until a1 \<I> a2) = Formula.Until (shiftI k a1) \<I> (shiftI k a2)"
  | "shiftI k (Formula.Trigger a1 \<I> a2) = Formula.Trigger (shiftI k a1) \<I> (shiftI k a2)"
  | "shiftI k (Formula.Release a1 \<I> a2) = Formula.Release (shiftI k a1) \<I> (shiftI k a2)"
  | "shiftI k (Formula.MatchF \<I> r) = Formula.MatchF \<I> (Regex.map_regex (shiftI k) r)"
  | "shiftI k (Formula.MatchP \<I> r) = Formula.MatchP \<I> (Regex.map_regex (shiftI k) r)"
  | "shiftI k (Formula.TP t) = Formula.TP (shiftTI k t)"
  | "shiftI k (Formula.TS t) = Formula.TS (shiftTI k t)"

abbreviation shift :: "'a Formula.formula \<Rightarrow> 'a Formula.formula" 
  where "shift \<equiv> shiftI 0"

lemma fvi_trm_shift: "b'\<le>b \<Longrightarrow> Formula.fvi_trm b t = Formula.fvi_trm (Suc b) (Rewriting.shiftTI b' t)"  
  by (induction t;auto)

lemma fvi_shift: "b' \<le> b \<Longrightarrow> Formula.fvi b \<phi> = Formula.fvi (Suc b) (Rewriting.shiftI b' \<phi>)"
proof(induction \<phi> arbitrary: b b')
  case (Agg x1 x2 x3 x4 \<phi>)
  then have le:"b' + length x3 \<le> b + length x3" by simp
  from Agg show ?case by(simp add:Agg(1)[OF le] fvi_trm_shift[OF le])
next
  case (MatchF I r)
  then show ?case by (induction r;auto)
next
  case (MatchP I r)
  then show ?case by (induction r;auto)
qed  (auto simp add: fvi_trm_shift)

primrec shiftI_r :: "nat \<Rightarrow> 'a formula \<Rightarrow> 'a formula" 
  where "shiftI_r k (Pred r ts) = Pred r (map (shiftTI k) ts)"
  | "shiftI_r k (Exists t a) = Exists t (shiftI_r (Suc k) a)"
  | "shiftI_r k (Let nm a b) = Let nm a (shiftI_r k b)" (*fixed error, a is not shifted*)
  | "shiftI_r k (LetPast nm a b) = LetPast nm a (shiftI_r k b)"
  | "shiftI_r k (Eq t1 t2) = Eq (shiftTI k t1) (shiftTI k t2)"
  | "shiftI_r k (Less t1 t2) =  Less (shiftTI k t1) (shiftTI k t2)"
  | "shiftI_r k (LessEq t1 t2) = LessEq (shiftTI k t1) (shiftTI k t2)"
  | "shiftI_r k (Neg a) = Neg (shiftI_r k a)"
  | "shiftI_r k (Or a b) = Or (shiftI_r k a) (shiftI_r k b)"
  | "shiftI_r k (And a b) = And (shiftI_r k a) (shiftI_r k b)"
  | "shiftI_r k (Ands as) = Ands (map (shiftI_r k) as)"
  | "shiftI_r k (Agg y op b t a) = Agg (if y < k then y else y + 1)
                                              op b (shiftTI (k + length b) t) (shiftI_r (k + length b) a)"
  | "shiftI_r k (Prev \<I> a) = Prev \<I> (shiftI_r k a)"
  | "shiftI_r k (Next \<I> a) = Next \<I> (shiftI_r k a)"
  | "shiftI_r k (Since a1 \<I> a2) = Since (shiftI_r k a1) \<I> (shiftI_r k a2)"
  | "shiftI_r k (Until a1 \<I> a2) = Until (shiftI_r k a1) \<I> (shiftI_r k a2)"
  | "shiftI_r k (Release a1 \<I> a2) = Release (shiftI_r k a1) \<I> (shiftI_r k a2)"
  | "shiftI_r k (Trigger a1 \<I> a2) = Trigger (shiftI_r k a1) \<I> (shiftI_r k a2)"
  | "shiftI_r k (Eventually \<I> a2) = Eventually \<I> (shiftI_r k a2)"
  | "shiftI_r k (Once \<I> a2) = Once \<I> (shiftI_r k a2)"
  | "shiftI_r k (Historically \<I> a2) = Historically \<I> (shiftI_r k a2)"
  | "shiftI_r k (Always \<I> a2) = Always \<I> (shiftI_r k a2)"
  | "shiftI_r k (MatchF \<I> r) = MatchF \<I> (Regex.map_regex (shiftI_r k) r)"
  | "shiftI_r k (MatchP \<I> r) = MatchP \<I> (Regex.map_regex (shiftI_r k) r)"
  | "shiftI_r k (TP t) = TP (shiftTI k t)"
  | "shiftI_r k (TS t) = TS (shiftTI k t)"

lemma project_shift: "project (shiftI_r b \<alpha>) = shiftI b (project \<alpha>)"
proof(induct \<alpha> arbitrary: b)
next
  case (MatchF I r)
  then show ?case 
    by (induction r) auto
next
  case (MatchP I r)
  then show ?case 
    by (induction r) auto
qed (auto simp: Formula.TT_def once_def always_def
    eventually_def historically_def)

lemma shift_fv_in_f: "(x+1) \<in> (Formula.fvi b (shiftI b \<phi>)) 
  \<longleftrightarrow> x \<in> (Formula.fvi b \<phi>)"
  using shift_fv_in_t 
proof (induction b \<phi> rule: Formula.fvi.induct)
  case (19 b I r)
  then show ?case by (induct r;auto)

next
case (20 b I r)
  then show ?case by (induct r;auto)
qed auto

lemma no_shift_t:  "b' \<le> x3 \<Longrightarrow> Formula.fvi_trm b' (shiftTI (b + x3) t) 
  \<subseteq> {0..<x3-b'} \<longleftrightarrow> Formula.fvi_trm b' t \<subseteq> {0..<x3-b'}"
  by (induction t; auto)

lemma no_shift:  "b' \<le> x3 \<Longrightarrow> Formula.fvi b' (shiftI (b + x3) \<phi>) \<subseteq> {0..<x3-b'} \<longleftrightarrow> Formula.fvi b' \<phi> \<subseteq> {0..<x3-b'}" (*MEETING: Do we want if on the top-lemma level?*)
proof(induction \<phi> arbitrary: b' x3)
  case (Ands x)
  then show ?case
    by fastforce (*MEETING: why do I have to instansiate b'? A: To obtain a faster proof by auto *)
next
  case (Pred r ts)
  thm no_shift_t[OF Pred(1)]
  then have helper: "((\<Union>a\<in>set ts. Formula.fvi_trm b' (shiftTI (b + x3) a)) \<subseteq> {0..<x3 - b'}) =
                     (\<Union> (Formula.fvi_trm b' ` set ts) \<subseteq> {0..<x3 - b'})" using no_shift_t[OF Pred(1)] by (auto;simp)
  from Pred helper show ?case by auto
next
  case (Exists \<phi>)
  from Exists(2) have suc_lemma: "Suc b' \<le> Suc x3" by simp
  from Exists(1)[OF suc_lemma] show ?case by simp
next
  case (Agg xy op bb' t \<phi>)
  define bb where [simp]: "bb = length bb'"
  from Agg(2) have plusbb: "b' + bb \<le> x3+bb" by simp
  from Agg(1)[OF plusbb] have helper1: "(Formula.fvi (b' + bb) (shiftI (b + (x3 + bb)) \<phi>)) \<subseteq> {0..<x3 - b'} =
                 ((Formula.fvi (b' + bb) \<phi>)  \<subseteq> {0..<x3 - b'})" by simp


  from no_shift_t[OF plusbb] have helper2: "(Formula.fvi_trm (b' + bb) (shiftTI (b + (x3 + bb)) t) \<subseteq> {0..<x3 - b'}) =
                                            (Formula.fvi_trm (b' + bb) t \<subseteq> {0..<x3 - b'}) " by simp

  from plusbb have helper3: "((if b' \<le> (if xy < b + x3 then xy else xy + 1) then {(if xy < b + x3 then xy else xy + 1) - b'} else {}) \<subseteq> {0..<x3 - b'}) =
                 ((if b' \<le> xy then {xy - b'} else {}) \<subseteq> {0..<x3 - b'})" by auto

  have helper: "(Formula.fvi (b' + bb) (shiftI (b + (x3 + bb)) \<phi>) \<union>
                Formula.fvi_trm (b' + bb) (shiftTI (b + (x3 + bb)) t) \<union>
                (if b' \<le> (if xy < b + x3 then xy else xy + 1) then {(if xy < b + x3 then xy else xy + 1) - b'} else {}) \<subseteq> {0..<x3 - b'}) =
                (Formula.fvi (b' + bb) \<phi> \<union>
                Formula.fvi_trm (b' + bb) t \<union>
                (if b' \<le> xy then {xy - b'} else {}) \<subseteq> {0..<x3 - b'})" 
    by (simp add: helper1 helper2 helper3 del:bb_def)
  have assoc: "b + x3 + bb = b + (x3 + bb)" by simp
  show ?case 
    by (simp only: shiftI.simps Formula.fvi.simps 
        helper assoc flip:bb_def) 
      (*'simp only' because we aim for the helper-lemma as the last goal*)
next
  case (MatchF I r)
  then show ?case 
    by (induction r) auto
next
  case (MatchP I r)
  then show ?case 
    by (induction r) auto
qed (auto simp: no_shift_t)

lemma match_map_regex: "(\<And>k a. a \<in> Regex.atms r \<Longrightarrow> sat1 k (f a) \<longleftrightarrow> sat2 k a) \<Longrightarrow>
  Regex.match sat1 (regex.map_regex f r) = Regex.match sat2 r"
  by (induction r) simp_all

lemma sat_shift: "length xs = b 
  \<Longrightarrow> Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) 
  \<longleftrightarrow> Formula.sat \<sigma> V (xs@v) i \<phi>"
proof(induction \<phi> arbitrary: V i xs b)
  case pred: (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (xs @ z # v) \<circ> shiftTI (length xs)) ts
             = map (Formula.eval_trm (xs @ v)) ts" by (auto simp:eval_trm_shiftTI)
  from pred show ?case by (auto split:option.splits simp:map_lemma)
  case (Exists \<phi>)
  then show ?case using Exists.IH[where xs= "_ # xs" and b="Suc b"] by (auto)
next
  case (Agg x1 x2 x3' x4 \<phi>)
  define x3 where [simp]:"x3 = length x3'"
  have rw11: "Formula.sat \<sigma> V (zs @ xs @ z # v) i (shiftI (b + x3) \<phi>) \<longleftrightarrow>
    Formula.sat \<sigma> V (zs @ xs @ v) i \<phi>" if "length zs = x3" for zs
    using Agg(1)[of "zs @ xs"] Agg(2) that
    by simp
  have rw12:
    "Formula.eval_trm (zs @ xs @ z # v) (shiftTI (b + x3) x4) =
    Formula.eval_trm (zs @ xs @ v) x4" if "length zs = x3" for zs
    using eval_trm_shiftTI[of "zs @ xs"] Agg(2) that
    by simp
  have rw1: "\<And>x. {zs. length zs = x3 \<and>
      Formula.sat \<sigma> V (zs @ xs @ z # v) i (shiftI (b + x3) \<phi>) \<and>
      Formula.eval_trm (zs @ xs @ z # v) (shiftTI (b + x3) x4) = x} =
    {zs. length zs = x3 \<and>
      Formula.sat \<sigma> V (zs @ xs @ v) i \<phi> \<and> Formula.eval_trm (zs @ xs @ v) x4 = x}"
    using rw11 rw12 by auto
  have rw2: "fv (shiftI (b + x3) \<phi>) \<subseteq> {0..<x3} \<longleftrightarrow> fv \<phi> \<subseteq> {0..<x3}" 
    using no_shift[where b'=0]
    apply (auto simp del:x3_def) using atLeastLessThan_iff by blast
  show ?case
    using Agg(2)
    by (auto simp add: rw1 rw2 nth_append simp flip:x3_def)
next
  case (Prev x1 \<phi>)
  then show ?case by (auto split:nat.splits)
next
  case (MatchF I r)
  have rw: "Regex.match (Formula.sat \<sigma> V (xs @ z # v)) (regex.map_regex (shiftI b) r) =
    Regex.match (Formula.sat \<sigma> V (xs @ v)) r"
    apply (rule match_map_regex)
    using MatchF
    by auto
  show ?case
    using MatchF
    by (simp add: rw)
next
  case (MatchP I r)
  have rw: "\<And>j. Regex.match (Formula.sat \<sigma> V (xs @ z # v)) (regex.map_regex (shiftI b) r) =
    Regex.match (Formula.sat \<sigma> V (xs @ v)) r"
    apply (rule match_map_regex)
    using MatchP
    by auto
  show ?case
    by (simp add: rw)
qed (auto simp: eval_trm_shiftTI)

(* I = [a, b] \<Longrightarrow> init_ivl I = [0, b]  *)
lift_definition init_ivl :: "\<I> \<Rightarrow> \<I>" is "\<lambda>(_,r,n). ((\<lambda>k. True),r,n)" 
  using zero_enat_def upclosed_def by auto

lemma left_init_ivl[simp]: "memL (init_ivl I) n"
  apply (clarsimp simp: memL_def init_ivl_def split: prod.splits)
  by (subst Abs_\<I>_inverse, transfer)
    (auto simp: upclosed_def downclosed_def)

lemma right_init_ivl[simp]: "memR (init_ivl I) = memR I" 
  by (transfer; auto)+

lemma nat_less_than_range: "\<And>i j:: nat. k \<in> {i..j} \<and> k' \<in>{i..j} \<Longrightarrow> (k-k') \<le> (j-i)"
proof -
  fix i j :: nat assume A:"k \<in> {i..j} \<and> k' \<in>{i..j}"
  show "(k-k') \<le> (j-i)"
  proof(cases "i\<le>j")
  case True
  then show ?thesis using A diff_le_mono2 by auto
next
  case False
  then show ?thesis using A by auto
qed
qed

lemma mem_of_init: "mem I j \<Longrightarrow>  \<forall>k\<le>j. mem (init_ivl I) k"
proof(induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then show ?case 
    by (metis left_init_ivl memR_antimono right_init_ivl)
qed

(*Main lemma used multiple times*)
lemma nat_less_mem_of_init: "\<And>i j. k \<in> {i..j} \<and> k' \<in>{i..j} 
  \<Longrightarrow> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) 
  \<Longrightarrow>  mem (init_ivl I) (\<tau> \<sigma> k - \<tau> \<sigma> k')"
proof -
  fix i j :: nat 
  assume A:"k \<in> {i..j} \<and> k' \<in>{i..j}" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)"
  then have "(\<tau> \<sigma> k - \<tau> \<sigma> k') \<le> (\<tau> \<sigma> j - \<tau> \<sigma> i)" 
    using nat_less_than_range by auto
  then show " mem (init_ivl I) (\<tau> \<sigma> k - \<tau> \<sigma> k')" 
    using A(2) mem_of_init by blast
qed

datatype argpos = Same | Swapped

fun size_argpos :: "argpos \<Rightarrow> nat"
  where "size_argpos Same = 1"
  | "size_argpos Swapped = 0"

primrec my_size_regex :: "('a \<Rightarrow> nat) \<Rightarrow> 'a Regex.regex \<Rightarrow> nat" 
  where "my_size_regex fun (Regex.Skip n) = 0"
  | "my_size_regex fun (Regex.Test \<phi>) = fun \<phi>"
  | "my_size_regex fun (Regex.Plus r s) = my_size_regex fun r + my_size_regex fun s"
  | "my_size_regex fun (Regex.Times r s) = my_size_regex fun r + my_size_regex fun s"
  | "my_size_regex fun (Regex.Star r) = my_size_regex fun r"

lemma my_size_regex_cong[fundef_cong]: "r = r' 
  \<Longrightarrow> (\<And>z. z \<in> Regex.atms r \<Longrightarrow> fun z = fun' z) 
  \<Longrightarrow> my_size_regex fun r = my_size_regex fun' r'"
  by (induct r arbitrary: r') auto

fun my_size_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" 
  where "my_size_list fun (f#fs) = fun f + my_size_list fun fs"
  | "my_size_list fun [] = 0"

lemma my_size_list_cong[fundef_cong]:
  "fs = fs' \<Longrightarrow> (\<And>z. z \<in> set fs \<Longrightarrow> fun z = fun' z) 
  \<Longrightarrow> my_size_list fun fs = my_size_list fun' fs'"
  by (induct fs arbitrary: fs') auto

(*define custom size function because it ignores everything but layers of formula constructors*)
fun my_size :: "'a formula \<Rightarrow> nat" where
  "my_size (Pred r ts) = 1"
| "my_size (Let p \<phi> \<psi>) = 1"
| "my_size (LetPast p \<phi> \<psi>) = 1"
| "my_size  (Eq t1 t2) = 1"
| "my_size (Less t1 t2) = 1"
| "my_size (LessEq t1 t2) = 1"
| "my_size (Or \<phi> \<psi>) =  1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (And \<phi> \<psi>) = 1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (Ands \<phi>s) = 1+ my_size_list my_size \<phi>s"
| "my_size (Exists t \<phi>) = 1 + my_size \<phi>"
| "my_size (Agg y \<omega> b' f \<phi>) = 1 + (my_size \<phi>)"
| "my_size (Prev I \<phi>) = 1+ my_size \<phi>"
| "my_size (Next I \<phi>) = 1+ my_size \<phi>"
| "my_size (Since \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (Until \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (Release \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (Trigger \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (MatchF I r) = 1 + (my_size_regex my_size r)"
| "my_size (MatchP I r) = 1 + (my_size_regex my_size r)"
| "my_size (Neg \<alpha>) = 1 + my_size \<alpha>"
| "my_size (Eventually I \<alpha>) = 1 + my_size \<alpha>"
| "my_size (Once I \<alpha>) =1 + my_size \<alpha>"
| "my_size (Always I \<alpha>) =1 + my_size \<alpha>"
| "my_size (Historically I \<alpha>) = 1 + my_size \<alpha>"
| "my_size (TP t) = 1"
| "my_size (TS t) = 1"

lemma ands_size: "my_size (Ands rs) > my_size_list my_size rs" 
  by simp

lemma my_size_neg_sub: "my_size a = my_size b \<Longrightarrow> my_size (Neg a) = my_size (Neg b)"
  by simp

lemma shift_size: "my_size (shiftI_r b \<alpha>) = my_size \<alpha>"
proof(induction \<alpha> arbitrary: b)
next
  case (Ands x)
  then show ?case 
    by (induction x) auto
next
  case (MatchF I r)
  then show ?case
    by (induction r) auto
next
  case (MatchP I r)
  then show ?case 
    by (induction r) auto
qed auto

lemma not_zero: "my_size \<alpha> > 0" 
  by (induction \<alpha>) auto

fun fix_r :: "'a formula \<Rightarrow> argpos \<Rightarrow> 'a formula"  
  where "fix_r (Since l I r) Swapped = Since r I l"
  | "fix_r (Until l I r) Swapped = Until r I l"
  | "fix_r r _ = r "

lemma not_swapped: "t \<noteq> Swapped \<Longrightarrow> t = Same" 
  by (induction t) auto

lemma fix_r_same: "fix_r r Same = r" 
  by auto

declare regex.map_cong[fundef_cong]

lemma my_size_list_estimation[termination_simp]: 
  "x \<in> set xs \<Longrightarrow> y < f x \<Longrightarrow> y < my_size_list f xs"
  by (induct xs) auto

lemma my_size_list_estimation'[termination_simp]: 
  "x \<in> set xs \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> my_size_list f xs"
  by (induct xs) auto

lemma my_size_regex_estimation[termination_simp]: 
  "x \<in> regex.atms r \<Longrightarrow> y < f x \<Longrightarrow> y < my_size_regex f r"
  by (induct r) auto

lemma my_size_regex_estimation'[termination_simp]: 
  "x \<in> regex.atms r \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> my_size_regex f r"
  by (induct r) auto

(* The function is inspired from "Section 5.3.4: 
Propagation of Range Restrictions" of Samuel Mueller's 
ETH PhD-thesis: Theory and applications of runtime
monitoring MFOTL. *)
function (sequential) rewrite :: "'a formula \<Rightarrow> argpos \<Rightarrow> 'a formula" 
  where
(*1*)  "rewrite (And \<alpha> (Or \<beta> \<gamma>)) t =
       (if prop_cond \<alpha> \<beta> \<or> prop_cond \<alpha> \<gamma>
       then Or (rewrite (And \<alpha> \<beta>) Same) (rewrite (And \<alpha> \<gamma>) Same)
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in And \<alpha>' (Or \<beta>' \<gamma>'))" (*added prop_cond gamma because the rewrite shouldn't be position dependent*)

(*2*) | "rewrite (And \<alpha> (Release \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then And (rewrite \<alpha> Same) (Release (rewrite (And \<beta> (Once (init_ivl I) \<alpha>)) Same) I (rewrite (And \<gamma> (Once I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (And \<alpha>' (Release \<beta>' I \<gamma>')))"

(*3*) | "rewrite (And \<alpha> (Trigger \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then And (rewrite \<alpha> Same) (Trigger (rewrite (And \<beta> (Eventually (init_ivl I) \<alpha>)) Same) I (rewrite (And \<gamma> (Eventually I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (And \<alpha>' (Trigger \<beta>' I \<gamma>')))"

(*4*) | "rewrite (And \<alpha> (Exists k \<beta>)) t =
       (if prop_cond \<alpha> \<beta>
        then Exists k (rewrite (And (shiftI_r 0 \<alpha>) \<beta>) Same)
        else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Exists k \<beta>'))"

(*5*) | "rewrite (And \<alpha> (Neg \<beta>)) t =
      (if prop_cond \<alpha> \<beta>
       then And (rewrite \<alpha> Same) ((Neg (rewrite (And \<alpha> \<beta>) Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Neg \<beta>'))"

(*10,12*) | "rewrite (And \<alpha> (Since \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Since (rewrite (And (Eventually (init_ivl I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Since (rewrite \<beta> Same) I (rewrite (And (Eventually I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in And \<alpha>' (Since \<beta>' I \<gamma>'))"

(*11,13*) | "rewrite (And \<alpha> (Until \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Until (rewrite (And (Once (init_ivl I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Until (rewrite \<beta> Same) I (rewrite (And (Once I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in And \<alpha>' (Until \<beta>' I \<gamma>'))"

(*18*) | "rewrite (And \<alpha> (Once I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I)
       then And (rewrite \<alpha> Same) (Once I (And (Eventually I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Once I \<beta>'))"

(*19*) | "rewrite (And \<alpha> (Eventually I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Eventually I (And (Once I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Eventually I \<beta>'))"

 (*20*) | "rewrite (And \<alpha> (Historically I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I)
       then And (rewrite \<alpha> Same) (Historically I (And (Eventually I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Historically I \<beta>'))" (*some of these rules don't rewrite the conjunction, of diamond/square, because it doesn't increase rr of the conjunction more than recursing the leaves*)

 (*21*) | "rewrite (And \<alpha> (Always I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Always I (And (Once I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Always I \<beta>'))"

 (*22*) | "rewrite (And \<alpha> (Prev I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Prev I (And (Next I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Prev I \<beta>'))"

(*23*) | "rewrite (And \<alpha> (Next I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Next I (And (Prev I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in (And \<alpha>' (Next I \<beta>')))"

(*6 first, then 8*)
| "rewrite (Since (And \<alpha> \<gamma>) I \<beta>) t =
             (let l = rewrite (And \<alpha> \<gamma>) Same;
                  r =      if t=Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> then rewrite (And (Eventually I \<alpha>) \<beta>) Same
                      else if t=Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> then rewrite (And (Eventually I \<gamma>) \<beta>) Same
                      else if t=Swapped \<and> bounded I \<and> prop_cond \<alpha> \<beta> then rewrite (And (Once (init_ivl I) \<alpha>) \<beta>) Same
                      else if t=Swapped \<and> bounded I \<and> prop_cond \<gamma> \<beta> then rewrite (And (Once (init_ivl I) \<gamma>) \<beta>) Same
                      else rewrite \<beta> Same
              in fix_r (Since l I r) t)"

(*7 first, else 9*) (*don't check bounded for 9 because rewrite doesn't alter monitorability for future unbounded temporal operators*)
| "rewrite (Until (And \<alpha> \<gamma>) I \<beta>) t =
             (let l = rewrite (And \<alpha> \<gamma>) Same;
                  r =      if t=Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta> then rewrite (And (Once I \<alpha>) \<beta>) Same
                      else if t=Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta> then rewrite (And (Once I \<gamma>) \<beta>) Same
                      else if t=Swapped \<and> prop_cond \<alpha> \<beta> then rewrite (And (Eventually (init_ivl I) \<alpha>) \<beta>) Same
                      else if t=Swapped \<and> prop_cond \<gamma> \<beta> then rewrite (And (Eventually (init_ivl I) \<gamma>) \<beta>) Same
                      else rewrite \<beta> Same
              in fix_r (Until l I r) t)"

| "rewrite (Since l I r) Same = rewrite (Since r I l) Swapped"
| "rewrite (Until l I r) Same = rewrite (Until r I l) Swapped"
| "rewrite (And l r) Same = rewrite (And r l) Swapped"

| "rewrite (Since l I r) Swapped = Since (rewrite r Same) I (rewrite l Same)" (*swap back before recursing on subformulas*)
| "rewrite (Until l I r) Swapped =  Until (rewrite r Same) I (rewrite l Same)"
| "rewrite (And l r) Swapped =  And (rewrite r Same) (rewrite l Same)"

| "rewrite (Or \<phi> \<psi>) t =  Or (rewrite \<phi> Same) (rewrite \<psi> Same)"

| "rewrite (Exists k \<phi>) t = Exists k (rewrite \<phi> Same)"
| "rewrite (Agg y \<omega> b' f \<phi>) t = Agg y \<omega> b' f (rewrite \<phi> Same)"
| "rewrite (Prev I \<phi>) t = Prev I (rewrite \<phi> Same)"
| "rewrite (Next I \<phi>) t = Next I (rewrite \<phi> Same)"

| "rewrite (Release \<phi> I \<psi>) t = Release (rewrite \<phi> Same) I (rewrite \<psi> Same)"
| "rewrite (Trigger \<phi> I \<psi>) t =  Trigger (rewrite \<phi> Same) I (rewrite \<psi> Same)"

| "rewrite (Neg \<alpha>) t = Neg (rewrite \<alpha> Same)"
| "rewrite (Eventually I \<alpha>) t = Eventually I (rewrite \<alpha> Same)"
| "rewrite (Once I \<alpha>) t = Once I (rewrite \<alpha> Same)"
| "rewrite (Always I \<alpha>) t = Always I (rewrite \<alpha> Same)"
| "rewrite (Historically I \<alpha>) t = Historically I (rewrite \<alpha> Same)"

| "rewrite (MatchF I r) t = MatchF I (regex.map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (MatchP I r) t = MatchP I (regex.map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (Ands \<phi>s) t = Ands (map (\<lambda>r. rewrite r Same) \<phi>s)"

| "rewrite f t =  f"
  by pat_completeness auto

(* 
(* TODO: Replace function above with the faster-loading version below *)
function (sequential) rewrite :: "'a formula \<Rightarrow> argpos \<Rightarrow> 'a formula"
  where "rewrite (And \<alpha> \<zeta>) t = (case \<zeta> of
      (Or \<beta> \<gamma>) \<Rightarrow> (if prop_cond \<alpha> \<beta> \<or> prop_cond \<alpha> \<gamma>
       then Or (rewrite (And \<alpha> \<beta>) Same) (rewrite (And \<alpha> \<gamma>) Same)
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in And \<alpha>' (Or \<beta>' \<gamma>')) 
      | (Release \<beta> I \<gamma>) \<Rightarrow>
      (if prop_cond \<alpha> \<beta>
       then And (rewrite \<alpha> Same) (Release (rewrite (And \<beta> (Once (init_ivl I) \<alpha>)) Same) I (rewrite (And \<gamma> (Once I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (And \<alpha>' (Release \<beta>' I \<gamma>')))
      | (Trigger \<beta> I \<gamma>) \<Rightarrow>
      (if prop_cond \<alpha> \<beta>
       then And (rewrite \<alpha> Same) (Trigger (rewrite (And \<beta> (Eventually (init_ivl I) \<alpha>)) Same) I (rewrite (And \<gamma> (Eventually I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (And \<alpha>' (Trigger \<beta>' I \<gamma>')))
      | (Exists k \<beta>) \<Rightarrow>
       (if prop_cond \<alpha> \<beta>
        then Exists k (rewrite (And (shiftI_r 0 \<alpha>) \<beta>) Same)
        else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Exists k \<beta>'))
      | (Neg \<beta>) \<Rightarrow>
      (if prop_cond \<alpha> \<beta>
       then And (rewrite \<alpha> Same) ((Neg (rewrite (And \<alpha> \<beta>) Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Neg \<beta>'))
      | (Since \<beta> I \<gamma>) \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Since (rewrite (And (Eventually (init_ivl I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Since (rewrite \<beta> Same) I (rewrite (And (Eventually I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in And \<alpha>' (Since \<beta>' I \<gamma>'))
      | Until \<beta> I \<gamma> \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Until (rewrite (And (Once (init_ivl I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (bounded I) then And (rewrite \<alpha> Same) (Until (rewrite \<beta> Same) I (rewrite (And (Once I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in And \<alpha>' (Until \<beta>' I \<gamma>'))
      | Once I \<beta> \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I)
       then And (rewrite \<alpha> Same) (Once I (And (Eventually I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Once I \<beta>'))
      | Eventually I \<beta> \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Eventually I (And (Once I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Eventually I \<beta>'))
      | Historically I \<beta> \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>) \<and> (bounded I)
       then And (rewrite \<alpha> Same) (Historically I (And (Eventually I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Historically I \<beta>')) 
      | Always I \<beta> \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Always I (And (Once I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Always I \<beta>'))
      | Prev I \<beta> \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Prev I (And (Next I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in And \<alpha>' (Prev I \<beta>'))
      | Next I \<beta> \<Rightarrow>
      (if (prop_cond \<alpha> \<beta>)
       then And (rewrite \<alpha> Same) (Next I (And (Prev I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in (And \<alpha>' (Next I \<beta>')))
      | _ => if t = Swapped then And (rewrite \<zeta> Same) (rewrite \<alpha> Same) else rewrite (And \<zeta> \<alpha>) Swapped)"
  | "rewrite (Since \<zeta> I \<beta>) t = (case \<zeta> of
    (And \<alpha> \<gamma>) \<Rightarrow> (let l = rewrite (And \<alpha> \<gamma>) Same;
                  r =      if t=Same \<and> \<not> (mem I 0) \<and> prop_cond \<alpha> \<beta> then rewrite (And (Eventually I \<alpha>) \<beta>) Same
                      else if t=Same \<and> \<not> (mem I 0) \<and> prop_cond \<gamma> \<beta> then rewrite (And (Eventually I \<gamma>) \<beta>) Same
                      else if t=Swapped \<and> bounded I \<and> prop_cond \<alpha> \<beta> then rewrite (And (Once (init_ivl I) \<alpha>) \<beta>) Same
                      else if t=Swapped \<and> bounded I \<and> prop_cond \<gamma> \<beta> then rewrite (And (Once (init_ivl I) \<gamma>) \<beta>) Same
                      else rewrite \<beta> Same
              in fix_r (Since l I r) t)
    | _ \<Rightarrow> (if t = Same then rewrite (Since \<beta> I \<zeta>) Swapped else Since (rewrite \<beta> Same) I (rewrite \<zeta> Same)))"
  | "rewrite (Until \<zeta> I \<beta>) t = (case \<zeta> of
    (And \<alpha> \<gamma>) \<Rightarrow> (let l = rewrite (And \<alpha> \<gamma>) Same;
                  r =      if t=Same \<and> \<not> (mem I 0) \<and> prop_cond \<alpha> \<beta> then rewrite (And (Once I \<alpha>) \<beta>) Same
                      else if t=Same \<and> \<not> (mem I 0) \<and> prop_cond \<gamma> \<beta> then rewrite (And (Once I \<gamma>) \<beta>) Same
                      else if t=Swapped \<and> prop_cond \<alpha> \<beta> then rewrite (And (Eventually (init_ivl I) \<alpha>) \<beta>) Same
                      else if t=Swapped \<and> prop_cond \<gamma> \<beta> then rewrite (And (Eventually (init_ivl I) \<gamma>) \<beta>) Same
                      else rewrite \<beta> Same
              in fix_r (Until l I r) t)
    | _ \<Rightarrow> if t = Same then rewrite (Until \<beta> I \<zeta>) Swapped else Until (rewrite \<beta> Same) I (rewrite \<zeta> Same))"
| "rewrite (Or \<phi> \<psi>) t =  Or (rewrite \<phi> Same) (rewrite \<psi> Same)"

| "rewrite (Exists k \<phi>) t = Exists k (rewrite \<phi> Same)"
| "rewrite (Agg y \<omega> b' f \<phi>) t = Agg y \<omega> b' f (rewrite \<phi> Same)"
| "rewrite (Prev I \<phi>) t = Prev I (rewrite \<phi> Same)"
| "rewrite (Next I \<phi>) t = Next I (rewrite \<phi> Same)"

| "rewrite (Release \<phi> I \<psi>) t = Release (rewrite \<phi> Same) I (rewrite \<psi> Same)"
| "rewrite (Trigger \<phi> I \<psi>) t =  Trigger (rewrite \<phi> Same) I (rewrite \<psi> Same)"

| "rewrite (Neg \<alpha>) t = Neg (rewrite \<alpha> Same)"
| "rewrite (Eventually I \<alpha>) t = Eventually I (rewrite \<alpha> Same)"
| "rewrite (Once I \<alpha>) t = Once I (rewrite \<alpha> Same)"
| "rewrite (Always I \<alpha>) t = Always I (rewrite \<alpha> Same)"
| "rewrite (Historically I \<alpha>) t = Historically I (rewrite \<alpha> Same)"

| "rewrite (MatchF I r) t = MatchF I (regex.map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (MatchP I r) t = MatchP I (regex.map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (Ands \<phi>s) t = Ands (map (\<lambda>r. rewrite r Same) \<phi>s)"

| "rewrite f t =  f"

  by pat_completeness auto 

termination
 apply(relation "measures [(\<lambda>(f,t). my_size f),(\<lambda>(f,t). size_argpos t)]")
                      apply (auto simp add:  shift_size not_zero ands_size map_cong termination_simp
      elim!: not_swapped) (*not_zero important because size of constructor then depends on its' number of arguments*)
              apply (frule not_swapped, simp)+
 done
*)


termination
  by (relation "measures [(\<lambda>(f,t). my_size f),(\<lambda>(f,t). size_argpos t)]")
    (auto simp add:  shift_size not_zero ands_size map_cong termination_simp
      elim!: not_swapped) (*not_zero important because size of constructor then depends on its' number of arguments*)


subsubsection \<open> Proof of correct rewriting \<close>

(* TODO: Unused definition, move to formula or delete? *)
definition trigger :: "'a Formula.formula \<Rightarrow> \<I> \<Rightarrow> 'a Formula.formula \<Rightarrow> 'a Formula.formula"
  where "trigger \<phi> I \<psi> = \<not>\<^sub>F (\<not>\<^sub>F \<phi> \<^bold>S I \<not>\<^sub>F \<psi>)"

lemma sat_trigger[simp]: "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> trigger \<phi> I \<psi> 
  \<longleftrightarrow> (\<forall>j\<le>i. mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<longrightarrow> \<langle>\<sigma>, V, v, j\<rangle> \<Turnstile> \<psi> \<or> (\<exists>k\<in>{j<..i}. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile> \<phi>))"
  unfolding release_def
  by (auto simp: trigger_def)

lemma sat_trigger_eq: "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> trigger \<phi> I \<psi> 
  \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi> \<^bold>T I \<psi>"
  by auto

lemma rewrite_fv: "Formula.fvi b (project \<alpha>) = Formula.fvi b (project (rewrite \<alpha> t))"
proof(induction \<alpha> t arbitrary:b rule:rewrite.induct)
  case (1 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta> ")
    case True
    then show ?thesis using 1 by fastforce
  next
    case False
    then show ?thesis using 1 by auto
  qed
next
  case (2 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta> ")
    case True
    then show ?thesis using 2 by fastforce
  next
    case False
    then show ?thesis using 2 by auto
  qed
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta>")
    case T1:True
    then show ?thesis
    proof(cases "prop_cond \<beta> \<alpha>")
      case T2:True
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        thm 3(1)
        case True
        then show ?thesis using 3[where ?b=b] T1 T2 by auto
      next
        case False
        then show ?thesis using 3[where ?b=b] T1 T2 by auto
      qed
    next
      case F1:False
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        case True
        then show ?thesis using 3[where ?b=b] T1 F1 by auto
      next
        case False
        then show ?thesis using 3[where ?b=b] T1 F1 by auto
      qed
    qed
  next
    case F1:False
    then show ?thesis
      proof(cases "prop_cond \<beta> \<alpha>")
      case T2:True
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        case True
        then show ?thesis using 3 F1 T2 by auto
      next
        case False
        then show ?thesis using 3 F1 T2 by auto
      qed
    next
      case F1:False
      then show ?thesis
      proof(cases "prop_cond \<gamma> \<alpha>")
        case True
        then show ?thesis using 3[where ?b=b] F1 F1 by auto
      next
        case False
        then show ?thesis using 3[where ?b=b] F1 F1 by auto
      qed
    qed
  qed
next
  case (4 \<alpha> t \<beta>)
  then show ?case
    proof(cases "prop_cond \<alpha> \<beta>")
      case True
      have helper:"fvi_r b \<alpha>  = Formula.fvi (Suc b) (Rewriting.shift (project \<alpha>))" 
        using fvi_shift by auto
      from True show ?thesis using 4 helper
        apply(simp only:rewrite.simps if_True)
        apply(simp only:project.simps)
        apply(simp only:Formula.fvi.simps)
        apply(simp only: 4(1)[OF True,of "Suc b",symmetric])
        apply(simp only:project.simps)
        apply(simp only: project_shift)
        apply(simp only:Formula.fvi.simps)
        done
    next
      case False
      then show ?thesis using 4 by auto
    qed
next
  case (5 \<alpha> \<beta> I t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta> ")
    case True
    then show ?thesis using 5 by fastforce
  next
    case False
    then show ?thesis using 5 by auto
  qed
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  then show ?case
      apply(simp add: 6(1)[symmetric])
    by fastforce
next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case
      apply(simp add: 7(1)[symmetric])
      by fastforce
next
  case (10 \<alpha> I \<beta> b t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta> ")
    case True
    then show ?thesis 
      using 10
      by (clarsimp simp: historically_def)
  next
    case False
    then show ?thesis
      using 10
      by (clarsimp simp: historically_def)
  qed
next
  case (11 \<alpha> I \<beta> b t)
  then show ?case
  proof(cases "prop_cond \<alpha> \<beta> ")
    case True
    then show ?thesis 
      using 11
      by (clarsimp simp: once_def always_def)
  next
    case False
    then show ?thesis
      using 11
      by (clarsimp simp: once_def always_def)
  qed
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> bounded I \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> bounded I \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a(*TODO use simplifier for these proofs, also prove shift_fv2*)
    then show ?thesis using 14
      apply(simp add: 14(1)[symmetric])
      by auto
  next
    case b
    then show ?thesis
    proof(cases "prop_cond \<alpha> \<beta>")
      case True
      then show ?thesis using b 14 by blast
    next
      case False
      then show ?thesis using b 14 by fastforce
    qed
  next
    case c
    then show ?thesis using 14
      apply(simp add: 14(1)[symmetric])
      by blast
  next
    case d
    then show ?thesis using 14
      apply(simp add: 14(1)[symmetric])
      by blast
  next
    case e
    then show ?thesis
      proof(cases "t=Swapped")
        case True
        then show ?thesis using e 14
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project.simps)
          by auto
      next
        case False
        then show ?thesis using e 14 not_swapped[OF False]
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project.simps)
          by auto
      qed
  qed
next
  case (15 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a(*TODO use simplifier for these proofs, also prove shift_fv2*)
    then show ?thesis using 15
      apply(simp add: 15(1)[symmetric])
      by auto
  next
    case b
    then show ?thesis
    proof(cases "prop_cond \<alpha> \<beta>")
      case True
      then show ?thesis using b 15 by blast
    next
      case False
      then show ?thesis using b 15 by fastforce
    qed
  next
    case c
    then show ?thesis using 15
      apply(simp add: 15(1)[symmetric])
      by blast
  next
    case d
    then show ?thesis using 15
      apply(simp add: 15(1)[symmetric])
      by blast
  next
    case e
    then show ?thesis
      proof(cases "t=Swapped")
        case True
        then show ?thesis using e 15
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project.simps)
          by auto
      next
        case False
        then show ?thesis using e 15 not_swapped[OF False]
          apply(simp only:rewrite.simps if_False Let_def fix_r.simps)
          apply(simp only:project.simps)
          by auto
      qed
    qed
next
  case ("16_11" v va vb vc vd I r)
  then show ?case by fastforce
next
  case ("17_11" v va vb vc vd I r)
  then show ?case by fastforce
next
  case ("18_9" l v va vb vc vd)
  then show ?case by fastforce
next
  case (23 \<phi> t)
  then show ?case by simp
next
  case (24 y \<omega> b' f \<phi> t)
  then show ?case by simp
next
case (34 I r t)
  then show ?case by (induction r;auto)
next
  case (35 I r t)
  then show ?case by (induction r;auto)
qed (auto simp: always_def historically_def)

lemma equiv_2: "sat \<sigma> V v i (Until \<alpha> I \<beta>) = sat \<sigma> V v i (Until (And \<alpha> (Eventually (init_ivl I) \<beta>) ) I \<beta>)"
(is "?L = ?R")
proof(rule iffI)
  assume ass:?L
  then obtain j where j: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" 
    "sat \<sigma> V v j \<beta>" "(\<forall>k\<in>{i..<j}. sat \<sigma> V v k \<alpha>)" by auto
  then have "\<forall>k\<in>{i..<j}.j\<ge>k " by auto
  moreover have "\<forall>k\<in>{i..<j}. mem (init_ivl I) (\<tau> \<sigma> j - \<tau> \<sigma> k)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{i..<j}. sat \<sigma> V v j \<beta>" using j(3) by auto
  ultimately have "\<forall>k\<in>{i..<j}. (\<exists>j\<ge>k. mem (init_ivl I) (\<tau> \<sigma> j - \<tau> \<sigma> k) \<and> sat \<sigma> V v j \<beta>)" by fast
  then show ?R using j by auto
qed auto

lemma equiv_4: " sat \<sigma> V v i (Since \<alpha> I \<beta>)  = sat \<sigma> V v i (Since (And \<alpha> (Once (init_ivl I) \<beta>) ) I \<beta>)"
(is "?L = ?R")
proof(rule iffI)
  assume ass:?L
  then obtain j where j: "j\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" 
    "sat \<sigma> V v j \<beta>" "(\<forall>k\<in>{j<..i}. sat \<sigma> V v k \<alpha>)" 
    by auto
  then have "\<forall>k\<in>{j<..i}.j\<le>k " by auto
  moreover have "\<forall>k\<in>{j<..i}. mem (init_ivl I) (\<tau> \<sigma> k - \<tau> \<sigma> j)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{j<..i}. sat \<sigma> V v j \<beta>" using j(3) by auto
  ultimately have "\<forall>k\<in>{j<..i}. (\<exists>j\<le>k. mem (init_ivl I) (\<tau> \<sigma> k - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<beta>)" by fast
  then show ?R using j by auto
qed auto

lemma sat_main_1:
  "sat \<sigma> V v i (And \<alpha> (Or \<beta> \<gamma>)) =
   sat \<sigma> V v i (Or (And \<alpha> \<beta>) (And \<alpha> \<gamma>))"
  by auto

lemma sat_main_2: "sat \<sigma> V v i (And \<alpha> (Release \<beta> I \<gamma>)) 
  \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Release (And \<beta> (Once (init_ivl I) \<alpha>)) I (And \<gamma> (Once I \<alpha>))))"
(is "?L = ?R" )
proof(rule iffI)
  assume ass: "?L"
  then have split_A: "sat \<sigma> V v i \<alpha>"
                   "(\<And>j. j\<ge>i \<Longrightarrow> \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or> sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. sat \<sigma> V v k \<beta>))"
    by auto

  then have "(\<And>j. j\<ge>i \<Longrightarrow> \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or>
               (sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<le>j. mem I (\<tau> \<sigma> j - \<tau> \<sigma> ja))) \<or>
              (\<exists>k\<in>{i..<j}.
                  (sat \<sigma> V v k \<beta> \<and> (\<exists>j\<le>k. mem (init_ivl I) (\<tau> \<sigma> k - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<alpha> ))))"
  proof -
  fix j assume le:"j\<ge>i"
  then have " \<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or> sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. sat \<sigma> V v k \<beta>)" using ass by auto
  then consider (a) "\<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" |
                (b) "(sat \<sigma> V v j \<gamma>) \<and>  mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" |
                (c) "(\<exists>k\<in>{i..<j}. sat \<sigma> V v k \<beta>)"  "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" by auto
  then show "(\<not> mem I (\<tau> \<sigma> j - \<tau> \<sigma> i) \<or>
               (sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<le>j. mem I (\<tau> \<sigma> j - \<tau> \<sigma> ja))) \<or>
              (\<exists>k\<in>{i..<j}.
                  (sat \<sigma> V v k \<beta> \<and> (\<exists>j\<le>k. mem (init_ivl I) (\<tau> \<sigma> k - \<tau> \<sigma> j) \<and> sat \<sigma> V v j \<alpha> ))))"
  proof(cases)
    case a
    then show ?thesis by auto
  next
    case b
    then show ?thesis using le by auto
  next
    case c
    then show ?thesis using split_A(1) nat_less_mem_of_init[OF _ c(2)] by auto
  qed
qed
  then show ?R using split_A(1)  by auto
qed auto

lemma sat_main_3: "sat \<sigma> V v i (And \<alpha> (Trigger \<beta> I \<gamma>)) 
  \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Trigger (And \<beta> (Eventually (init_ivl I) \<alpha>)) I (And \<gamma> (Eventually I \<alpha>))))"
(is "?L = ?R" )
proof(rule iffI)
  assume ass: "?L"
  then have split_A: "sat \<sigma> V v i \<alpha>"
                     "(\<And>j. i\<ge>j \<Longrightarrow> \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or> sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{j<..i}. sat \<sigma> V v k \<beta>))" by auto
  then have "(\<And>j. i\<ge>j \<Longrightarrow> \<not>mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or>
              (sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<ge>j. mem I (\<tau> \<sigma> ja - \<tau> \<sigma> j))) \<or>
              (\<exists>k\<in>{j<..i}. (sat \<sigma> V v k \<beta> \<and> (\<exists>j\<ge>k. mem (init_ivl I) (\<tau> \<sigma> j - \<tau> \<sigma> k) \<and> sat \<sigma> V v j \<alpha>))))"
  proof -
    fix j assume le:"i\<ge>j"
    then have " \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or> sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{j<..i}. sat \<sigma> V v k \<beta>)" using ass by auto
    then consider (a) "\<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" |
                  (b) "sat \<sigma> V v j \<gamma> \<and> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" |
                  (c) "(\<exists>k\<in>{j<..i}. sat \<sigma> V v k \<beta>)" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" by auto
    then show "\<not>mem I (\<tau> \<sigma> i - \<tau> \<sigma> j) \<or>
              (sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<ge>j. mem I (\<tau> \<sigma> ja - \<tau> \<sigma> j))) \<or>
              (\<exists>k\<in>{j<..i}. (sat \<sigma> V v k \<beta> \<and> (\<exists>j\<ge>k. mem (init_ivl I) (\<tau> \<sigma> j - \<tau> \<sigma> k) \<and> sat \<sigma> V v j \<alpha>)))"
  proof(cases)
    case a
    then show ?thesis by blast
  next
    case b
    then show ?thesis using le by auto
  next
    case c
    then show ?thesis using split_A(1) nat_less_mem_of_init[OF _ c(2)] by auto
  qed
qed
then show ?R using split_A(1) by auto
qed auto

lemma sat_main_4: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists t \<beta>)) =
                    Formula.sat \<sigma> V v i (Formula.Exists t (Formula.And (shift \<alpha>) \<beta> ))"
  using sat_shift[of "[]"] by auto

lemma sat_main_5: "sat \<sigma> V v i (And \<alpha> (Neg \<beta>))
  \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Neg (And \<alpha> \<beta>)))"
  by auto

lemma sat_main_6: "\<not> mem I 0 
  \<Longrightarrow> sat \<sigma> V v i (Since (And \<alpha> \<gamma>) I \<beta> )
  \<longleftrightarrow> sat \<sigma> V v i (Since (And \<alpha> \<gamma>) I (And (Eventually I \<alpha>) \<beta>))" 
  by fastforce

lemma sat_main_7: "\<not> mem I 0 
  \<Longrightarrow> sat \<sigma> V v i (Until (And \<alpha> \<gamma>) I \<beta> ) 
  \<longleftrightarrow> sat \<sigma> V v i (Until (And \<alpha> \<gamma>) I (And (Once I \<alpha>) \<beta>))" 
  by fastforce

lemma sat_main_8: "sat \<sigma> V v i (Since \<beta> I (And \<alpha> \<gamma>) ) 
  \<longleftrightarrow> sat \<sigma> V v i (Since (And (Once (init_ivl I) \<alpha>) \<beta>) I (And \<alpha> \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_4 L] by fastforce
qed auto

lemma sat_main_9: "sat \<sigma> V v i (Until \<beta> I (And \<alpha> \<gamma>)) 
  \<longleftrightarrow> sat \<sigma> V v i (Until (And (Eventually (init_ivl I) \<alpha>) \<beta>) I (And \<alpha> \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_2 L] by fastforce
qed auto

lemma sat_main_10: "sat \<sigma> V v i (And \<alpha> (Since \<beta> I \<gamma>))
  \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Since (And (Eventually (init_ivl I) \<alpha>) \<beta>) I \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<le>i" "mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)" 
    "sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{j<..i}. sat \<sigma> V v i \<alpha> \<and> sat \<sigma> V v k \<beta>)" by auto
  then have "\<forall>k\<in>{j<..i}. mem (init_ivl I) (\<tau> \<sigma> i - \<tau> \<sigma> k)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto

lemma sat_main_11: "sat \<sigma> V v i (And \<alpha> (Until \<beta> I \<gamma>)) 
  \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Until (And (Once (init_ivl I) \<alpha>) \<beta>) I \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<ge>i" "mem I (\<tau> \<sigma> j - \<tau> \<sigma> i)" 
    "sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{i..<j}.  sat \<sigma> V v i \<alpha> \<and> sat \<sigma> V v k \<beta>)" 
    by auto
  then have "\<forall>k\<in>{i..<j}. mem (init_ivl I) (\<tau> \<sigma> k - \<tau> \<sigma> i)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto

lemma sat_main_12: "sat \<sigma> V v i (And \<alpha> (Since \<gamma> I \<beta>)) 
 \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Since \<gamma> I (And (Eventually I \<alpha>)\<beta>)))"
  by auto

lemma sat_main_13: "sat \<sigma> V v i (And \<alpha> (Until \<gamma> I \<beta>))
  \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Until \<gamma> I (And (Once I \<alpha>)\<beta>)))" 
  by auto

lemma sat_main_22: "sat \<sigma> V v i (And \<alpha> (Prev I \<beta>))
  \<longleftrightarrow> sat \<sigma> V v i (And \<alpha> (Prev I (And (Next I \<alpha>) \<beta>)))" 
  by (auto split: nat.splits)

inductive f_con where
f_con_1_t: "f_con (\<lambda>f1. Formula.Exists t f1)"|
f_con_2_t: "f_con (\<lambda>f1. Formula.Neg f1)" |
f_con_3_t: "f_con (\<lambda>f1. Formula.Since Formula.TT I f1)" |
f_con_4_t: "f_con (\<lambda>f1. Formula.Until Formula.TT I f1)"|
f_con_5_t: "f_con (\<lambda>f1. Formula.Next I f1)"|
f_con_6_t: "f_con (\<lambda>f1. Formula.Prev I f1)"

lemma sub_1: "f_con P \<Longrightarrow> (\<And>v i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>)) 
  \<Longrightarrow> Formula.sat \<sigma> V v i (P (project \<alpha>)) = Formula.sat \<sigma> V v i (P (project \<beta>))"
proof(induction P arbitrary: v rule:f_con.induct)
case f_con_1_t
  then show ?case by simp
next
  case (f_con_6_t I)
  then show ?case by (simp split:nat.splits)
qed simp_all

inductive f_conr where
f_conr_1_t: "f_conr (\<lambda>f1. Exists t f1)"|
f_conr_2_t: "f_conr (\<lambda>f1. Neg f1)" |
f_conr_3_t: "f_conr (\<lambda>f1. Once I f1)"|
f_conr_4_t: "f_conr (\<lambda>f1. Eventually I f1)" |
f_conr_5_t: "f_conr (\<lambda>f1. Next I f1)"|
f_conr_6_t: "f_conr (\<lambda>f1. Prev I f1)"

inductive trans where
trans1: "trans (\<lambda>f1. Exists t f1) (\<lambda>f1. Formula.Exists t f1)" |
trans2: "trans (\<lambda>f1. Neg f1) (\<lambda>f1. Formula.Neg f1)" |
trans3: "trans (\<lambda>f1. Once I f1) (\<lambda>f1. Formula.Since Formula.TT I f1)"|
trans4: "trans (\<lambda>f1. Eventually I f1)  (\<lambda>f1. Formula.Until Formula.TT I f1)" |
trans5: "trans (\<lambda>f1. Next I f1) (\<lambda>f1. Formula.Next I f1)"|
trans6: "trans (\<lambda>f1. Prev I f1) (\<lambda>f1. Formula.Prev I f1)"

lemma trans1: "trans P P' \<Longrightarrow> f_conr P \<and> f_con P' "
proof(induction P P' rule: trans.induct)
  case trans1
  then show ?case using f_conr_1_t f_con_1_t by auto
next
  case trans2
  then show ?case using f_conr_2_t f_con_2_t by auto
next
  case (trans3 I)
  then show ?case using f_conr_3_t f_con_3_t by auto
next
case (trans4 I)
  then show ?case using f_conr_4_t f_con_4_t by auto
next
  case (trans5 I)
  then show ?case using f_conr_5_t f_con_5_t by auto
next
  case (trans6 I)
  then show ?case using f_conr_6_t f_con_6_t by auto
qed

lemma trans2: "trans P P' \<Longrightarrow> project (P r) = P' (project r)"
  by(induction P P' rule:trans.induct; simp add: once_def eventually_def)

lemma trans3: "f_conr P \<Longrightarrow> \<exists>P'. trans P P'"
  using f_conr.simps trans.trans1 trans.trans2 trans3 trans4 trans5 trans6  by metis

lemma rsub_1: "f_conr P \<Longrightarrow> (\<And>v i. sat \<sigma> V v i \<alpha> = sat \<sigma> V v i \<beta>) \<Longrightarrow> sat \<sigma> V v i (P \<alpha>) = sat \<sigma> V v i (P \<beta>)"
proof -
  assume A: "f_conr P" "(\<And>v i. sat \<sigma> V v i \<alpha> = sat \<sigma> V v i \<beta>)"
  then obtain P2 where P2: "trans P P2" using trans3[OF A(1)] by auto
  moreover have L1: "f_con P2" using trans1[OF P2] by auto
  moreover have L2:"(\<And>v i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>))" 
    using A(2) sat_project by simp
  ultimately show ?thesis
    using Rewriting.trans2 sub_1
    by (smt (verit, ccfv_SIG) sat_project)
qed


inductive f_con2 where
f_con2_1_t: "f_con2 (\<lambda>f1 f2. Formula.Or f1 f2)" |
f_con2_2_t: "f_con2 (\<lambda>f1 f2. Formula.And f1 f2)" |
f_con2_3_t: "f_con2 (\<lambda>f1 f2. Formula.Release f1 I f2)"|
f_con2_4_t: "f_con2 (\<lambda>f1 f2. Formula.Trigger f1 I f2)" |
f_con2_5_t: "f_con2 (\<lambda>f1 f2. Formula.Since f1 I f2)"|
f_con2_6_t: "f_con2 (\<lambda>f1 f2. Formula.Until f1 I f2)"

lemma sub_2: "f_con2 P 
  \<Longrightarrow> (\<And>v i. Formula.sat \<sigma> V v i (project a1) = Formula.sat \<sigma> V v i (project b1)) 
  \<Longrightarrow> (\<And>v i. Formula.sat \<sigma> V v i (project a2) = Formula.sat \<sigma> V v i (project b2)) 
  \<Longrightarrow> Formula.sat \<sigma> V v i (P (project a1) (project a2)) = Formula.sat \<sigma> V v i (P (project b1) (project b2))"
  by(induction P rule:f_con2.induct;auto)

inductive f_conr2 where
f_conr2_1_t: "f_conr2 (\<lambda>f1 f2. Or f1 f2)" |
f_conr2_2_t: "f_conr2 (\<lambda>f1 f2. And f1 f2)" |
f_conr2_3_t: "f_conr2 (\<lambda>f1 f2. Release f1 I f2)"|
f_conr2_4_t: "f_conr2 (\<lambda>f1 f2. Trigger f1 I f2)" |
f_conr2_5_t: "f_conr2 (\<lambda>f1 f2. Since f1 I f2)"|
f_conr2_6_t: "f_conr2 (\<lambda>f1 f2. Until f1 I f2)"

inductive trans2 where
trans2_1: "trans2 (\<lambda>f1 f2. Or f1 f2)  (\<lambda>f1 f2. Formula.Or f1 f2)" |
trans2_2: "trans2 (\<lambda>f1 f2. And f1 f2) (\<lambda>f1 f2. Formula.And f1 f2)" |
trans2_3: "trans2 (\<lambda>f1 f2. Release f1 I f2) (\<lambda>f1 f2. Formula.Release f1 I f2)"|
trans2_4: "trans2 (\<lambda>f1 f2. Trigger f1 I f2) (\<lambda>f1 f2. Formula.Trigger f1 I f2)" |
trans2_5: "trans2 (\<lambda>f1 f2. Since f1 I f2) (\<lambda>f1 f2. Formula.Since f1 I f2)"|
trans2_6: "trans2 (\<lambda>f1 f2. Until f1 I f2) (\<lambda>f1 f2. Formula.Until f1 I f2)"

lemma trans2_1: "trans2 P P' \<Longrightarrow> f_conr2 P \<and> f_con2 P' "
  unfolding f_con2.simps f_conr2.simps trans2.simps by auto

lemma trans2_2: "trans2 P P' \<Longrightarrow> project (P r r2) = P' (project r) (project r2)"
  by (induction P P' rule:trans2.induct;simp)

lemma trans2_3: "f_conr2 P \<Longrightarrow> \<exists>P'. trans2 P P'"
  apply(induction P rule:f_conr2.induct)
  using trans2.trans2_1 trans2.trans2_2 trans2.trans2_3 trans2.trans2_4 trans2.trans2_5 trans2.trans2_6 apply blast+
  done

lemma rsub_2: "f_conr2 P \<Longrightarrow> (\<And>v i. sat \<sigma> V v i a1 = sat \<sigma> V v i b1) \<Longrightarrow> (\<And>v i. sat \<sigma> V v i a2 = sat \<sigma> V v i b2) \<Longrightarrow> sat \<sigma> V v i (P a1 a2) = sat \<sigma> V v i (P b1 b2)"
proof -
  assume A: "f_conr2 P" "(\<And>v i. sat \<sigma> V v i a1 = sat \<sigma> V v i b1)" "(\<And>v i. sat \<sigma> V v i a2 = sat \<sigma> V v i b2)"
  then obtain P2 where P2: "trans2 P P2" using trans2_3[OF A(1)] by auto
  moreover have L1: "f_con2 P2" using trans2_1[OF P2] by auto
  moreover have L2:"(\<And>v i. Formula.sat \<sigma> V v i (project a1) = Formula.sat \<sigma> V v i (project b1))"
    using A(2) by (simp add: sat_project)
  moreover have L3:"(\<And>v i. Formula.sat \<sigma> V v i (project a2) = Formula.sat \<sigma> V v i (project b2))" 
    using A(3) by (simp add: sat_project)
  ultimately show ?thesis
    using Rewriting.trans2_2 sub_2
    by (smt (verit, ccfv_SIG) Rewriting.trans2_1 sat_project
        \<open>\<And>thesis. (\<And>P2. trans2 P P2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>) 
qed


inductive f_con_agg where
f_con_agg_1_t: "f_con_agg (\<lambda>f1. Formula.Agg n1 op n2 t f1)"

lemma sub_agg: "f_con_agg P \<Longrightarrow> (\<And>v i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>)) \<Longrightarrow> fv (project \<alpha>) = fv (project \<beta>)
                          \<Longrightarrow> Formula.sat \<sigma> V v i (P (project \<alpha>)) = Formula.sat \<sigma> V v i (P (project \<beta>))"
proof(induction P rule: f_con_agg.induct)
  case (f_con_agg_1_t n1 op n2 t)
  then show ?case by simp
qed

inductive f_conr_agg where
f_conr_agg_t: "f_conr_agg (\<lambda>f1. Agg n1 op n2 t f1)"

inductive trans_agg where
trans_agg_1: "trans_agg (\<lambda>f1. Agg n1 op n2 t f1) (\<lambda>f1. Formula.Agg n1 op n2 t f1)"

lemma trans_agg_1: "trans_agg P P' \<Longrightarrow> f_conr_agg P \<and> f_con_agg P' "
  using f_con_agg.simps f_conr_agg.simps trans_agg.simps by blast

lemma trans_agg_2: "trans_agg P P' \<Longrightarrow> project (P r) = P' (project r)"
  by (induction P P' rule:trans_agg.induct;simp)

lemma trans_agg_3: "f_conr_agg P \<Longrightarrow> \<exists>P'. trans_agg P P'"
  apply(induction P rule:f_conr_agg.induct)
  using trans_agg.trans_agg_1 apply blast
  done

lemma rsub_agg: "f_conr_agg P \<Longrightarrow> (\<And>v i. sat \<sigma> V v i a = sat \<sigma> V v i b) 
  \<Longrightarrow> fv (project a) = fv (project b)
  \<Longrightarrow> sat \<sigma> V v i (P a) = sat \<sigma> V v i (P b)"
proof -
  assume A: "f_conr_agg P" "(\<And>v i. sat \<sigma> V v i a = sat \<sigma> V v i b)" 
    "fv (project a) = fv (project b) "
  then obtain P2 where P2: "trans_agg P P2" using trans_agg_3[OF A(1)] by auto
  moreover have L1: "f_con_agg P2" using trans_agg_1[OF P2] by auto
  moreover have L2:"(\<And>v i. Formula.sat \<sigma> V v i (project a) = Formula.sat \<sigma> V v i (project b))" 
    using A(2) by (simp add: sat_project)
  ultimately show ?thesis
    using Rewriting.trans_agg_2 sub_agg[OF L1 L2 A(3)]
    by (metis (mono_tags, lifting) sat_project)
qed

lemma sat_rewrite: "sat \<sigma> V v i (rewrite r t) = sat \<sigma> V v i (fix_r r t)"
proof(induction r t arbitrary: v i rule: rewrite.induct)
  case (1 \<alpha> \<beta> \<gamma> t)
  thm rsub_2[OF f_conr2_1_t 1(1-2)]
  then show ?case 
    using sat_main_1 by simp
next
  case (2 \<alpha> \<beta> I \<gamma> t)
  then show ?case 
    using sat_main_2 by simp
next
  case (3 \<alpha> \<beta> I \<gamma> t)
  then show ?case 
    using sat_main_3 by simp
next
  case (4 \<alpha> t \<beta>)

  then show ?case
  proof(cases "prop_cond \<alpha> \<beta>")
    case True
    moreover have obs: "project (shiftI_r 0 \<alpha>) = shiftI 0 (project \<alpha>)" 
      by (rule project_shift[of 0])
    ultimately show ?thesis using
       sat_main_4
      apply (simp only: fix_r.simps rewrite.simps if_True)
      apply(simp only: rsub_1[OF f_conr_1_t 4(1)[OF True] ] fix_r.simps)
      apply(simp only:  project.simps  fix_r.simps project_shift)
      by (metis obs project.simps(11) project.simps(9) sat_project)(*remove embedding*)
  next
    case False
    then show ?thesis
      apply(simp only: fix_r.simps rewrite.simps if_False Let_def)
      apply(simp only: rsub_2[OF f_conr2_2_t 4(2)[OF False] rsub_1[OF f_conr_1_t 4(3)[OF False refl]]] fix_r.simps)
      done
  qed
next
  case (5 \<alpha> \<beta> t)
  then show ?case
    using sat_main_5
    by simp
next
  case (6 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases"(prop_cond \<alpha> \<beta>) \<and> (bounded I)")
    case True
  then show ?thesis
    apply(simp only:rewrite.simps rsub_2[OF f_conr2_2_t 6(1)[OF True] rsub_2[OF f_conr2_5_t 6(2,3)[OF True]]] split:if_splits)
    apply(simp only: project.simps  fix_r.simps)(*remove embedding*)
    apply(simp only: sat_main_10[symmetric]) (*rewrite lemma*)
    apply(simp)
    done
next
  case F1:False
  then show ?thesis
  proof(cases "(prop_cond \<alpha> \<gamma>) \<and> (bounded I)")
    case True
    then show ?thesis using F1
      apply(simp only: rewrite.simps rsub_2[OF f_conr2_2_t 6(4)[OF F1 True] rsub_2[OF f_conr2_5_t 6(5,6)[OF F1 True]]] split:if_splits)
      apply(simp only: project.simps  fix_r.simps)(*remove embedding*)
    apply(simp only: sat_main_12[symmetric]) (*rewrite lemma*)
    apply(simp)
      done
next
  case False
  then show ?thesis using F1 6
    apply(simp only:rewrite.simps Let_def  split:if_splits)
    apply(simp only: rsub_2[OF f_conr2_2_t 6(7)[OF F1 False] rsub_2[OF f_conr2_5_t 6(8)[OF F1 False refl] 6(9)[OF F1 False refl refl]]])
    apply(simp)
      done
qed
qed

next
  case (7 \<alpha> \<beta> I \<gamma> t)
  then show ?case
  proof(cases"(prop_cond \<alpha> \<beta>) \<and> (bounded I)")
    case True
  then show ?thesis
    apply(simp only:rewrite.simps rsub_2[OF f_conr2_2_t 7(1)[OF True] rsub_2[OF f_conr2_6_t 7(2,3)[OF True]]] split:if_splits)
    apply(simp only: project.simps  fix_r.simps)(*remove embedding*)
    apply(simp only: sat_main_11[symmetric]) (*rewrite lemma*)
    apply(simp)
    done
next
  case F1:False
  then show ?thesis
  proof(cases "(prop_cond \<alpha> \<gamma>) \<and> (bounded I)")
    case True
    then show ?thesis using F1
      apply(simp only: rewrite.simps rsub_2[OF f_conr2_2_t 7(4)[OF F1 True] rsub_2[OF f_conr2_6_t 7(5,6)[OF F1 True]]] split:if_splits)
      apply(simp only: project.simps  fix_r.simps)(*remove embedding*)
    apply(simp only: sat_main_13[symmetric]) (*rewrite lemma*)
    apply(simp)
      done
next
  case False
  then show ?thesis using F1
    apply(simp only:rewrite.simps Let_def  split:if_splits)
    apply(simp only: rsub_2[OF f_conr2_2_t 7(7)[OF F1 False] rsub_2[OF f_conr2_6_t 7(8)[OF F1 False refl] 7(9)[OF F1 False refl refl]]])
    apply(simp)
      done
  qed
  qed
next
  case (8 \<alpha> I \<beta> t)
  then show ?case by (auto simp add:)
next
  case (9 \<alpha> I \<beta> t)
  then show ?case  by (auto simp add:)
next
case (10 \<alpha> I \<beta> t)
  then show ?case  by (auto simp add:)
next
  case (11 \<alpha> I \<beta> t)
  then show ?case by (auto simp add:)
next
  case (12 \<alpha> I \<beta> t)
  then show ?case
proof(cases "prop_cond \<alpha> \<beta> ")
  case True
  then show ?thesis using rsub_2[OF f_conr2_2_t 12(1)[OF True] rsub_1[OF f_conr_6_t rsub_2[OF f_conr2_2_t rsub_1[OF f_conr_5_t 12(1)[OF True]] 12(3)[OF True]]]] sat_main_22[symmetric]
    apply(simp only: rewrite.simps fix_r.simps  split:if_splits)
    apply(simp split: nat.splits)
    using "12.IH"(1) "12.IH"(3) by force
next
  case False
  then show ?thesis 
    using rsub_2[OF f_conr2_2_t 12(4)[OF False] rsub_1[OF f_conr_6_t 12(5)[OF False refl]]] by simp
qed
next
  case (13 \<alpha> I \<beta> t)
  then show ?case by (auto simp add: )
next
  case (14 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> bounded I \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> bounded I \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a
    then have ex:"\<not> mem I 0" by auto
    from a show ?thesis
          apply(simp del: sat.simps add: rsub_2[OF f_conr2_5_t 14(1) 14(2)[OF refl a ]]  split:if_splits )
          apply(simp only:sat_main_6[OF ex, symmetric])(*apply rewrite lemma*)
      done
  next
    case b
    then have ex:"\<not> mem I 0" by auto
    have swap: "sat \<sigma> V v i (Since (And \<alpha> \<gamma>) I (And (Eventually I \<gamma>) \<beta>)) = sat \<sigma> V v i (Since (And \<alpha> \<gamma>) I \<beta>) \<longleftrightarrow>
                sat \<sigma> V v i (Since (And \<gamma> \<alpha>) I (And (Eventually I \<gamma>) \<beta>)) = sat \<sigma> V v i (Since (And \<gamma> \<alpha>) I \<beta>)" 
      by (simp add: ;fast)
    from b show ?thesis using swap
      apply(simp only:rewrite.simps)
        apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(1) 14(3)[OF refl b]]  split:if_splits) (*remove recursion*)
        apply(rule sat_main_6[OF ex, symmetric])(*apply rewrite lemma*)
      done
next
  case c
  then show ?thesis
    apply(simp only:rewrite.simps)
        apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(4)[OF refl c] 14(1)]  split:if_splits) (*remove recursion*)
    apply(rule sat_main_8[symmetric])
    done
next
  case d
  have swap:"sat \<sigma> V v i (Since (And (Once (init_ivl I) \<gamma>) \<beta>) I (And \<alpha> \<gamma>)) =
             sat \<sigma> V v i (Since (And (Once (init_ivl I) \<gamma>) \<beta>) I (And \<gamma> \<alpha>))"
            "sat \<sigma> V v i (Since \<beta> I (And \<alpha> \<gamma>)) = sat \<sigma> V v i (Since \<beta> I (And \<gamma> \<alpha>))" 
    by auto
  from d show ?thesis
    apply(simp only:rewrite.simps)
    apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(5)[OF refl d] 14(1)]  split:if_splits) (*remove recursion*)
    apply(simp only: swap)
    apply(rule sat_main_8[symmetric])
    done
next
  case e
  then show ?thesis
  proof(cases "t=Swapped")
    case True
    then show ?thesis using e
      apply(simp only:rewrite.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(6)[OF refl e]] 14(1)  split:if_splits) (*remove recursion*)
      done
  next
    case False
    then show ?thesis using e not_swapped[OF False]
      apply(simp only:rewrite.simps fix_r.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_5_t 14(1) 14(6)[OF refl e]]  split:if_splits) (*remove recursion*)
      done
  qed
qed
next
case (15 \<alpha> \<gamma> I \<beta> t)
  let ?a = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<alpha> \<beta>"
  let ?b = "t=Same \<and> \<not> mem I 0 \<and> prop_cond \<gamma> \<beta>"
  let ?c = "t=Swapped \<and> prop_cond \<alpha> \<beta>"
  let ?d = "t=Swapped \<and> prop_cond \<gamma> \<beta>"
  consider (a) ?a |
           (b) "\<not>?a" "?b" |
           (c) "\<not>?a" "\<not>?b" "?c" |
           (d) "\<not>?a" "\<not>?b" "\<not>?c" "?d" |
           (e) "\<not>?a" "\<not>?b" "\<not>?c" "\<not>?d"  by argo
  then show ?case
  proof(cases)
    case a
    then have ex:"\<not> mem I 0" by auto
    from a show ?thesis
          apply(simp del: sat.simps add: rsub_2[OF f_conr2_6_t 15(1) 15(2)[OF refl a ]]  split:if_splits )
          apply(simp only:sat_main_7[OF ex, symmetric])(*apply rewrite lemma*)
      done
  next
    case b
    then have ex:"\<not> mem I 0" by auto
    have swap: "sat \<sigma> V v i (Until (And \<alpha> \<gamma>) I (And (Once I \<gamma>) \<beta>)) = sat \<sigma> V v i (Until (And \<gamma> \<alpha>) I (And (Once I \<gamma>) \<beta>))"
               "sat \<sigma> V v i (Since (And \<alpha> \<gamma>) I \<beta>) = sat \<sigma> V v i (Since (And \<gamma> \<alpha>) I \<beta>)"
      by auto
    from b show ?thesis
      apply(simp only:rewrite.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(1) 15(3)[OF refl b]]  split:if_splits) (*remove recursion*)
      apply(simp only: swap)
      apply(simp only: sat_main_7[OF ex, symmetric])(*apply rewrite lemma*)
      apply(auto)
      done
next
  case c
  thm 15(1)
  thm 15(4)[OF refl ]
  thm rsub_2[OF f_conr2_5_t  ]
  thm sat_main_8[symmetric]
  then show ?thesis
    apply(simp only:rewrite.simps)
        apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(4)[OF refl c] 15(1)]  split:if_splits) (*remove recursion*)
    apply(rule sat_main_9[symmetric])
    done
next
  case d
  have swap:"sat \<sigma> V v i (Until (And (Eventually (init_ivl I) \<gamma>) \<beta>) I (And \<alpha> \<gamma>)) =
             sat \<sigma> V v i (Until (And (Eventually (init_ivl I) \<gamma>) \<beta>) I (And \<gamma> \<alpha>))"
            "sat \<sigma> V v i (Until \<beta> I (And \<alpha> \<gamma>)) = sat \<sigma> V v i (Until \<beta> I (And \<gamma> \<alpha>))" 
    by auto
  from d show ?thesis using swap
    apply(simp only:rewrite.simps)
    apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(5)[OF refl d] 15(1)]  split:if_splits) (*remove recursion*)
    apply(simp only: swap)
    apply(rule sat_main_9[symmetric])
    done
next
  case e
  then show ?thesis
  proof(cases "t=Swapped")
    case True
    then show ?thesis using e
      apply(simp only:rewrite.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(6)[OF refl e]] 15(1)  split:if_splits) (*remove recursion*)
      done
  next
    case False
    then show ?thesis using e not_swapped[OF False]
      apply(simp only:rewrite.simps fix_r.simps)
      apply(simp del: sat.simps  add: rsub_2[OF f_conr2_6_t 15(1) 15(6)[OF refl e]]  split:if_splits) (*remove recursion*)
      done
  qed
qed
next
  case (24 y \<omega> b' f \<phi> t)
  then show ?case
    apply(simp only:rewrite.simps fix_r.simps rsub_agg[OF f_conr_agg_t 24[symmetric],simplified fix_r.simps, OF rewrite_fv])
    done
next
  case (25 I \<phi> t)
  then show ?case
    apply(simp only:rewrite.simps fix_r.simps rsub_1[OF f_conr_6_t 25])
    done
next
  case (34 I r t)
  then show ?case by (simp add: regex.map_comp o_def match_map_regex cong: regex.map_cong)
next
  case (35 I r t)
  then show ?case by (simp add: regex.map_comp o_def match_map_regex cong: regex.map_cong)
qed (simp only:rewrite.simps fix_r.simps;auto)+

lemma final_sat: "\<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> (project (rewrite (embed \<phi>) Same)) \<longleftrightarrow> \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile> \<phi>"
  unfolding sat_project sat_rewrite
  unfolding sat_embed[symmetric]
  by simp


subsection \<open> Simplify terms \<close>

definition st where
  "st t = (if Formula.fv_trm t = {} then Formula.Const (Formula.eval_trm [] t) else t)"

lemma eval_st:
  "Formula.eval_trm v (st t) = Formula.eval_trm v t"
  unfolding st_def by (induction t) auto

fun simplify_terms where
  "simplify_terms (Formula.Pred r ts) = Formula.Pred r (map st ts)"
| "simplify_terms (Formula.Let p \<phi> \<psi>) = Formula.Let p (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.Eq t1 t2) = Formula.Eq (st t1) (st t2)"
| "simplify_terms (Formula.Less t1 t2) = Formula.Less (st t1) (st t2)"
| "simplify_terms (Formula.LessEq t1 t2) = Formula.LessEq (st t1) (st t2)"
| "simplify_terms (Formula.Neg \<phi>) = Formula.Neg (simplify_terms \<phi>)"
| "simplify_terms (Formula.Or \<phi> \<psi>) = Formula.Or (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.And \<phi> \<psi>) = Formula.And (simplify_terms \<phi>) (simplify_terms \<psi>)"
| "simplify_terms (Formula.Ands l) = Formula.Ands (map simplify_terms l)"
| "simplify_terms (Formula.Exists t \<phi>) = Formula.Exists t (simplify_terms \<phi>)"
| "simplify_terms (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (simplify_terms \<phi>)"
| "simplify_terms (Formula.Prev I \<phi>) = Formula.Prev I (simplify_terms \<phi>)"
| "simplify_terms (Formula.Next I \<phi>) = Formula.Next I (simplify_terms \<phi>)"
| "simplify_terms (Formula.Since \<phi> I \<psi>) = Formula.Since (simplify_terms \<phi>) I (simplify_terms \<psi>)"
| "simplify_terms (Formula.Until \<phi> I \<psi>) = Formula.Until (simplify_terms \<phi>) I (simplify_terms \<psi>)"
| "simplify_terms (Formula.Trigger \<phi> I \<psi>) = Formula.Trigger (simplify_terms \<phi>) I (simplify_terms \<psi>)"
| "simplify_terms (Formula.Release \<phi> I \<psi>) = Formula.Release (simplify_terms \<phi>) I (simplify_terms \<psi>)"
| "simplify_terms (Formula.MatchP I r) = Formula.MatchP I (regex.map_regex simplify_terms r)"
| "simplify_terms (Formula.MatchF I r) = Formula.MatchF I (regex.map_regex simplify_terms r)"
| "simplify_terms (Formula.TP t) = Formula.TP (st t)"
| "simplify_terms (Formula.TS t) = Formula.TS (st t)"

lemma st_fvi:
  "Formula.fvi_trm b (st a) = Formula.fvi_trm b a"
  unfolding st_def
  by(induction a) auto

lemma simplify_terms_fvi:
  "Formula.fvi b (simplify_terms \<phi>) = Formula.fvi b \<phi>"
  by(induction \<phi> arbitrary: b rule:simplify_terms.induct) (auto simp:st_fvi fv_regex_alt regex.set_map)

lemma simplify_terms_nfv:
  "Formula.nfv (simplify_terms \<phi>) = Formula.nfv \<phi>" 
    unfolding Formula.nfv_def simplify_terms_fvi by auto

lemma simplify_terms_sat:
  "Formula.sat \<sigma> V v i (simplify_terms f) = Formula.sat \<sigma> V v i f"
proof(induction f arbitrary: V v i rule:simplify_terms.induct)
  case (1 r ts)
  then show ?case by(auto simp: comp_def eval_st split:option.splits)
next
  case (2 p \<phi> \<psi>)
  then show ?case unfolding simplify_terms.simps Formula.sat.simps 2 simplify_terms_nfv by auto
next
  case (3 p \<phi> \<psi>)
  then show ?case unfolding simplify_terms.simps Formula.sat.simps 3 simplify_terms_nfv by auto
next
qed (auto simp:eval_st Rewriting.match_map_regex simplify_terms_fvi split:nat.splits)


subsection \<open> Push negation \<close>

fun push_negation where
  "push_negation (Formula.Neg (Formula.And \<phi> \<psi>)) = Formula.Or (push_negation (Formula.Neg \<phi>)) (push_negation (Formula.Neg \<psi>))"
| "push_negation (Formula.Neg (Formula.Or \<phi> \<psi>)) = Formula.And (push_negation (Formula.Neg \<phi>)) (push_negation (Formula.Neg \<psi>))"
| "push_negation (Formula.Let p \<phi> \<psi>) = Formula.Let p (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.Neg \<phi>) = Formula.Neg (push_negation \<phi>)"
| "push_negation (Formula.Or \<phi> \<psi>) = Formula.Or (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.And \<phi> \<psi>) = Formula.And (push_negation \<phi>) (push_negation \<psi>)"
| "push_negation (Formula.Ands l) = Formula.Ands (map push_negation l)"
| "push_negation (Formula.Exists t \<phi>) = Formula.Exists t (push_negation \<phi>)"
| "push_negation (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (push_negation \<phi>)"
| "push_negation (Formula.Prev I \<phi>) = Formula.Prev I (push_negation \<phi>)"
| "push_negation (Formula.Next I \<phi>) = Formula.Next I (push_negation \<phi>)"
| "push_negation (Formula.Since \<phi> I \<psi>) = Formula.Since (push_negation \<phi>) I (push_negation \<psi>)"
| "push_negation (Formula.Until \<phi> I \<psi>) = Formula.Until (push_negation \<phi>) I (push_negation \<psi>)"
| "push_negation (Formula.MatchP I r) = Formula.MatchP I (regex.map_regex push_negation r)"
| "push_negation (Formula.MatchF I r) = Formula.MatchF I (regex.map_regex push_negation r)"
| "push_negation \<phi> = \<phi>"

lemma push_negation_fvi:
  "Formula.fvi b (push_negation \<phi>) = Formula.fvi b \<phi>"
  by(induction \<phi> arbitrary: b rule:push_negation.induct) (auto simp: fv_regex_alt regex.set_map)

lemma push_negation_nfv:
  "Formula.nfv (push_negation \<phi>) = Formula.nfv \<phi>" 
  unfolding Formula.nfv_def push_negation_fvi by auto

lemma push_negation_sat:
  "Formula.sat \<sigma> V v i (push_negation f) = Formula.sat \<sigma> V v i f"
proof(induction f arbitrary: V v i rule:push_negation.induct)
  case (3 p \<phi> \<psi>)
  then show ?case unfolding push_negation.simps Formula.sat.simps 3 push_negation_nfv by auto
next
  case (4 p \<phi> \<psi>)
  then show ?case unfolding push_negation.simps Formula.sat.simps 4 push_negation_nfv by auto
next
qed (auto simp: Rewriting.match_map_regex push_negation_fvi split:nat.splits)

fun elim_double_negation where
  "elim_double_negation (Formula.Neg (Formula.Neg \<phi>)) = elim_double_negation \<phi>"
| "elim_double_negation (Formula.Let p \<phi> \<psi>) = Formula.Let p (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.LetPast p \<phi> \<psi>) = Formula.LetPast p (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.Neg \<phi>) = Formula.Neg (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Or \<phi> \<psi>) = Formula.Or (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.And \<phi> \<psi>) = Formula.And (elim_double_negation \<phi>) (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.Ands l) = Formula.Ands (map elim_double_negation l)"
| "elim_double_negation (Formula.Exists t \<phi>) = Formula.Exists t (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Agg y \<omega> tys f \<phi>) = Formula.Agg y \<omega> tys f (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Prev I \<phi>) = Formula.Prev I (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Next I \<phi>) = Formula.Next I (elim_double_negation \<phi>)"
| "elim_double_negation (Formula.Since \<phi> I \<psi>) = Formula.Since (elim_double_negation \<phi>) I (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.Until \<phi> I \<psi>) = Formula.Until (elim_double_negation \<phi>) I (elim_double_negation \<psi>)"
| "elim_double_negation (Formula.MatchP I r) = Formula.MatchP I (regex.map_regex elim_double_negation r)"
| "elim_double_negation (Formula.MatchF I r) = Formula.MatchF I (regex.map_regex elim_double_negation r)"
| "elim_double_negation \<phi> = \<phi>"

lemma elim_double_negation_fvi:
  "Formula.fvi b (elim_double_negation \<phi>) = Formula.fvi b \<phi>"
  by(induction \<phi> arbitrary: b rule:elim_double_negation.induct) (auto simp: fv_regex_alt regex.set_map)

lemma elim_double_negation_nfv:
  "Formula.nfv (elim_double_negation \<phi>) = Formula.nfv \<phi>" 
  unfolding Formula.nfv_def elim_double_negation_fvi by auto

lemma elim_double_negation_sat:
  "Formula.sat \<sigma> V v i (elim_double_negation f) = Formula.sat \<sigma> V v i f"
proof(induction f arbitrary: V v i rule:elim_double_negation.induct)
  case (2 p \<phi> \<psi>)
  then show ?case unfolding elim_double_negation.simps Formula.sat.simps 2 elim_double_negation_nfv by auto
next
  case (3 p \<phi> \<psi>)
  then show ?case unfolding elim_double_negation.simps Formula.sat.simps 3 elim_double_negation_nfv by auto
next
qed (auto simp: Rewriting.match_map_regex elim_double_negation_fvi split:nat.splits)

definition normalize where
  "normalize = elim_double_negation \<circ> push_negation \<circ> simplify_terms"

lemma normalize_sat:
  "Formula.sat \<sigma> V v i (normalize f) = Formula.sat \<sigma> V v i f"
  unfolding normalize_def comp_apply 
  using simplify_terms_sat push_negation_sat elim_double_negation_sat 
  by auto


unbundle MFODL_no_notation
unbundle rewrite_no_notation

end
