(*<*)
theory Queue
  imports Preliminaries
begin
(*>*)

subsection \<open>Optimized queue data structure\<close>

lemma less_enat_iff: "a < enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j < i)"
  by (cases a) auto

type_synonym 'a queue_t = "'a list \<times> 'a list"

definition queue_invariant :: "'a queue_t \<Rightarrow> bool" where
  "queue_invariant q = (case q of ([], []) \<Rightarrow> True | (fs, l # ls) \<Rightarrow> True | _ \<Rightarrow> False)"

typedef 'a queue = "{q :: 'a queue_t. queue_invariant q}"
  by (auto simp: queue_invariant_def split: list.splits)

setup_lifting type_definition_queue

lift_definition linearize :: "'a queue \<Rightarrow> 'a list" is "(\<lambda>q. case q of (fs, ls) \<Rightarrow> fs @ rev ls)" .

lift_definition empty_queue :: "'a queue" is "([], [])"
  by (auto simp: queue_invariant_def split: list.splits)

lemma empty_queue_rep: "linearize empty_queue = []"
  by transfer (simp add: empty_queue_def linearize_def)

lift_definition is_empty :: "'a queue \<Rightarrow> bool" is "\<lambda>q. (case q of ([], []) \<Rightarrow> True | _ \<Rightarrow> False)" .

lemma linearize_t_Nil: "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = [] \<longleftrightarrow> q = ([], [])"
  by (auto split: prod.splits)

lemma is_empty_alt: "is_empty q \<longleftrightarrow> linearize q = []"
  by transfer (auto simp: linearize_t_Nil list.case_eq_if)

fun prepend_queue_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "prepend_queue_t a ([], []) = ([], [a])"
| "prepend_queue_t a (fs, l # ls) = (a # fs, l # ls)"
| "prepend_queue_t a (f # fs, []) = undefined"

lift_definition prepend_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is prepend_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim: prepend_queue_t.elims)

lemma prepend_queue_rep: "linearize (prepend_queue a q) = a # linearize q"
  by transfer
    (auto simp add: queue_invariant_def linearize_def elim: prepend_queue_t.elims split: prod.splits)

lift_definition append_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is
  "(\<lambda>a q. case q of (fs, ls) \<Rightarrow> (fs, a # ls))"
  by (auto simp: queue_invariant_def split: list.splits)

lemma append_queue_rep: "linearize (append_queue a q) = linearize q @ [a]"
  by transfer (auto simp add: linearize_def split: prod.splits)

fun safe_last_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_last_t ([], []) = (None, ([], []))"
| "safe_last_t (fs, l # ls) = (Some l, (fs, l # ls))"
| "safe_last_t (f # fs, []) = undefined"

lift_definition safe_last :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_last_t
  by (auto simp: queue_invariant_def split: prod.splits list.splits)

lemma safe_last_rep: "safe_last q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = last (linearize q))"
  by transfer (auto simp: queue_invariant_def split: list.splits elim: safe_last_t.elims)

fun safe_hd_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_hd_t ([], []) = (None, ([], []))"
| "safe_hd_t ([], [l]) = (Some l, ([], [l]))"
| "safe_hd_t ([], l # ls) = (let fs = rev ls in (Some (hd fs), (fs, [l])))"
| "safe_hd_t (f # fs, l # ls) = (Some f, (f # fs, l # ls))"
| "safe_hd_t (f # fs, []) = undefined"

lift_definition(code_dt) safe_hd :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_hd_t
proof -
  fix q :: "'a queue_t"
  assume "queue_invariant q"
  then show "pred_prod top queue_invariant (safe_hd_t q)"
    by (cases q rule: safe_hd_t.cases) (auto simp: queue_invariant_def Let_def split: list.split)
qed

lemma safe_hd_rep: "safe_hd q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = hd (linearize q))"
  by transfer
    (auto simp add: queue_invariant_def Let_def hd_append split: list.splits elim: safe_hd_t.elims)

fun replace_hd_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_hd_t a ([], []) = ([], [])"
| "replace_hd_t a ([], [l]) = ([], [a])"
| "replace_hd_t a ([], l # ls) = (let fs = rev ls in (a # tl fs, [l]))"
| "replace_hd_t a (f # fs, l # ls) = (a # fs, l # ls)"
| "replace_hd_t a (f # fs, []) = undefined"

lift_definition replace_hd :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_hd_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_hd_t.elims)

lemma tl_append: "xs \<noteq> [] \<Longrightarrow> tl xs @ ys = tl (xs @ ys)"
  by simp

lemma replace_hd_rep: "linearize q = f # fs \<Longrightarrow> linearize (replace_hd a q) = a # fs"
proof (transfer fixing: f fs a)
  fix q
  assume "queue_invariant q" and "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = f # fs"
  then show "(case replace_hd_t a q of (fs, ls) \<Rightarrow> fs @ rev ls) = a # fs"
    by (cases "(a, q)" rule: replace_hd_t.cases) (auto simp: queue_invariant_def tl_append)
qed

fun replace_last_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_last_t a ([], []) = ([], [])"
| "replace_last_t a (fs, l # ls) = (fs, a # ls)"
| "replace_last_t a (fs, []) = undefined"

lift_definition replace_last :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_last_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_last_t.elims)

lemma replace_last_rep: "linearize q = fs @ [f] \<Longrightarrow> linearize (replace_last a q) = fs @ [a]"
  by transfer (auto simp: queue_invariant_def split: list.splits prod.splits elim!: replace_last_t.elims)

fun tl_queue_t :: "'a queue_t \<Rightarrow> 'a queue_t" where
  "tl_queue_t ([], []) = ([], [])"
| "tl_queue_t ([], [l]) = ([], [])"
| "tl_queue_t ([], l # ls) = (tl (rev ls), [l])"
| "tl_queue_t (a # as, fs) = (as, fs)"

lift_definition tl_queue :: "'a queue \<Rightarrow> 'a queue" is tl_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim!: tl_queue_t.elims)

lemma tl_queue_rep: "linearize (tl_queue q) = tl (linearize q)"
  by transfer (auto simp: tl_append split: prod.splits list.splits elim!: tl_queue_t.elims)

lemma length_tl_queue_rep: "\<not>is_empty q \<Longrightarrow>
  length (linearize (tl_queue q)) < length (linearize q)"
  by transfer (auto split: prod.splits list.splits elim: tl_queue_t.elims)

lemma length_tl_queue_safe_hd:
  assumes "safe_hd q = (Some a, q')"
  shows "length (linearize (tl_queue q')) < length (linearize q)"
  using safe_hd_rep[OF assms]
  by (auto simp add: length_tl_queue_rep is_empty_alt)

function dropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "dropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a then dropWhile_queue f (tl_queue q') else q')"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma dropWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  dropWhile P xs = (if P (hd xs) then dropWhile P (tl xs) else xs)"
  by (cases xs) auto

lemma dropWhile_queue_rep: "linearize (dropWhile_queue f q) = dropWhile f (linearize q)"
  by (induction f q rule: dropWhile_queue.induct)
     (auto simp add: tl_queue_rep dropWhile_hd_tl is_empty_alt
      split: prod.splits option.splits dest: safe_hd_rep)

function takeWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> ('a queue \<times> 'a queue)" where
  "takeWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', q')
  | (Some a, q') \<Rightarrow> if f a
    then let (q'', rem) = takeWhile_queue f (tl_queue q') in (prepend_queue a q'', q')
    else (empty_queue, q'))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takeWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  takeWhile P xs = (if P (hd xs) then hd xs # takeWhile P (tl xs) else [])"
  by (cases xs) auto

lemma takeWhile_queue_rep_fst: "linearize (fst (takeWhile_queue f q)) = takeWhile f (linearize q)"
proof(induction f q rule: takeWhile_queue.induct)
  case (1 f q)
  then obtain hd rm where safe_hd_eq: "safe_hd q = (hd, rm)" by (meson prod.exhaust_sel)
  then show ?case 
  proof(cases "hd")
    case None
    then show ?thesis using safe_hd_eq by(auto dest: safe_hd_rep)
  next
    case (Some a)
    then show ?thesis 
    proof(cases "f a")
      case True
      then show ?thesis using safe_hd_eq Some 1[OF safe_hd_eq[symmetric] Some True] 
        by(auto simp add: prepend_queue_rep tl_queue_rep  takeWhile_hd_tl is_empty_alt split: prod.splits dest: safe_hd_rep)
    next
      case False
      then show ?thesis using safe_hd_eq Some by(auto simp add: empty_queue_rep takeWhile_hd_tl  dest: safe_hd_rep) 
    qed
  qed
qed

lemma takeWhile_queue_rep_snd: "linearize (snd (takeWhile_queue f q)) = linearize q"
proof(induction f q rule: takeWhile_queue.induct)
  case (1 f q)
  then obtain hd rm where safe_hd_eq: "safe_hd q = (hd, rm)" by (meson prod.exhaust_sel)
  then show ?case 
  proof(cases "hd")
    case None
    then show ?thesis using safe_hd_eq by (simp add: safe_hd_rep)
  next
    case (Some a)
    then show ?thesis
    proof(cases "f a")
      case True
      then show ?thesis apply(auto) using 1[OF safe_hd_eq[symmetric] Some True] safe_hd_eq Some
        by(auto simp: safe_hd_rep split:prod.splits)
    next
      case False
      then show ?thesis using safe_hd_eq Some by (simp add: safe_hd_rep)
    qed
  qed
qed

function takedropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue \<times> 'a list" where
  "takedropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', [])
  | (Some a, q') \<Rightarrow> if f a
    then (case takedropWhile_queue f (tl_queue q') of (q'', as) \<Rightarrow> (q'', a # as))
    else (q', []))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takedropWhile_queue_fst: "fst (takedropWhile_queue f q) = dropWhile_queue f q"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits) (auto simp add: case_prod_unfold split: option.splits)
qed

lemma takedropWhile_queue_snd: "snd (takedropWhile_queue f q) = takeWhile f (linearize q)"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits)
      (auto simp add: case_prod_unfold tl_queue_rep takeWhile_hd_tl is_empty_alt
        split: option.splits dest: safe_hd_rep)
qed

lemma not_empty_head_q:
  assumes "\<not>is_empty q"
  shows "\<exists>ts tss. safe_hd q = (Some ts, tss)"
  using assms apply(transfer) apply(auto) 
proof -
  fix xs ys
  assume "queue_invariant ((xs :: 'a list), ys)" "\<not> (case xs of [] \<Rightarrow> (case ys of [] \<Rightarrow> True | a # list \<Rightarrow> False) | aa # list \<Rightarrow> False)"
  then obtain y ys' where "ys = y#ys'" unfolding queue_invariant_def by(auto split:list.splits)
  then show "\<exists>ts aa ba. queue_invariant (aa, ba) \<and> safe_hd_t (xs, ys) = (Some ts, aa, ba) " 
    by(cases xs; cases ys') (auto simp:queue_invariant_def Let_def list.case_eq_if) 
qed

fun pop_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "pop_t ([], []) = (None, ([], []))"
| "pop_t ([], [y]) = (Some y, ([], []))"
| "pop_t ([], y # ys) = (case rev ys of z # ys' \<Rightarrow> (Some z, (ys', [y])))"
| "pop_t (x # xs, ys) = (Some x, (xs, ys))"

lift_definition (code_dt) pop :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is pop_t
proof -
  fix q :: "'a queue_t"
  assume "queue_invariant q"
  then show "pred_prod top queue_invariant (pop_t q)"
    by (induction q rule: pop_t.induct)
      (simp_all add: queue_invariant_def split: list.split)
qed

lemma pop_rep: "pop q = (x, q') \<Longrightarrow> (case x of
    None \<Rightarrow> linearize q = [] \<and> q' = q
  | Some y \<Rightarrow> linearize q = y # linearize q')"
  by transfer (auto split: list.splits elim!: pop_t.elims)

end