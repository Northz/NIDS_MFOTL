(*<*)
theory Correctness
  imports
    Correct_Un_Ops
    Correct_Regex
    Correct_Since
    Correct_Trigger
    "MFOTL_Monitor_Devel.Abstract_Monitor"
begin
(*>*)


subsection \<open> Well-formed mformula invariant \<close>

inductive (in maux) wf_mformula :: "Formula.trace \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat 
  \<Rightarrow> event_data list set \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula \<Rightarrow> ty Formula.formula \<Rightarrow> bool" for \<sigma> j 
  where Eq: "is_simple_eq t1 t2 
    \<Longrightarrow> \<forall>x\<in>Formula.fv_trm t1. x < n \<Longrightarrow> \<forall>x\<in>Formula.fv_trm t2. x < n
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MRel (eq_rel n t1 t2)) (Formula.Eq t1 t2)"
  | Pred: "\<forall>x\<in>Formula.fv ((Formula.Pred e ts) :: ty Formula.formula). x < n 
    \<Longrightarrow> \<forall>t\<in>set ts. Formula.is_Var t \<or> Formula.is_Const t
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MPred e ts (pred_mode_of n ts)) (Formula.Pred e ts)"
  | Let: "wf_mformula \<sigma> j P V m UNIV \<phi> \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j (P((p, m) \<mapsto> progress \<sigma> P \<phi>' j)) 
      (V((p, m) \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>')) n R \<psi> \<psi>'
    \<Longrightarrow> {0..<m} \<subseteq> Formula.fv \<phi>' \<Longrightarrow> m = Formula.nfv \<phi>' \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MLet p m \<phi> \<psi>) (Formula.Let p \<phi>' \<psi>')"
  | LetPast: "wf_mformula \<sigma> j (P((p, m)\<mapsto>i)) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) m UNIV \<phi> \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j (P((p, m) \<mapsto> letpast_progress \<sigma> P (p, m) \<phi>' j)) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) n R \<psi> \<psi>'
    \<Longrightarrow> (case buf of
      None \<Rightarrow> i = letpast_progress \<sigma> P (p, m) \<phi>' j
    | Some Z \<Rightarrow> Suc i = letpast_progress \<sigma> P (p, m) \<phi>' j \<and>
        qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
          (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i) Z)
    \<Longrightarrow> safe_letpast (p, m) \<phi>' \<le> PastRec 
    \<Longrightarrow> \<comment> \<open>safe\<close> {0..<m} \<subseteq> Formula.fv \<phi>' \<Longrightarrow> m = Formula.nfv \<phi>'
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MLetPast p m \<phi> \<psi> i buf) (Formula.LetPast p \<phi>' \<psi>')"
  | And: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if pos then \<chi> = Formula.And \<phi>' \<psi>'
      else \<chi> = Formula.And \<phi>' (Formula.Neg \<psi>') \<and> Formula.fv \<psi>' \<subseteq> Formula.fv \<phi>'
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAnd (fv \<phi>') \<phi> pos (fv \<psi>') \<psi> buf) \<chi>"
  | AndAssign: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow>
    x < n \<Longrightarrow> x \<notin> Formula.fv \<phi>' \<Longrightarrow> Formula.fv_trm t \<subseteq> Formula.fv \<phi>' \<Longrightarrow> (x, t) = conf
    \<Longrightarrow> \<psi>' = Formula.Eq (Formula.Var x) t \<or> \<psi>' = Formula.Eq t (Formula.Var x)
    \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAndAssign \<phi> conf) (Formula.And \<phi>' \<psi>')"
  | AndRel: "wf_mformula \<sigma> j P V n R \<phi> \<phi>'
    \<Longrightarrow> \<psi>' = formula_of_constraint conf
    \<Longrightarrow> (let (t1, _, _, t2) = conf in Formula.fv_trm t1 \<union> Formula.fv_trm t2 \<subseteq> Formula.fv \<phi>')
    \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAndRel \<phi> conf) (Formula.And \<phi>' \<psi>')"
  | And_Trigger: "wf_mformula \<sigma> j P V n R \<alpha> \<alpha>' \<Longrightarrow> wf_mbuft2' \<sigma> P V j n R \<alpha>' \<phi>'' I \<psi>' buf1
    \<Longrightarrow> fv (Formula.Trigger \<phi>'' I \<psi>') \<subseteq> fv \<alpha>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>' \<Longrightarrow>
    if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<phi> \<phi>'
    \<Longrightarrow> safe_formula \<phi>'' = args_pos args \<Longrightarrow> args_ivl args = I \<Longrightarrow> args_n args = n
    \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> \<forall>x\<in>Formula.fv \<psi>'. x < n 
    \<Longrightarrow> if mem I 0 then Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' else Formula.fv \<phi>' = Formula.fv \<psi>'
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf2
    \<Longrightarrow> wf_ts \<sigma> P j \<phi>' \<psi>' nts
    \<Longrightarrow> wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Trigger \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAndTrigger (fv \<alpha>') \<alpha> buf1 args \<phi> \<psi> buf2 nts aux) 
      (Formula.And \<alpha>' (Formula.Trigger \<phi>'' I \<psi>'))"
  | And_Release: "\<not> mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> Formula.fv \<phi>' = Formula.fv \<psi>' 
    \<Longrightarrow> Formula.fv \<psi>' \<subseteq> Formula.fv \<alpha>' \<Longrightarrow> safe_formula \<alpha>'
    \<Longrightarrow> safe_formula (release_safe_bounded \<phi>' I \<psi>')
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R (formula.And \<alpha>' (formula.Neg (Formula.eventually I Formula.TT))) (formula.And \<alpha>' (release_safe_bounded \<phi>' I \<psi>')) buf
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>')
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (Formula.And \<alpha>' (Formula.Release \<phi>' I \<psi>'))"
  | Ands: "list_all2 (\<lambda>\<phi> \<phi>'. wf_mformula \<sigma> j P V n R \<phi> \<phi>') l (l_pos @ map remove_neg l_neg)
    \<Longrightarrow> wf_mbufn (progress \<sigma> P (Formula.Ands l') j) 
      (map (\<lambda>\<psi>. progress \<sigma> P \<psi> j) (l_pos @ map remove_neg l_neg)) 
      (map (\<lambda>\<psi> i. qtable n (Formula.fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>)) 
        (l_pos @ map remove_neg l_neg)) buf
    \<Longrightarrow> (l_pos, l_neg) = partition safe_formula l' \<Longrightarrow> l_pos \<noteq> []
    \<Longrightarrow> list_all safe_formula (map remove_neg l_neg)
    \<Longrightarrow> A_pos = map fv l_pos \<Longrightarrow> A_neg = map fv l_neg \<Longrightarrow> \<Union>(set A_neg) \<subseteq> \<Union>(set A_pos)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAnds A_pos A_neg l buf) (Formula.Ands l')"
  | Or: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> Formula.fv \<phi>' = Formula.fv \<psi>' \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr \<phi> \<psi> buf) (Formula.Or \<phi>' \<psi>')"
  | Neg: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> Formula.fv \<phi>' = {} \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MNeg \<phi>) (Formula.Neg \<phi>')"
  | Exists: "wf_mformula \<sigma> j P V (Suc n) (lift_envs R) \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MExists \<phi>) (Formula.Exists t \<phi>')"
  | Agg: "wf_mformula \<sigma> j P V (length tys + n) (lift_envs' (length tys) R) \<phi> \<phi>'
    \<Longrightarrow> y < n \<Longrightarrow> y + (length tys) \<notin> Formula.fv \<phi>' \<Longrightarrow> {0..<length tys} \<subseteq> Formula.fv \<phi>'
    \<Longrightarrow> Formula.fv_trm f \<subseteq> Formula.fv \<phi>' \<Longrightarrow> aggargs_g0 args = (Formula.fv \<phi>' \<subseteq> {0..<length tys})
    \<Longrightarrow> aggargs_cols args = fv \<phi>' \<Longrightarrow> aggargs_n args = n \<Longrightarrow> aggargs_y args = y
    \<Longrightarrow> aggargs_\<omega> args = \<omega> \<Longrightarrow> aggargs_tys args = tys \<Longrightarrow> aggargs_f args = f \<Longrightarrow> safe_formula \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MAgg args \<phi>) (Formula.Agg y \<omega> tys f \<phi>')"
  | Prev: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> first \<longleftrightarrow> j = 0
    \<Longrightarrow> list_all2 (\<lambda>i (r). qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>') r)
      [min (progress \<sigma> P \<phi>' j) (j-1)..<progress \<sigma> P \<phi>' j] buf
    \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [min (progress \<sigma> P \<phi>' j) (j-1)..<j] nts
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MPrev I \<phi> first buf nts) (Formula.Prev I \<phi>')"
  | Next: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> first \<longleftrightarrow> progress \<sigma> P \<phi>' j = 0
    \<Longrightarrow> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress \<sigma> P \<phi>' j - 1..<j] nts
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MNext I \<phi> first nts) (Formula.Next I \<phi>')"
  | Since: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> args_ivl args = I \<Longrightarrow> args_n args = n
    \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')
    \<Longrightarrow> Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>'
    \<Longrightarrow> wf_mbuf2S \<sigma> P V j n R \<phi>' I \<psi>' buf (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j)) 
      (progress \<sigma> P (Formula.Since \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_since_aux \<sigma> V R args \<phi>' \<psi>' aux (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j)) 
      (progress \<sigma> P (Formula.Since \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_mformula \<sigma> j P V (agg_n args) R' (MSince args \<phi> \<psi> buf aux) 
      (packagg args (Formula.Since \<phi>'' I \<psi>'))"
  | Until: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'
    \<Longrightarrow> safe_formula \<phi>' \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> args_ivl args = I \<Longrightarrow> args_n args = n
    \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')
    \<Longrightarrow> Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf
    \<Longrightarrow> wf_ts \<sigma> P j \<phi>' \<psi>' nts
    \<Longrightarrow> t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j))))
    \<Longrightarrow> wf_until_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Until \<phi>'' I \<psi>') j)
    \<Longrightarrow> progress \<sigma> P (Formula.Until \<phi>'' I \<psi>') j + length_muaux args aux 
      = min (progress \<sigma> P \<phi>' j) (progress \<sigma> P \<psi>' j)
    \<Longrightarrow> wf_mformula \<sigma> j P V (agg_n args) R' (MUntil args \<phi> \<psi> buf nts t aux) 
      (packagg args (Formula.Until \<phi>'' I \<psi>'))"
  | Trigger_0: "wf_mformula \<sigma> j P V n R \<psi> \<psi>'
    \<Longrightarrow> if args_pos args then \<phi>'' = \<phi>' else \<phi>'' = Formula.Neg \<phi>'
    \<Longrightarrow> wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> safe_formula \<phi>'' = args_pos args \<Longrightarrow> args_ivl args = I
    \<Longrightarrow> args_n args = n \<Longrightarrow> args_L args = Formula.fv \<phi>' \<Longrightarrow> args_R args = Formula.fv \<psi>'
    \<Longrightarrow> \<forall>x\<in>Formula.fv \<psi>'. x < n \<Longrightarrow> mem I 0
    \<Longrightarrow> if mem I 0 then (Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>') else Formula.fv \<phi>' = Formula.fv \<psi>'
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R \<phi>' \<psi>' buf \<Longrightarrow> wf_ts \<sigma> P j \<phi>' \<psi>' nts
    \<Longrightarrow> wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (progress \<sigma> P (Formula.Trigger \<phi>'' I \<psi>') j)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MTrigger args \<phi> \<psi> buf nts aux) (Formula.Trigger \<phi>'' I \<psi>')"
  | Release_0: "mem I 0 \<Longrightarrow> bounded I \<Longrightarrow> Formula.fv \<phi>' \<subseteq> Formula.fv \<psi>' 
    \<Longrightarrow> safe_formula \<psi>' \<Longrightarrow> safe_formula (release_safe_0 \<phi>' I \<psi>')
    \<Longrightarrow> wf_mbuf2' \<sigma> P V j n R (Formula.Until \<psi>' I (Formula.And \<psi>' \<phi>')) (always_safe_0 I \<psi>') buf
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (release_safe_0 \<phi>' I \<psi>')
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MOr L\<^sub>M R\<^sub>M buf) (Formula.Release \<phi>' I \<psi>')"
  | MatchP: "(case to_mregex r of (mr', \<phi>s') 
      \<Rightarrow> list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<phi>s' \<and> mr = mr')
    \<Longrightarrow> mrs = sorted_list_of_set (RPDs mr) \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Past Strict r
    \<Longrightarrow> wf_mbufn' \<sigma> P V j n R r buf \<Longrightarrow> wf_ts_regex \<sigma> P j r nts
    \<Longrightarrow> wf_matchP_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchP I r) j)
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MMatchP I mr mrs \<phi>s buf nts aux) (Formula.MatchP I r)"
  | MatchF: "(case to_mregex r of (mr', \<phi>s') 
      \<Rightarrow> list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<phi>s' \<and> mr = mr')
    \<Longrightarrow> mrs = sorted_list_of_set (LPDs mr) \<Longrightarrow> Regex.safe_regex fv rgx_safe_pred Futu Strict r
    \<Longrightarrow> wf_mbufn' \<sigma> P V j n R r buf \<Longrightarrow> wf_ts_regex \<sigma> P j r nts
    \<Longrightarrow> t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (progress_regex \<sigma> P r j)))
    \<Longrightarrow> wf_matchF_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchF I r) j) 0
    \<Longrightarrow> progress \<sigma> P (Formula.MatchF I r) j + length aux = progress_regex \<sigma> P r j
    \<Longrightarrow> wf_mformula \<sigma> j P V n R (MMatchF I mr mrs \<phi>s buf nts t aux) (Formula.MatchF I r)"
  | MTP: "\<forall>x\<in>Formula.fv_trm t. x < n \<Longrightarrow> Formula.is_Var t \<or> Formula.is_Const t
    \<Longrightarrow> mtrm_of_trm t = mt \<Longrightarrow> wf_mformula \<sigma> j P V n R (MTP mt j) (Formula.TP t)"
  | MTS: "\<forall>x\<in>Formula.fv_trm t. x < n \<Longrightarrow> Formula.is_Var t \<or> Formula.is_Const t
    \<Longrightarrow> mtrm_of_trm t = mt \<Longrightarrow> wf_mformula \<sigma> j P V n R (MTS mt) (Formula.TS t)"

definition (in maux) wf_mstate :: "sig \<Rightarrow> tyenv \<Rightarrow> ty Formula.formula \<Rightarrow> Formula.prefix 
  \<Rightarrow> event_data list set \<Rightarrow> ('msaux, 'muaux, 'mtaux) mstate \<Rightarrow> bool" 
  where "wf_mstate S E \<phi> \<pi> R st 
  \<longleftrightarrow> mstate_j st = plen \<pi> \<and> mstate_n st = Formula.nfv \<phi> \<and> S, E \<turnstile> \<phi> \<and> wty_prefix S \<pi> 
    \<and> (\<forall>\<sigma>. prefix_of \<pi> \<sigma> \<and> wty_trace S \<sigma> 
      \<longrightarrow> mstate_i st = progress \<sigma> Map.empty \<phi> (plen \<pi>) 
        \<and> wf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (mstate_n st) R (mstate_m st) \<phi>) 
        \<and> mstate_t st = drop (mstate_i st) (pts \<pi>)"

definition (in maux) letpast_meval_invar 
  where "letpast_meval_invar n V \<sigma> P \<phi>' m j' i ys xs p ts db \<phi> k 
  = (let j = j' - length ts in
    wf_mformula \<sigma> j (P((p, m)\<mapsto>i)) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) m UNIV \<phi> \<phi>' 
    \<and> i + length xs \<le> progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j 
    \<and> i + length xs \<le> letpast_progress \<sigma> P (p, m) \<phi>' j 
    \<and> list_all2 
      (\<lambda>i X. qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i) X)
      [i..<progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j] xs
    \<and> list_all2 
      (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i))
      [k..<progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j] ys 
    \<and> k \<le> progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' j)"

definition (in maux) letpast_meval_post 
  where "letpast_meval_post n V \<sigma> P \<phi>' m j i' xs buf' p \<phi>f k
  = (wf_mformula \<sigma> j (P((p, m)\<mapsto>i')) 
      (V((p, m) \<mapsto> letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>'))) m UNIV \<phi>f \<phi>' 
    \<and> (case buf' of
      None \<Rightarrow> i' = letpast_progress \<sigma> P (p, m) \<phi>' j
    | Some Z \<Rightarrow> Suc i' = letpast_progress \<sigma> P (p, m) \<phi>' j 
      \<and> qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i') Z) 
    \<and> list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) 
        (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i))
      [k..<letpast_progress \<sigma> P (p, m) \<phi>' j] xs)"

lemma (in maux) letpast_meval_invar_init:
  assumes "pred_mapping (\<lambda> x. x \<le> (j - length ts)) P"
  assumes "wf_mformula \<sigma> (j-length ts) P V n R (MLetPast p m \<phi> \<psi> i buf) (Formula.LetPast p \<phi>' \<psi>')"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i [] (list_of_option buf) p ts db \<phi> (letpast_progress \<sigma> P (p, m) \<phi>' (j-length ts))"
proof -
  from assms have
    1: "wf_mformula \<sigma> (j - length ts) (P((p, m)\<mapsto>i)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi> \<phi>'" 
    and 2: "case buf of
      None \<Rightarrow> i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)
    | Some Z \<Rightarrow> Suc i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts) \<and>
        qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i) Z" 
    and 3: "safe_letpast (p, m) \<phi>' \<le> PastRec"
    by (auto elim: wf_mformula.cases)
  moreover have progress: "progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' (j-length ts) = letpast_progress \<sigma> P (p, m) \<phi>' (j-length ts)"
  proof (cases buf)
    case None
    with 2 have "i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)" by simp
    then show ?thesis using assms(1) by (simp add: letpast_progress_fixpoint)
  next
    case (Some Z)
    with 2 have "Suc i = letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)" by simp
    then show ?thesis
      using assms(1) 3 by (simp add: progress_Suc_letpast_progress_eq)
  qed
  moreover have "i + length (list_of_option buf) \<le> letpast_progress \<sigma> P (p, m) \<phi>' (j - length ts)"
    using 2 by (cases buf) simp_all
  moreover have "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
      [i..<progress \<sigma> (P((p, m)\<mapsto>i)) \<phi>' (j-length ts)] (list_of_option buf)"
    unfolding progress using 2
    by (cases buf) (auto simp add: list_all2_Cons2 upt_eq_Cons_conv)
  ultimately show ?thesis unfolding letpast_meval_invar_def
    by (simp add: Let_def)
qed

lemma (in maux) invar_recursion_invar:
  assumes "pred_mapping (\<lambda> x. x\<le>(j-length ts)) P"
  assumes "pred_mapping (\<lambda> x. x\<le>j) P'"
  assumes "rel_mapping (\<le>) P P'"
  assumes meval: "case meval j m ts (Mapping.update (p, m) xs db) \<phi> of (xs', \<phi>\<^sub>n) \<Rightarrow>
    wf_mformula \<sigma> j (P'((p, m) \<mapsto> i + length xs)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
    [progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j-length ts)..<progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>' j] xs'"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k\<Longrightarrow>
  (ys', \<phi>f) = meval j m ts (Mapping.update (p, m) xs db) \<phi> \<Longrightarrow>
  ys' \<noteq> [] \<Longrightarrow>
  i + length xs < j \<Longrightarrow>
  letpast_meval_invar n V \<sigma> P' \<phi>' m j (i + length xs) (ys@ys') ys' p [] (Mapping.map_values (\<lambda>_ _. []) db) \<phi>f k"
  unfolding letpast_meval_invar_def Let_def using assms
  apply(simp_all split: prod.splits)
  apply clarify
  apply (subgoal_tac "i \<le> j - length ts")
   apply(subgoal_tac "i + length xs = progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)")
    apply(subgoal_tac "i + length xs + length ys' = progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>' j")
     apply(intro conjI)
         apply(erule ord_eq_le_trans)
         apply (rule progress_mono_gen; simp)
        apply (erule ord_eq_le_trans)
        apply (rule le_letpast_progress_preservation) (* TODO(JS): adjust lemma to simplify steps below? *)
            apply assumption
           apply assumption
          apply (simp add: rel_mapping_reflp reflp_def)
         apply (rule order_trans[of _ "i + length xs"])
          apply simp
         apply (erule order_trans[of _ "letpast_progress _ _ _ _ _"])
         apply (rule letpast_progress_mono; assumption?)
         apply simp
        apply simp
       apply simp
      apply simp
      apply(subst list_all2_append2)
      apply(rule exI[where x="[k..<Progress.progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)]"])
      apply(rule exI[where x="[Progress.progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)..<(Progress.progress \<sigma> (P'((p, m) \<mapsto> i+length xs)) \<phi>' j)]"])
      apply(simp)
      apply(intro conjI)
        apply(rule upt_add_eq_append')
         apply(simp)
        apply(rule progress_mono_gen)
           apply(simp)
          apply(rule pred_mapping_map_upd; assumption)
         apply(rule pred_mapping_map_upd)
          apply(simp)
         apply(erule pred_mapping_mono)
         apply force
        apply(intro rel_mapping_map_upd)
         apply(simp)
        apply(simp add: rel_mapping_reflp reflp_def)
       apply (metis (no_types, lifting) length_upt list_all2_lengthD)
      apply (metis (no_types, lifting) length_upt list_all2_lengthD)
     apply (smt (z3) add_cancel_left_right add_diff_inverse_nat add_lessD1 diff_is_0_eq' list_all2_Nil nat_le_linear nat_neq_iff rev_min_pm upt_conv_Nil zero_less_diff)
    apply (drule list_all2_lengthD[where ys=ys'])
    apply simp
    apply (subst (asm) le_imp_diff_is_add)
     apply (rule progress_mono_gen; simp)
    apply simp
   apply (metis (no_types, lifting) add_leD1 diff_add_inverse eq_diff_iff le_add1 length_upt list_all2_lengthD)
  apply (drule (1) order_trans[OF _ letpast_progress_le])
  by simp

lemma (in maux) invar_recursion_post:
  assumes "safe_letpast (p, m) \<phi>' \<le> PastRec"
  assumes "pred_mapping (\<lambda> x. x\<le>(j-length ts)) P"
  assumes "pred_mapping (\<lambda> x. x\<le>j) P'"
  assumes "rel_mapping (\<le>) P P'"
  assumes meval: "case meval j m ts (Mapping.update (p, m) xs db) \<phi> of (xs', \<phi>\<^sub>n) \<Rightarrow>
    wf_mformula \<sigma> j (P'((p, m) \<mapsto> i + length xs)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
    [progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j-length ts)..<progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>' j] xs'"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k\<Longrightarrow>
  (ys', \<phi>f) = meval j m ts (Mapping.update (p, m) xs db) \<phi> \<Longrightarrow>
  i' = i + length xs \<Longrightarrow>
  (case ys' of [] \<Rightarrow> buf' = None | Z # _ \<Rightarrow> buf' = Some Z \<and> Suc i' \<ge> j) \<Longrightarrow>
  letpast_meval_post n V \<sigma> P' \<phi>' m j i' (ys@ys') buf' p \<phi>f k"
  unfolding letpast_meval_invar_def letpast_meval_post_def Let_def using assms
  apply clarsimp
  apply (rule context_conjI)
  subgoal
    apply (clarsimp simp add: list_all2_Cons2 upt_eq_Cons_conv less_eq_Suc_le split: list.splits)
    subgoal
      apply (rule antisym)
       apply (erule order_trans[of _ "letpast_progress _ _ _ _ _"])
       apply (rule letpast_progress_mono; assumption?)
       apply simp
      apply (subst letpast_progress_def)
      apply (rule cInf_lower)
       apply simp
       apply (rule conjI)
        apply (erule order_trans[of _ "letpast_progress _ _ _ _ _"])
        apply (rule order_trans[OF letpast_progress_le]; assumption?)
        apply simp
       apply (drule list_all2_lengthD[where ys=xs])
       apply (simp (asm_lr) add: le_imp_diff_is_add add.commute)
       apply (rule antisym)
        apply (rule order_trans[of _ "progress _ _ _ _"], assumption)
        apply (rule progress_mono_gen) (* TODO(JS): should add subgoal_tac; subgoal is needed again below *)
           apply simp
          apply (rule pred_mapping_map_upd)
           apply (rule order_trans[OF order_trans, of i "i + length xs" "letpast_progress _ _ _ _ _"])
             apply simp
            apply assumption
           apply (rule letpast_progress_le; assumption)
          apply assumption
         apply (rule pred_mapping_map_upd)
          apply (erule order_trans[of _ "letpast_progress _ _ _ _ _"])
          apply (rule order_trans[OF letpast_progress_le]; assumption?)
          apply simp
         apply assumption
        apply simp
       apply linarith
      apply simp
      done
    subgoal for Z ys''
      apply (subgoal_tac "i + length xs = Progress.progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)")
       apply simp
       apply (rule antisym)
        apply (erule order_trans)
        apply (rule le_letpast_progress_preservation; assumption?)
          apply (rule rel_mapping_order_refl)
         apply (erule order_trans)
         apply (rule letpast_progress_mono; assumption?)
         apply simp
        apply simp
       apply (erule order_trans[rotated])
       apply (rule letpast_progress_le; assumption)
      by (metis (no_types, lifting) add_leD1 diff_add_inverse eq_diff_iff le_add1 length_upt list_all2_lengthD)
    done
  subgoal
    apply (subst list_all2_append2)
    apply (rule exI[where x="[k..<Progress.progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)]"])
    apply (rule exI[where x="[Progress.progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)..<
      Progress.progress \<sigma> (P'((p, m) \<mapsto> i + length xs)) \<phi>' j]"])
    apply (intro conjI)
        apply (subst upt_add_eq_append'[symmetric]; assumption?)
         apply (rule progress_mono_gen)
            apply simp
           apply (rule pred_mapping_map_upd)
            apply (rule order_trans[OF order_trans, of i "i + length xs" "letpast_progress _ _ _ _ _"])
              apply simp
             apply assumption
            apply (rule letpast_progress_le; assumption)
           apply assumption
          apply (rule pred_mapping_map_upd)
           apply (erule order_trans[of _ "letpast_progress _ _ _ _ _"])
           apply (rule order_trans[OF letpast_progress_le]; assumption?)
           apply simp
          apply assumption
         apply simp
        apply (simp add: letpast_progress_fixpoint progress_Suc_letpast_progress_eq split: list.splits)
    using list_all2_lengthD apply blast
    using list_all2_lengthD apply blast
    by assumption+
  done

lemma (in maux) letpast_meval_ys: "(ys', i', buf', \<phi>f) = letpast_meval m j i ys xs p ts db \<phi> \<Longrightarrow> \<exists> zs. ys' = ys@zs"
  apply (induction i ys xs p ts db \<phi> arbitrary: i' buf' ys' \<phi>f taking: m j rule: letpast_meval_induct)
  apply(subst(asm)(2) letpast_meval_code)
  apply(fastforce simp add: Let_def split:prod.splits list.splits if_splits)
  done

lemma (in maux) wf_mformula_wf_set: "wf_mformula \<sigma> j P V n R \<phi> \<phi>' \<Longrightarrow> wf_set n (Formula.fv \<phi>')"
  unfolding wf_set_def
proof (induction rule: wf_mformula.induct)
  case (AndRel P V n R \<phi> \<phi>' \<psi>' conf)
  then show ?case by (auto simp: fv_formula_of_constraint dest!: subsetD)
next
  case (And_Release I \<phi>' \<psi>' P V n R aux \<alpha>')
  then show ?case using release_fvi(3) by auto
next
  case (Ands P V n R l l_pos l_neg l' buf A_pos A_neg)
  from Ands.IH have "\<forall>\<phi>'\<in>set (l_pos @ map remove_neg l_neg). \<forall>x\<in>fv \<phi>'. x < n"
    unfolding list_all2_iff
    by (metis (no_types, lifting) case_prodD in_set_impl_in_set_zip2)
  then have "\<forall>\<phi>'\<in>set (l_pos @ l_neg). \<forall>x\<in>fv \<phi>'. x < n"
    using fv_remove_neg
    by fastforce
  then show ?case using Ands by auto
next
  case (Agg P V tys n R \<phi> \<phi>' y f args \<omega>)
  then have "Formula.fvi_trm (length tys) f \<subseteq> Formula.fvi (length tys) \<phi>'"
    by (auto simp: fvi_trm_iff_fv_trm[where b="length (aggargs_tys args)"] 
        fvi_iff_fv[where b="length (aggargs_tys args)"])
  with Agg show ?case by (auto 0 3 simp: Un_absorb2 fvi_iff_fv[where b="length (aggargs_tys args)"])
next
  case (Release_0)
  then show ?case using release_fvi(1) by auto
next
  case (MatchP r P V n R \<phi>s mr mrs buf nts I aux)
  then obtain \<phi>s' where conv: "to_mregex r = (mr, \<phi>s')" by blast
  with MatchP have "\<forall>\<phi>'\<in>set \<phi>s'. \<forall>x\<in>fv \<phi>'. x < n"
    by (simp add: list_all2_conv_all_nth all_set_conv_all_nth[of \<phi>s'])
  with conv show ?case
    thm fv_regex_alt
    by (simp add: to_mregex_ok[THEN conjunct1] fv_regex_alt2[OF \<open>Regex.safe_regex _ _ _ _ r\<close>])
next
  case (MatchF r  P V n R \<phi>s mr mrs buf nts I aux)
  then obtain \<phi>s' where conv: "to_mregex r = (mr, \<phi>s')" by blast
  with MatchF have "\<forall>\<phi>'\<in>set \<phi>s'. \<forall>x\<in>fv \<phi>'. x < n"
    by (simp add: list_all2_conv_all_nth all_set_conv_all_nth[of \<phi>s'])
  with conv show ?case
    by (simp add: to_mregex_ok[THEN conjunct1] fv_regex_alt2[OF \<open>Regex.safe_regex _ _ _ _ r\<close>])
next
  case (Until P V n R \<phi> \<phi>' \<psi> \<psi>' args \<phi>'' I R' buf nts t aux)
  then have valid: "valid_aggargs n (Formula.fv \<psi>') (args_agg args)"
    by (auto simp: wf_until_aux_def)
  then show ?case
    using Until(3,6,11,16,17)
  proof (cases "args_agg args")
    case (Some aggargs)
    have "Formula.fvi_trm (length (aggargs_tys aggargs)) (aggargs_f aggargs) 
      \<subseteq> Formula.fvi (length (aggargs_tys aggargs)) (formula.Since \<phi>' I \<psi>')"
      using valid
      by (auto simp: fvi_trm_iff_fv_trm[where b="length (aggargs_tys aggargs)"] 
          fvi_iff_fv[where b="length (aggargs_tys aggargs)"] valid_aggargs_def safe_aggargs_def Some)
    then show ?thesis
      using Until(3,6,11,16,17) valid
      by (auto 0 3 simp: Un_absorb2 fvi_iff_fv[where b="length (aggargs_tys aggargs)"] 
          packagg_def agg_n_def Some valid_aggargs_def safe_aggargs_def split: if_splits)
  next
    case (None)
    then show ?thesis using Until(3,6,7,11,16,17) Until.IH(2) valid by(auto simp:packagg_def agg_n_def split:if_splits) 
  qed 
next
  case (Since P V n R \<phi> \<phi>' \<psi> \<psi>' args \<phi>'' I R' buf aux)
  then have valid: "valid_aggargs n (Formula.fv \<psi>') (args_agg args)"
    by (auto simp: wf_since_aux_def)
  then show ?case
    using Since(3,6,11,13,14)
  proof (cases "args_agg args")
    case (Some aggargs)
    have "Formula.fvi_trm (length (aggargs_tys aggargs)) (aggargs_f aggargs) \<subseteq> Formula.fvi (length (aggargs_tys aggargs)) (formula.Since \<phi>' I \<psi>')"
      using valid
      by (auto simp: fvi_trm_iff_fv_trm[where b="length (aggargs_tys aggargs)"] fvi_iff_fv[where b="length (aggargs_tys aggargs)"] valid_aggargs_def safe_aggargs_def Some)
    then show ?thesis
      using Since(3,6,11,13,14) valid
      by (auto 0 3 simp: Un_absorb2 fvi_iff_fv[where b="length (aggargs_tys aggargs)"] 
          packagg_def agg_n_def Some valid_aggargs_def safe_aggargs_def split: if_splits)
  next
    case (None)
    then show ?thesis using Since(3,6,7,11,13,14) Since.IH(2) valid by(auto simp:packagg_def agg_n_def split:if_splits) 
  qed 
qed (auto simp: fvi_Suc split: if_splits)

lemma (in maux) wf_mformula_release: "wf_mformula \<sigma> j P V n R \<phi> (release_safe_0 \<phi>' I \<psi>') 
  \<Longrightarrow> (case \<phi> of (MOr \<alpha> \<beta> buf) \<Rightarrow> True | _ \<Rightarrow> False)"
  by (cases rule: wf_mformula.cases) 
    (auto simp add: release_safe_0_def packagg_def split: if_splits option.splits)


subsection \<open> Correct initialisation \<close>

lemma (in maux) wf_minit0_op:
  assumes "safe_formula \<psi>" "fv \<phi> \<subseteq> fv \<psi>"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>" "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>) \<psi>"
    "valid_aggargs n (fv \<psi>) (args_agg args)"
    "pred_mapping (\<lambda>x. x = 0) P"
    "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
    "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) (safe_formula \<phi>') agg"
    "safe_formula \<phi>' \<Longrightarrow> \<phi>' = \<phi>"
    "\<not>safe_formula \<phi>' \<Longrightarrow> \<phi>' = Formula.Neg \<phi> \<and> safe_formula \<phi>"
    "(op = formula.Since \<and> init = init_since) \<or> (op = formula.Until \<and> init = init_until)"
  shows "wf_mformula \<sigma> 0 P V (agg_n args) R' (init minit0 n agg \<phi>' I \<psi>) (packagg args (op \<phi>' I \<psi>))"
proof -
  have args_props: "args_n args = n" "args_pos args = safe_formula \<phi>'" "args_ivl args = I"
    "args_L args = fv \<phi>" "args_R args = fv \<psi>" "args_agg args = agg"
    by (auto simp: assms(8) init_args_def agg_n_def agg_tys_def packagg_def split: option.splits)
  have args_fold: "safe_formula \<phi>' \<Longrightarrow> init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True agg = args"
    "\<not>safe_formula \<phi>' \<Longrightarrow> init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) False agg = args"
    using assms(8)
    by auto
  show ?thesis
    using assms(11)
  proof (rule disjE)
    assume "op = formula.Since \<and> init = init_since"
    then have unf: "op = formula.Since" "init = init_since" by auto
    show ?thesis 
    proof(cases "safe_formula \<phi>'")
      case True
      note \<phi>_eq = assms(9)[OF True]
      have wf_since: "wf_since_aux \<sigma> V R args \<phi> \<psi> (init_msaux args) (min (Progress.progress \<sigma> P \<phi> 0) (Progress.progress \<sigma> P \<psi> 0)) (Progress.progress \<sigma> P (formula.Since \<phi>' I \<psi>) 0)"
        using wf_since_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by force
      show ?thesis unfolding unf init_since_def Let_def args_fold(1)[OF True, folded \<phi>_eq] 
        using wf_mformula.Since[OF assms(3, 4) _ True[unfolded \<phi>_eq] assms(1) args_props(3,1,4,5) assms(7,2) _ wf_since]
        using True args_props(2) assms(9) assms(6) by auto
    next
      case False
      have \<phi>_eq: "\<phi>' = Formula.Neg \<phi>" "safe_formula \<phi>" "fv \<phi>' = fv \<phi>"
        using assms(10)[OF False] by auto
      have wf_since: "wf_since_aux \<sigma> V R args \<phi> \<psi> (init_msaux args) (min (Progress.progress \<sigma> P \<phi> 0) (Progress.progress \<sigma> P \<psi> 0)) (Progress.progress \<sigma> P (formula.Since \<phi>' I \<psi>) 0)"
        using wf_since_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by force
      show ?thesis unfolding unf init_since_def Let_def args_fold(2)[OF False, folded \<phi>_eq(3)] using \<phi>_eq(1-2) False
        wf_mformula.Since[OF assms(3, 4) _ \<phi>_eq(2) assms(1) args_props(3,1,4,5) assms(7,2) _ wf_since]
        by (simp add: args_props(2) assms(6))
    qed
next
    assume "op = formula.Until \<and> init = init_until"
    then have unf: "op = formula.Until" "init = init_until" by auto
    show ?thesis 
    proof(cases "safe_formula \<phi>'")
      case True
      note \<phi>_eq = assms(9)[OF True]
      have wf_until: "wf_until_aux \<sigma> V R args \<phi> \<psi> (init_muaux args) (Progress.progress \<sigma> P (formula.Until \<phi>' I \<psi>) 0)"
        using wf_until_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by (metis progress_0_gen)
      show ?thesis unfolding unf init_until_def Let_def args_fold(1)[OF True, folded \<phi>_eq] 
        using wf_mformula.Until[OF assms(3, 4) _ True[unfolded \<phi>_eq] assms(1) args_props(3,1,4,5) assms(7,2) wf_mbuf2'_0[OF assms(6)] wf_ts_0 _ wf_until]
        unfolding valid_length_muaux[OF valid_init_muaux[OF assms(2)], of n agg I "safe_formula \<phi>'", folded assms(8), OF assms(5)[unfolded args_props(6)]] args_props(2)
        using True \<phi>_eq by (simp add: Inf_UNIV_nat assms(6))
    next
      case False
      have \<phi>_eq: "\<phi>' = Formula.Neg \<phi>" "safe_formula \<phi>" "fv \<phi>' = fv \<phi>"
        using assms(10)[OF False] by auto
      have wf_until: "wf_until_aux \<sigma> V R args \<phi> \<psi> (init_muaux args) (Progress.progress \<sigma> P (formula.Until \<phi>' I \<psi>) 0)"
        using wf_until_aux_Nil[OF assms(2)[unfolded \<phi>_eq] assms(5), unfolded args_props(6), of _ _ _ I "safe_formula \<phi>'", folded assms(8), of \<sigma> V R]
        assms(6) by (metis progress_0_gen)
      show ?thesis unfolding unf init_until_def Let_def args_fold(2)[OF False, folded \<phi>_eq(3)] 
        using wf_mformula.Until[OF assms(3, 4) _ \<phi>_eq(2) assms(1) args_props(3,1,4,5) assms(7,2) wf_mbuf2'_0[OF assms(6)] wf_ts_0 _ wf_until]
        unfolding valid_length_muaux[OF valid_init_muaux[OF assms(2)], of n agg I "safe_formula \<phi>'", folded assms(8), OF assms(5)[unfolded args_props(6)]] args_props(2)
        using False \<phi>_eq by (simp add: Inf_UNIV_nat assms(6))
    qed
  qed
qed

lemma (in maux) wf_minit0: "safe_formula \<phi> \<Longrightarrow> \<forall>x\<in>Formula.fv \<phi>. x < n \<Longrightarrow>
  pred_mapping (\<lambda>x. x = 0) P \<Longrightarrow>
  wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
proof (induction arbitrary: n R P V rule: safe_formula_induct)
  case (Eq_Const c d)
  then have wf_props:
    "is_simple_eq (trm.Const c) (trm.Const d)"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    "\<forall>x\<in>fv_trm (trm.Const d). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Eq_Var1 c x)
  then have wf_props:
    "is_simple_eq (trm.Const c) (trm.Var x)"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    "\<forall>x\<in>fv_trm (trm.Var x). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Eq_Var2 c x)
  then have wf_props:
    "is_simple_eq (trm.Var x) (trm.Const c)"
    "\<forall>x\<in>fv_trm (trm.Var x). x < n"
    "\<forall>x\<in>fv_trm (trm.Const c). x < n"
    by (auto simp add: is_simple_eq_def simp del: eq_rel.simps)
  show ?case
    using wf_mformula.Eq[OF wf_props]
    by auto
next
  case (Pred e ts)
  then show ?case by (auto intro!: wf_mformula.Pred)
next
  case (Let p \<phi> \<psi>)
  with fvi_less_nfv show ?case
    by (auto simp: pred_mapping_alt dom_def intro!: wf_mformula.Let Let(4,5))
next
  case (LetPast p \<phi> \<psi>)
  then show ?case
    by (auto simp: pred_mapping_alt dom_def letpast_progress0 fvi_less_nfv 
        intro!: wf_mformula.LetPast)
next
  case (And_assign \<phi> \<psi>)
  then have 1: "\<forall>x\<in>fv \<psi>. x < n" by simp
  from 1 \<open>safe_assignment (fv \<phi>) \<psi>\<close>
  obtain x t where
    "x < n" "x \<notin> fv \<phi>" "fv_trm t \<subseteq> fv \<phi>"
    "\<psi> = Formula.Eq (Formula.Var x) t \<or> \<psi> = Formula.Eq t (Formula.Var x)"
    unfolding safe_assignment_def by (force split: formula.splits trm.splits)
  with And_assign show ?case
    by (auto intro!: wf_mformula.AndAssign split: trm.splits)
next
  case (And_safe \<phi> \<psi>)
  then show ?case by (auto intro!: wf_mformula.And wf_mbuf2'_0)
next
  case (And_constraint \<phi> \<psi>)
  from \<open>fv \<psi> \<subseteq> fv \<phi>\<close> \<open>is_constraint \<psi>\<close>
  obtain t1 p c t2 where
    "(t1, p, c, t2) = split_constraint \<psi>"
    "formula_of_constraint (split_constraint \<psi>) = \<psi>"
    "fv_trm t1 \<union> fv_trm t2 \<subseteq> fv \<phi>"
    by (induction rule: is_constraint.induct) auto
  with And_constraint show ?case
    by (auto 0 3 intro!: wf_mformula.AndRel)
next
  case (And_Not \<phi> \<psi>)
  then show ?case by (auto intro!: wf_mformula.And wf_mbuf2'_0)
next
  case (And_Trigger \<phi> \<phi>' I \<psi>')
  have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
    using And_Trigger(5,8,9)
    by auto
  define t where "t = formula.Trigger \<phi>' I \<psi>'"
  define f where "f = formula.And \<phi> t"
  define args where "args = init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>') True None"
  define aux where "aux = (init_mtaux args)"

 have t_not_safe_assign: "\<not> safe_assignment (fv \<phi>) t"
  unfolding safe_assignment_def
  by (cases t) (auto simp add: t_def)

  have t_not_constraint: "\<not>is_constraint t"
    by (auto simp add: t_def)

  have wf_\<phi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
    using And_Trigger(6,8,9)
    by auto
  have wf_\<psi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>') \<psi>'"
    using And_Trigger(7,8,9)
    by auto
  have if_pos: "if args_pos args then \<phi>' = \<phi>' else \<phi>' = formula.Neg \<phi>'"
    unfolding args_def init_args_def
    by auto
  have args: "safe_formula \<phi>' = args_pos args"
    "args_ivl args = I"
    "args_n args = n"
    "args_L args = fv \<phi>'"
    "args_R args = fv \<psi>'"
    "\<forall>x\<in>fv \<psi>'. x < n"
    "if mem I 0 then fv \<phi>' \<subseteq> fv \<psi>' else fv \<phi>' = fv \<psi>'"
    using And_Trigger(2,3,8)
    unfolding args_def init_args_def safe_dual_def
    by auto
  hence fv_union: "fv \<phi>' \<union> fv \<psi>' = fv \<psi>'"
    by (auto split: if_splits)

  have buf_ts:
    "wf_mbuf2' \<sigma> P V 0 n R \<phi>' \<psi>' ([], [])"
    "wf_ts \<sigma> P 0 \<phi>' \<psi>' []"
    unfolding wf_mbuf2'_def wf_mbuf2_def wf_ts_def
    by (auto simp add: And_Trigger(9))

  have aux: "wf_trigger_aux \<sigma> V R args \<phi>' \<psi>' aux (Progress.progress \<sigma> P (formula.Trigger \<phi>' I \<psi>') 0)"
    using And_Trigger(3) valid_init_mtaux[of I "fv \<phi>'" "fv \<psi>'" True n]
    unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
    by (auto simp add: Let_def And_Trigger(9) split: if_splits)

  have if_pos: "if args_pos args then \<phi>' = \<phi>' else \<phi>' = formula.Neg \<phi>'"
    unfolding args_def init_args_def
    by auto
  have wf_buf:
    "wf_mbuf2' \<sigma> P V 0 n R \<phi> t ([], [])"
    "wf_mbuft2' \<sigma> P V 0 n R \<phi> \<phi>' I \<psi>' ([], [])"
    "wf_mbuf2' \<sigma> P V 0 n R \<phi>' \<psi>' ([],[])"
    "wf_ts \<sigma> P 0  \<phi>' \<psi>' []"
    unfolding wf_mbuf2'_def wf_mbuft2'_def wf_mbuf2_def wf_mbuf2_def wf_ts_def
    by (auto simp add: And_Trigger(9))

  show ?case
  proof (cases "safe_formula t")
    case True
    then have mem: "mem I 0"
      unfolding t_def
      by (auto simp add: safe_dual_def split: if_splits)

    have wf_t: "wf_mformula \<sigma> 0 P V n R (minit0 n t) t"
      using And_Trigger(2) 
        wf_mformula.Trigger_0[OF wf_\<psi>' if_pos wf_\<phi>' args(1-6) mem args(7) buf_ts aux]
      unfolding t_def aux_def args_def
      by (auto simp: init_trigger_def split: if_splits)
    show ?thesis 
      using wf_mformula.And[OF wf_\<phi> wf_t _ wf_buf(1) And_Trigger(1) True]
      using True And_Trigger(2) t_not_safe_assign t_not_constraint fv_union
      unfolding f_def t_def args_def aux_def
      by (auto simp: init_trigger_def split: if_splits)
  next
    case False
    then show ?thesis 
      using wf_mformula.And_Trigger[OF wf_\<phi> wf_buf(2)[unfolded t_def] And_Trigger(4) 
          wf_\<psi>' if_pos wf_\<phi>' args wf_buf(3-4) aux]
      using And_Trigger(2) t_not_safe_assign t_not_constraint
      unfolding f_def t_def args_def aux_def
      by (auto simp: init_trigger_def init_and_trigger_def split: if_splits)
  qed
next
  case (And_Release \<phi> \<phi>' I \<psi>')
  note fvs = release_fvi(3)[of 0 \<phi> \<phi>' I \<psi>']
  have safe_release_bdd: "safe_formula (release_safe_bounded \<phi>' I \<psi>')"
    using And_Release(1-7) 
    by (auto simp: safe_release_bdd_iff)
  have "fv \<psi>' \<subseteq> fv \<phi>"
    using And_Release(7) by auto
  have fv_eq: "fv (formula.And \<phi> (formula.Release \<phi>' I \<psi>')) = fv \<phi>"
    using And_Release(7)
    by auto
  then have release_subformulas:
    "\<forall>x\<in>fv \<phi>'. x < n"
    "\<forall>x\<in>fv \<psi>'. x < n"
    using And_Release(7) And_Release.prems(1)
    unfolding fvi.simps
    by auto
  have wf_formula:
    "wf_mformula \<sigma> 0 P V n R (minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>')) 
      (and_release_safe_bounded \<phi> \<phi>' I \<psi>')"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
    "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>') \<psi>'"
    using And_Release.IH(1)[OF And_Release.prems(1)[unfolded fvs]]
          And_Release.IH(2)[OF And_Release.prems(1)[unfolded fv_eq]]
          And_Release.IH(3)[OF release_subformulas(1)]
          And_Release.IH(4)[OF release_subformulas(2)]
      And_Release.prems(2)
    by auto
  then obtain L\<^sub>M R\<^sub>M buf 
    where obs: "wf_mbuf2' \<sigma> P V 0 n R (formula.And \<phi> (formula.Neg (Formula.eventually I Formula.TT))) (formula.And \<phi> (release_safe_bounded \<phi>' I \<psi>')) buf"
      "wf_mformula \<sigma> 0 P V n R (MOr L\<^sub>M R\<^sub>M buf) (and_release_safe_bounded \<phi> \<phi>' I \<psi>')" 
      "minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>') = MOr L\<^sub>M R\<^sub>M buf"
    using safe_release_bdd And_Release(1-7) 
    apply (atomize_elim)
    apply (rule_tac x="([],[])" in exI)
    apply (rule_tac x="(MAnd (fv \<phi>) (minit0 n \<phi>) True {} (MNeg (minit0 n (Formula.eventually I Formula.TT))) ([], []))" in exI)
    apply (rule_tac x="(MAnd (fv \<phi>) (minit0 n \<phi>) True (fv \<phi>' \<union> fv \<psi>') (minit0 n (release_safe_bounded \<phi>' I \<psi>')) ([], []))" in exI)
    by (auto simp: wf_mbuf2'_def wf_mbuf2_def eventually_def release_safe_bounded_def 
        always_safe_bounded_def safe_assignment_iff and_release_safe_bounded_def)
  have "\<not> safe_assignment (fv \<phi>) (formula.Release \<phi>' I \<psi>')"
    unfolding safe_assignment_def
    by auto
  moreover have "\<not> safe_formula (formula.Release \<phi>' I \<psi>')"
    using And_Release(6)
    by auto
  moreover have "\<not> is_constraint (formula.Release \<phi>' I \<psi>')"
    by auto
  ultimately have "minit0 n (formula.And \<phi> (formula.Release \<phi>' I \<psi>'))
    = minit0 n (and_release_safe_bounded \<phi> \<phi>' I \<psi>') "
    by auto
  then show ?case 
    using wf_mformula.And_Release[OF And_Release(6,5,4) \<open>fv \<psi>' \<subseteq> fv \<phi>\<close> 
        And_Release(1) safe_release_bdd obs(1,2)]
    by (clarsimp simp: obs)
next
  case (Ands l pos neg)
  note posneg = "Ands.hyps"(1)
  let ?wf_minit = "\<lambda>x. wf_mformula \<sigma> 0 P V n R (minit0 n x)"
  let ?pos = "filter safe_formula l"
  let ?neg = "filter (Not \<circ> safe_formula) l"
  have "list_all2 ?wf_minit ?pos pos"
    using Ands.IH(1) Ands.prems posneg by (auto simp: list_all_iff intro!: list.rel_refl_strong)
  moreover have "list_all2 ?wf_minit (map remove_neg ?neg) (map remove_neg neg)"
    using Ands.IH(2) Ands.prems posneg by (auto simp: list.rel_map list_all_iff intro!: list.rel_refl_strong)
  moreover have "list_all3 (\<lambda>_ _ _. True) (?pos @ map remove_neg ?neg) (?pos @ map remove_neg ?neg) l"
    by (auto simp: list_all3_conv_all_nth comp_def sum_length_filter_compl)
  moreover have "l \<noteq> [] \<Longrightarrow> (MIN \<phi>\<in>set l. (0 :: nat)) = 0"
    by (cases l) (auto simp: Min_eq_iff)
  ultimately show ?case using Ands.hyps Ands.prems(2)
    by (auto simp: wf_mbufn_def list_all3_map list.rel_map map_replicate_const[symmetric] subset_eq
        map_map[symmetric] map_append[symmetric] simp del: map_map map_append
        intro!: wf_mformula.Ands list_all2_appendI)
next
  case (Neg \<phi>)
  then show ?case 
    by (auto intro!: wf_mformula.Neg)
next
  case (Or \<phi> \<psi>)
  then show ?case 
    by (auto intro!: wf_mformula.Or wf_mbuf2'_0)
next
  case (Exists \<phi>)
  then show ?case 
    by (auto simp: fvi_Suc_bound intro!: wf_mformula.Exists[unfolded fvi.simps])
next
  case (Agg y \<omega> tys f \<phi>)
  define default where "default = MAgg (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f) (minit0 (length tys + n) \<phi>)"
  have fv_le: "\<forall>x\<in>fv \<phi>. x < length tys + n"
    using Agg
    by (auto intro!: fvi_plus_bound)
  have wf_default: "wf_mformula \<sigma> 0 P V n R default (formula.Agg y \<omega> tys f \<phi>)"
    using Agg
    by (auto simp: default_def init_aggargs_def intro!: wf_mformula.Agg Agg.IH fvi_plus_bound)
  {
    fix y0 \<phi>' I \<psi>' 
      and op :: "ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula \<Rightarrow> ty Formula.formula"
      and init :: "(nat \<Rightarrow> ty Formula.formula \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula) 
        \<Rightarrow> nat \<Rightarrow> aggargs option \<Rightarrow> ty Formula.formula \<Rightarrow> \<I> \<Rightarrow> ty Formula.formula 
        \<Rightarrow> ('msaux, 'muaux, 'mtaux) mformula"
    assume op_def: "(op = formula.Since \<and> init = init_since) 
      \<or> (op = formula.Until \<and> init = init_until)"
    assume agg_def: "\<phi> = op \<phi>' I \<psi>'"
    define \<phi>'' where "\<phi>'' = (if safe_formula \<phi>' then \<phi>' else remove_neg \<phi>')"
    define aggargs where "aggargs = Some (init_aggargs (fv \<phi>) n (fv \<phi> \<subseteq> {0..<length tys}) y \<omega> tys f)"
    define args where "args = init_args I (length tys + n) (fv \<phi>') (fv \<psi>') (safe_formula \<phi>') aggargs"
    have "wf_mformula \<sigma> 0 P V (agg_n args) R (init minit0 (length tys + n) aggargs \<phi>' I \<psi>') (packagg args (op \<phi>' I \<psi>'))"
    proof (rule wf_minit0_op[where op=op])
      have Neg_case: "\<not> safe_formula \<phi>' 
        \<Longrightarrow> \<phi>' = formula.Neg (remove_neg \<phi>') \<and> safe_formula (remove_neg \<phi>') 
          \<and> size' (remove_neg \<phi>') \<le> size' \<phi>"
        using Agg.hyps op_def
        by (auto simp: agg_def split: formula.splits)
      show safe_\<psi>': "safe_formula \<psi>'"
        using Agg.hyps op_def by (auto simp: agg_def)
      show "fv \<phi>'' \<subseteq> fv \<psi>'"
        using Agg.hyps op_def by (auto simp: agg_def \<phi>''_def)
      show "wf_mformula \<sigma> 0 P V (length tys + n) (lift_envs' (length tys) R) (minit0 (length tys + n) \<phi>'') \<phi>''"
      proof (cases "safe_formula \<phi>'")
        case True
        then show ?thesis
          using Agg.prems op_def fv_le
          by (auto simp: agg_def \<phi>''_def intro!: Agg.IH)
      next
        case False
        then show ?thesis
          using Agg.prems op_def fv_le Neg_case
          by (auto simp: agg_def \<phi>''_def intro!: Agg.IH)
      qed
      show "wf_mformula \<sigma> 0 P V (length tys + n) (lift_envs' (length tys) R) (minit0 (length tys + n) \<psi>') \<psi>'"
        using Agg.prems op_def fv_le safe_\<psi>'
        by (auto simp: agg_def intro!: Agg.IH)
      show "valid_aggargs (length tys + n) (fv \<psi>') (args_agg args)"
        using Agg op_def fv_le
        by (auto simp: valid_aggargs_def args_def init_args_def aggargs_def init_aggargs_def
            safe_aggargs_def agg_def)
      show "mem_restr (lift_envs' (length tys) R) = mem_restr (lift_envs' (length (agg_tys args)) R)"
        by (simp add: args_def init_args_def agg_tys_def aggargs_def init_aggargs_def)
      show "args = init_args I (length tys + n) (fv \<phi>'') (fv \<psi>') (safe_formula \<phi>') aggargs"
        by (simp add: args_def \<phi>''_def)
      show "\<not> safe_formula \<phi>' \<Longrightarrow> \<phi>' = formula.Neg \<phi>'' \<and> safe_formula \<phi>''"
        using Neg_case by (auto simp: \<phi>''_def)
    qed (simp_all add: Agg.prems \<phi>''_def op_def)
    then have "wf_mformula \<sigma> 0 P V n R (init minit0 (length tys + n) aggargs \<phi>' I \<psi>') (formula.Agg y \<omega> tys f (op \<phi>' I \<psi>'))"
      by (simp add: args_def init_args_def aggargs_def init_aggargs_def agg_n_def packagg_def)
  }
  then show ?case
    using wf_default
    by (fastforce simp: default_def[symmetric] split: formula.splits prod.splits agg_type.splits)
next
  case (Prev I \<phi>)
  then show ?case 
    by (auto intro!: wf_mformula.Prev)
next
  case (Next I \<phi>)
  then show ?case 
    by (auto intro!: wf_mformula.Next)
next
  case (Since \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'=\<phi> and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Not_Since \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'="Formula.Neg \<phi>" and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Until \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'=\<phi> and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Not_Until \<phi> I \<psi>)
  then show ?case
    using wf_minit0_op[where \<phi>=\<phi> and \<phi>'="Formula.Neg \<phi>" and ?agg=None]
    by (auto simp: init_args_def agg_n_def agg_tys_def packagg_def valid_aggargs_def)
next
  case (Trigger_0 \<phi> I \<psi>)
  have wf_\<psi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<psi>) \<psi>"
    using Trigger_0
    by auto
  show ?case
  proof (cases "safe_formula \<phi> \<and> (\<forall>x. (\<forall>xa\<in>fv \<phi>. xa < x) \<longrightarrow> (\<forall>xa xaa. pred_mapping (\<lambda>x. x = 0) xaa \<longrightarrow> (\<forall>xaaa. wf_mformula \<sigma> 0 xaa xaaa x xa (minit0 x \<phi>) \<phi>)))")
    define args where "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None"
    define aux where "aux = init_mtaux args"
    case True
    then have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
      using Trigger_0
      by auto
    have if_pos: "if args_pos args then \<phi> = \<phi> else \<phi> = formula.Neg \<phi>"
      unfolding args_def init_args_def
      by auto
    have args:
      "safe_formula \<phi> = args_pos args"
      "args_ivl args = I"
      "args_n args = n"
      "args_L args = fv \<phi>"
      "args_R args = fv \<psi>"
      "\<forall>x\<in>fv \<psi>. x < n"
      "if mem I 0 then fv \<phi> \<subseteq> fv \<psi> else fv \<phi> = fv \<psi>"
      and mem: "mem I 0"
      using Trigger_0(1,3,6) True
      unfolding args_def init_args_def
      by auto
    have aux: "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux (Progress.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
      using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>" "fv \<psi>" True n]
      unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
      by (auto simp add: Let_def Trigger_0(7) split: if_splits)

    show ?thesis
      using True wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi> args(1-6) mem args(7) 
          wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux ]
      unfolding aux_def args_def
      by (auto simp: init_trigger_def)
  next
    define args where "args = init_args I n (Formula.fv \<phi>) (Formula.fv \<psi>) True None"
    define aux where "aux = init_mtaux args"
    case False
    then obtain \<phi>' where \<phi>'_props: "\<phi> = Formula.Neg \<phi>'" "safe_formula \<phi>'"
      "(\<forall>x. (\<forall>xa\<in>fv \<phi>'. xa < x) 
        \<longrightarrow> (\<forall>xa xaa. pred_mapping (\<lambda>x. x = 0) xaa 
          \<longrightarrow> (\<forall>xaaa. wf_mformula \<sigma> 0 xaa xaaa x xa (minit0 x \<phi>') \<phi>')))"
      using Trigger_0(4)
      by (cases \<phi>) (auto)
    show ?thesis
    proof (cases "safe_formula \<phi>")
      case True
      then have "fv \<phi>' = {}"
        using \<phi>'_props(1,2)
        by auto
      moreover have "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
        using Trigger_0(6,7) \<phi>'_props(1,3)
        by auto
      ultimately have wf_\<phi>: "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>) \<phi>"
        using \<phi>'_props(1) True
        by (auto intro!: wf_mformula.Neg)
      have if_pos: "if args_pos args then \<phi> = \<phi> else \<phi> = formula.Neg \<phi>"
        unfolding args_def init_args_def
        by auto
      have args:
        "safe_formula \<phi> = args_pos args"
        "args_ivl args = I"
        "args_n args = n"
        "args_L args = fv \<phi>"
        "args_R args = fv \<psi>"
        "\<forall>x\<in>fv \<psi>. x < n"
        "if mem I 0 then fv \<phi> \<subseteq> fv \<psi> else fv \<phi> = fv \<psi>"
        and mem: "mem I 0"
        using Trigger_0(1,3,6) True
        unfolding args_def init_args_def
        by auto
      have aux: "wf_trigger_aux \<sigma> V R args \<phi> \<psi> aux (Progress.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
        using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>" "fv \<psi>" True n]
        unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
        by (auto simp add: Let_def Trigger_0(7) split: if_splits)
  
      show ?thesis
        using True wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi> args(1-6) mem args(7) 
            wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux]
        unfolding aux_def args_def
        by (auto simp: init_trigger_def)
    next
      define args where "args = init_args I n (Formula.fv \<phi>') (Formula.fv \<psi>) False None"
      define aux where "aux = init_mtaux args"
      case False
      have wf_\<phi>': "wf_mformula \<sigma> 0 P V n R (minit0 n \<phi>') \<phi>'"
        using \<phi>'_props Trigger_0
        by auto
      have if_pos: "if args_pos args then \<phi> = \<phi>' else \<phi> = formula.Neg \<phi>'"
        unfolding \<phi>'_props(1) args_def init_args_def
        by auto
      have args:
        "safe_formula \<phi> = args_pos args"
        "args_ivl args = I"
        "args_n args = n"
        "args_L args = fv \<phi>'"
        "args_R args = fv \<psi>"
        "\<forall>x\<in>fv \<psi>. x < n"
        "if mem I 0 then fv \<phi>' \<subseteq> fv \<psi> else fv \<phi>' = fv \<psi>"
        and mem: "mem I 0"
        using \<phi>'_props(1) Trigger_0(1,3,6) False
        unfolding args_def init_args_def
        by auto
      have aux: "wf_trigger_aux \<sigma> V R args \<phi>' \<psi> aux (Progress.progress \<sigma> P (formula.Trigger \<phi> I \<psi>) 0)"
        using Trigger_0(1,3) valid_init_mtaux[of I "fv \<phi>'" "fv \<psi>" False n] \<phi>'_props(1)
        unfolding safe_dual_def wf_trigger_aux_def aux_def args_def
        by (auto simp add: Let_def Trigger_0(7) split: if_splits)
  
      show ?thesis
        using False \<phi>'_props(1) wf_mformula.Trigger_0[OF wf_\<psi> if_pos wf_\<phi>' args(1-6) mem args(7) 
            wf_mbuf2'_0[OF Trigger_0(7)] wf_ts_0 aux]
        unfolding aux_def args_def
        by (auto simp: init_trigger_def)
    qed
  qed
next
  case (Trigger \<phi> I \<psi>)
  then show ?case by auto
next
  case (Release_0 \<phi> I \<psi>)
  hence "safe_formula \<psi>"
    by auto
  moreover have "wf_mformula \<sigma> 0 P V n R (minit0 n (release_safe_0 \<phi> I \<psi>)) (release_safe_0 \<phi> I \<psi>)"
    using Release_0.IH[OF Release_0.prems[unfolded release_fvi(1)]]
    by auto
  moreover with this have "safe_formula (release_safe_0 \<phi> I \<psi>)"
    unfolding release_safe_0_def
    by (cases rule: wf_mformula.cases)
      (auto simp: packagg_def split: option.splits)
  moreover have "wf_mbuf2' \<sigma> P V 0 n R (formula.Until \<psi> I (formula.And \<psi> \<phi>)) (always_safe_0 I \<psi>) ([],[])"
    by (auto simp: wf_mbuf2'_def wf_mbuf2_def)
  ultimately show ?case
    using minit0_release_0[OF Release_0(1)] wf_mformula.Release_0[OF Release_0(1-2,4)]
    by (auto simp: release_safe_0_def)
next
  case (Release \<phi> I \<psi>)
  then show ?case 
    by auto
next
  case (MatchP I r)
  then show ?case
    by (auto simp: list.rel_map fv_regex_alt2 simp del: progress_simps split: prod.split
        intro!: wf_mformula.MatchP list.rel_refl_strong wf_mbufn'_0 wf_ts_regex_0 wf_matchP_aux_Nil
        dest!: to_mregex_safe_atms)
next
  case (MatchF I r)
  then show ?case
    by (auto simp: list.rel_map fv_regex_alt2 progress_le Min_eq_iff progress_regex_def
        simp del: progress_simps split: prod.split
        intro!: wf_mformula.MatchF list.rel_refl_strong wf_mbufn'_0 wf_ts_regex_0 wf_matchF_aux_Nil
        dest!: to_mregex_safe_atms)
next
  case (TP t)
  then show ?case 
    by (auto intro!: wf_mformula.MTP)
next
  case (TS t)
  then show ?case 
    by (auto intro!: wf_mformula.MTS)
qed

lemma (in maux) wf_mstate_minit: 
  "safe_formula \<phi> \<Longrightarrow> S, E \<turnstile> \<phi> \<Longrightarrow> wf_mstate S E \<phi> pnil R (minit \<phi>)"
  unfolding wf_mstate_def minit_def Let_def
  by (auto simp add: pts.rep_eq pnil.rep_eq intro!: wf_minit0 fvi_less_nfv wty_pnil)


subsection \<open> Main correctness result \<close>

lemma (in maux) letpast_meval_invar_post:
  assumes "safe_letpast (p, m) \<phi>' \<le> PastRec"
  assumes "pred_mapping (\<lambda> x. x\<le>(j-length ts)) P"
  assumes "pred_mapping (\<lambda> x. x\<le>j) P'"
  assumes "rel_mapping (\<le>) P P'"
  assumes "m = Formula.nfv \<phi>'" and "{0..<m} \<subseteq> fv \<phi>'"
  assumes "wf_mformula \<sigma> (j-length ts) (P((p,m)\<mapsto>i)) (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))) m UNIV \<phi> \<phi>'"
  assumes "wf_envs S \<sigma> (j-length ts) (length ts) P P' V db"
  assumes "\<And> xs db \<phi>_m us P P' V S E. size \<phi>_m = size \<phi> \<Longrightarrow> wf_mformula \<sigma> (j-length us) P V m UNIV \<phi>_m \<phi>' \<Longrightarrow>
    wf_envs S \<sigma> (j-length us) (length us) P P' V (Mapping.update (p, m) xs db) \<Longrightarrow>
    S, E \<turnstile> \<phi>' \<Longrightarrow>
    us=[]\<or>us = ts \<Longrightarrow>
    case meval j m us (Mapping.update (p, m) xs db) \<phi>_m of (xs', \<phi>\<^sub>n) \<Rightarrow>
    wf_mformula \<sigma> j P' V m UNIV \<phi>\<^sub>n \<phi>' \<and>
    list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
    [progress \<sigma> P \<phi>' (j-length us)..<progress \<sigma> P' \<phi>' j] xs'"
  assumes "length ts \<le> j"
  assumes "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<phi>'"
  assumes "safe_formula \<phi>'"
  shows "letpast_meval_invar n V \<sigma> P \<phi>' m j i ys xs p ts db \<phi> k\<Longrightarrow>
  (ys', i', buf', \<phi>f) = letpast_meval m j i ys xs (p, m) ts db \<phi> \<Longrightarrow>
  letpast_meval_post n V \<sigma> P' \<phi>' m j i' ys' buf' p \<phi>f k"
  using assms
proof (induction i ys xs "(p, m)" ts db \<phi> arbitrary: p i' buf' ys' \<phi>f P P' taking: m j rule: letpast_meval_induct)
  case (step i ys xs ts db \<phi>)
  note invar = step.prems(1)
  note eq = step.prems(2)
  note safe = step.prems(3)
  note PP' = step.prems(4-6)
  note fv = step.prems(7-8)
  note mformula = step.prems(9)
  note envs = step.prems(10)
  note meval = step.prems(11)
  note wty = step.prems(13)
  note safe_formula = step.prems(14)
  define ysp where "ysp = meval j m ts (Mapping.update (p, m) xs db) \<phi>"
  let ?P = "P((p, m) \<mapsto> i)"
  let ?V = "V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>'))"
  let ?S = "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>'))"
  have i'_j: "i + length xs \<le> j - length ts"
    using invar letpast_progress_le[OF PP'(1), of \<sigma>] 
    unfolding letpast_meval_invar_def Let_def
    apply (auto elim: order_trans)
    using le_trans by blast
  have "list_all2
     (\<lambda>i. qtable m (fv \<phi>') (mem_restr UNIV)
           (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) u k \<phi>') (map the v) i))
     [i..<Progress.progress \<sigma> (P((p, m) \<mapsto> i)) \<phi>' (j - length ts)] xs" (is "list_all2 ?Q _ _")
    using invar unfolding letpast_meval_invar_def Let_def by simp
  then have xs: "list_all2 ?Q [i..<i + length xs] xs"
    by (smt (verit, del_insts) add_diff_cancel_left' eq_diff_iff length_upt list_all2_lengthD nat_le_linear upt_conv_Nil)

  show ?case
  proof (cases "fst ysp = [] \<or> j \<le> Suc (i + length xs)")
    case stop: True
    then have eqs: "i' = i + length xs" "ys' = ys @ fst ysp" "\<phi>f = snd ysp"
      "buf' = (case fst ysp of [] \<Rightarrow> None | Z # _ \<Rightarrow> Some Z)"
      using eq by (simp_all add: letpast_meval_code split_beta flip: ysp_def split: list.splits)
    let ?P' = "P'((p, m) \<mapsto> i')"
    have "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> ?V (map the v) i \<phi>'))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
    proof (rule meval[of \<phi> ts ?P ?V ?S ?P' xs db, folded ysp_def])
      show "wf_mformula \<sigma> (j - length ts) ?P ?V m UNIV \<phi> \<phi>'" by fact
      show "wf_envs ?S \<sigma> (j - length ts) (length ts) ?P ?P' ?V (Mapping.update (p, m) xs db)"
        unfolding eqs by (intro wf_envs_update2) (fact | use i'_j in simp)+
      show " S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<phi>'" using wty by auto
    qed simp_all
    then have ysp: "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
      apply (rule iffD1[OF prod.case_cong[OF refl], rotated])
      apply (rule arg_cong[OF list.rel_cong, OF refl refl])
      apply (rule fun_cong[OF qtable_cong_strong, OF refl])
      apply (subst letpast_sat.simps)
      apply (rule V_subst_letpast[OF safe])
      by simp
    show ?thesis
      unfolding eqs
      apply (rule invar_recursion_post)
             apply fact+
          apply (rule ysp[unfolded ysp_def eqs])
         apply fact
        apply (simp add: ysp_def)
       apply simp
      using stop by (auto split: list.splits)
  next
    case cont: False
    then have eqs: "(ys', i', buf', \<phi>f) =
      letpast_meval m j (i + length xs) (ys @ fst ysp)
       (fst ysp) (p, m) []
       (Mapping.map_values (\<lambda>_ _. []) db) (snd ysp)"
      using eq
      by (subst (asm) letpast_meval_code) (simp_all add: split_beta flip: ysp_def split: list.splits)
    let ?P' = "P'((p, m) \<mapsto> i + length xs)"
    have "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> ?V (map the v) i \<phi>'))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
    proof (rule meval[of \<phi> ts ?P ?V ?S ?P' xs db, folded ysp_def])
      show "wf_mformula \<sigma> (j - length ts) ?P ?V m UNIV \<phi> \<phi>'" by fact
      show "wf_envs ?S \<sigma> (j - length ts) (length ts) ?P ?P' ?V (Mapping.update (p, m) xs db)"
        by (intro wf_envs_update2) (fact | use i'_j in simp)+
      show "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>')), E' \<turnstile> \<phi>'" using wty by auto
    qed simp_all
    then have ysp: "case ysp of (ys, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> j ?P' ?V m UNIV \<phi>\<^sub>n \<phi>' \<and>
      list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>') (map the v) i))
      [progress \<sigma> ?P \<phi>' (j-length ts)..<progress \<sigma> ?P' \<phi>' j] ys"
      apply (rule iffD1[OF prod.case_cong[OF refl], rotated])
      apply (rule arg_cong[OF list.rel_cong, OF refl refl])
      apply (rule fun_cong[OF qtable_cong_strong, OF refl])
      apply (subst letpast_sat.simps)
      apply (rule V_subst_letpast[OF safe])
      by simp
    show ?thesis
      apply (rule step.hyps[of "fst ysp" "snd ysp" P'])
                     apply (simp add: ysp_def)
      using cont apply simp
      using cont apply simp
      subgoal
        apply (rule invar_recursion_invar)
               apply fact+
            defer
            apply fact
           apply (simp add: ysp_def)
        using cont apply simp
        using cont apply simp
        apply (rule ysp[unfolded ysp_def])
        done
                apply fact+
              apply simp
              apply fact+
            apply (simp add: rel_mapping_reflp reflp_def)
           apply fact+
      using ysp apply (simp add: ysp_def split_beta)
        apply simp
        apply (metis diff_add envs step.prems(12) wf_envs_empty)
       apply (rule meval; simp add: ysp_def size_snd_meval)
      apply simp using wty safe_formula by auto
  qed
qed

lemma (in maux) wf_mformula_and_release_safe_bddE:
  "wf_mformula \<sigma> j P V n R \<phi>\<^sub>M (and_release_safe_bounded \<alpha>' \<phi>' I \<psi>') 
  \<Longrightarrow> \<exists>\<phi>\<^sub>M' \<psi>\<^sub>M' buf1 buf2. \<phi>\<^sub>M = MOr \<phi>\<^sub>M' \<psi>\<^sub>M' (buf1, buf2)"
  by (erule wf_mformula.cases; clarsimp simp: and_release_safe_bounded_def
      packagg_def split: option.splits if_splits)

lemma (in maux) wf_mformula_and_release_safe0E:
  "wf_mformula \<sigma> j P V n R \<phi>\<^sub>M (release_safe_0 \<phi>' I \<psi>') 
  \<Longrightarrow> \<exists>\<phi>\<^sub>M' \<psi>\<^sub>M' buf1 buf2. \<phi>\<^sub>M = MOr \<phi>\<^sub>M' \<psi>\<^sub>M' (buf1, buf2)"
  by (erule wf_mformula.cases; clarsimp simp: release_safe_0_def
      packagg_def split: option.splits if_splits)

unbundle MFODL_notation

lemma (in maux) meval_correct:
  assumes "wf_mformula \<sigma> j P V n R \<phi> \<phi>'" "wf_envs S \<sigma> j \<delta> P P' V db" "S, E \<turnstile> \<phi>'"
  shows "case meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> 
    of (xs, \<phi>\<^sub>n) \<Rightarrow> wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>' 
      \<and> list_all2 (\<lambda>i. qtable n (FV \<phi>') (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>'))
          [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] xs"
  using assms
proof (induction \<phi> arbitrary: db P P' V n R \<phi>' j \<delta> S E rule: mformula_induct)
  case (MRel rel) (* other repo-branches have ?case2 and ?case3 *)
  let ?case1 = "\<lambda>t1 t2. \<phi>' = t1 =\<^sub>F t2 \<and> rel = eq_rel n t1 t2
  \<and> is_simple_eq t1 t2 \<and> (\<forall>x\<in>FV\<^sub>t t1. x < n) \<and> (\<forall>x\<in>FV\<^sub>t t2. x < n)" 
  obtain t1 and t2 where cases: "?case1 t1 t2"
    using MRel(1) 
    by (cases rule: wf_mformula.cases)
      (auto simp: and_release_safe_bounded_def release_safe_0_def always_safe_0_def
        elim: wf_mformula.cases)
  moreover have "?case1 t1 t2 \<Longrightarrow> ?case"
    by (auto split: prod.splits intro!: qtable_eq_relI  wf_mformula.Eq)
  ultimately show "?case"
    using cases by (metis (no_types, lifting))
next
  case (MPred p ts mode)
  let ?p = "(p, length ts)"
  have inits: "\<phi>' = p \<dagger> ts" "\<forall>x\<in>FV (p \<dagger> ts). x < n" 
    "\<forall>t\<in>set ts. trm.is_Var t \<or> trm.is_Const t"
    using MPred(1) 
    by (cases rule: wf_mformula.cases, 
        auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)+
  have wfmf: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MPred p ts mode) (p \<dagger> ts)"
    "MPred p ts mode = MPred p ts (pred_mode_of n ts)"
    using MPred(1) by (cases rule: wf_mformula.cases, auto intro!: wf_mformula.Pred
        dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)+
  show ?case
  proof (cases "?p \<in> dom P") \<comment> \<open>notice @{term "dom P = dom V"}\<close>
    case True
    hence "?p \<in> Mapping.keys db" "?p \<in> dom P'" "?p \<in> dom V" and
      "list_all2 (\<lambda>i X. X = map Some ` {v. length v = length ts \<and> the (V ?p) v i}) 
        [the (P ?p)..<the (P' ?p)] (the (Mapping.lookup db ?p))" 
      using MPred(2) unfolding wf_envs_def 
      by (auto simp: dom_def rel_mapping_alt dest: bspec[where x="?p"])
    then obtain m m' Rs and pred 
      where wtnss: "P ?p = Some m" "P' ?p = Some m'" 
        "V ?p = Some pred" "Mapping.lookup db ?p = Some Rs" 
        and key: "list_all2 (\<lambda>i X. X = map Some ` {v. length v = length ts \<and> pred v i}) [m..<m'] Rs"
      using True by (auto simp: dom_def keys_dom_lookup)
    hence case1: "is_copy_pattern n ts 
      \<Longrightarrow> list_all2 (\<lambda>i. qtable n (FV \<phi>') (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>')) [m..<m'] Rs"
      using qtable_copy_pattern(1)
      by - (erule list.rel_mono_strong, clarsimp simp: inits)
    moreover have case2: "is_simple_pattern ts 0 
      \<Longrightarrow> list_all2 (\<lambda>i T. qtable n (FV \<phi>') (mem_restr R) 
        (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>') (simple_match n 0 ts ` T)) [m..<m'] Rs"
      using key wtnss inits qtable_simple_pattern 
      by - (erule list.rel_mono_strong, clarsimp)
    moreover have case3: "\<not> is_copy_pattern n ts \<Longrightarrow> \<not> is_simple_pattern ts 0 
      \<Longrightarrow> list_all2 (\<lambda>i T. qtable n (FV \<phi>') (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>')
             ((\<lambda>x. tabulate x 0 n) ` Option.these (match ts ` T)))
          [m..<m'] Rs"
      using key wtnss inits qtable_no_pattern(1)
      by - (erule list.rel_mono_strong, clarsimp)
    ultimately show ?thesis
      using wtnss wfmf inits 
      by (clarsimp simp: list.rel_map split: pred_mode.split)
  next
    let ?next_keys = "\<Union>k \<in> {j ..< j + \<delta>}. {(p, n). \<exists>x. (p, x) \<in> \<Gamma> \<sigma> k \<and> n = length x}"
    let "?option_sats_at k" = "map Some ` {v. (p, v) \<in> \<Gamma> \<sigma> k \<and> length v = length ts}"
    case False
    hence obs: "?p \<notin> dom P'" "?p \<notin> dom V" "?p \<in> ?next_keys \<longrightarrow> ?p \<in> Mapping.keys db"
      using MPred(2)
      unfolding wf_envs_def rel_mapping_alt 
      by (auto simp: subset_iff)
    have key: "?p \<in> Mapping.keys db \<Longrightarrow> Mapping.lookup db ?p 
      = Some (map ?option_sats_at [j ..< j + \<delta>])"
      using False MPred(2) 
      unfolding wf_envs_def keys_dom_lookup
      by (clarsimp, erule_tac x="?p" in ballE, auto)
    hence case1: "Mapping.lookup db ?p = None \<Longrightarrow> ?thesis"
      using wfmf inits obs False
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map wf_tuple_def 
          qtable_empty_iff[unfolded empty_table_def])
        (erule_tac x="j+i" in ballE; force)
    moreover have case2: "\<exists>x. Mapping.lookup db ?p = Some x \<Longrightarrow> is_copy_pattern n ts \<Longrightarrow> ?thesis"
      using wfmf inits False obs key qtable_copy_pattern(2) 
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map image_image 
          split: pred_mode.split intro!: list.rel_refl_strong)
    moreover have case3: "\<exists>x. Mapping.lookup db ?p = Some x \<Longrightarrow> \<not> is_copy_pattern n ts 
      \<Longrightarrow> is_simple_pattern ts 0 \<Longrightarrow> ?thesis"
      using wfmf inits False obs key qtable_simple_pattern(2)
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map image_image 
          split: pred_mode.split intro!: list.rel_refl_strong)
    moreover have case4: "\<exists>x. Mapping.lookup db ?p = Some x \<Longrightarrow> \<not> is_copy_pattern n ts 
      \<Longrightarrow> \<not> is_simple_pattern ts 0 \<Longrightarrow> ?thesis"
      using wfmf inits False obs key qtable_no_pattern(2)
      by (clarsimp simp: keys_dom_lookup dom_def list.rel_map image_image 
          split: pred_mode.split intro!: list.rel_refl_strong)
    ultimately show ?thesis
      by (meson not_None_eq)
  qed
next
  case (MLet p m \<phi>1 \<phi>2)
  let ?pn = "(p, m)"
  from MLet.prems(1) obtain \<phi>1' \<phi>2' where Let: "\<phi>' = Formula.Let p \<phi>1' \<phi>2'" and
    1: "wf_mformula \<sigma> j P V m UNIV \<phi>1 \<phi>1'" and
    fv: "m = Formula.nfv \<phi>1'" "{0..<m} \<subseteq> fv \<phi>1'" and
    2: "wf_mformula \<sigma> j (P(?pn \<mapsto> progress \<sigma> P \<phi>1' j))
      (V(?pn \<mapsto> \<lambda>w j. Formula.sat \<sigma> V w j \<phi>1'))
      n R \<phi>2 \<phi>2'" and
    safe1: "safe_formula \<phi>1'" and
    safe2: "safe_formula \<phi>2'" 
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MLet.prems(3) Let obtain E' where
    wty1: "S, E' \<turnstile> \<phi>1'" and
    wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1')), E \<turnstile> \<phi>2'"
    unfolding fv by (cases pred: wty_formula) simp_all
  obtain xs \<phi>1_new where e1: "meval (j + \<delta>) m (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1 = (xs, \<phi>1_new)" and
      wf1: "wf_mformula \<sigma> (j + \<delta>) P' V m UNIV \<phi>1_new \<phi>1'" and
      res1: "list_all2 (\<lambda>i. qtable m (fv \<phi>1') (mem_restr UNIV) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>1'))
       [progress \<sigma> P \<phi>1' j..<progress \<sigma> P' \<phi>1' (j + \<delta>)] xs"
    using MLet(1)[OF 1(1) MLet.prems(2) wty1] by (auto simp: eqTrueI[OF mem_restr_UNIV, abs_def])
  from MLet(2)[OF 2 wf_envs_update[OF MLet.prems(2) fv res1 safe1 wty1] wty2] wf1 e1 fv safe1 safe2
  show ?case unfolding Let
    by (auto simp: fun_upd_def intro!: wf_mformula.Let)
next
  case (MLetPast p m \<phi>1 \<phi>2 i buf)
  let ?pn = "(p, m)"
  from MLetPast.prems(1) obtain \<phi>1' \<phi>2' 
    where LetPast: "\<phi>' = Formula.LetPast p \<phi>1' \<phi>2'" 
      and 1: "wf_mformula \<sigma> j (P(?pn\<mapsto>i)) 
        (V(?pn \<mapsto> letpast_sat (\<lambda>X v i. \<langle>\<sigma>, V(?pn \<mapsto> X), v, i\<rangle> \<Turnstile> \<phi>1'))) m UNIV \<phi>1 \<phi>1'" 
      and buf: "case buf of
        None \<Rightarrow> i = letpast_progress \<sigma> P ?pn \<phi>1' j
      | Some Z \<Rightarrow> Suc i = letpast_progress \<sigma> P ?pn \<phi>1' j 
          \<and> qtable m (Formula.fv \<phi>1') (mem_restr UNIV) 
            (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>1') (map the v) i) Z" 
      and fv: "m = Formula.nfv \<phi>1'" "{0..<m} \<subseteq> fv \<phi>1'" 
      and 2:  "wf_mformula \<sigma> j (P(?pn \<mapsto> letpast_progress \<sigma> P ?pn \<phi>1' j))
      (V(?pn \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(?pn \<mapsto> X)) v i \<phi>1'))) n R \<phi>2 \<phi>2'" 
      and safe: "safe_letpast ?pn \<phi>1' \<le> PastRec" 
      and safe1: "safe_formula \<phi>1'" 
      and safe2: "safe_formula \<phi>2'"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MLetPast.prems(3) LetPast obtain E' 
    where wty1: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1')), E' \<turnstile> \<phi>1'" 
      and wty2: "S((p, m) \<mapsto> tabulate E' 0 (Formula.nfv \<phi>1')), E \<turnstile> \<phi>2'"
    unfolding fv by (cases pred: wty_formula) simp_all
  from MLetPast(4) have pred: "pred_mapping (\<lambda> x. x\<le>j) P"
    by auto
  from MLetPast(3) pred LetPast
  have invar:"letpast_meval_invar n V \<sigma> P \<phi>1' m (j+\<delta>) i [] (list_of_option buf) p (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1 (letpast_progress \<sigma> P ?pn \<phi>1' j)"
    by(auto intro!: letpast_meval_invar_init[where j="j+\<delta>" and ts="(map (\<tau> \<sigma>) [j ..< j + \<delta>])" and \<phi> = "\<phi>1" and \<phi>'= "\<phi>1'", simplified])

  obtain ys' i' buf' \<phi>f \<phi>f1 \<phi>f2 xs' where
    e1: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db (MLetPast p m \<phi>1 \<phi>2 i buf) = (xs', \<phi>f)" and
    e_letpast: "(ys', i', buf', \<phi>f1) = letpast_meval m (j+\<delta>) i [] (list_of_option buf) ?pn (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>1" and
    e2: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) (Mapping.update ?pn ys' db) \<phi>2 = (xs', \<phi>f2)" and
    \<phi>f: "\<phi>f = MLetPast p m \<phi>f1 \<phi>f2 i' buf'"
      apply(simp)
    apply(atomize_elim)
    apply (auto split: prod.splits)
    done
  have pred_alt: "pred_mapping (\<lambda>x. x \<le> j + \<delta> - length (map (\<tau> \<sigma>) [j..<j + \<delta>])) P" 
    using pred by fastforce
  have pred_alt_2: "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'" 
    using MLetPast.prems(2) wf_envs_P_simps(2) by blast
  have rel_map:  "rel_mapping (\<le>) P P'" 
    using MLetPast.prems(2) by auto
  have wf_form: "wf_mformula \<sigma> (j + \<delta> - length (map (\<tau> \<sigma>) [j..<j + \<delta>])) (P((p, m) \<mapsto> i))
 (V((p, m) \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V((p, m) \<mapsto> X)) v i \<phi>1'))) m UNIV \<phi>1 \<phi>1'" by (simp add: "1")
  have wf_envs: "wf_envs S \<sigma> (j + \<delta> - length (map (\<tau> \<sigma>) [j..<j + \<delta>])) (length (map (\<tau> \<sigma>) [j..<j + \<delta>])) P P' V db" 
    using MLetPast.prems(2) by force
  have post: "letpast_meval_post n V \<sigma> P' \<phi>1' m (j+\<delta>) i' ys' buf' p \<phi>f1 (letpast_progress \<sigma> P ?pn \<phi>1' j)"
    apply(rule letpast_meval_invar_post[OF safe pred_alt pred_alt_2 rel_map fv wf_form wf_envs _ _ wty1 safe1 invar e_letpast])
    subgoal for xs db \<phi>_m us P P' V S
      apply(cases "us=[]")
       apply simp_all
      subgoal
        apply (intro MLetPast.IH(1)[where j4="j+\<delta>" and \<delta>4="0", simplified])
          apply simp_all
        done
      apply(intro MLetPast.IH)
        apply(simp_all)
      done
    apply simp
    done

  from e1 e_letpast e2 have
    wf_letpast: "wf_mformula \<sigma> (j+\<delta>) (P'(?pn\<mapsto>i')) (V(?pn \<mapsto> letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(?pn \<mapsto> X)) v i \<phi>1'))) m UNIV \<phi>f1 \<phi>1'" and
    buf': "case buf' of
        None \<Rightarrow> i' = letpast_progress \<sigma> P' ?pn \<phi>1' (j+\<delta>)
      | Some Z \<Rightarrow> Suc i' = letpast_progress \<sigma> P' ?pn \<phi>1' (j+\<delta>) \<and>
          qtable m (Formula.fv \<phi>1') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X u k. Formula.sat \<sigma> (V(?pn \<mapsto> X)) u k \<phi>1') (map the v) i') Z" and
    list_letpast_full: "list_all2 (\<lambda>i. qtable m (Formula.fv \<phi>1') (mem_restr UNIV) (\<lambda>v. letpast_sat (\<lambda>X v i. Formula.sat \<sigma> (V(?pn \<mapsto> X)) v i \<phi>1') (map the v) i))
      [letpast_progress \<sigma> P ?pn \<phi>1' j..<letpast_progress \<sigma> P' ?pn \<phi>1' (j+\<delta>)] ys'"
    using post by (auto simp add: letpast_meval_post_def)
  from MLetPast(2)[OF 2 wf_envs_update_sup[OF MLetPast.prems(2) fv list_letpast_full safe1 wty1] wty2] e1 fv safe e_letpast \<phi>f buf' e2 wf_letpast safe1 safe2
  show ?case unfolding LetPast
    by (auto simp: fun_upd_def Let_def intro!: wf_mformula.LetPast simp del: fun_upd_apply)
next
  case (MAnd A_\<phi> \<phi> pos A_\<psi> \<psi> buf)
  from MAnd.prems obtain \<phi>'' \<psi>'' where
    \<phi>'_eq: "\<phi>' = (if pos then \<phi>'' \<and>\<^sub>F \<psi>'' else \<phi>'' \<and>\<^sub>F \<not>\<^sub>F \<psi>'')"
    by (cases rule: wf_mformula.cases) 
      (auto split: if_splits dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MAnd.prems(3) obtain "S, E \<turnstile> \<phi>''" and "S, E \<turnstile> \<psi>''"
    by (cases rule: wty_formula.cases) 
      (auto simp: \<phi>'_eq split: if_splits elim: wty_formula.cases)
  with MAnd.prems show ?case
    by (cases rule: wf_mformula.cases) 
      (auto simp: sat_the_restrict \<phi>'_eq simp del: bin_join.simps
         dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E
         dest!: MAnd.IH split: if_splits prod.splits intro!: wf_mformula.And qtable_bin_join
         elim: mbuf2_take_add'(1) list.rel_mono_strong[OF mbuf2_take_add'(2)])
next
  case (MAndAssign \<phi> conf)
  from MAndAssign.prems obtain \<phi>'' x t \<psi>'' where
    wf_envs: "wf_envs S \<sigma> j \<delta> P P' V db" and
    \<phi>'_eq: "\<phi>' = formula.And \<phi>'' \<psi>''" and
    wf_\<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''" and
    "x < n" and
    "x \<notin> fv \<phi>''" and
    fv_t_subset: "fv_trm t \<subseteq> fv \<phi>''" and
    conf: "(x, t) = conf" and
    \<psi>''_eqs: "\<psi>'' = formula.Eq (trm.Var x) t \<or> \<psi>'' = formula.Eq t (trm.Var x)" and
    safe: "safe_formula \<phi>''"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MAndAssign.prems(3) obtain "S, E \<turnstile> \<phi>''" and "S, E \<turnstile> \<psi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with wf_\<phi> wf_envs obtain xs \<phi>\<^sub>n where
    meval_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>\<^sub>n)" and
    wf_\<phi>\<^sub>n: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>n \<phi>''" and
    xs: "list_all2 (\<lambda>i. qtable n (fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>''))
        [progress \<sigma> P \<phi>'' j..<progress \<sigma> P' \<phi>'' (j + \<delta>)] xs"
    by (auto dest!: MAndAssign.IH)
  have progress_eqs:
      "progress \<sigma> P \<phi>' j = progress \<sigma> P \<phi>'' j"
      "progress \<sigma> P' \<phi>' (j + \<delta>) = progress \<sigma> P' \<phi>'' (j + \<delta>)"
    using \<psi>''_eqs wf_envs_progress_le[OF wf_envs, of \<phi>''] unfolding \<phi>'_eq by auto
  show ?case proof (simp add: meval_eq, intro conjI)
    show "wf_mformula \<sigma> (j + \<delta>) P' V n R (MAndAssign \<phi>\<^sub>n conf) \<phi>'"
      unfolding \<phi>'_eq
      by (rule wf_mformula.AndAssign) fact+
  next
    show "list_all2 (\<lambda>i. qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'))
        [progress \<sigma> P \<phi>' j..<progress \<sigma> P' \<phi>' (j + \<delta>)] (map ((`) (eval_assignment conf)) xs)"
      unfolding list.rel_map progress_eqs conf[symmetric] eval_assignment.simps
      using xs
    proof (rule list.rel_mono_strong)
      fix i X
      assume qtable: "qtable n (fv \<phi>'') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>'') X"
      then show "qtable n (fv \<phi>') (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>')
          ((\<lambda>y. y[x := Some (meval_trm t y)]) ` X)"
      proof (rule qtable_assign)
        show "x < n" by fact
        show "insert x (fv \<phi>'') = fv \<phi>'"
          using \<psi>''_eqs fv_t_subset by (auto simp: \<phi>'_eq)
        show "x \<notin> fv \<phi>''" by fact
      next
        fix v
        assume wf_v: "wf_tuple n (fv \<phi>') v" and "mem_restr R v"
        then show "mem_restr R (restrict (fv \<phi>'') v)" by simp

        assume sat: "Formula.sat \<sigma> V (map the v) i \<phi>'"
        then have A: "Formula.sat \<sigma> V (map the (restrict (fv \<phi>'') v)) i \<phi>''" (is ?A)
          by (simp add: \<phi>'_eq sat_the_restrict)
        have "map the v ! x = Formula.eval_trm (map the v) t"
          using sat \<psi>''_eqs by (auto simp: \<phi>'_eq)
        also have "... = Formula.eval_trm (map the (restrict (fv \<phi>'') v)) t"
          using fv_t_subset by (auto simp: map_the_restrict intro!: eval_trm_fv_cong)
        finally have "map the v ! x = meval_trm t (restrict (fv \<phi>'') v)"
          using meval_trm_eval_trm[of n "fv \<phi>''" "restrict (fv \<phi>'') v" t]
            fv_t_subset wf_v wf_mformula_wf_set[unfolded wf_set_def, OF wf_\<phi>]
          by (fastforce simp: \<phi>'_eq intro!: wf_tuple_restrict)
        then have B: "v ! x = Some (meval_trm t (restrict (fv \<phi>'') v))" (is ?B)
          using \<psi>''_eqs wf_v \<open>x < n\<close> by (auto simp: wf_tuple_def \<phi>'_eq)
        from A B show "?A \<and> ?B" ..
      next
        fix v
        assume wf_v: "wf_tuple n (fv \<phi>'') v" and "mem_restr R v"
          and sat: "Formula.sat \<sigma> V (map the v) i \<phi>''"
        let ?v = "v[x := Some (meval_trm t v)]"
        from sat have A: "Formula.sat \<sigma> V (map the ?v) i \<phi>''"
          using \<open>x \<notin> fv \<phi>''\<close> by (simp add: sat_the_update)
        have "y \<in> fv_trm t \<Longrightarrow> x \<noteq> y" for y
          using fv_t_subset \<open>x \<notin> fv \<phi>''\<close> by auto
        then have B: "Formula.sat \<sigma> V (map the ?v) i \<psi>''"
          using \<psi>''_eqs meval_trm_eval_trm[of n "fv \<phi>''" v t] \<open>x < n\<close>
            fv_t_subset wf_v wf_mformula_wf_set[unfolded wf_set_def, OF wf_\<phi>]
          by (auto simp: wf_tuple_def map_update intro!: eval_trm_fv_cong)
        from A B show "Formula.sat \<sigma> V (map the ?v) i \<phi>'"
          by (simp add: \<phi>'_eq)
      qed
    qed
  qed
next
  case (MAndTrigger args X\<^sub>\<phi> \<phi>' \<gamma>' \<beta>' buf1 buf2 nts aux db P P' V n R z)
  from MAndTrigger.prems obtain \<phi> \<gamma> \<alpha> I \<beta>
    where z_eq: "z = formula.And \<phi> (Formula.Trigger \<alpha> I \<beta>)"
      and wf_phi: "wf_mformula \<sigma> j P V n R \<phi>' \<phi>"
      and wf_gamma: "wf_mformula \<sigma> j P V n R \<gamma>' \<gamma>"
      and wf_beta: "wf_mformula \<sigma> j P V n R \<beta>' \<beta>"
      and wf_buf1: "wf_mbuft2' \<sigma> P V j n R \<phi> \<alpha> I \<beta> buf1" 
      and wf_buf2: "wf_mbuf2' \<sigma> P V j n R \<gamma> \<beta> buf2"
      and pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = Formula.Neg \<gamma>"
      and pos_eq: "safe_formula \<alpha> = args_pos args" 
      and fv_t_subset: "FV (\<alpha> \<^bold>T I \<beta>) \<subseteq> FV \<phi>" 
      and args_ivl: "args_ivl args = I" 
      and args_n: "args_n args = n" 
      and args_L: "args_L args = Formula.fv \<gamma>" 
      and args_R: "args_R args = Formula.fv \<beta>"
      and fv_l_n: "\<forall>x\<in>fv \<beta>. x < n" and fv_phi_eq: "X\<^sub>\<phi> = fv \<phi>"
      and nts: "wf_ts \<sigma> P j \<gamma> \<beta> nts" 
      and fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>" 
      and aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux (progress \<sigma> P (\<alpha> \<^bold>T I \<beta>) j)"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)    
  have "S, E \<turnstile> \<phi>" "S, E \<turnstile> \<alpha>" "S, E \<turnstile> \<beta>" "S, E \<turnstile> \<gamma>"
    using wty_formula_AndD[OF MAndTrigger.prems(3)[unfolded z_eq]]
      wty_formula_TriggerD[of S E \<alpha> I \<beta>] pos wty_formula_NegD[of S E \<gamma>]
    by (auto elim!: wty_formulaD split: if_splits)
  define z' where "z' \<equiv> MAndTrigger X\<^sub>\<phi> \<phi>' buf1 args \<gamma>' \<beta>' buf2 nts aux"
  then obtain zs and z''
    where zs_def: "zs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db z')" 
      and z''_def: "z'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db z')"
      and ztuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db z' = (zs, z'')"
    by fastforce
  obtain xs and \<phi>''
    where xs_def: "xs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>')" 
      and phi''_def: "\<phi>'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>')"
      and xtuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>' = (xs, \<phi>'')"
    by fastforce
  have IH_phi: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>'' \<phi>"
    "list_all2 (\<lambda>i. qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>)) 
      [Progress.progress \<sigma> P \<phi> j..<Progress.progress \<sigma> P' \<phi> (j + \<delta>)] xs"
    using MAndTrigger.IH(1)[OF wf_phi MAndTrigger.prems(2) \<open>S, E \<turnstile> \<phi>\<close>] xtuple_eq
    by auto
  obtain as and \<gamma>''
    where as_def: "as = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>')"
      and gamma''_def: "\<gamma>'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>')"
      and atuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<gamma>' = (as, \<gamma>'')"
    by fastforce
  have IH_gamma: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<gamma>'' \<gamma>"
    "list_all2 (\<lambda>i. qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<gamma>)) 
      [Progress.progress \<sigma> P \<gamma> j..<Progress.progress \<sigma> P' \<gamma> (j + \<delta>)] as"
    using MAndTrigger.IH(2)[OF wf_gamma MAndTrigger.prems(2) \<open>S, E \<turnstile> \<gamma>\<close>] atuple_eq
    by auto
  obtain bs and \<beta>''
    where bs_def: "bs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>')"
      and beta''_def: "\<beta>'' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>')"
      and btuple_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<beta>' = (bs, \<beta>'')"
    by fastforce
  have IH_beta:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<beta>'' \<beta>"
    "list_all2 (\<lambda>i. qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<beta>)) 
      [Progress.progress \<sigma> P \<beta> j..<Progress.progress \<sigma> P' \<beta> (j + \<delta>)] bs"
    using MAndTrigger.IH(3)[OF wf_beta MAndTrigger.prems(2) \<open>S, E \<turnstile> \<beta>\<close>] btuple_eq
    by auto

  have args_props:
    "args_n args = n"
    "args_R args = fv \<alpha> \<union> fv \<beta>"
    "fv \<gamma> = fv \<alpha>"
    using pos args_n args_L args_R fvi_subset
    by (auto split: if_splits)

  define tuple where "tuple = mbuf2T_take (\<lambda>r1 r2 t (zs, aux). let
    aux = update_mtaux args t r1 r2 aux;
    (fv_z, z) = result_mtaux args aux
    in (zs @ [(fv_z, z)], aux)
  ) ([], aux) (mbuf2_add as bs buf2) (nts @ map (\<tau> \<sigma>) [j..<j + \<delta>])"
  
  define zs' where "zs' = fst (fst tuple)"
  define aux' where "aux' = snd (fst tuple)"
  define buf2' where "buf2' = fst (snd tuple)"
  define nts' where "nts' = snd (snd tuple)"

  have tuple_eq: "tuple = ((zs', aux'), buf2', nts')"
    unfolding zs'_def aux'_def buf2'_def nts'_def Let_def
    by auto

  have pred_mapping:
    "pred_mapping (\<lambda>i. i \<le> j) P"
    "pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
    "rel_mapping (\<le>) P P'"
    using MAndTrigger.prems(2)
    by auto

  from MAndTrigger.prems(2) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<gamma> j) (progress \<sigma> P \<beta> j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts
    unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)

  have wf_buf_ts_trigger:
    "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R \<gamma> \<beta> buf2'"
    "wf_ts \<sigma> P' (j + \<delta>) \<gamma> \<beta> nts'"
    using mbuf2T_take_add'[OF tuple_eq[unfolded tuple_def] pred_mapping 
        wf_buf2 nts_snoc IH_gamma(2) IH_beta(2)] by auto
  have \<alpha>_\<gamma>_props: "Formula.fv \<alpha> = Formula.fv \<gamma>" "progress \<sigma> P \<alpha> j = progress \<sigma> P \<gamma> j"
  "progress \<sigma> P' \<alpha> j = progress \<sigma> P' \<gamma> j" for j
    using pos
    by (simp_all split: if_splits)

  have update_trigger:
    "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (zs', aux')) (progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>))
  \<and> list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (\<alpha> \<^bold>T I \<beta>) 
      \<and> qtable n dfvs (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha> \<^bold>T I \<beta>) r)
    [progress \<sigma> P (\<alpha> \<^bold>T I \<beta>) j..<progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>)] (fst (zs', aux'))"
    unfolding progress_simps \<alpha>_\<gamma>_props
  proof (rule mbuf2T_take_add_induct'[where j=j and j'="j + \<delta>" and z'="(zs', aux')",
        OF tuple_eq[unfolded tuple_def] pred_mapping wf_buf2 nts_snoc IH_gamma(2) IH_beta(2)],
      goal_cases _ base step) (*  *)
  next
    case base
    then show ?case
      using aux \<alpha>_\<gamma>_props base
      unfolding progress_simps
      by auto
  next
    case (step k X Y acc)
    define zs where "zs = fst acc"
    define aux where "aux = snd acc"
    have z_eq: "acc = (zs, aux)"
      unfolding zs_def aux_def
      by auto

    have table:
      "table (args_n args) (args_L args) X"
      "table (args_n args) (args_R args) Y"
      using step(4,5) args_n args_L args_R
      unfolding qtable_def
      by auto

    have wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
      using step(6)
      unfolding aux_def
      by auto
    then have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> "
      unfolding wf_trigger_aux_def
      by auto

    have wf_trigger_aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
      using update_trigger[OF wf_trigger step(4,5) args_n args_L args_R]
      by auto

    then obtain auxlist' where
      valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')" and
      sorted_wrt: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'" and
      auxlist_len: "length auxlist' = Suc k" and
      auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
         Suc k \<noteq> 0 \<and>
         t = \<tau> \<sigma> i \<and>
         t \<le> \<tau> \<sigma> k \<and>
         qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
         qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
      )" and
      auxlist_mem: "(\<forall>i.
          Suc k \<noteq> 0 \<and>
          i \<le> k
          \<longrightarrow>
          (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
      )"
      unfolding wf_trigger_aux_def
      by auto

    define zs' where "zs' = fst (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))"
    define aux' where "aux' = snd (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))"

    have "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux))) (Suc k)"
      using wf_trigger_aux
      unfolding z_eq Let_def
      by (auto split: prod.splits)
    moreover have "list_all2 (\<lambda>i a. case a of (dfvs, r) \<Rightarrow> wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
     [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]
     (fst (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [(fv_z, z)], aux)))"
    proof -
      have aux'_eq: "aux' = update_mtaux args (\<tau> \<sigma> k) X Y aux"
        unfolding aux'_def Let_def
        by (auto split: prod.splits)
      define fv_z where "fv_z = fst (result_mtaux args aux')"
      define z where "z = snd (result_mtaux args aux')"
      define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"

      have valid_mtaux': "valid_mtaux args (\<tau> \<sigma> k) aux' auxlist''"
        unfolding aux'_eq auxlist''_def
        using valid_mtaux
        by auto
      have z_eq: "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have fv_z_eq: "fv_z = fst (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding fv_z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
        unfolding auxlist''_def filter_filter
        by (metis (mono_tags, lifting) case_prod_beta')

      show ?thesis
      proof (cases "0 < length (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')")
        case non_empty: True
        have equiv: "(x \<in> z) = Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)" if
          restr: "mem_restr R x" and
          wf_x: "wf_tuple (args_n args) (args_R args) x"
        for x
          unfolding z_eq auxlist''_def
          using trigger_sat_equiv[OF restr wf_x pos args_n args_ivl args_L args_R fvi_subset 
              fv_l_n(1) valid_mtaux sorted_wrt auxlist_len auxlist_props auxlist_mem non_empty]
          by auto

        have int_non_empty: "\<not>(\<forall>j\<le>k. \<not> mem I (\<tau> \<sigma> k - \<tau> \<sigma> j))"
        proof -
          define auxlist''' where "auxlist''' = (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
          have "auxlist''' \<noteq> []"
            unfolding auxlist'''_def
            using non_empty
            by auto
          then obtain t X where "(t, X) \<in> set auxlist'''"
            by (metis filter_True filter_empty_conv prod.exhaust)
          then have mem:
            "mem (args_ivl args) (\<tau> \<sigma> k - t)"
            "(t, X) \<in> set auxlist'"
            unfolding auxlist'''_def
            by auto
          then obtain i where i_props:
            "i \<in> {0..<length auxlist'}"
            "(t, X) = auxlist'!i"
            by (metis atLeastLessThan_iff in_set_conv_nth zero_le)
          then have "(i, t, X)\<in>set (zip [0..<length auxlist'] auxlist')"
            using mem
            using in_set_zip by fastforce
          then have t_eq: "t = \<tau> \<sigma> i"
            using auxlist_len auxlist_props
            by auto
          show ?thesis
            using mem(1)[unfolded t_eq] i_props(1)[unfolded auxlist_len] not_le_imp_less
            unfolding args_ivl
            by fastforce
        qed

        have "fv_z = args_R args"
          using non_empty filter_inv
          unfolding fv_z_eq auxlist''_def trigger_results.simps
          by auto
        then have fv_z_eq'': "fv_z = fv \<alpha> \<union> fv \<beta>"
          using args_props
          by auto
  
        have "result_mtaux args aux' = trigger_results args (\<tau> \<sigma> k) auxlist''"
          using valid_result_mtaux[OF valid_mtaux]
          unfolding aux'_def auxlist''_def
          by auto
        moreover have "(length (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') > 0)"
          using filter_inv non_empty
          unfolding auxlist''_def
          by auto
        ultimately have z_eq': "z = {
          tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
            (\<forall>i \<in> {0..<(length auxlist'')}.
              let (t, l, r) = auxlist''!i in
              mem (args_ivl args) ((\<tau> \<sigma> k) - t) \<longrightarrow> 
              (
                tuple \<in> r \<or>
                (\<exists>j \<in> {i<..<(length auxlist'')}.
                  join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
                )
              )
            )
          }"
          unfolding z_def
          by auto
  
        have args_R_simp: "args_R args = fv \<alpha> \<union> fv \<beta>"
          using args_L args_R pos fvi_subset
          by (auto split: if_splits)
        have table: "table n (fv \<alpha> \<union> fv \<beta>) z"
          using z_eq'
          unfolding table_def args_R_simp args_n
          by auto
  
        have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
          using equiv args_props
          by auto
  
        have completeness: "\<And>x. wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
          using equiv args_props
          by auto
  
        have qtable_k: "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
          using qtableI[OF table correctness completeness]
          by auto
  
        have zs'_eq: "zs' = zs @ [(fv_z, z)]"
          unfolding zs'_def fv_z_def z_def aux'_eq  Let_def
          by (auto split: prod.splits)
  
        have IH: "list_all2
          (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
          [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs"
          using step(6) zs_def args_props(3)
          by auto
        then have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
          unfolding list_all2_iff
          by auto
        then have len: "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
          unfolding zs'_eq length_append
          by (simp add: step(1))
  
        moreover have "(\<forall>(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs').
        wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
        qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
        proof -
          {
            fix i dfvs r
            assume assm: "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs')"
            
            have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
              using step(6) zs_def
              unfolding list_all2_iff
              by auto
            moreover have "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] @ [k] =
                           [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]"
              by (simp add: step(1))
            ultimately have zip_eq:
              "zip ([min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
               zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [(fv_z, z)]"
              unfolding zs'_eq
              using zip_append[of "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[(fv_z, z)]"]
              by auto
            {
              assume "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using step(6) args_props(3) zs_def
                unfolding list_all2_iff
                by auto
            }
            moreover {
              assume "(i, (dfvs, r)) \<notin> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have eqs: "(i, dfvs, r) = (k, fv_z, z)"
                using assm zip_eq
                by auto
              moreover have "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                using eqs int_non_empty
                unfolding fv_z_eq'' wf_dfvs_def
                by auto
              ultimately have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using qtable_k fv_z_eq''
                by auto
            }
            ultimately have
              "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
              "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              by auto
          }
          then show ?thesis by auto
        qed
  
        ultimately show ?thesis
          unfolding list_all2_iff zs'_def zs_def aux_def
          by (auto split: prod.splits)
        
      next
        case False
        then have empty: "length (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') = 0"
          by auto

        have int_empty:"\<forall>j\<le>k. \<not> mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
        proof -
          {
            assume "\<exists>j\<le>k. mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
            then obtain j where j_props: "j \<le> k" "mem I (\<tau> \<sigma> k - \<tau> \<sigma> j)"
              by blast
            then obtain X where "(\<tau> \<sigma> j, X) = auxlist' ! j"
              using auxlist_mem
              by auto
            then have  "(\<tau> \<sigma> j, X) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
              using auxlist_len j_props args_ivl
              by auto
            then have "False"
              using empty length_pos_if_in_set[of "(\<tau> \<sigma> j, X)"]
              by auto
          }
          then show ?thesis by blast
        qed

        have sat: "\<And>v. Formula.sat \<sigma> V v k (formula.Trigger \<alpha> I \<beta>)"
          using int_empty
          by auto

        have z_eq': "z = {replicate (args_n args) None}"
          using empty filter_inv
          unfolding z_eq auxlist''_def trigger_results.simps
          by auto

        have fv_z_eq': "fv_z = {}"
          using empty filter_inv
          unfolding fv_z_eq auxlist''_def trigger_results.simps
          by auto

        have table: "table n {} z"
          unfolding fv_z_eq' z_eq'
          by (simp add: args_n table_def wf_tuple_empty_iff)

        have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n {} x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
          using sat
          by auto
  
        have completeness: "\<And>x. wf_tuple n {} x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
          using sat
          unfolding z_eq'
          by (simp add: args_n wf_tuple_empty_iff)
  
        have qtable_k: "qtable n {} (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
          using qtableI[OF table correctness completeness]
          by auto
  
        have zs'_eq: "zs' = zs @ [(fv_z, z)]"
          unfolding zs'_def fv_z_def z_def aux'_eq  Let_def
          by (auto split: prod.splits)
  
        have IH: "list_all2
          (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
          [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs"
          using step(6) zs_def args_props(3)
          by auto
        then have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
          unfolding list_all2_iff
          by auto
        then have len: "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
          unfolding zs'_eq length_append
          by (simp add: step(1))
  
        moreover have "(\<forall>(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs').
        wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
        qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
        proof -
          {
            fix i dfvs r
            assume assm: "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs')"
            
            have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
              using step(6) zs_def
              unfolding list_all2_iff
              by auto
            moreover have "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] @ [k] =
                           [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]"
              by (simp add: step(1))
            ultimately have zip_eq:
              "zip ([min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
               zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [(fv_z, z)]"
              unfolding zs'_eq
              using zip_append[of "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[(fv_z, z)]"]
              by auto
            {
              assume "(i, (dfvs, r)) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using step(6) args_props(3) zs_def
                unfolding list_all2_iff
                by auto
            }
            moreover {
              assume "(i, (dfvs, r)) \<notin> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
              then have eq: "(i, dfvs, r) = (k, fv_z, z)"
                using assm zip_eq
                by auto
              moreover have "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                using sat eq fv_z_eq' int_empty
                unfolding wf_dfvs_def
                by auto
              ultimately have
                "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
                "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
                using qtable_k fv_z_eq'
                by auto
            }
            ultimately have
              "wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
              "qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              by auto
          }
          then show ?thesis by auto
        qed
  
        ultimately show ?thesis
          unfolding list_all2_iff zs'_def zs_def aux_def
          by (auto split: prod.splits)
      qed
    qed
    ultimately show ?case 
      using args_props(3) by auto
  qed auto
  (* same but this time without the conjunction *)
  then have update_trigger:
    "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux' (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))"
    "list_all2 (\<lambda>i (dfvs, r). wf_dfvs dfvs \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and> qtable n dfvs (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)
     [Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] zs'"
    by auto

  define tuple' where "tuple' = mbuf2_take (\<lambda>r1 (V_trigger, r2).
      bin_join n (fv \<phi>) r1 True V_trigger r2
  ) (mbuf2_add xs zs' buf1)"

  have zs_eq: "zs = fst tuple'"
    unfolding zs_def z'_def meval.simps tuple'_def Let_def \<open>X\<^sub>\<phi> = fv \<phi>\<close>
    apply (auto simp only: xtuple_eq atuple_eq btuple_eq tuple_def[unfolded Let_def, symmetric] tuple_eq)
    by (simp add: case_prod_beta')
    
  define buf1' where "buf1' = snd tuple'"

  have tuple'_eq: "tuple' = (zs, buf1')"
    unfolding zs_eq buf1'_def
    by auto

  have z''_eq: "z'' = MAndTrigger (fv \<phi>) \<phi>'' buf1' args \<gamma>'' \<beta>'' buf2' nts' aux'"
    unfolding z''_def z'_def meval.simps Let_def \<open>X\<^sub>\<phi> = fv \<phi>\<close>
    apply (auto simp only: xtuple_eq atuple_eq btuple_eq tuple_def[unfolded Let_def, symmetric]
        tuple_eq tuple'_def[unfolded Let_def, symmetric] tuple'_eq)
    by (simp add: case_prod_beta')

  have buf_and:
    "wf_mbuft2' \<sigma> P' V (j + \<delta>) n R \<phi> \<alpha> I \<beta> buf1'"
    "list_all2
     (\<lambda>i Z. \<exists>X V_Y Y.
                qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
                wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
                qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and>
                Z = bin_join n (fv \<phi>) X True V_Y Y)
     [min (Progress.progress \<sigma> P \<phi> j) (Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..<
      min (Progress.progress \<sigma> P' \<phi> (j + \<delta>)) (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))]
     zs"
    using mbuft2_take_add'[OF tuple'_eq[unfolded tuple'_def] 
        wf_buf1 pred_mapping(3,1,2) IH_phi(2) update_trigger(2)]
    by auto

  have "wf_mformula \<sigma> (j + \<delta>) P' V n R z'' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))"
    unfolding z''_eq
    using  wf_mformula.And_Trigger[OF IH_phi(1) buf_and(1) fv_t_subset 
        IH_beta(1) pos IH_gamma(1) pos_eq args_ivl args_n args_L args_R fv_l_n(1) fvi_subset 
        wf_buf_ts_trigger update_trigger(1)] .
  moreover have "list_all2
       (\<lambda>i. qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))))
       [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs" 
  proof -
    have "length [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] = length zs"
      using buf_and(2)
      unfolding list_all2_iff
      by auto
    moreover have "\<And>i r. (i, r)\<in>set (zip [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs) \<Longrightarrow>
        qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) r"
    proof -
      fix i r
      assume "(i, r)\<in>set (zip [Progress.progress \<sigma> P (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) j..<Progress.progress \<sigma> P' (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) (j + \<delta>)] zs)"
      then have "(i, r)\<in>set (zip [min (Progress.progress \<sigma> P \<phi> j) (Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)..< min (Progress.progress \<sigma> P' \<phi> (j + \<delta>)) (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>))] zs)"
        by auto
      then have "\<exists>X V_Y Y.
           qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X \<and>
           wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>) \<and>
           qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y \<and> r = bin_join n (fv \<phi>) X True V_Y Y"
        using buf_and(2)
        unfolding list_all2_iff
        by fast
      then obtain X V_Y Y where qtables:
        "qtable n (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<phi>) X"
        "qtable n V_Y (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) Y"
        "wf_dfvs V_Y \<sigma> I i (formula.Trigger \<alpha> I \<beta>)"
        "r = bin_join n (fv \<phi>) X True V_Y Y"
        by blast

      have "V_Y \<subseteq> fv (formula.Trigger \<alpha> I \<beta>)"
        using qtables(3)
        unfolding wf_dfvs_def
        by (auto split: if_splits)
      then have fvs: "(fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) = fv \<phi> \<union> V_Y"
        using fv_t_subset
        by auto

      have "\<And>x. Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> = Formula.sat \<sigma> V (map the x) i \<phi>"
        using sat_the_restrict
        by auto

      have qtable_pos: "(\<And>x.
          wf_tuple n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) x \<Longrightarrow>
          mem_restr R x \<Longrightarrow>
          Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>)))"
      proof (cases "\<forall>j\<le>i. \<not> mem I (\<tau> \<sigma> i - \<tau> \<sigma> j)")
        case True
        fix x
        show "Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>))"
          using sat_the_restrict True
          by auto
      next
        case False
        then have V_Y_eq: "V_Y = fv (formula.Trigger \<alpha> I \<beta>)"
          using qtables(3)
          unfolding wf_dfvs_def
          by auto

        fix x
        show "Formula.sat \<sigma> V (map the x) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>)) =
          (Formula.sat \<sigma> V (map the (restrict (fv \<phi>) x)) i \<phi> \<and> Formula.sat \<sigma> V (map the (restrict V_Y x)) i (formula.Trigger \<alpha> I \<beta>))"
          unfolding V_Y_eq
          using sat_the_restrict
          by auto
      qed

      then show "qtable n (fv (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.And \<phi> (formula.Trigger \<alpha> I \<beta>))) r"
        unfolding qtables(4)
        using qtable_bin_join[OF qtables(1-2) _ fvs _ qtable_pos, of True]
        by auto
    qed
    ultimately show ?thesis
      unfolding list_all2_iff
      by blast
  qed

  ultimately show ?case 
    using ztuple_eq  
    by (auto simp: z'_def fv_phi_eq z_eq)
next
  case (MAndRel \<phi> conf)
  from MAndRel.prems obtain \<phi>'' \<psi>'' where
  \<phi>'_eq: "\<phi>' = formula.And \<phi>'' \<psi>''"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MAndRel.prems(3) obtain "S, E \<turnstile> \<phi>''" and "S, E \<turnstile> \<psi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with MAndRel.prems show ?case
    by (cases rule: wf_mformula.cases)
      (auto simp: progress_constraint progress_le list.rel_map fv_formula_of_constraint \<phi>'_eq
        Un_absorb2 wf_mformula_wf_set[unfolded wf_set_def] split: prod.splits
        dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E
        dest!: MAndRel.IH eval_constraint_sat_eq[THEN iffD2]
        intro!: wf_mformula.AndRel
        elim!: list.rel_mono_strong qtable_filter eval_constraint_sat_eq[THEN iffD1])
next
  case (MAnds A_pos A_neg l buf)
  note mbufn_take.simps[simp del] mbufn_add.simps[simp del] mmulti_join.simps[simp del]

  from MAnds.prems obtain pos neg l' 
    where wf_l: "list_all2 (wf_mformula \<sigma> j P V n R) l (pos @ map remove_neg neg)" 
      and wf_buf: "wf_mbufn (progress \<sigma> P (\<And>\<^sub>F l') j) 
        (map (\<lambda>\<psi>. progress \<sigma> P \<psi> j) (pos @ map remove_neg neg))
        (map (\<lambda>\<psi> i. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<psi>)) (pos @ map remove_neg neg)) 
        buf" 
      and posneg: "(pos, neg) = partition safe_formula l'" 
      and "pos \<noteq> []"
      and safe_neg: "list_all safe_formula (map remove_neg neg)"
      and A_eq: "A_pos = map fv pos" "A_neg = map fv neg"
      and fv_subset: "\<Union> (set A_neg) \<subseteq> \<Union> (set A_pos)"
      and \<phi>'_eq: "\<phi>' = Formula.Ands l'"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  have progress_eq: "progress \<sigma> P'  (\<And>\<^sub>F l') (j + \<delta>) =
      Mini (progress \<sigma> P (\<And>\<^sub>F l') j) (map (\<lambda>\<psi>. progress \<sigma> P' \<psi> (j + \<delta>)) (pos @ map remove_neg neg))"
    using \<open>pos \<noteq> []\<close> posneg
    by (auto simp: Mini_def image_Un[symmetric] Collect_disj_eq[symmetric] 
        intro!: arg_cong[where f=Min])

  have join_ok: "qtable n (\<Union> (fv ` set l')) (mem_restr R)
        (\<lambda>v. list_all (Formula.sat \<sigma> V (map the v) k) l')
        (mmulti_join n A_pos A_neg L)"
    if args_ok: "list_all2 (\<lambda>x. qtable n (fv x) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k x))
        (pos @ map remove_neg neg) L"
    for k L
  proof (rule qtable_mmulti_join)
    let ?ok = "\<lambda>A Qi X. qtable n A (mem_restr R) Qi X \<and> wf_set n A"
    let ?L_pos = "take (length A_pos) L"
    let ?L_neg = "drop (length A_pos) L"
    have 1: "length pos \<le> length L"
      using args_ok by (auto dest!: list_all2_lengthD)
    show "list_all3 ?ok A_pos (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k \<psi>) pos) ?L_pos"
      using args_ok wf_l unfolding A_eq
      by (auto simp add: list_all3_conv_all_nth list_all2_conv_all_nth nth_append
          split: if_splits intro!: wf_mformula_wf_set[of \<sigma> j P V n R]
          dest: order.strict_trans2[OF _ 1]) 
    have prems_neg: "list_all2 (\<lambda>\<psi>. qtable n (fv \<psi>) (mem_restr R) 
        (\<lambda>v. \<langle>\<sigma>, V, v, k\<rangle> \<Turnstile>\<^sub>M remove_neg \<psi>)) neg ?L_neg"
      using args_ok
      by (auto simp: A_eq list_all2_append1 list.rel_map)
    show "list_all3 ?ok A_neg (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k (remove_neg \<psi>)) neg) ?L_neg"
      using prems_neg wf_l unfolding A_eq
      by (auto simp add: list_all3_conv_all_nth list_all2_conv_all_nth list_all_length 
          nth_append less_diff_conv split: if_splits 
          intro!: wf_mformula_wf_set[of \<sigma> j P V n R _ "remove_neg _", simplified])
    show "\<Union>(fv ` set l') = \<Union>(set A_pos)"
      using fv_subset posneg unfolding A_eq by auto
    show "L = take (length A_pos) L @ drop (length A_pos) L" by simp
    show "A_pos \<noteq> []" using \<open>pos \<noteq> []\<close> A_eq by simp

    fix x :: "event_data tuple"
    assume "wf_tuple n (\<Union> (fv ` set l')) x" and "mem_restr R x"
    then show "list_all (\<lambda>A. mem_restr R (restrict A x)) A_pos"
      and "list_all (\<lambda>A. mem_restr R (restrict A x)) A_neg"
      by (simp_all add: list.pred_set)

    have "list_all Formula.is_Neg neg"
      using posneg safe_neg
      by (auto 0 3 simp add: list.pred_map elim!: list.pred_mono_strong
          intro: formula.exhaust[of \<psi> "Formula.is_Neg \<psi>" for \<psi>])
    then have "list_all (\<lambda>\<psi>. Formula.sat \<sigma> V (map the v) i (remove_neg \<psi>) \<longleftrightarrow>
      \<not> Formula.sat \<sigma> V (map the v) i \<psi>) neg" for v i
      by (fastforce simp: Formula.is_Neg_def elim!: list.pred_mono_strong)
    then show "list_all (Formula.sat \<sigma> V (map the x) k) l' =
       (list_all2 (\<lambda>A Qi. Qi (restrict A x)) A_pos
         (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k \<psi>) pos) \<and>
        list_all2 (\<lambda>A Qi. \<not> Qi (restrict A x)) A_neg
         (map (\<lambda>\<psi> v. Formula.sat \<sigma> V (map the v) k
                       (remove_neg \<psi>))
           neg))"
      using posneg
      by (auto simp add: A_eq list_all2_conv_all_nth list_all_length sat_the_restrict
          elim: nth_filter nth_partition[where P=safe_formula and Q="Formula.sat _ _ _ _"])
  qed fact
  have split: 
    "\<phi> \<in> set pos \<Longrightarrow> \<phi> \<in> set l'"
    "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow> Formula.Neg \<phi> \<in> set l' \<or> \<phi> \<in> set l'" for \<phi> 
    using posneg
    apply auto subgoal for x apply(cases x) by auto done
  from MAnds.prems(3) have all_wty: "\<forall>\<phi>\<in>set l'. S, E \<turnstile> \<phi>"
    unfolding \<phi>'_eq by (cases rule: wty_formula.cases) auto
  have "\<phi> \<in> set pos \<Longrightarrow> S, E \<turnstile> \<phi>" for \<phi> using split(1) all_wty by auto
  moreover have "\<phi> \<in> set (map remove_neg neg) \<Longrightarrow> S, E \<turnstile> \<phi>" for \<phi> 
  proof -
    assume asm: "\<phi> \<in> set (map remove_neg neg)"
    show "S, E \<turnstile> \<phi>" using split(2)[OF asm] all_wty
      by(auto elim:wty_formula.cases)
  qed
  ultimately have "\<forall>\<phi>\<in>set (pos @ map remove_neg neg). S, E \<turnstile> \<phi>"
    by auto
  with MAnds.prems(2) show ?case
    unfolding \<phi>'_eq
    by (auto 0 3 simp add: list.rel_map progress_eq map2_map_map list_all3_map
        list_all3_list_all2_conv list.pred_map
        simp del: set_append map_append progress_simps split: prod.splits
        intro!: wf_mformula.Ands[OF _ _ posneg \<open>pos \<noteq> []\<close> safe_neg A_eq fv_subset]
        list.rel_mono_strong[OF wf_l] wf_mbufn_add[OF wf_buf]
        list.rel_flip[THEN iffD1, OF list.rel_mono_strong, OF wf_l]
        list.rel_refl join_ok[unfolded list.pred_set]
        dest!: MAnds.IH[where E4=E, OF _ _ MAnds.prems(2), rotated]
        elim!: wf_mbufn_take list_all2_appendI
        elim: mbufn_take_induct[OF _ wf_mbufn_add[OF wf_buf]])
next
  case (MOr \<phi> \<psi> buf)
  from MOr.prems obtain \<phi>'' \<psi>'' \<alpha>' J where
    \<phi>'_eq: "\<phi>' = \<phi>'' \<or>\<^sub>F \<psi>'' \<or> \<phi>' = \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'') \<or> \<phi>' = \<phi>'' \<^bold>R J \<psi>''"
    by (cases rule: wf_mformula.cases)
      auto
  have pred_mappings: "rel_mapping (\<le>) P P'"
    "pred_mapping (\<lambda>x. x \<le> j) P"
    "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'"
    using MOr.prems by auto
  have wty_phi: "S, E \<turnstile> \<phi>''" 
    and wty_psi: "S, E \<turnstile> \<psi>''"
    and wty_alpha: "\<phi>' = \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'') \<Longrightarrow> S, E \<turnstile> \<alpha>'"
     apply (cases rule: wty_formula.cases)
    using \<phi>'_eq MOr.prems(3)
    by (auto dest: wty_formulaD)
  {assume phi'_eq: "\<phi>' = \<phi>'' \<or>\<^sub>F \<psi>''"
    from MOr.prems(3) and this
    obtain "S, E \<turnstile> \<phi>''" and "S, E \<turnstile> \<psi>''"
      by (cases rule: wty_formula.cases)
      (auto simp: \<phi>'_eq)
    with MOr.prems have ?case
      unfolding phi'_eq
      by (cases rule: wf_mformula.cases)
        (auto dest!: MOr.IH split: if_splits prod.splits intro!: wf_mformula.Or qtable_union
          elim: mbuf2_take_add'(1) list.rel_mono_strong[OF mbuf2_take_add'(2)])
  } moreover {
    let ?ff = "\<not>\<^sub>F Formula.eventually J Formula.TT" 
      and ?Rbdd = "release_safe_bounded \<phi>'' J \<psi>''"
      and ?AndRbdd = "and_release_safe_bounded \<alpha>' \<phi>'' J \<psi>''"
    assume phi'_eq: "\<phi>' = \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')"
    (* obtain hyps for inductive hypothesis *)
    hence wtys: "S, E \<turnstile> \<alpha>' \<and>\<^sub>F ?ff" "S, E \<turnstile> \<alpha>' \<and>\<^sub>F ?Rbdd"
      using wty_phi wty_psi wty_alpha[OF phi'_eq]
      by (auto simp: Formula.eventually_def release_safe_bounded_def 
          always_safe_bounded_def once_def intro!: wty_formula.intros)
    have progress_eq: "progress \<sigma> W ?AndRbdd i 
      = min (progress \<sigma> W (\<alpha>' \<and>\<^sub>F ?ff) i) (progress \<sigma> W (\<alpha>' \<and>\<^sub>F ?Rbdd) i)" for i W
      by (clarsimp simp: and_release_safe_bounded_def)
    from MOr.prems have "\<not> mem J 0" and "bounded J" 
      and fvs: "FV \<phi>'' = FV \<psi>''" "FV \<psi>'' \<subseteq> FV \<alpha>'" "FV \<alpha>' \<union> FV \<psi>'' = FV \<alpha>'"
      and safes: "safe_formula \<alpha>'" "safe_formula ?Rbdd" 
      and wf_buf: "wf_mbuf2' \<sigma> P V j n R (\<alpha>' \<and>\<^sub>F ?ff) (\<alpha>' \<and>\<^sub>F ?Rbdd) buf"
      by (cases rule: wf_mformula.cases; force simp: phi'_eq)+
    from MOr.prems have wf_MOr: "wf_mformula \<sigma> j P V n R (MOr \<phi> \<psi> buf) ?AndRbdd"
      by (cases rule: wf_mformula.cases; clarsimp simp: phi'_eq)
    hence wf_psi: "wf_mformula \<sigma> j P V n R \<psi> (\<alpha>' \<and>\<^sub>F ?Rbdd)"
      by (cases rule: wf_mformula.cases; clarsimp simp: and_release_safe_bounded_def)
    have wf_phi: "wf_mformula \<sigma> j P V n R \<phi> (\<alpha>' \<and>\<^sub>F ?ff)"
      using wf_MOr
      by (cases rule: wf_mformula.cases; clarsimp simp: 
          and_release_safe_bounded_def Formula.eventually_def)
    (* apply inductive hypothesis *)
    obtain \<phi>s \<phi>\<^sub>M and \<psi>s \<psi>\<^sub>M and \<phi>\<psi>s buf'
      where meval_defs: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (\<phi>s, \<phi>\<^sub>M)"
        "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (\<psi>s, \<psi>\<^sub>M)"
        "mbuf2_take (\<union>) (mbuf2_add \<phi>s \<psi>s buf) = (\<phi>\<psi>s, buf')"
      by (meson eq_snd_iff)
    hence preIH: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>M (\<alpha>' \<and>\<^sub>F ?ff)"
      "list_all2 (\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F ?ff)) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F ?ff))
        [progress \<sigma> P (\<alpha>' \<and>\<^sub>F ?ff) j..< progress \<sigma> P' (\<alpha>' \<and>\<^sub>F ?ff) (j + \<delta>)] \<phi>s"
      "wf_mformula \<sigma> (j + \<delta>) P' V n R \<psi>\<^sub>M (\<alpha>' \<and>\<^sub>F ?Rbdd)"
      "list_all2 (\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F ?Rbdd)) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F ?Rbdd))
       [Progress.progress \<sigma> P (\<alpha>' \<and>\<^sub>F ?Rbdd) j..<Progress.progress \<sigma> P' (\<alpha>' \<and>\<^sub>F ?Rbdd) (j + \<delta>)] \<psi>s"
      using MOr.IH(1)[OF wf_phi MOr.prems(2) wtys(1)] MOr.IH(2)[OF wf_psi MOr.prems(2) wtys(2)]
      by auto
    note mbuf'_obs = mbuf2_take_add'[OF meval_defs(3) wf_buf pred_mappings(1) 
        preIH(2,4) _ pred_mappings(2,3)]
    have IH1: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MOr \<phi>\<^sub>M \<psi>\<^sub>M buf') ?AndRbdd"
      using MOr.prems meval_defs preIH
      unfolding phi'_eq 
      by (cases rule: wf_mformula.cases)
        (auto simp: and_release_safe_bounded_def split: prod.splits
          intro!: wf_mformula.And_Release wf_mformula.Or[OF preIH(1,3)]
          elim: mbuf2_take_add'(1))
    have IH2: 
      "list_all2 (\<lambda>i. qtable n (fv ?AndRbdd) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?AndRbdd))
        [progress \<sigma> P ?AndRbdd j..< progress \<sigma> P' ?AndRbdd (j + \<delta>)] \<phi>\<psi>s"
      using MOr.prems meval_defs preIH
      unfolding phi'_eq 
      apply (cases rule: wf_mformula.cases, unfold progress_eq)
      by (rule list.rel_mono_strong[OF mbuf'_obs(2)])
        (auto simp: fvs and_release_safe_bounded_def intro!: qtable_union)
    (* translate encoding *)
    have key: "(\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>''))) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')))
      = (\<lambda>i. qtable n (FV ?AndRbdd) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?AndRbdd))"
      apply (rule ext)+
      apply (subst qtable_cong_strong[of "FV (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>''))" "FV ?AndRbdd" n "mem_restr R"])
      using fvs \<open>\<not> mem J 0\<close> \<open>bounded J\<close> sat_and_release_rewrite by auto
    have "wf_mformula \<sigma> (j + \<delta>) P' V n R (MOr \<phi>\<^sub>M \<psi>\<^sub>M buf') (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>''))"
      using wf_mformula.intros(9)[OF \<open>\<not> mem J 0\<close> \<open>bounded J\<close> fvs(1,2) safes mbuf'_obs(1) IH1] 
      by force
    moreover have "list_all2 (\<lambda>i. qtable n (FV (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>''))) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')))
       [Progress.progress \<sigma> P (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')) j..<Progress.progress \<sigma> P' (\<alpha>' \<and>\<^sub>F (\<phi>'' \<^bold>R J \<psi>'')) (j + \<delta>)] \<phi>\<psi>s"
      unfolding progress_and_release_rewrite_bounded[OF \<open>\<not> mem J 0\<close> \<open>bounded J\<close>, symmetric]
      apply (subst key)
      using IH2 .
    ultimately have ?case
      using meval_defs
      unfolding meval.simps phi'_eq
      by fastforce
  } moreover {
    let ?R0 = "release_safe_0 \<phi>'' J \<psi>''" and ?A0 = "always_safe_0 J \<psi>''"
    assume phi'_eq: "\<phi>' = \<phi>'' \<^bold>R J \<psi>''"
    (* obtain hyps for inductive hypothesis *)
    with MOr.prems have "wf_envs S \<sigma> j \<delta> P P' V db"
      and "S, E \<turnstile> \<phi>'' \<^bold>R J \<psi>''"
      and "mem J 0"
      and "bounded J"
      and "FV \<phi>'' \<subseteq> FV \<psi>''"
      and safes: "safe_formula \<psi>''" "safe_formula (?R0)"
      and wf_mOr: "wf_mformula \<sigma> j P V n R (MOr \<phi> \<psi> buf) (?R0)"
      and wf_buf: "wf_mbuf2' \<sigma> P V j n R (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') (?A0) buf"
      unfolding phi'_eq
      by (cases rule: wf_mformula.cases, clarsimp)+
    hence fvs: "FV (\<phi>'' \<^bold>R J \<psi>'') = FV \<psi>''"
      "FV (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') = FV \<psi>''"
      "FV (?A0) = FV \<psi>''"
      "FV (?R0) = FV \<psi>''"
      by auto
    have wtys: "S, E \<turnstile> \<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>''" "S, E \<turnstile> ?A0"
      using wty_phi wty_psi
      unfolding always_safe_0_def
      by (auto intro!: wty_formula.intros)
    have wf_phi: "wf_mformula \<sigma> j P V n R \<phi> (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')"
      using wf_mOr
      by (cases rule: wf_mformula.cases; clarsimp simp: release_safe_0_def)
    have wf_psi: "wf_mformula \<sigma> j P V n R \<psi> ?A0"
      using wf_mOr
      by (cases rule: wf_mformula.cases; clarsimp simp: release_safe_0_def)
    (* apply inductive hypothesis *)
    obtain \<phi>s \<phi>\<^sub>M and \<psi>s \<psi>\<^sub>M and \<phi>\<psi>s buf'
      where meval_defs: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (\<phi>s, \<phi>\<^sub>M)"
        "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (\<psi>s, \<psi>\<^sub>M)"
        "mbuf2_take (\<union>) (mbuf2_add \<phi>s \<psi>s buf) = (\<phi>\<psi>s, buf')"
      by (meson eq_snd_iff)
    hence preIH: "wf_mformula \<sigma> (j + \<delta>) P' V n R \<phi>\<^sub>M (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')"
      "list_all2 (\<lambda>i. qtable n (FV (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'')))
        [progress \<sigma> P (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') j..< progress \<sigma> P' (\<psi>'' \<^bold>U J \<psi>'' \<and>\<^sub>F \<phi>'') (j + \<delta>)] \<phi>s"
      "wf_mformula \<sigma> (j + \<delta>) P' V n R \<psi>\<^sub>M ?A0"
      "list_all2 (\<lambda>i. qtable n (FV ?A0) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?A0))
        [progress \<sigma> P ?A0 j..< progress \<sigma> P' ?A0 (j + \<delta>)] \<psi>s"
      using MOr.IH(1)[OF wf_phi MOr.prems(2) wtys(1)] MOr.IH(2)[OF wf_psi MOr.prems(2) wtys(2)]
      by auto
    note mbuf'_obs = mbuf2_take_add'[OF meval_defs(3) wf_buf pred_mappings(1) 
        preIH(2,4) _ pred_mappings(2,3)]
    have IH1: "wf_mformula \<sigma> (j + \<delta>) P' V n R (MOr \<phi>\<^sub>M \<psi>\<^sub>M buf') ?R0"
      using MOr.prems meval_defs preIH safes
      unfolding phi'_eq 
      by (cases rule: wf_mformula.cases)
        (auto simp: release_safe_0_def split: prod.splits
          intro!: wf_mformula.Release_0 wf_mformula.Or[OF preIH(1,3)]
          elim: mbuf2_take_add'(1)) (* 10 secs *)
    have IH2: "list_all2 (\<lambda>i. qtable n (FV ?R0) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M ?R0))
        [progress \<sigma> P ?R0 j..< progress \<sigma> P' ?R0 (j + \<delta>)] \<phi>\<psi>s"
      using MOr.prems meval_defs preIH
      unfolding phi'_eq progress_release_rewrite_0[OF \<open>mem J 0\<close>, symmetric]
      apply (cases rule: wf_mformula.cases)
      by (rule list.rel_mono_strong[OF mbuf'_obs(2), folded progress.simps(8) release_safe_0_def])
        (auto simp: fvs release_safe_0_def intro!: qtable_union)
    have "list_all2 (\<lambda>i. qtable n (FV ?R0) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<phi>'' \<^bold>R J \<psi>''))
      [progress \<sigma> P (\<phi>'' \<^bold>R J \<psi>'') j..< progress \<sigma> P' (\<phi>'' \<^bold>R J \<psi>'') (j + \<delta>)] \<phi>\<psi>s"
      using IH2 
      unfolding sat_release_rewrite_0[OF \<open>mem J 0\<close> \<open>bounded J\<close>] progress_release_rewrite_0[OF \<open>mem J 0\<close>]
      by auto
    moreover note wf_mformula.Release_0[OF \<open>mem J 0\<close> \<open>bounded J\<close> \<open>FV \<phi>'' \<subseteq> FV \<psi>''\<close> safes mbuf'_obs(1) IH1] 
    ultimately have ?case
      using meval_defs
      unfolding meval.simps phi'_eq fvs
      by auto
  }
  ultimately show ?case
    using \<phi>'_eq by metis
next
  case (MNeg \<phi>)
  have *: "qtable n {} (mem_restr R) (\<lambda>v. P v) X \<Longrightarrow>
    \<not> qtable n {} (mem_restr R) (\<lambda>v. \<not> P v) empty_table \<Longrightarrow> x \<in> X \<Longrightarrow> False" for P x X
    using nullary_qtable_cases qtable_unit_empty_table by fastforce
  from MNeg.prems obtain \<phi>'' where \<phi>'_eq: "\<phi>' = formula.Neg \<phi>''"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MNeg.prems(3) have "S, E \<turnstile> \<phi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with MNeg.prems show ?case
    unfolding \<phi>'_eq
    by (cases rule: wf_mformula.cases)
      (auto 0 4 intro!: wf_mformula.Neg dest!: MNeg.IH
        simp add: list.rel_map
        dest: nullary_qtable_cases qtable_unit_empty_table intro!: qtable_empty_unit_table
        elim!: list.rel_mono_strong elim: *)
next
  case (MExists P V n R \<phi> \<phi>')
  from MExists.prems obtain \<phi>'' t where \<phi>'_eq: "\<phi>' = formula.Exists t \<phi>''"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MExists.prems(3) obtain t where "S, case_nat t E \<turnstile> \<phi>''"
    by (cases rule: wty_formula.cases) (auto simp: \<phi>'_eq)
  with MExists.prems show ?case
    unfolding \<phi>'_eq
    by (cases rule: wf_mformula.cases)
      (force simp: list.rel_map fvi_Suc sat_fv_cong nth_Cons'
        intro!: wf_mformula.Exists dest!: MExists.IH qtable_project_fv
        elim!: list.rel_mono_strong table_fvi_tl qtable_cong sat_fv_cong[THEN iffD1, rotated -1]
        split: if_splits)+
next
  case (MAgg args \<phi>)
  from MAgg.prems obtain \<phi>'' where \<phi>'_eq: "\<phi>' = formula.Agg (aggargs_y args) (aggargs_\<omega> args) (aggargs_tys args) (aggargs_f args) \<phi>''"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MAgg.prems(3) have "S, agg_env E (aggargs_tys args) \<turnstile> \<phi>''" 
    unfolding \<phi>'_eq
    by (cases rule: wty_formula.cases) auto
  with MAgg.prems show ?case
    using wf_mformula_wf_set[OF MAgg.prems(1), unfolded wf_set_def]
    unfolding \<phi>'_eq
    by (cases rule: wf_mformula.cases)
      (auto 0 3 simp add: list.rel_map eval_aggargs_def simp del: sat.simps fvi.simps split: prod.split
        intro!: wf_mformula.Agg qtable_eval_agg dest!: MAgg.IH elim!: list.rel_mono_strong)
next
  case (MPrev I \<phi> first buf nts)
  from MPrev.prems show ?case
  proof (cases rule: wf_mformula.cases)
    case (Prev \<psi>)
    from MPrev.prems(3) Prev have wty: "S, E \<turnstile> \<psi>"
      by (cases rule: wty_formula.cases) auto
    let ?xs = "fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
    let ?\<phi> = "snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
    let ?ls = "fst (mprev_next I (buf @ ?xs) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]))"
    let ?rs = "fst (snd (mprev_next I (buf @ ?xs) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
    let ?ts = "snd (snd (mprev_next I (buf @ ?xs) (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
    let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) X"
    let ?i = "min (progress \<sigma> P \<psi> j) (j - 1)"
    let ?j = "j + \<delta>"
    let ?j' = "progress \<sigma> P' \<psi> (j + \<delta>)"
    define mini where "mini = min ?j' (if ?i = ?j then ?j else ?j - 1)"
    from Prev MPrev.IH[OF _ MPrev.prems(2) wty, of n R] have IH: "wf_mformula \<sigma> (j + \<delta>) P' V n R ?\<phi> \<psi>" and
      "list_all2 ?P [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> (j + \<delta>)] ?xs" by auto
    with Prev(5,6) MPrev.prems(2) have
      "list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then ?P i X else X = empty_table) [?i..<mini] ?ls \<and>
       list_all2 ?P [mini..<?j'] ?rs \<and> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [mini..< ?j] ?ts"
      unfolding mini_def
      by (intro mprev) (auto intro!: list_all2_upt_append list_all2_appendI order.trans[OF min.cobounded1]
        list.rel_refl simp: list.rel_map)
    moreover have "min (Suc (progress \<sigma> P \<psi> j)) j = Suc (min (progress \<sigma> P \<psi> j) (j-1))" if "j > 0" for P j
      using that by auto
    ultimately show ?thesis using Prev(1,3,4) MPrev.prems(2) IH
      upt_conv_Cons[OF zero_less_Suc, of "min (Progress.progress \<sigma> P' \<psi> \<delta>) (\<delta> - Suc 0)"]
      by (auto 0 3 simp: map_Suc_upt[symmetric] list.rel_map qtable_empty_iff mini_def
          simp del: upt_Suc elim!: wf_mformula.Prev list.rel_mono_strong dest: wf_envs_progress_le
          split: prod.split if_split_asm) (* slow 25 sec*)
  qed
next
  case (MNext I \<phi> first nts)
  from MNext.prems show ?case
  proof (cases rule: wf_mformula.cases)
    case (Next \<psi>)
    from MNext.prems(3) Next have wty: "S, E \<turnstile> \<psi>"
      by (cases rule: wty_formula.cases) auto
    have min[simp]:
      "min (progress \<sigma> P \<psi> j - Suc 0) (j - Suc 0) = progress \<sigma> P \<psi> j - Suc 0"
      "min (progress \<sigma> P' \<psi> (j + \<delta>) - Suc 0) (j + \<delta> - Suc 0) = progress \<sigma> P' \<psi> (j + \<delta>) - Suc 0"
      using wf_envs_progress_le[OF MNext.prems(2), of \<psi>] by auto

    let ?xs = "fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
    let ?ys = "case (?xs, first) of (_ # xs, True) \<Rightarrow> xs | _ \<Rightarrow> ?xs"
    let ?\<phi> = "snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>)"
    let ?ls = "fst (mprev_next I ?ys (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]))"
    let ?rs = "fst (snd (mprev_next I ?ys (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
    let ?ts = "snd (snd (mprev_next I ?ys (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])))"
    let ?P = "\<lambda>i X. qtable n (fv \<psi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<psi>) X"
    let ?i = "progress \<sigma> P \<psi> j - 1"
    let ?j = "j + \<delta>"
    let ?j' = "progress \<sigma> P' \<psi> (j + \<delta>)"
    define mini where "mini = min (?j' - 1) (if ?i = ?j then ?j else ?j - 1)"

    from Next MNext.IH[OF _ MNext.prems(2) wty, of n R] have IH: "wf_mformula \<sigma> (j + \<delta>) P' V  n R ?\<phi> \<psi>"
      "list_all2 ?P [progress \<sigma> P \<psi> j..<progress \<sigma> P' \<psi> (j + \<delta>)] ?xs" by auto
    with Next have "list_all2 (\<lambda>i X. if mem I ((\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i)) then ?P (Suc i) X else X = empty_table)
         [?i..<mini] ?ls \<and>
       list_all2 ?P [Suc mini..<?j'] ?rs \<and> list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [mini..<?j] ?ts"
       if "progress \<sigma> P \<psi> j < progress \<sigma> P' \<psi> (j + \<delta>)"
      using that wf_envs_progress_le[OF MNext.prems(2), of \<psi>] unfolding mini_def
      by (intro mnext)
        (auto simp: list_all2_Cons2 upt_eq_Cons_conv list.rel_map
          intro!: list_all2_upt_append list_all2_appendI list.rel_refl split: list.splits)
    then show ?thesis using wf_envs_progress_le[OF MNext.prems(2), of \<psi>]
      upt_add_eq_append[of 0 j \<delta>] upt_add_eq_append[of "?j' - 1" j \<delta>]
      wf_envs_progress_mono[OF MNext.prems(2), of \<psi>, simplified] Next IH
      by (cases "progress \<sigma> P' \<psi> (j + \<delta>) > progress \<sigma> P \<psi> j")
        (auto 0 3 simp: qtable_empty_iff le_Suc_eq le_diff_conv mini_def list.rel_map
          elim!: wf_mformula.Next list.rel_mono_strong list_all2_appendI intro!: list.rel_refl
          split: prod.split list.splits if_split_asm)  (* slow 15 sec*)
  qed
next
  case (MSince args \<phi> \<psi> buf  aux db P P' V n' R' \<phi>')
  note sat.simps[simp del]
  from MSince.prems obtain \<phi>'' \<phi>''' \<psi>'' I n R pos where Since_eq: "\<phi>' = packagg args (Formula.Since \<phi>''' I \<psi>'')"
    and pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
    and safe1: "safe_formula \<phi>''"
    and safe2: "safe_formula \<psi>''"
    and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<psi>''"
    and fvi_subset: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
    and buf: "wf_mbuf2S \<sigma> P V j n R \<phi>'' I \<psi>'' buf (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))
      (progress \<sigma> P (Sincep (args_pos args) \<phi>'' I \<psi>'') j)"
    and aux: "wf_since_aux \<sigma> V R args \<phi>'' \<psi>'' aux (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))
      (progress \<sigma> P (Sincep (args_pos args) \<phi>'' I \<psi>'') j)"
    and args: "args_ivl args = I" "args_n args = n" "args_L args = Formula.fv \<phi>''"
    "args_R args = Formula.fv \<psi>''" "args_pos args = pos"
    "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')" "agg_n args = n'"
    by (cases rule: wf_mformula.cases)
      (auto simp: Sincep_def 
        dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E split: if_splits)

  from MSince.prems(3) pos obtain 
    wty1: "case args_agg args of None \<Rightarrow> S, E \<turnstile> \<phi>'' |
            Some aggargs => S, agg_env E (aggargs_tys aggargs) \<turnstile> \<phi>''" and
    wty2: "case args_agg args of None \<Rightarrow> S, E \<turnstile> \<psi>'' |
            Some aggargs => S, agg_env E (aggargs_tys aggargs) \<turnstile> \<psi>''"
    by (cases rule: wty_formula.cases) (auto simp: Since_eq packagg_def split: if_splits option.splits elim:wty_formula.cases)
  have valid_aggargs: "valid_aggargs n (fv \<psi>'') (args_agg args)"
    using aux
    by (auto simp: wf_since_aux_def args)
  obtain xs \<phi>n where eq1: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi> = (xs, \<phi>n)"
    by (elim prod.exhaust)
  note meval1 = MSince.IH(1)[OF \<phi> MSince.prems(2), simplified eq1 prod.case]
  obtain ys \<psi>n where eq2: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<psi> = (ys, \<psi>n)"
    by (elim prod.exhaust)
  note meval2 = MSince.IH(2)[OF \<psi> MSince.prems(2), simplified eq2 prod.case]
  obtain zs buf' aux' where eval_eq: "(zs, buf', aux') 
    = eval_since args [] (mbuf2S_add xs ys (map (\<tau> \<sigma>) [j..<j + \<delta>]) buf) aux"
    by (metis surj_pair)
  have env: "pred_mapping (\<lambda>x. x \<le> j) P" "pred_mapping (\<lambda>x. x \<le> j + \<delta>) P'" "rel_mapping (\<le>) P P'"
    using MSince.prems(2) unfolding wf_envs_def by auto
  have alt:
    "progress \<sigma> P (packagg args (Sincep (args_pos args) \<phi>'' I \<psi>'')) j = progress \<sigma> P \<phi>' j" for P j
    using pos fvi_subset by (simp add: Since_eq Sincep_def)
  then show ?case
    unfolding meval.simps args(2) eq1 eq2 Let_def prod.case eval_eq[symmetric]
    using meval1[THEN conjunct1] meval2[THEN conjunct1]
      eval_since[OF eval_eq buf aux meval1[THEN conjunct2] meval2[THEN conjunct2] env fvi_subset args(1-4) _ args(6-7)]
      pos fvi_subset args wty1 wty2 safe1 safe2
    by (auto simp add: Since_eq args(1) Sincep_def simp del: progress_simps 
        intro!: wf_mformula.Since split:option.splits)
next
  case (MUntil args \<phi> \<psi> buf nts t aux  db P P' V n' R' \<phi>')
  note sat.simps[simp del] progress_simps[simp del]
  from MUntil.prems obtain \<phi>'' \<phi>''' \<psi>'' I n R where Until_eq: "\<phi>' = packagg args (Formula.Until \<phi>''' I \<psi>'')"
    and pos: "if args_pos args then \<phi>''' = \<phi>'' else \<phi>''' = Formula.Neg \<phi>''"
    and safe1: "safe_formula \<phi>''"
    and safe2: "safe_formula \<psi>''"
    and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<phi>''"
    and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<psi>''"
    and fvi_subset: "Formula.fv \<phi>'' \<subseteq> Formula.fv \<psi>''"
    and buf: "wf_mbuf2' \<sigma> P V j n R \<phi>'' \<psi>'' buf"
    and nts: "wf_ts \<sigma> P j \<phi>'' \<psi>'' nts"
    and aux: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
    and args_ivl: "args_ivl args = I"
    and args_n: "args_n args = n"
    and args_L: "args_L args = Formula.fv \<phi>''"
    and args_R: "args_R args = Formula.fv \<psi>''"
    and mr: "mem_restr R = mem_restr (lift_envs' (length (agg_tys args)) R')"
    and agg_n: "agg_n args = n'"
    and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j))))"
    and length_aux: "progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j + length_muaux args aux =
      min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MUntil.prems(3) pos obtain
    wty1: "case args_agg args of None \<Rightarrow> S, E \<turnstile> \<phi>'' |
            Some aggargs => S, agg_env E (aggargs_tys aggargs) \<turnstile> \<phi>''" and
    wty2: "case args_agg args of None \<Rightarrow> S, E \<turnstile> \<psi>'' |
            Some aggargs => S, agg_env E (aggargs_tys aggargs) \<turnstile> \<psi>''"
    by (cases rule: wty_formula.cases) (auto simp: Until_eq packagg_def split: if_splits option.splits elim:wty_formula.cases)
  define pos where args_pos: "pos = args_pos args"
  have \<phi>''': "progress \<sigma> P \<phi>''' j = progress \<sigma> P \<phi>'' j"  "progress \<sigma> P' \<phi>''' j = progress \<sigma> P' \<phi>'' j" for j
    using pos by (simp_all add: progress.simps split: if_splits)
  have valid_aggargs: "valid_aggargs n (fv \<psi>'') (args_agg args)"
    using aux
    by (auto simp: wf_until_aux_def args_n)
  from MUntil.prems(2) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<phi>'' j) (progress \<sigma> P \<psi>'' j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  {
    fix xs ys zs aux' aux'' buf' nts' nt
    assume eval_\<phi>: "fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<phi>) = xs"
      and eval_\<psi>: "fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db \<psi>) = ys"
      and eq1: "mbuf2t_take (add_new_muaux args) aux (mbuf2_add xs ys buf) t (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) =
        (aux', buf', nt, nts')"
      and eq2: "eval_muaux args nt aux' = (zs, aux'')"
    note nt_def = mbuf2t_take_nt[OF eq1]
    define ne where "ne \<equiv> progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j"
    have update1: "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j) \<and>
      ne + length_muaux args aux' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
      using MUntil.IH(1)[OF \<phi> MUntil.prems(2)] eval_\<phi> MUntil.IH(2)[OF \<psi> MUntil.prems(2)]
        eval_\<psi> nts_snoc nts_snoc length_aux aux fvi_subset wty1 wty2
      unfolding \<phi>'''
      by (elim mbuf2t_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF MUntil.prems(2)] buf])
        (auto simp: prod.case_eq_if args_n args_L args_R ne_def wf_update_until split:option.splits)
    then obtain cur auxlist' where valid_aux': "valid_muaux args cur aux' auxlist'" and
      cur: "cur = (if ne + length auxlist' = 0 then 0 else \<tau> \<sigma> (ne + length auxlist' - 1))" and
      wf_auxlist': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' (progress \<sigma> P (Formula.Until \<phi>''' I \<psi>'') j)"
      unfolding wf_until_aux_def ne_def args_ivl args_n args_pos by auto
    have length_aux': "length_muaux args aux' = length auxlist'"
      using valid_length_muaux[OF valid_aux'] .
    have nts': "wf_ts \<sigma> P' (j + \<delta>) \<phi>'' \<psi>'' nts'"
      using MUntil.IH(1)[OF \<phi> MUntil.prems(2)] eval_\<phi> MUntil.IH(2)[OF \<psi> MUntil.prems(2)]
        MUntil.prems(2) eval_\<psi> nts_snoc wty1 wty2
      unfolding wf_ts_def
      by (intro mbuf2t_take_eqD(2)[OF eq1]) (auto simp: prod.case_eq_if intro: wf_mbuf2_add buf[unfolded wf_mbuf2'_def] split:option.splits)
    have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
      using nts nts' unfolding nt_def t
      apply (auto simp: hd_append hd_rev last_map wf_ts_def)
      using list_all2_hdD(1) list_all2_hdD(2) apply fastforce
      using list_all2_lastD  apply fastforce
        apply (metis (mono_tags) list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
       apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      done
    define zs'' where "zs'' = fst (eval_until I nt auxlist')"
    define auxlist'' where "auxlist'' = snd (eval_until I nt auxlist')"
    have current_w_le: "cur \<le> nt"
    proof (cases nts')
      case Nil
      have p_le: "min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<le> j + \<delta>"
        using wf_envs_progress_le[OF MUntil.prems(2)]
        by (auto simp: min_def le_diff_conv)
      then show ?thesis
        unfolding cur conjunct2[OF update1, unfolded length_aux'] nt
        using Nil by (auto simp: \<phi>''' intro!: \<tau>_mono)
    next
      case (Cons nt x)
      have progress_\<phi>''': "progress \<sigma> P' \<phi>'' (j + \<delta>) = progress \<sigma> P' \<phi>''' (j + \<delta>)"
        using pos by (auto simp add: progress.simps split: if_splits)
      have p_le: "min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<le> j + \<delta>"
        using wf_envs_progress_le[OF MUntil.prems(2)]
        by (auto simp: min_def le_diff_conv)
      then show ?thesis
        unfolding cur conjunct2[OF update1, unfolded length_aux'] Cons progress_\<phi>''' nt
        by (auto split: if_splits list.splits intro!: \<tau>_mono)
    qed
    have valid_aux'': "valid_muaux args cur aux'' auxlist''"
      using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
      by (auto simp add: args_ivl zs''_def auxlist''_def)
    have length_aux'': "length_muaux args aux'' = length auxlist''"
      using valid_length_muaux[OF valid_aux''] .
    have eq2': "eval_until I nt auxlist' = (zs'', auxlist'')"
      using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'']
      by (auto simp add: args_ivl zs''_def auxlist''_def)
    have length_aux'_aux'': "length_muaux args aux' = length zs'' + length_muaux args aux''"
      using eval_until_length[OF eq2'] unfolding length_aux' length_aux'' .
    have "i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist' i \<Longrightarrow>
      i + length auxlist' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<Longrightarrow>
      wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' auxlist'' (progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
        i + length zs'' = progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
        i + length zs'' + length auxlist'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
        list_all2 (\<lambda>i. qtable n (Formula.fv \<psi>'') (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Untilp pos \<phi>'' I \<psi>'')))
          [i..<i + length zs''] zs''" for i
      using eq2'
    proof (induction auxlist' arbitrary: zs'' auxlist'' i)
      case Nil
      then show ?case
        by (auto dest!: antisym[OF progress_Until_le])
    next
      case (Cons a aux')
      obtain t a1 a2 where "a = (t, a1, a2)" by (cases a)
      from Cons.prems(2) have aux': "wf_until_auxlist \<sigma> V n R pos \<phi>'' I \<psi>'' aux' (Suc i)"
        by (rule wf_until_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (Formula.fv \<psi>'') (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Formula.sat \<sigma> V (map the v) j \<psi>'' \<and>
        (\<forall>k\<in>{i..<j}. if pos then Formula.sat \<sigma> V (map the v) k \<phi>'' else \<not> Formula.sat \<sigma> V (map the v) k \<phi>''))) a2"
        unfolding \<open>a = (t, a1, a2)\<close> by (rule wf_until_aux_Cons3)
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' =
          min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>))"
        by simp
      have "i \<ge> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
        if "memR I (nt - t)"
        using that nts' unfolding wf_ts_def progress.simps nt
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv \<phi>'''
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> P' (Formula.Until \<phi>''' I \<psi>'') (j + \<delta>)"
        if "\<not> memR I (nt - t)"
      proof -
        have \<tau>_min:  "\<tau> \<sigma> (min (j + \<delta> - 1) k) = min (\<tau> \<sigma> (j + \<delta> - 1)) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "j + \<delta> \<le> progress \<sigma> P' \<phi> (j + \<delta>) \<longleftrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) = (j + \<delta>)" for \<phi> :: "'t Formula.formula"
          using wf_envs_progress_le[OF MUntil.prems(2), of \<phi>] by auto
        let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
        let ?min = "min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> (j + \<delta>)"
          by (rule \<tau>_mono) auto
        from that have "?X \<noteq> {}"
          by (auto simp: \<phi>''' intro!: exI[of _ "progress \<sigma> P' \<phi>'' (j + \<delta>)"])
        show ?thesis
          using that nts' Suc_i_aux' unfolding wf_ts_def progress.simps nt
        by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
          (auto 0 3 simp: 1 \<phi>''' list_all2_Cons2 upt_eq_Cons_conv
            simp del: upt_Suc split: list.splits if_splits
            dest!: spec[of _ "?min"]
            intro: diff_le_mono diff_le_mono2 order_trans[OF diff_le_mono diff_le_mono2] \<tau>_mono
            elim!: contrapos_np[of _ "Suc i \<le> _"])
      qed
      moreover have *: "k < progress \<sigma> P' \<psi> (j + \<delta>)" if
        "\<not> memR I (nt - \<tau> \<sigma> i)"
        "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" "\<psi> = \<psi>'' \<or> \<psi> = \<phi>''" for k \<psi>
        using that nts' unfolding wf_ts_def nt
        by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, a1, a2)\<close>
        by (auto simp: Untilp_def \<phi>''' 1 sat.simps upt_conv_Cons 
            dest!: Cons.IH[OF _ aux' Suc_i_aux']
            simp del: upt_Suc split: if_splits prod.splits 
            intro!: iff_exI qtable_cong[OF 3 refl])
    qed
    note wf_aux'' = this[OF wf_envs_progress_mono[OF MUntil.prems(2)]
      wf_auxlist' conjunct2[OF update1, unfolded ne_def length_aux']]
    have zs_def: "zs = map (eval_args_agg args) zs''"
    using valid_eval_muaux[OF valid_aux' current_w_le eq2, of zs'' auxlist'']
    unfolding eval_args_agg_def
    by (auto simp add: args_ivl zs''_def auxlist''_def split: option.splits)
    have len_zs'': "length zs'' = length zs"
      by (auto simp: zs_def)
    have "list_all2 (\<lambda>i. qtable n (fv \<psi>'') (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Untilp pos \<phi>'' I \<psi>'')))
      [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
       Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)] zs''"
    using wf_aux''
    by auto
    have fv: "fv (Formula.Until (if pos then \<phi>'' else formula.Neg \<phi>'') I \<psi>'') = fv \<psi>''"
      using fvi_subset
      by (auto)
    have "list_all2 (\<lambda>i. qtable n (fv \<psi>'') (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Untilp pos \<phi>'' I \<psi>'')))
      [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
       Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)] zs''"
    using wf_aux''
    by auto
    then have list_all2_zs: "list_all2 (\<lambda>i. qtable (agg_n args) (fv (packagg args (Untilp pos \<phi>'' I \<psi>''))) (mem_restr R')
        (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (Untilp pos \<phi>'' I \<psi>''))))
        [Progress.progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<
         Progress.progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)] zs"
      unfolding zs_def list_all2_map2 Untilp_def
      apply (rule list_all2_mono)
      apply (rule qtable_eval_args_agg[of _ _ R])
      apply (auto simp: mr args_n fv valid_aggargs Un_absorb1 fvi_subset)
      done
    have "progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length auxlist' =
      progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist''"
      using wf_aux'' valid_aux'' length_aux'_aux''
      by (auto simp add: ne_def length_aux' length_aux'')
    then have "cur =
      (if progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' = 0 then 0
      else \<tau> \<sigma> (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) + length auxlist'' - 1))"
      unfolding cur ne_def by auto
    then have "wf_until_aux \<sigma> V R args \<phi>'' \<psi>'' aux'' (progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>)) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs = progress \<sigma> P' (formula.Until \<phi>''' I \<psi>'') (j + \<delta>) \<and>
      progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs + length_muaux args aux'' = min (progress \<sigma> P' \<phi>''' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)) \<and>
      list_all2 (\<lambda>i. qtable (agg_n args) (fv (packagg args (formula.Until \<phi>''' I \<psi>''))) (mem_restr R') (\<lambda>v. Formula.sat \<sigma> V (map the v) i (packagg args (formula.Until (if pos then \<phi>'' else formula.Neg \<phi>'') I \<psi>''))))
      [progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j..<progress \<sigma> P (formula.Until \<phi>''' I \<psi>'') j + length zs] zs \<and>
      nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (min (progress \<sigma> P' \<phi>'' (j + \<delta>)) (progress \<sigma> P' \<psi>'' (j + \<delta>)))))"
      using aux wf_aux'' valid_aux'' fvi_subset list_all2_zs pos
      unfolding wf_until_aux_def length_aux'' args_ivl args_n args_pos nt len_zs'' Untilp_def
      by (auto simp only: length_aux'') (smt (verit, best) list_all2_mono)
  }
  note update = this[OF refl refl, rotated]
  from MUntil.IH(1)[OF \<phi> MUntil.prems(2)] MUntil.IH(2)[OF \<psi> MUntil.prems(2)] pos fvi_subset wty1 wty2 
  show ?case
    unfolding meval.simps Let_def 
    by (auto simp: args_ivl args_n args_pos agg_n[symmetric] Until_eq \<phi>''' progress.simps(7) Let_def
        split: prod.split if_splits option.splits dest!: update
        intro!: wf_mformula.Until[OF _ _ _ safe1 safe2 args_ivl args_n args_L args_R mr fvi_subset]
        elim!: list.rel_mono_strong qtable_cong
        elim: mbuf2t_take_add'(1)[OF _ wf_envs_P_simps[OF MUntil.prems(2)] buf nts_snoc]
        mbuf2t_take_add'(2)[OF _ wf_envs_P_simps[OF MUntil.prems(2)] buf nts_snoc])
next
  case (MTrigger args \<phi> \<psi> buf nts aux db P P' V)
  from MTrigger.prems obtain \<gamma> I \<alpha> \<beta>
    where phi'_eq: "\<phi>' = Formula.Trigger \<alpha> I \<beta>"
      and pos: "if args_pos args then \<alpha> = \<gamma> else \<alpha> = formula.Neg \<gamma>"
      and pos_eq: "safe_formula \<alpha> = args_pos args"
      and \<phi>: "wf_mformula \<sigma> j P V n R \<phi> \<gamma>"
      and \<psi>: "wf_mformula \<sigma> j P V n R \<psi> \<beta>"
      and fvi_subset: "if mem I 0 then fv \<gamma> \<subseteq> fv \<beta> else fv \<gamma> = fv \<beta>"
      and buf: "wf_mbuf2' \<sigma> P V j n R \<gamma> \<beta> buf"
      and nts: "wf_ts \<sigma> P j \<gamma> \<beta> nts"
      and aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux (Progress.progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j)"
      and args_ivl: "args_ivl args = I"
      and args_n: "args_n args = n"
      and args_L: "args_L args = fv \<gamma>"
      and args_R: "args_R args = fv \<beta>"
      and fv_l_n: "\<forall>x\<in>fv \<beta>. x < n"
      and mem0: "mem I 0"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)

  have "S, E \<turnstile> \<alpha>" "S, E \<turnstile> \<beta>" "S, E \<turnstile> \<gamma>"
    using wty_formula_TriggerD[OF MTrigger.prems(3)[unfolded phi'_eq]] 
      pos wty_formula_NegD[of S E \<gamma>]
    by (auto elim!: wty_formulaD split: if_splits)

  have args_props:
    "args_n args = n"
    "args_R args = fv \<alpha> \<union> fv \<beta>"
    "fv \<gamma> = fv \<alpha>"
    using pos args_n args_L args_R fvi_subset
    by (auto split: if_splits)

  note IH_\<phi> = MTrigger.IH(1)[OF \<phi> MTrigger.prems(2) \<open>S, E \<turnstile> \<gamma>\<close>]
  note IH_\<psi> = MTrigger.IH(2)[OF \<psi> MTrigger.prems(2) \<open>S, E \<turnstile> \<beta>\<close>]

  define zs where "zs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MTrigger args \<phi> \<psi> buf nts aux))"
  define \<eta> where "\<eta> = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db (MTrigger args \<phi> \<psi> buf nts aux))"

  define xs where "xs = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"
  define \<gamma>' where "\<gamma>' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi>)"

  have \<phi>_pair_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<phi> = (xs, \<gamma>')"
    unfolding xs_def \<gamma>'_def
    by auto

  have \<gamma>_props:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<gamma>' \<gamma>"
    "list_all2 (\<lambda>i. qtable n (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>)) [Progress.progress \<sigma> P \<gamma> j..<Progress.progress \<sigma> P' \<gamma> (j + \<delta>)] xs"
    using IH_\<phi>
    unfolding \<phi>_pair_eq
    by auto

  define ys where "ys = fst (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"
  define \<beta>' where "\<beta>' = snd (meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi>)"

  have \<psi>_pair_eq: "meval (j + \<delta>) n (map (\<tau> \<sigma>) [j..<j + \<delta>]) db \<psi> = (ys, \<beta>')"
    unfolding ys_def \<beta>'_def
    by auto

  have \<beta>_props:
    "wf_mformula \<sigma> (j + \<delta>) P' V n R \<beta>' \<beta>"
    "list_all2 (\<lambda>i. qtable n (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>)) [Progress.progress \<sigma> P \<beta> j..<Progress.progress \<sigma> P' \<beta> (j + \<delta>)] ys"
    using IH_\<psi>
    unfolding \<psi>_pair_eq
    by auto

  define tuple where "tuple = mbuf2T_take (\<lambda>r1 r2 t (zs, aux). let
    aux = update_mtaux args t r1 r2 aux;
    (fv_z, z) = result_mtaux args aux
    in
      (zs @ [z], aux)
  ) ([], aux) (mbuf2_add xs ys buf) (nts @ map (\<tau> \<sigma>) [j..<j + \<delta>])"

  have zs_eq: "zs = fst (fst tuple)"
    unfolding tuple_def zs_def meval.simps Let_def xs_def ys_def
    by (auto split: prod.splits)

  define aux' where "aux' = snd (fst tuple)"
  define buf' where "buf' = fst (snd tuple)"
  define nts' where "nts' = snd (snd tuple)"

  have tuple_eq: "tuple = ((zs, aux'), buf', nts')"
    unfolding zs_eq aux'_def buf'_def nts'_def Let_def
    by auto

  have \<eta>_eq: "\<eta> = MTrigger args \<gamma>' \<beta>' buf' nts' aux'"
    unfolding \<eta>_def meval.simps \<gamma>'_def \<beta>'_def aux'_def buf'_def nts'_def tuple_def xs_def ys_def Let_def
    by (auto split: prod.splits)

  have pred_mapping:
    "pred_mapping (\<lambda>i. i \<le> j) P"
    "pred_mapping (\<lambda>i. i \<le> j + \<delta>) P'"
    "rel_mapping (\<le>) P P'"
    using MTrigger.prems(2)
    by auto

  from MTrigger.prems(2) have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [min (progress \<sigma> P \<gamma> j) (progress \<sigma> P \<beta> j)..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts
    unfolding wf_ts_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_le[THEN min.coboundedI1] list.rel_map
      intro!: list_all2_appendI list.rel_refl)

  have wf_buf_ts:
    "wf_mbuf2' \<sigma> P' V (j + \<delta>) n R \<gamma> \<beta> buf'"
    "wf_ts \<sigma> P' (j + \<delta>) \<gamma> \<beta> nts'"
    using mbuf2T_take_add'[OF tuple_eq[unfolded tuple_def] pred_mapping buf nts_snoc \<gamma>_props(2) \<beta>_props(2)]
    by auto

  have \<alpha>_\<gamma>_props: "Formula.fv \<alpha> = Formula.fv \<gamma>" "progress \<sigma> P \<alpha> j = progress \<sigma> P \<gamma> j"
  "progress \<sigma> P' \<alpha> j = progress \<sigma> P' \<gamma> j" for j
    using pos
    by (simp_all split: if_splits)

  have update: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (zs, aux')) (Progress.progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)) \<and>
  list_all2 (\<lambda>i. qtable n (Formula.fv \<alpha> \<union> Formula.fv \<beta>) (mem_restr R)
    (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
    [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (formula.Trigger \<alpha> I \<beta>) (j + \<delta>)] (fst (zs, aux'))"
  unfolding progress_simps \<alpha>_\<gamma>_props
  proof (rule mbuf2T_take_add_induct'[where j=j and j'="j + \<delta>" and z'="(zs, aux')",
      OF tuple_eq[unfolded tuple_def] wf_envs_P_simps[OF MTrigger.prems(2)] buf nts_snoc],
      goal_cases xs ys _ base step)
    case xs
    then show ?case using \<gamma>_props(2) by auto
  next
    case ys
    then show ?case using \<beta>_props(2) by auto
  next
    case base
    then show ?case
      using aux \<alpha>_\<gamma>_props
      unfolding progress_simps 
      by auto
  next
    case (step k X Y acc)
    define zs where "zs = fst acc"
    define aux where "aux = snd acc"
    have z_eq: "acc = (zs, aux)"
      unfolding zs_def aux_def
      by auto

    have table:
      "table (args_n args) (args_L args) X"
      "table (args_n args) (args_R args) Y"
      using step(4-5) args_n args_L args_R
      unfolding qtable_def
      by auto

    define zs' where "zs' = fst (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux))"
    define aux' where "aux' = snd (let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux))"
    define cur' where "cur' = \<tau> \<sigma> k"

    have wf_trigger: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux k"
      using step(6)
      unfolding aux_def
      by auto
    then have fv_subset: "fv \<gamma> \<subseteq> fv \<beta> "
      unfolding wf_trigger_aux_def
      by auto

    have wf_trigger_aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (update_mtaux args (\<tau> \<sigma> k) X Y aux) (Suc k)"
      using update_trigger[OF wf_trigger step(4-5) args_n args_L args_R]
      by auto

    then obtain auxlist' where
      valid_mtaux: "valid_mtaux args (\<tau> \<sigma> k) (update_mtaux args (\<tau> \<sigma> k) X Y aux) (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')" and
      sorted_wrt: "sorted_wrt (\<lambda>x y. fst x \<le> fst y) auxlist'" and
      auxlist_len: "length auxlist' = Suc k" and
      auxlist_props: "(\<forall>(i, t, l, r)\<in>set (zip [0..<length auxlist'] auxlist').
         Suc k \<noteq> 0 \<and>
         t = \<tau> \<sigma> i \<and>
         t \<le> \<tau> \<sigma> k \<and>
         qtable (args_n args) (fv \<gamma>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<gamma>) l \<and>
         qtable (args_n args) (fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i \<beta>) r
      )" and
      auxlist_mem: "(\<forall>i.
          Suc k \<noteq> 0 \<and>
          i \<le> k
          \<longrightarrow>
          (\<exists>X. (\<tau> \<sigma> i, X) = auxlist'!i)
      )"
      unfolding wf_trigger_aux_def
      by auto

    then have sorted: "sorted (map fst auxlist')"
      using sorted_wrt
      by (simp add: sorted_map)
    have "\<exists>X. (\<tau> \<sigma> k, X) \<in> set auxlist'"
      using auxlist_mem auxlist_len
      by (metis Zero_not_Suc less_Suc_eq_le nth_mem order_refl)
    then obtain X_tmp where "(\<tau> \<sigma> k, X_tmp) \<in> set (filter (\<lambda>(t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"
      using args_ivl mem0
      by auto
    then have non_empty: "(length (filter (\<lambda> (t, _). mem (args_ivl args) (\<tau> \<sigma> k - t)) auxlist') > 0)"
      using length_pos_if_in_set[of "(\<tau> \<sigma> k, X_tmp)"]
      by auto
    
    have "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> (snd (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux)))
 (Suc k)"
      using wf_trigger_aux
      unfolding z_eq Let_def
      by (auto split: prod.splits)
    moreover have "list_all2
    (\<lambda>i. qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
    [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]
    (fst (case acc of (zs, aux) \<Rightarrow> let aux = update_mtaux args (\<tau> \<sigma> k) X Y aux; (fv_z, z) = result_mtaux args aux in (zs @ [z], aux)))"
    proof -
      have aux'_eq: "aux' = update_mtaux args (\<tau> \<sigma> k) X Y aux"
        unfolding aux'_def Let_def
        by (auto split: prod.splits)
      define fv_z where "fv_z = fst (result_mtaux args aux')"
      define z where "z = snd (result_mtaux args aux')"
      define auxlist'' where "auxlist'' = (filter (\<lambda>(t, _). memR (args_ivl args) (\<tau> \<sigma> k - t)) auxlist')"

      have valid_mtaux': "valid_mtaux args (\<tau> \<sigma> k) aux' auxlist''"
        unfolding aux'_eq auxlist''_def
        using valid_mtaux
        by auto
      have z_eq: "z = snd (trigger_results args (\<tau> \<sigma> k) auxlist'')"
        unfolding z_def
        using valid_result_mtaux[OF valid_mtaux']
        by (auto)

      have equiv: "(x \<in> z) =
         Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>)" if
          restr: "mem_restr R x" and
          wf_x: "wf_tuple (args_n args) (args_R args) x"
        for x
        unfolding z_eq auxlist''_def
        using trigger_sat_equiv[OF restr wf_x pos args_n args_ivl args_L args_R fvi_subset fv_l_n valid_mtaux sorted_wrt auxlist_len auxlist_props auxlist_mem non_empty]
        by auto

      have filter_inv: "(filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist'') = (filter (\<lambda> (t, _). mem (args_ivl args) ((\<tau> \<sigma> k) - t)) auxlist')"
        unfolding auxlist''_def filter_filter
        by (metis (mono_tags, lifting) case_prod_beta')

      have "result_mtaux args aux' = trigger_results args cur' auxlist''"
        using valid_result_mtaux[OF valid_mtaux]
        unfolding aux'_def cur'_def auxlist''_def
        by auto
      moreover have "(length (filter (\<lambda> (t, _). mem (args_ivl args) (cur' - t)) auxlist'') > 0)"
        using filter_inv non_empty
        unfolding cur'_def auxlist''_def
        by auto
      ultimately have z_eq': "z = {
        tuple. wf_tuple (args_n args) (args_R args) tuple \<and>
          (\<forall>i \<in> {0..<(length auxlist'')}.
            let (t, l, r) = auxlist''!i in
            mem (args_ivl args) (cur' - t) \<longrightarrow> 
            (
              tuple \<in> r \<or>
              (\<exists>j \<in> {i<..<(length auxlist'')}.
                join_cond (args_pos args) ((fst o snd) (auxlist''!j)) (proj_tuple (join_mask (args_n args) (args_L args)) tuple)
              )
            )
          )
        }"
        unfolding z_def
        by auto

      have args_R_simp: "args_R args = fv \<alpha> \<union> fv \<beta>"
        using args_L args_R pos fvi_subset
        by (auto split: if_splits)
      have table: "table n (fv \<alpha> \<union> fv \<beta>) z"
        using z_eq'
        unfolding table_def args_R_simp args_n
        by auto

      have correctness: "(\<And>x. x \<in> z \<Longrightarrow> wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>))"
        using equiv args_props
        by auto

      have completeness: "\<And>x. wf_tuple n (fv \<alpha> \<union> fv \<beta>) x \<Longrightarrow> mem_restr R x \<Longrightarrow> Formula.sat \<sigma> V (map the x) k (formula.Trigger \<alpha> I \<beta>) \<Longrightarrow> x \<in> z"
        using equiv args_props
        by auto

      have qtable_k: "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) k (formula.Trigger \<alpha> I \<beta>)) z"
        using qtableI[OF table correctness completeness]
        by auto

      have zs'_eq: "zs' = zs @ [z]"
        unfolding zs'_def z_def aux'_eq  Let_def
        by (auto split: prod.splits)

      have IH: "list_all2
        (\<lambda>i. qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)))
        [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs"
        using step(6) zs_def args_props(3)
        by auto
      then have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
        unfolding list_all2_iff
        by auto
      then have len: "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] = length zs'"
        unfolding zs'_eq length_append
        by (simp add: step(1))

      moreover have "(\<forall>(i, r) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs').
      qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r)"
      proof -
        {
          fix i r
          assume assm: "(i, r) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k] zs')"
          
          have "length [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] = length zs"
            using step(6) zs_def
            unfolding list_all2_iff
            by auto
          moreover have "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] @ [k] =
                         [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]"
            by (simp add: step(1))
          ultimately have zip_eq:
            "zip ([min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<Suc k]) zs' =
             zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs @ zip [k] [z]"
            unfolding zs'_eq
            using zip_append[of "[min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k]" "zs" "[k]" "[z]"]
            by auto
          {
            assume "(i, r) \<in> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
            then have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              using step(6) args_props(3) zs_def
              unfolding list_all2_iff
              by auto
          }
          moreover {
            assume "(i, r) \<notin> set (zip [min (Progress.progress \<sigma> P \<gamma> j) (Progress.progress \<sigma> P \<beta> j)..<k] zs)"
            then have "(i, r) = (k, z)"
              using assm zip_eq
              by auto
            then have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
              using qtable_k
              by auto
          }
          ultimately have "qtable n (fv \<alpha> \<union> fv \<beta>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> V (map the v) i (formula.Trigger \<alpha> I \<beta>)) r"
            by blast
        }
        then show ?thesis by auto
      qed

      ultimately show ?thesis
        unfolding list_all2_iff zs'_def zs_def aux_def
        by (auto split: prod.splits)
    qed

    ultimately show ?case using args_props(3) by auto
  qed (auto)

  have aux: "wf_trigger_aux \<sigma> V R args \<gamma> \<beta> aux' (progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>))"
    using update
    by auto

  have "wf_mformula \<sigma> (j + \<delta>) P' V n R \<eta> (formula.Trigger \<alpha> I \<beta>)"
    unfolding \<eta>_eq
    using wf_mformula.Trigger_0[OF \<beta>_props(1) pos \<gamma>_props(1) pos_eq args_ivl 
        args_n args_L args_R fv_l_n mem0 fvi_subset wf_buf_ts aux]
    by auto

  moreover have "list_all2 (\<lambda>i. qtable n (FV (\<alpha> \<^bold>T I \<beta>)) (mem_restr R) (\<lambda>v. \<langle>\<sigma>, V, v, i\<rangle> \<Turnstile>\<^sub>M \<alpha> \<^bold>T I \<beta>))
    [progress \<sigma> P (formula.Trigger \<alpha> I \<beta>) j..<progress \<sigma> P' (\<alpha> \<^bold>T I \<beta>) (j + \<delta>)] zs"
    using update
    by auto

  ultimately show ?case
    unfolding zs_def \<eta>_def phi'_eq
    by auto
next
  case (MMatchP I mr mrs \<phi>s buf nts aux)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del]
  from MMatchP.prems obtain r \<psi>s where eq: "\<phi>' = Formula.MatchP I r"
    and safe: "Regex.safe_regex fv rgx_safe_pred Past Strict r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (RPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and nts: "wf_ts_regex \<sigma> P j r nts"
    and aux: "wf_matchP_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchP I r) j)"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MMatchP.prems(3) have wty: "\<forall>\<psi>\<in>set \<psi>s. S, E \<turnstile> \<psi>"
    using mr apply (cases pred: wty_formula) apply(auto simp: eq) 
    using pred_regex_wty_formula to_mregex_safe_atms by blast
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i) [progress_regex \<sigma> P r j..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_regex_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_regex_le[OF MMatchP.prems(2)] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  have update: "wf_matchP_aux \<sigma> V n R I r (snd (zs, aux')) (progress \<sigma> P' (Formula.MatchP I r) (j + \<delta>)) \<and>
    list_all2 (\<lambda>i. qtable n (Formula.fv_regex r) (mem_restr R)
      (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.MatchP I r)))
      [progress \<sigma> P (Formula.MatchP I r) j..<progress \<sigma> P' (Formula.MatchP I r) (j + \<delta>)] (fst (zs, aux'))"
    if eval: "map (fst o meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db) \<phi>s = xss"
      and eq: "mbufnt_take (\<lambda>rels t (zs, aux).
        case update_matchP n I mr mrs rels t aux of (z, x) \<Rightarrow> (zs @ [z], x))
        ([], aux) (mbufn_add xss buf) 0 (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) = ((zs, aux'), buf', nt, nts')"
    for xss zs aux' buf' nt nts'
    unfolding progress_simps
  proof (rule mbufnt_take_add_induct'[where j'="j + \<delta>" and z'="(zs, aux')", OF eq wf_envs_P_simps[OF MMatchP.prems(2)] safe mr buf nts_snoc],
      goal_cases xss _ base step)
    case xss
    then show ?case
      using eval \<psi>s wty
      by (auto simp: list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map
          list.rel_flip[symmetric, of _ \<psi>s \<phi>s] dest!: MMatchP.IH(1)[OF _ _ MMatchP.prems(2)]
          elim!: list.rel_mono_strong split: prod.splits)
  next
    case base
    then show ?case
      using aux by auto
  next
    case (step k Xs z)
    then show ?case
      by (auto simp: Un_absorb1 mrs safe mr elim!: update_matchP(1) list_all2_appendI
          dest!: update_matchP(2) split: prod.split)
  qed simp
  then show ?case using \<psi>s wty
    by (auto simp: eq mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
        list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map intro!: wf_mformula.intros
        elim!: list.rel_mono_strong mbufnt_take_add'(1)[OF _ wf_envs_P_simps[OF MMatchP.prems(2)] safe mr buf nts_snoc]
        mbufnt_take_add'(2)[OF _ wf_envs_P_simps[OF MMatchP.prems(2)] safe mr buf nts_snoc]
        dest!: MMatchP.IH[OF _ _ MMatchP.prems(2)] split: prod.splits)
next
  case (MMatchF I mr mrs \<phi>s buf nts t aux)
  note sat.simps[simp del] mbufnt_take.simps[simp del] mbufn_add.simps[simp del] progress_simps[simp del]
  from MMatchF.prems obtain r \<psi>s where eq: "\<phi>' = Formula.MatchF I r"
    and safe: "Regex.safe_regex fv rgx_safe_pred Futu Strict r"
    and mr: "to_mregex r = (mr, \<psi>s)"
    and mrs: "mrs = sorted_list_of_set (LPDs mr)"
    and \<psi>s: "list_all2 (wf_mformula \<sigma> j P V n R) \<phi>s \<psi>s"
    and buf: "wf_mbufn' \<sigma> P V j n R r buf"
    and nts: "wf_ts_regex \<sigma> P j r nts"
    and aux: "wf_matchF_aux \<sigma> V n R I r aux (progress \<sigma> P (Formula.MatchF I r) j) 0"
    and t: "t = (if j = 0 then 0 else \<tau> \<sigma> (min (j - 1) (progress_regex \<sigma> P r j)))"
    and length_aux: "progress \<sigma> P (Formula.MatchF I r) j + length aux = progress_regex \<sigma> P r j"
    by (cases rule: wf_mformula.cases)
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  from MMatchF.prems(3) have wty: "\<forall>\<psi>\<in>set \<psi>s. S, E \<turnstile> \<psi>"
    using mr apply (cases pred: wty_formula) apply(auto simp: eq) 
    using pred_regex_wty_formula to_mregex_safe_atms by blast
  have nts_snoc: "list_all2 (\<lambda>i t. t = \<tau> \<sigma> i)
    [progress_regex \<sigma> P r j..< j + \<delta>] (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>])"
    using nts unfolding wf_ts_regex_def
    by (subst upt_add_eq_append) (auto simp add: wf_envs_progress_regex_le[OF MMatchF.prems(2)] list.rel_map
      intro!: list_all2_appendI list.rel_refl)
  {
    fix xss zs aux' aux'' buf' nts' nt
    assume eval: "map (fst o meval (j + \<delta>) n (map (\<tau> \<sigma>) [j ..< j + \<delta>]) db) \<phi>s = xss"
      and eq1: "mbufnt_take (update_matchF n I mr mrs) aux (mbufn_add xss buf) t (nts @ map (\<tau> \<sigma>) [j ..< j + \<delta>]) =
        (aux', buf', nt, nts')"
      and eq2: "eval_matchF I mr nt aux' = (zs, aux'')"
    note nt_def = mbufnt_take_nt[OF eq1]
    have update1: "wf_matchF_aux \<sigma> V n R I r aux' (progress \<sigma> P (Formula.MatchF I r) j) 0 \<and>
      progress \<sigma> P (Formula.MatchF I r) j + length aux' = progress_regex \<sigma> P' r (j + \<delta>)"
      using eval nts_snoc nts_snoc length_aux aux \<psi>s wty
      by (elim mbufnt_take_add_induct'[where j'="j + \<delta>", OF eq1 wf_envs_P_simps[OF MMatchF.prems(2)] safe mr buf])
        (auto simp: length_update_matchF
          list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
          dest!: MMatchF.IH[OF _ _ MMatchF.prems(2)]
          elim: wf_update_matchF[OF _ safe mr mrs] elim!: list.rel_mono_strong)
    from MMatchF.prems(2) have nts': "wf_ts_regex \<sigma> P' (j + \<delta>) r nts'"
      using eval eval nts_snoc \<psi>s wty
      unfolding wf_ts_regex_def
      apply (intro mbufnt_take_eqD(2)[OF eq1 wf_mbufn_add[where js'="map (\<lambda>\<phi>. progress \<sigma> P' \<phi> (j + \<delta>)) \<psi>s",
              OF buf[unfolded wf_mbufn'_def mr prod.case]]])
      apply (auto simp: to_mregex_progress[OF safe mr] Mini_def
          list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
          list_all2_Cons1 elim!: list.rel_mono_strong intro!: list.rel_refl_strong
          dest!: MMatchF.IH[OF _ _ MMatchF.prems(2)])
      apply (auto simp: list_all2_conv_all_nth)
      done
    have nt: "nt = (if j + \<delta> = 0 then 0 else \<tau> \<sigma> (min (j + \<delta> - 1) (progress_regex \<sigma> P' r (j + \<delta>))))"
      using nts nts' unfolding nt_def t
      apply (auto simp: hd_append hd_rev last_map wf_ts_regex_def)
      using list_all2_hdD(1) list_all2_hdD(2) apply fastforce
      using list_all2_lastD apply fastforce
        apply (metis (mono_tags) list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
       apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      apply (metis (mono_tags, lifting) add_gr_0 list_all2_hdD(1) list_all2_hdD(2) min.absorb2 Suc_diff_Suc diff_zero less_Suc_eq_le)
      done
    have "i \<le> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>) \<Longrightarrow>
      wf_matchF_aux \<sigma> V n R I r aux' i 0 \<Longrightarrow>
      i + length aux' = progress_regex \<sigma> P' r (j + \<delta>) \<Longrightarrow>
      wf_matchF_aux \<sigma> V n R I r aux'' (progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)) 0 \<and>
        i + length zs = progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>) \<and>
        i + length zs + length aux'' = progress_regex \<sigma> P' r (j + \<delta>) \<and>
        list_all2 (\<lambda>i. qtable n (Formula.fv_regex r) (mem_restr R)
          (\<lambda>v. Formula.sat \<sigma> V (map the v) i (Formula.MatchF I r)))
          [i..<i + length zs] zs" for i
      using eq2
    proof (induction aux' arbitrary: zs aux'' i)
      case Nil
      then show ?case by (auto dest!: antisym[OF progress_MatchF_le])
    next
      case (Cons a aux')
      obtain t rels rel where "a = (t, rels, rel)" by (cases a)
      from Cons.prems(2) have aux': "wf_matchF_aux \<sigma> V n R I r aux' (Suc i) 0"
        by (rule wf_matchF_aux_Cons)
      from Cons.prems(2) have 1: "t = \<tau> \<sigma> i"
        unfolding \<open>a = (t, rels, rel)\<close> by (rule wf_matchF_aux_Cons1)
      from Cons.prems(2) have 3: "qtable n (Formula.fv_regex r) (mem_restr R) (\<lambda>v.
        (\<exists>j\<ge>i. j < Suc (i + length aux') \<and> mem I ((\<tau> \<sigma> j - \<tau> \<sigma> i)) \<and> Regex.match (Formula.sat \<sigma> V (map the v)) r i j)) rel"
        unfolding \<open>a = (t, rels, rel)\<close> using wf_matchF_aux_Cons3 by force
      from Cons.prems(3) have Suc_i_aux': "Suc i + length aux' = progress_regex \<sigma> P' r (j + \<delta>)"
        by simp
      have "i \<ge> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)"
        if "memR I (nt - t)"
        using that nts' unfolding wf_ts_regex_def progress_simps nt
        by (auto simp add: 1 list_all2_Cons2 upt_eq_Cons_conv
          intro!: cInf_lower \<tau>_mono diff_le_mono simp del: upt_Suc split: if_splits list.splits)
      moreover
      have "Suc i \<le> progress \<sigma> P' (Formula.MatchF I r) (j + \<delta>)"
        if "\<not> memR I (nt - t)"
      proof -
        have \<tau>_min:  "\<tau> \<sigma> (min (j + \<delta> - 1) k) = min (\<tau> \<sigma> (j + \<delta> - 1) ) (\<tau> \<sigma> k)" for k
          by (simp add: min_of_mono monoI)
        have le_progress_iff[simp]: "j + \<delta> \<le> progress \<sigma> P' \<phi> (j + \<delta>) \<longleftrightarrow> progress \<sigma> P' \<phi> (j + \<delta>) = (j + \<delta>)" for \<phi> :: "'t Formula.formula"
          using wf_envs_progress_le[OF MMatchF.prems(2), of \<phi>] by auto
        have min_Suc[simp]: "min j (j + \<delta>) = j" by auto
        let ?X = "{i. \<forall>k. k < j + \<delta> \<and> k \<le> progress_regex \<sigma> P' r (j + \<delta>) \<longrightarrow> memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)}"
        let ?min = "min (j + \<delta> - 1) (progress_regex \<sigma> P' r (j + \<delta>))"
        have "\<tau> \<sigma> ?min \<le> \<tau> \<sigma> (j + \<delta>)"
          by (rule \<tau>_mono) auto
        from that have "?X \<noteq> {}"
          by (auto intro!: exI[of _ "progress_regex \<sigma> P' r (j + \<delta>)"])
        show ?thesis
          using that nts' wf_envs_progress_regex_le[OF MMatchF.prems(2), of r]
          unfolding wf_ts_regex_def progress_simps nt
          by (intro cInf_greatest[OF \<open>?X \<noteq> {}\<close>])
            (auto 0 3 simp: 1 list_all2_Cons2 upt_eq_Cons_conv
              simp del: upt_Suc split: list.splits if_splits
              dest!: spec[of _ "?min"]
              intro!: diff_le_mono diff_le_mono2 order_trans[OF diff_le_mono diff_le_mono2] \<tau>_mono
              elim!: contrapos_np[of _ "Suc i \<le> _"])
      qed
      moreover have *: "k < progress_regex \<sigma> P' r (j + \<delta>)" if
        "\<not> memR I (nt - \<tau> \<sigma> i)"
        "memR I (\<tau> \<sigma> k - \<tau> \<sigma> i)" for k
        using that nts' unfolding wf_ts_regex_def nt
        by (auto simp: list_all2_Cons2 upt_eq_Cons_conv
          simp del: upt_Suc split: list.splits if_splits
          elim!: contrapos_np[of _ "k < _"] intro!: diff_le_mono diff_le_mono2)
      ultimately show ?case using Cons.prems Suc_i_aux'[simplified]
        unfolding \<open>a = (t, rels, rel)\<close>
        by (auto simp: 1 sat.simps upt_conv_Cons dest!: Cons.IH[OF _ aux' Suc_i_aux']
            simp del: upt_Suc split: if_splits prod.splits intro!: iff_exI qtable_cong[OF 3 refl])

    qed
    note conjI[OF nt this[OF progress_mono_gen[OF le_add1] conjunct1[OF update1] conjunct2[OF update1]]]
  }
  note update = this[OF refl, rotated]
  from MMatchF.prems(2) show ?case using \<psi>s wty
    by (auto simp: eq mr mrs safe map_split_alt list.rel_flip[symmetric, of _ \<psi>s \<phi>s]
        list_all3_map map2_map_map list_all3_list_all2_conv list.rel_map Let_def
        intro!: wf_mformula.intros
        elim!: list.rel_mono_strong mbufnt_take_add'(1)[OF _ wf_envs_P_simps[OF MMatchF.prems(2)] safe mr buf nts_snoc]
        mbufnt_take_add'(2)[OF _ wf_envs_P_simps[OF MMatchF.prems(2)] safe mr buf nts_snoc]
        dest!: MMatchF.IH[OF _ _ MMatchF.prems(2)] update split: prod.splits)

next
  case (MTP mt i)
  then obtain t where "\<forall>x\<in>fv_trm t. x < n" "Formula.is_Var t \<or> Formula.is_Const t"
    "mt = mtrm_of_trm t" "\<phi>' = Formula.TP t" "i = j"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  then show ?case
    by (auto simp add: list.rel_map intro!: wf_mformula.MTP list.rel_refl qtable_eval_mtrm)
next
  case (MTS mt)
  then obtain t where "\<forall>x\<in>fv_trm t. x < n" "Formula.is_Var t \<or> Formula.is_Const t"
    "mt = mtrm_of_trm t" "\<phi>' = Formula.TS t"
    by (cases rule: wf_mformula.cases) 
      (auto dest: wf_mformula_and_release_safe_bddE wf_mformula_and_release_safe0E)
  then show ?case
    by (auto simp add: list.rel_map intro!: wf_mformula.MTS list.rel_refl qtable_eval_mtrm)
qed

unbundle MFODL_no_notation


subsection \<open> Correct step \<close>

lemma wty_db_empty: "wty_db S {}"
  by (simp add: wty_db_def)

lemma prefix_of_wty_trace:
  assumes "wty_trace S \<sigma>" and "prefix_of \<pi> \<sigma>"
  shows "wty_prefix S \<pi>"
proof -
  from assms(1) have "\<forall>i. wty_db S (\<Gamma> \<sigma> i)"
    by (simp add: wty_envs_def wty_db_def)
  with assms(2) show ?thesis
    by (transfer fixing: S) (metis in_set_conv_nth stake_nth)
qed

lemma ex_prefix_of_wty:
  assumes "wty_prefix S p"
  shows "\<exists>s. prefix_of p s \<and> wty_trace S s"
proof -
  from assms have "\<exists>s. prefix_of p s \<and> (\<forall>i. wty_db S (\<Gamma> s i))"
    proof (transfer fixing: S, intro bexI CollectI conjI)
    fix p :: "((string8 \<times> event_data list) set \<times> nat) list"
    assume *: "sorted (map snd p)"
    let ?\<sigma> = "p @- smap (Pair {}) (fromN (snd (last p)))"
    show "stake (length p) ?\<sigma> = p" by (simp add: stake_shift)
    assume "\<forall>x\<in>set p. wty_db S (fst x)"
    then show "\<forall>i. wty_db S (fst (snth ?\<sigma> i))"
      by (simp add: shift_snth wty_db_empty)
    have le_last: "snd (p ! i) \<le> snd (last p)" if "i < length p" for i
      using sorted_nth_mono[OF *, of i "length p - 1"] that
      by (cases p) (auto simp: last_conv_nth nth_Cons')
    with * show "ssorted (smap snd ?\<sigma>)"
      by (force simp: ssorted_iff_mono sorted_iff_nth_mono shift_snth)
    show "sincreasing (smap snd ?\<sigma>)"
    proof (rule sincreasingI)
      fix x
      have "x < snth (smap snd ?\<sigma>) (Suc (length p + x))"
        by simp (metis Suc_pred add.commute diff_Suc_Suc length_greater_0_conv less_add_Suc1 less_diff_conv)
      then show "\<exists>i. x < snth (smap snd ?\<sigma>) i" ..
    qed
  qed
  then show ?thesis by (auto simp: wty_envs_def wty_db_def)
qed

lemma (in maux) wf_mstate_mstep:
  assumes "wf_mstate S E \<phi> \<pi> R st" and "wty_db S (fst tdb)" and  "last_ts \<pi> \<le> snd tdb"
  shows "wf_mstate S E \<phi> (psnoc \<pi> tdb) R (snd (mstep (apfst mk_db tdb) st))"
proof -
  from assms(1) have "mstate_i st \<le> plen \<pi>"
    using ex_prefix_of_wty
    unfolding wf_mstate_def
    by (metis progress_le)
  with assms show ?thesis
    unfolding wf_mstate_def mstep_def
    by (force simp: progress_mono le_imp_diff_is_add pts_psnoc length_pts_eq_plen add.commute
        split: prod.splits intro!:wty_psnoc  
        elim!: prefix_of_psnocE dest: meval_correct[OF _ wf_envs_mk_db] list_all2_lengthD)
qed

definition "flatten_verdicts Vs = (\<Union> (set (map (\<lambda>(i, t, X). (\<lambda>v. (i, t, v)) ` X) Vs)))"

lemma flatten_verdicts_append[simp]:
  "flatten_verdicts (Vs @ Us) = flatten_verdicts Vs \<union> flatten_verdicts Us"
  unfolding flatten_verdicts_def by simp

lemma (in maux) mstep_output_iff:
  assumes "wf_mstate S E \<phi> \<pi> R st" "last_ts \<pi> \<le> snd tdb" "prefix_of (psnoc \<pi> tdb) \<sigma>" "wty_trace S \<sigma>" "mem_restr R v"
  shows "(i, t, v) \<in> flatten_verdicts (fst (mstep (apfst mk_db tdb) st)) \<longleftrightarrow>
    progress \<sigma> Map.empty \<phi> (plen \<pi>) \<le> i \<and> i < progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>)) \<and> t = \<tau> \<sigma> i \<and>
    wf_tuple (Formula.nfv \<phi>) (Formula.fv \<phi>) v \<and> Formula.sat \<sigma> Map.empty (map the v) i \<phi>"
  (is "?L \<longleftrightarrow> ?R")
proof -
  let ?p = "progress \<sigma> Map.empty \<phi> (plen \<pi>)"
  let ?p' = "progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>))"
  from prefix_of_psnocE[OF assms(3,2)] have "prefix_of \<pi> \<sigma>"
    and tdb_eqs: "\<Gamma> \<sigma> (plen \<pi>) = fst tdb" "\<tau> \<sigma> (plen \<pi>) = snd tdb" by auto
  from assms(1, 4) \<open>prefix_of \<pi> \<sigma>\<close> have
    state_eqs:
    "mstate_n st = Formula.nfv \<phi>" "mstate_j st = plen \<pi>"
    "mstate_i st = ?p" "mstate_t st = drop ?p (pts \<pi>)"
    and wf_m: "wf_mformula \<sigma> (plen \<pi>) Map.empty Map.empty (Formula.nfv \<phi>) R (mstate_m st) \<phi>" and
    wty: "S, E \<turnstile> \<phi>"
    unfolding wf_mstate_def by auto
  from meval_correct[OF wf_m wf_envs_mk_db[OF assms(4)] wty]
  obtain Vs st' where
    meval_eq: "meval (Suc (plen \<pi>)) (Formula.nfv \<phi>) [snd tdb] (mk_db (fst tdb)) (mstate_m st) = (Vs, st')"
    and wf_m': "wf_mformula \<sigma> (Suc (plen \<pi>)) Map.empty Map.empty (Formula.nfv \<phi>) R st' \<phi>"
    and "list_all2 (\<lambda>i. qtable (Formula.nfv \<phi>) (fv \<phi>) (mem_restr R) (\<lambda>v. Formula.sat \<sigma> Map.empty (map the v) i \<phi>))
      [progress \<sigma> Map.empty \<phi> (plen \<pi>)..<progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>))] Vs"
    by (auto simp add: tdb_eqs state_eqs)
  then have
    length_Vs: "length Vs = ?p' - ?p"
    and set_Vs: "\<forall>i < ?p'-?p. v \<in> Vs ! i \<longleftrightarrow>
      wf_tuple (Formula.nfv \<phi>) (Formula.fv \<phi>) v \<and> Formula.sat \<sigma> Map.empty (map the v) (?p + i) \<phi>"
    using assms(5)
    by (auto simp add: list_all2_conv_all_nth in_set_conv_nth elim!: in_qtableE in_qtableI)
  have \<tau>_eq: "(drop ?p (pts \<pi>) @ [snd tdb]) ! (i - ?p) = \<tau> \<sigma> i" if "?p \<le> i" "i < ?p'"
  proof (cases "i = plen \<pi>")
    case True
    then show ?thesis
      by (auto simp add: nth_append length_pts_eq_plen tdb_eqs)
  next
    case False
    with that(2) have "i < plen \<pi>"
      by (metis less_trans_Suc linorder_not_less nat_neq_iff progress_le)
    with that(1) show ?thesis
      by (auto simp add: nth_append length_pts_eq_plen nth_pts_eq_\<tau>[OF \<open>prefix_of \<pi> \<sigma>\<close>])
  qed
  show ?thesis
  proof
    assume ?L
    then show ?R
      unfolding flatten_verdicts_def mstep_def using set_Vs \<tau>_eq
      by (auto simp add: in_set_enumerate_eq state_eqs meval_eq length_pts_eq_plen length_Vs
          split: prod.splits)
  next
    assume ?R
    then have "i \<le> plen \<pi>"
      by (metis Suc_leI Suc_le_mono le_trans progress_le)
    with \<open>?R\<close> show ?L
      unfolding flatten_verdicts_def mstep_def using set_Vs \<tau>_eq
      by (auto simp add: in_set_enumerate_eq state_eqs meval_eq length_pts_eq_plen length_Vs
          min_add_distrib_left split: prod.splits 
          intro!: bexI[where x="(i, \<tau> \<sigma> i, Vs ! (i - ?p))"])
  qed
qed


section \<open> Specification \<close>

definition pprogress :: "'t Formula.formula \<Rightarrow> Formula.prefix \<Rightarrow> nat" where
  "pprogress \<phi> \<pi> = (THE n. \<forall>\<sigma>. prefix_of \<pi> \<sigma> \<longrightarrow> progress \<sigma> Map.empty \<phi> (plen \<pi>) = n)"

lemma pprogress_eq: "prefix_of \<pi> \<sigma> \<Longrightarrow> pprogress \<phi> \<pi> = progress \<sigma> Map.empty \<phi> (plen \<pi>)"
  unfolding pprogress_def using progress_prefix_conv
  by blast

locale wty_mfodl =
  fixes \<phi> :: "ty Formula.formula" and SIG :: sig and ENV :: tyenv
  assumes well_typed: "SIG, ENV \<turnstile> \<phi>"
begin

definition "traces = {\<sigma>. wty_trace SIG \<sigma>}"

sublocale traces_downward_closed traces
  by unfold_locales (auto simp add: traces_def wty_envs_def)

end

locale future_bounded_mfodl = wty_mfodl +
   assumes future_bounded: "Safety.future_bounded \<phi>"

sublocale future_bounded_mfodl \<subseteq> sliceable_timed_progress "Formula.nfv \<phi>" "Formula.fv \<phi>" traces "relevant_events \<phi>"
  "\<lambda>\<sigma> v i. Formula.sat \<sigma> Map.empty v i \<phi>" "pprogress \<phi>"
proof (unfold_locales, goal_cases)
  case (1 \<pi>' \<pi>)
  moreover obtain \<sigma> where "prefix_of \<pi>' \<sigma>"
    using ex_prefix_of ..
  moreover have "prefix_of \<pi> \<sigma>"
    using prefix_of_antimono[OF \<open>\<pi> \<le> \<pi>'\<close> \<open>prefix_of \<pi>' \<sigma>\<close>] .
  ultimately show ?case
    by (simp add: pprogress_eq plen_mono progress_mono)
next
  case (2 \<sigma> x)
  obtain j where "x \<le> progress \<sigma> Map.empty \<phi> j"
    using future_bounded progress_ge by blast
  then have "x \<le> pprogress \<phi> (take_prefix j \<sigma>)"
    by (simp add: pprogress_eq[of _ \<sigma>])
  then show ?case by force
next
  case (3 \<sigma> \<pi> \<sigma>' i v)
  then have "i < progress \<sigma> Map.empty \<phi> (plen \<pi>)"
    by (simp add: pprogress_eq)
  with 3 show ?case
    using sat_prefix_conv by blast
next
  case (4 \<pi> \<pi>')
  then have "plen \<pi> = plen \<pi>'"
    unfolding length_pts_eq_plen[symmetric] by auto
  moreover obtain \<sigma> \<sigma>' where "prefix_of \<pi> \<sigma>" "prefix_of \<pi>' \<sigma>'"
    using ex_prefix_of by blast+
  moreover have "\<forall>i < plen \<pi>. \<tau> \<sigma> i = \<tau> \<sigma>' i"
    using 4 calculation nth_pts_eq_\<tau>[OF calculation(3)] nth_pts_eq_\<tau>[OF calculation(2)]
    by auto
  ultimately show ?case
    by (simp add: pprogress_eq progress_time_conv)
qed

lemma (in future_bounded_mfodl) prefixes_alt: "formula_slicer.prefixes = {\<pi>. wty_prefix SIG \<pi>}"
  unfolding formula_slicer.prefixes_def
  using ex_prefix_of_wty prefix_of_wty_trace
  by (fastforce simp: traces_def)

locale verimon_spec = wty_mfodl +
   assumes monitorable: "mmonitorable \<phi>"

sublocale verimon_spec \<subseteq> future_bounded_mfodl
  using monitorable by unfold_locales (simp add: mmonitorable_def)

context maux
begin

lemma minit_safe_minit: "mmonitorable \<phi> \<Longrightarrow> minit_safe \<phi> = minit \<phi>"
  unfolding minit_safe_def monitorable_formula_code by simp

lemma wf_mstate_minit_safe: "S, E \<turnstile> \<phi> \<Longrightarrow> mmonitorable \<phi> \<Longrightarrow> wf_mstate S E \<phi> pnil R (minit_safe \<phi>)"
  using wf_mstate_minit minit_safe_minit mmonitorable_def by metis

end

locale verimon = verimon_spec + maux

lemma (in verimon) Mt_pnil: "Mt pnil = {}"
  by (simp add: Mt_def M_def pprogress_eq)

lemma (in verimon) fst_M_less_plen: 
  assumes "(i, v) \<in> M \<pi>" 
  shows "i < plen \<pi>"
proof -
  obtain \<sigma> where "prefix_of \<pi> \<sigma>"
    using ex_prefix_of by blast
  then have "pprogress \<phi> \<pi> \<le> plen \<pi>"
    by (simp add: pprogress_eq)
  with assms show ?thesis
    unfolding M_def by simp
qed

lemma (in verimon) mono_monitor': "\<pi>' \<in> formula_slicer.prefixes \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> Mt \<pi> \<subseteq> Mt \<pi>'"
  unfolding Mt_def using mono_monitor[of \<pi>' \<pi>] fst_M_less_plen[of _ _ \<pi>]
  by (auto simp add: nth_pts_prefix_cong dest!: subsetD)

lemma (in verimon) mstep_mverdicts:
  assumes wf: "wf_mstate SIG ENV \<phi> \<pi> R st"
    and wty: "wty_db SIG (fst tdb)"
    and le[simp]: "last_ts \<pi> \<le> snd tdb"
    and restrict: "mem_restr R v"
  shows "(i, t, v) \<in> flatten_verdicts (fst (mstep (apfst mk_db tdb) st)) \<longleftrightarrow>
    (i, t, v) \<in> Mt (psnoc \<pi> tdb) - Mt \<pi>"
proof -
  have "wty_prefix SIG (psnoc \<pi> tdb)"
    using wf wty by (auto simp: wf_mstate_def intro!: wty_psnoc)
  then obtain \<sigma> where p2: "prefix_of (psnoc \<pi> tdb) \<sigma>" and wty_\<sigma>: "wty_trace SIG \<sigma>"
    using ex_prefix_of_wty by blast
  with le have p1: "prefix_of \<pi> \<sigma>" by (blast elim!: prefix_of_psnocE)
  have "i < progress \<sigma> Map.empty \<phi> (Suc (plen \<pi>)) \<Longrightarrow> i < Suc (plen \<pi>)"
    by (metis order.strict_trans2 progress_le)
  then show ?thesis 
    unfolding Mt_def M_def using wty_\<sigma>
    by (auto 0 3 simp: p2 progress_prefix_conv[OF _ p1] sat_prefix_conv[OF _ p1] not_less
        pprogress_eq[OF p1] pprogress_eq[OF p2] nth_pts_eq_\<tau>[OF p1] nth_pts_eq_\<tau>[OF p2]
        image_iff less_Suc_eq traces_def cong: conj_cong
        dest: mstep_output_iff[OF wf le p2 _ restrict, THEN iffD1] spec[of _ \<sigma>]
        mstep_output_iff[OF wf le _ _ restrict, THEN iffD1] progress_sat_cong[OF _ p1]
        intro: mstep_output_iff[OF wf le p2 _ restrict, THEN iffD2] p1)
qed

lemma (in verimon) wf_mstate_msteps: 
  "wf_mstate SIG ENV \<phi> \<pi> R st \<Longrightarrow> mem_restr R v \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> wty_prefix SIG \<pi>' \<Longrightarrow>
  X = msteps (pdrop (plen \<pi>) \<pi>') st \<Longrightarrow> wf_mstate SIG ENV \<phi> \<pi>' R (snd X) \<and>
  ((i, t, v) \<in> flatten_verdicts (fst X)) = ((i, t, v) \<in> Mt \<pi>' - Mt \<pi>)"
proof (induct "plen \<pi>' - plen \<pi>" arbitrary: X st \<pi> \<pi>')
  case 0
  from 0(1,4,5,6) have "\<pi> = \<pi>'"  "X = ([], st)"
    by (transfer; auto)+
  with 0(2) show ?case unfolding flatten_verdicts_def by simp
next
  case (Suc x)
  from Suc(2,5,6) obtain \<pi>'' tdb where "x = plen \<pi>'' - plen \<pi>"  "\<pi> \<le> \<pi>''" "wty_prefix SIG \<pi>''" "wty_db SIG (fst tdb)"
    "\<pi>' = psnoc \<pi>'' tdb" "pdrop (plen \<pi>) (psnoc \<pi>'' tdb) = psnoc (pdrop (plen \<pi>) \<pi>'') tdb"
    "last_ts (pdrop (plen \<pi>) \<pi>'') \<le> snd tdb" "last_ts \<pi>'' \<le> snd tdb"
    "\<pi>'' \<le> psnoc \<pi>'' tdb"
  proof (atomize_elim, transfer, elim exE, goal_cases prefix)
    case (prefix _ _ \<pi>' _ \<pi>_tdb)
    then show ?case
    proof (cases \<pi>_tdb rule: rev_cases)
      case (snoc \<pi> tdb)
      with prefix show ?thesis
        by (intro bexI[of _ "\<pi>' @ \<pi>"] exI[of _ tdb])
          (force simp: sorted_append append_eq_Cons_conv split: list.splits if_splits)+
    qed simp
  qed
  with Suc(1)[OF this(1) Suc.prems(1,2) this(2,3) refl] Suc.prems show ?case
    by (auto simp: msteps_psnoc split_beta mstep_mverdicts
        dest: mono_monitor'[THEN set_mp, rotated, unfolded prefixes_alt] intro!: wf_mstate_mstep)
qed

lemma (in verimon) wf_mstate_msteps_stateless:
  assumes "wf_mstate SIG ENV \<phi> \<pi> R st" "mem_restr R v" "\<pi> \<le> \<pi>'" "wty_prefix SIG \<pi>'"
  shows "(i, t, v) \<in> flatten_verdicts (msteps_stateless (pdrop (plen \<pi>) \<pi>') st) \<longleftrightarrow>
    (i, t, v) \<in> Mt \<pi>' - Mt \<pi>"
  using wf_mstate_msteps[OF assms refl] unfolding msteps_msteps_stateless by simp

lemma (in verimon) wf_mstate_msteps_stateless_UNIV: 
  "wf_mstate SIG ENV \<phi> \<pi> UNIV st \<Longrightarrow> \<pi> \<le> \<pi>' \<Longrightarrow> wty_prefix SIG \<pi>' 
  \<Longrightarrow> flatten_verdicts (msteps_stateless (pdrop (plen \<pi>) \<pi>') st) = Mt \<pi>' - Mt \<pi>"
  by (auto dest: wf_mstate_msteps_stateless[OF _ mem_restr_UNIV])

lemma (in verimon) monitor_mverdicts: 
  "wty_prefix SIG \<pi> \<Longrightarrow> flatten_verdicts (monitor \<phi> \<pi>) = Mt \<pi>"
  unfolding monitor_def using monitorable
  by (subst wf_mstate_msteps_stateless_UNIV[OF wf_mstate_minit_safe, simplified])
    (auto simp: mmonitorable_def Mt_pnil well_typed)


section \<open>Collected correctness results\<close>

context verimon
begin

text \<open>We summarize the main results proved above.
\begin{enumerate}
\item The term @{term M} describes semantically the monitor's expected behaviour:
\begin{itemize}
\item @{thm[source] mono_monitor}: @{thm mono_monitor[no_vars]}
\item @{thm[source] sound_monitor}: @{thm sound_monitor[no_vars]}
\item @{thm[source] complete_monitor}: @{thm complete_monitor[no_vars]}
\item @{thm[source] sliceable_M}: @{thm sliceable_M[no_vars]}
\end{itemize}
\item The executable monitor's online interface @{term minit_safe} and @{term mstep}
  preserves the invariant @{term wf_mstate} and produces the the verdicts according
  to @{term M}:
\begin{itemize}
\item @{thm[source] wf_mstate_minit_safe}: @{thm wf_mstate_minit_safe[no_vars]}
\item @{thm[source] wf_mstate_mstep}: @{thm wf_mstate_mstep[no_vars]}
\item @{thm[source] mstep_mverdicts}: @{thm mstep_mverdicts[no_vars]}
\end{itemize}
\item The executable monitor's offline interface @{term monitor} implements @{term M}:
\begin{itemize}
\item @{thm[source] monitor_mverdicts}: @{thm monitor_mverdicts[no_vars]}
\end{itemize}
\end{enumerate}
\<close>

end

(*<*)
end
(*>*)
