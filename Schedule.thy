section \<open>Follow for Component Scheduling\<close>

theory Schedule
  imports Model
begin

type_synonym 's Follow = "('s \<times> CompId \<times> 's) set"

definition follow where "follow (a::'a Follow) s c = { s' | s'. (s, c, s') \<in> a }"

text \<open>Non-determinism only occurs through external choices.\<close>
definition folunique where 
  "folunique a \<equiv> \<forall>s c s' s''. (s, c, s') \<in> a \<and> (s, c, s'') \<in> a \<longrightarrow> s' = s''"

definition folwf where "folwf a \<equiv> wf { (s, s') | s c s'. (s, c, s') \<in> a }"

definition states where "states a = { x | x s c s'. x \<in> {s, s'} \<and> (s, c, s') \<in> a }"

lemma folwf_on_states: "folwf a = wf_on (states a) { (s, s') | s c s'. (s, c, s') \<in> a }"
proof
  show "folwf a \<Longrightarrow> wf_on (states a) { (s, s') | s c s'. (s, c, s') \<in> a }"
  unfolding folwf_def states_def
  using wf_on_subset by auto
next
  assume a: "wf_on (states a) { (s, s') | s c s'. (s, c, s') \<in> a }"
  show "folwf a"
  proof - {
      fix A
      assume b: "A \<subseteq> { (s, s') | s c s'. (s, c, s') \<in> a } `` A"
      hence c: "A \<subseteq> states a" unfolding states_def using ImageE by blast
      hence "A = {}" using a b by (simp add: wf_onE_pf)
    }
    thus ?thesis unfolding folwf_def using wfI_pf by blast
  qed
qed

definition foliso where "foliso a b \<equiv> 
  \<exists>f. bij_betw f (states a) (states b) \<and>
  (\<forall>s\<in>states a.\<forall>c.\<forall>s'\<in>states a. (s, c, s') \<in> a \<longleftrightarrow> (f s, c, f s') \<in> b)"

lemma foliso_refl: "foliso a a"
proof -
  have h1: "bij_betw Fun.id (states a) (states a)" by blast
  have h2: "\<forall>s\<in>states a.\<forall>c.\<forall>s'\<in>states a. (s, c, s') \<in> a \<longleftrightarrow> (Fun.id s, c, Fun.id s') \<in> a"
    by simp
  thus ?thesis unfolding foliso_def using h1 h2 by blast
qed

lemma foliso_sym: assumes "foliso a b" shows "foliso b a"
proof -
  obtain f where f1: "bij_betw f (states a) (states b)"
             and f2: "\<forall>s\<in>states a.\<forall>c.\<forall>s'\<in>states a. (s, c, s') \<in> a \<longleftrightarrow> (f s, c, f s') \<in> b"
    using assms unfolding foliso_def by blast
  obtain g where g1: "\<forall>x \<in> states a. f x \<in> states b \<and> g(f x) = x"
             and g2: "\<forall>y \<in> states b. g y \<in> states a \<and> f(g y) = y" 
    using f1 bij_betw_iff_bijections[of f "states a" "states b"]
    by blast
  have g3: "bij_betw g (states b) (states a)"
    using bij_betw_iff_bijections g1 g2 by blast
  have g4: "\<forall>s\<in>states b.\<forall>c.\<forall>s'\<in>states b. (s, c, s') \<in> b \<longrightarrow> (g s, c, g s') \<in> a"
    using f2 g2 unfolding states_def by simp
  have g5: "\<forall>s\<in>states b.\<forall>c.\<forall>s'\<in>states b. (g s, c, g s') \<in> a \<longrightarrow> (s, c, s') \<in> b"
    by (simp add: f2 g2)
  thus ?thesis using g3 g4 unfolding foliso_def by blast
qed

lemma foliso_trans: assumes A: "foliso a b" and B: "foliso b c" shows "foliso a c"
proof -
  obtain f where f1: "bij_betw f (states a) (states b)"
             and f2: "\<forall>s\<in>states a.\<forall>c.\<forall>s'\<in>states a. (s, c, s') \<in> a \<longleftrightarrow> (f s, c, f s') \<in> b"
    using A unfolding foliso_def by blast
  obtain g where g1: "bij_betw g (states b) (states c)"
             and g2: "\<forall>s\<in>states b.\<forall>c'.\<forall>s'\<in>states b. (s, c', s') \<in> b \<longleftrightarrow> (g s, c', g s') \<in> c"
    using B unfolding foliso_def by blast
  have h1: "bij_betw (g \<circ> f) (states a) (states c)"
    using bij_betw_comp_iff f1 g1 by blast
  have h2: "\<forall>s\<in>states a.\<forall>c'.\<forall>s'\<in>states a. (s, c', s') \<in> a \<longleftrightarrow> ((g \<circ> f) s, c', (g \<circ> f) s') \<in> c"
    using bij_betw_apply f1 f2 g2 by fastforce
  thus ?thesis unfolding foliso_def using h1 h2 by blast
qed

text \<open>Deterministic follow relations permit maximally to choose one component and one 
      successor state in each state.\<close>
definition foldet where 
  "foldet a \<equiv> \<forall>s c c' s' s''. (s, c, s') \<in> a \<and> (s, c', s'') \<in> a \<longrightarrow> c = c' \<and> s' = s''"

lemma foldet_unique: "foldet a \<Longrightarrow> folunique a"
  unfolding foldet_def folunique_def by blast

type_synonym 's Schedule = "'s \<times> 's Follow"

thm trancl_induct

text \<open>The big steps are built backwards.\<close>
inductive_set bigstep for a :: "'s Follow" where 
  BB: "(s, c, s') \<in> a \<Longrightarrow> (s, [c], s') \<in> bigstep a"
| BI: "\<lbrakk>(s', c, s'') \<in> a; (s, x, s') \<in> bigstep a\<rbrakk> \<Longrightarrow> (s, c#x, s'') \<in> bigstep a"

lemma bigstep_trancl: "{ (s, s') | s c s'. (s, c, s') \<in> a }\<^sup>+ = { (s, s') | s c s'. (s, c, s') \<in> bigstep a }"
proof
  show "{ (s, s') | s c s'. (s, c, s') \<in> a }\<^sup>+ \<subseteq> { (s, s') | s c s'. (s, c, s') \<in> bigstep a }" 
  proof - {
    fix s s'
    assume "(s, s') \<in> { (s, s') | s c s'. (s, c, s') \<in> a }\<^sup>+"
    hence "(s, s') \<in> { (s, s') | s c s'. (s, c, s') \<in> bigstep a }"
    proof (induction rule: trancl_induct)
      case (base y)
      then show ?case using bigstep.BB by fastforce
    next
      case (step y z)
      then show ?case using bigstep.BI by fastforce
    qed
    } thus ?thesis using subrelI by blast 
  qed
next
  show "{ (s, s') | s c s'. (s, c, s') \<in> bigstep a } \<subseteq> { (s, s') | s c s'. (s, c, s') \<in> a }\<^sup>+"
  proof - {
      fix s c s'
      assume "(s, c, s') \<in> bigstep a"
      hence "(s, s') \<in> { (s, s') | s c s'. (s, c, s') \<in> a }\<^sup>+"
      proof (induction rule: bigstep.induct)
        case (BB s c s')
        then show ?case by blast
      next
        case (BI s' c s'' s x)
        hence "(s', s'') \<in> { (s1, s2) | s1 c0 s2. (s1, c0, s2) \<in> a }" by blast
        then show ?case using BI.IH
          by (meson Transitive_Closure.trancl_into_trancl)
      qed
      } thus ?thesis by blast
  qed
qed

lemma bigstepwf_folwf: assumes "folwf a" shows "folwf (bigstep a)"
  using assms wf_trancl[of "{ (s, s') | s c s'. (s, c, s') \<in> a }"] 
  unfolding folwf_def 
  by (simp add: bigstep_trancl)

lemma bigstepwf_not_refl:
  assumes wf: "folwf a"
      and bs: "(s, x, s') \<in> bigstep a"
    shows "s \<noteq> s'"
  using wf bs bigstepwf_folwf wf_not_refl unfolding folwf_def
  by fastforce

fun maxstepp where 
  "maxstepp a (s, x, s') = ((s, x, s') \<in> bigstep a \<and> (\<forall>c. follow a s' c = {}))"

definition maxstep where "maxstep a = { ms | ms. maxstepp a ms }"

inductive_set history for a :: "'s Follow" where 
  BB: "(s, c, s') \<in> a \<Longrightarrow> (s, [c], [s']) \<in> history a"
| BI: "\<lbrakk>(s', c, s'') \<in> a; (s, x, s'#t) \<in> history a\<rbrakk> \<Longrightarrow> (s, c#x, s''#s'#t) \<in> history a"

lemma history_ne1: "(s, x, s') \<in> history a \<Longrightarrow> x \<noteq> []"
  using history.cases by force

lemma history_ne2: "(s, x, s') \<in> history a \<Longrightarrow> s' \<noteq> []"
  using history.cases by force

lemma history_app:
  assumes hi: "(s', x, t) \<in> history a"
      and ac: "(s, c, s') \<in> a"
    shows "(s, x @ [c], t @ [s']) \<in> history a"
using hi ac proof (induction rule: history.induct)
  case (BB s c s')
  then show ?case by (simp add: history.BB history.BI)
next
  case (BI s' c s'' s x t)
  then show ?case by (simp add: history.BI)
qed

inductive_set bhistory for a :: "'s Follow" where
  HB: "(s, c, s') \<in> a \<Longrightarrow> (s, [c], [s']) \<in> bhistory a"
| HI: "\<lbrakk>(s, c, s') \<in> a; (s', x, t) \<in> bhistory a\<rbrakk> \<Longrightarrow> (s, x@[c], t@[s']) \<in> bhistory a"

lemma bhistory_ne1: "(s, x, s') \<in> bhistory a \<Longrightarrow> x \<noteq> []"
  using bhistory.cases by force

lemma bhistory_ne2: "(s, x, s') \<in> bhistory a \<Longrightarrow> s' \<noteq> []"
  using bhistory.cases by force

lemma history_len: "(s, x, s') \<in> history a \<Longrightarrow> length x = length s'"
proof (induction rule: history.induct)
  case (BB s c s')
  then show ?case by simp
next
  case (BI s' c s'' s x t)
  then show ?case by simp
qed

lemma history_back: "\<lbrakk>(s, x, s') \<in> history a; length x > 1 \<rbrakk> \<Longrightarrow> (s, tl x, tl s') \<in> history a"
proof (induction rule: history.induct)
  case (BB s c s')
  then show ?case by simp
next
  case (BI s' c s'' s x t)
  then show ?case by simp
qed

lemma history_first: "\<lbrakk>(s, x, s') \<in> history a \<rbrakk> \<Longrightarrow> (s, last x, last s') \<in> a"
proof (induction rule: history.induct)
  case (BB s c s')
  then show ?case by simp
next
  case (BI s' c s'' s x t)
  then show ?case apply simp using history_len by force
qed

lemma bhistory_prep:
  assumes bh: "(s, x, s'#t) \<in> bhistory a"
      and ac: "(s', c, s'') \<in> a"
  shows "(s, c#x, s''#s'#t) \<in> bhistory a"
proof -
  obtain u where u: "u = s'#t" by blast
  hence "(s, x, u) \<in> bhistory a" using bh by blast
  thus ?thesis using ac u
  proof (induction arbitrary: t rule: bhistory.induct)
    case (HB t' d t'')
    have c: "(s', [c], [s'']) \<in> bhistory a" by (simp add: ac bhistory.HB)
    then show ?case
      using HB.hyps HB.prems(2) bhistory.simps by fastforce
  next
    case (HI v d v' x t')
    hence a: "t = [] \<Longrightarrow> t' = []" by simp
    have "t' \<noteq> []" using HI.hyps(2) bhistory_ne2 by fastforce
    hence "t \<noteq> []" using a by blast
    then obtain w r where wr1: "t = w@[r]" by (meson rev_exhaust)
    hence "v' = r" using HI.prems(2) by fastforce
    hence b: "t' = s' # w" using HI.prems(2) wr1 by force
    hence "(v', c # x, s'' # s' # w) \<in> bhistory a" using HI.IH ac by blast
    then show ?case using HI.hyps(1) HI.prems(2) b bhistory.HI by fastforce
  qed
qed

lemma history_cut: assumes "(s, x, s') \<in> history a" and "butlast x \<noteq> []"
  shows "(last s', butlast x, butlast s') \<in> history a"
using assms proof (induction rule: history.induct)
  case (BB s d s')
  then show ?case by force
next
  case (BI s' d s'' s x t)
  hence a: "length x = length (s' # t)" by (simp add: history_len)
  then show ?case
  proof (cases "length x = 1")
    case True
    then obtain e where e: "x = [e]" apply simp by (metis length_0_conv length_Suc_conv)
    hence b: "t = []" using a by force
    hence c: "last (s'' # s' # t) = s'" by simp
    have d: "butlast (d # x) = [d]" by (simp add: e)
    have f: "butlast (s'' # s' # t) = [s'']" by (simp add: b)
    then show ?thesis using BI.hyps(1) d history.BB by fastforce
  next
    case False
    have a: "length x > 1" using False a by fastforce
    hence b: "butlast x \<noteq> []" apply simp
      by (metis a length_butlast less_numeral_extra(3) list.size(3) zero_less_diff)
    have c: "last (s'' # s' # t) = last (s' # t)" by auto
    have d: "butlast (d # x) = d # butlast x" using a by force
    have e: "butlast (s'' # s' # t) = s'' # butlast (s' # t)" by simp
    show ?thesis using BI.IH BI.hyps(1) BI.hyps(2) b apply (simp add: c d e)
      using a history.BI history_len by fastforce
  qed
qed

lemma history_bh: "(s, c, s') \<in> history a \<Longrightarrow> (s, c, s') \<in> bhistory a"
proof (induction rule: history.induct)
  case (BB s c s')
  then show ?case by (simp add: bhistory.HB)
next
  case (BI t' d t'' u x t)
  then show ?case by (simp add: bhistory_prep)
qed

lemma history_hb: "(s, c, s') \<in> bhistory a \<Longrightarrow> (s, c, s') \<in> history a"
proof (induction rule: bhistory.induct)
  case (HB s c s')
  then show ?case by (simp add: history.BB)
next
  case (HI s c s' x t)
  then show ?case by (simp add: history_app)
qed

lemma history_rule_inv: assumes "(s, c#x, s''#s'#t) \<in> history a"
  shows "(s', c, s'') \<in> a \<and> (s, x, s'#t) \<in> history a"
proof -
  obtain cx where a: "cx = c#x" by blast
  obtain sst where b: "sst = s''#s'#t" by blast
  have "(s, cx, sst) \<in> history a" using assms by (simp add: a b)
  thus ?thesis
  using a b proof (induction rule: history.induct)
    case (BB u d u')
      then show ?case by force
  next
    case (BI s' c s'' s x t)
      then show ?case by simp
  qed
qed

lemma bigstep_history: "bigstep a = { (s, x, s') | s x s' t. (s, x, s'#t) \<in> history a }"
proof
  show "bigstep a \<subseteq> { (s, x, s') | s x s' t. (s, x, s'#t) \<in> history a }"
  proof - {
    fix s x s'
    assume "(s, x, s') \<in> bigstep a"
    hence "(s, x, s') \<in> { (s, x, s') | s x s' t. (s, x, s'#t) \<in> history a }"
    proof (induction rule: bigstep.induct)
      case (BB s c s')
      then show ?case using history.BB by fastforce
    next
      case (BI s' c s'' s x)
      then show ?case using history.BI by fastforce
    qed
  } thus ?thesis by force
  qed
next
  show "{ (s, x, s') | s x s' t. (s, x, s'#t) \<in> history a } \<subseteq> bigstep a"
  proof - {
      fix s x s' t
      assume a: "(s, x, s'#t) \<in> history a"
      obtain u where u: "u = s'#t" by blast
      hence "(s, x, u) \<in> history a" using a by blast
      hence "(s, x, hd u) \<in> bigstep a"
      proof (induction rule: history.induct)
        case (BB v c v')
        then show ?case by (simp add: bigstep.BB)
      next
        case (BI s' c s'' s x t)
        then show ?case by (simp add: bigstep.BI)
      qed
      hence "(s, x, s') \<in> bigstep a" by (simp add: u)
    } thus ?thesis by blast
  qed
qed

lemma history_transitive: "\<lbrakk> (s, x, s') \<in> history a; (hd s', y, s'') \<in> history a \<rbrakk> \<Longrightarrow> (s, y@x, s''@s') \<in> history a"
proof (induction arbitrary: y s'' rule: history.induct)
  case (BB s c s')
  then show ?case by (simp add: history_app)
next
  case (BI t' c t'' s x t)
  then show ?case using BI.IH BI.hyps(1) BI.prems history_app by fastforce
qed

lemma bigstep_transitive: 
  assumes sx: "(s, x, s') \<in> bigstep a"
      and sy: "(s', y, s'') \<in> bigstep a"
    shows "(s, y@x, s'') \<in> bigstep a"
proof -
  obtain t' where a: "(s, x, s'#t') \<in> history a" using bigstep_history sx by fastforce
  obtain t'' where b: "(s', y, s''#t'') \<in> history a" using bigstep_history sy by fastforce
  from a b have "(s, y@x, (s''#t'')@(s'#t')) \<in> history a"
    using history_transitive[of s x "s'#t'" a y "s''#t''"] by simp
  hence "(s, y@x, s''#(t''@s'#t')) \<in> history a" by simp
  thus ?thesis using bigstep_history by blast
qed

lemma history_cut_left: 
  assumes hi: "(s, y@x, s''@s') \<in> history a"
      and ne: "x \<noteq> []"
      and le: "length y = length s''"
    shows "(s, x, s') \<in> history a"
using hi le ne proof (induction y arbitrary: s'')
  case Nil
  then show ?case by simp
next
  case (Cons c y)
  have a: "Suc (length y) = length s''" using Cons.prems(2) by fastforce
  hence "s'' \<noteq> []" by force
  hence b: "hd s''#tl s'' = s''" by simp
  have c: "length (c#y @ x) > 1" using Cons.prems(3) by simp
  hence "(s, c#y @ x, (hd s''#tl s'') @ s') \<in> history a" using Cons.prems(1) by (simp add: b)
  hence "(s, c#y @ x, hd s''#tl s'' @ s') \<in> history a" by simp  
  hence "(s, y @ x, tl s'' @ s') \<in> history a" using c using history_back by force
  then show ?case using Cons.IH a ne by auto
qed

lemma history_cut_right: 
  assumes hi: "(s, y@x, s''@s') \<in> history a"
      and ne: "y \<noteq> []"
      and le: "length x = length s'"
      and xe: "x = [] \<Longrightarrow> w = s"
      and xne: "x \<noteq> [] \<Longrightarrow> w = hd s'"
    shows "(w, y, s'') \<in> history a"
proof -
  obtain z where z: "z = y@x" by blast
  obtain u where u: "u = s''@s'" by blast
  have "(s, z, u) \<in> bhistory a" using hi z u by (simp add: history_bh)
  thus ?thesis using z u le ne xe xne
  proof (induction arbitrary: x y s'' s' w rule: bhistory.induct)
    case (HB t' c t'')
    hence "x = []" by (simp add: Cons_eq_append_conv)
    then show ?case using HB history.BB by fastforce
  next
    case (HI t' c t'' z t)
    then show ?case
    proof (cases "x = []")
      case True
      then show ?thesis using HI bhistory.HI history_hb apply simp by fastforce
    next
      case False
      hence x: "x \<noteq> []" by simp
      then obtain p q where pq: "x = p @ [q]" by (meson rev_exhaust)
      hence qc: "q = c" using HI.prems(1) by force
      have a: "z = y @ p" using HI.prems(1) pq by fastforce
      have "s' \<noteq> []" using False HI.prems(3) by force
      then obtain p' q' where pp: "s' = p' @ [q']" by (meson rev_exhaust)
      have b: "t = s'' @ p'" using HI.prems(2) pp by force
      have c: "length p = length p'" using HI.prems(3) pp pq by fastforce
      have d: "z \<noteq> []" using HI.prems(4) a by blast
      have e: "y \<noteq> []" by (simp add: HI.prems(4))
      show ?thesis
      proof (cases "p = []")
        case True
        then show ?thesis
          using False HI.hyps(2) HI.prems(2) HI.prems(6) a c history_hb pp by force
      next
        case False
        then have f: "(hd p', y, s'') \<in> history a" using HI.IH a b c e by blast
        then show ?thesis using False HI.prems(3) HI.prems(6) x c apply simp
          by (metis hd_append2 length_greater_0_conv pp)
      qed
    qed
  qed
qed

lemma maxstepp_unbound:
  assumes "a \<noteq> {}"
      and "\<forall>ms. \<not>maxstepp a ms"
    shows "\<exists>s x s'. (s, x, s') \<in> bigstep a \<and> length x \<ge> n"
using assms proof (induction n)
  case 0
  then show ?case using bigstep.BB by fastforce
next
  case (Suc n)
  hence "\<forall>s x s'. (s, x, s') \<in> bigstep a \<longrightarrow> (\<exists>c. follow a s' c \<noteq> {})" by simp
  hence u: "\<forall>s x s'. (s, x, s') \<in> bigstep a \<longrightarrow> (\<exists>c s''. (s', c, s'') \<in> a)"
    unfolding follow_def by simp
  obtain s x s' where a: "(s, x, s') \<in> bigstep a" and b: "n \<le> length x"
    using Suc.IH assms(1) assms(2) by blast
  obtain c s'' where "(s', c, s'') \<in> a" using assms(2) a u by blast
  then show ?case using a b bigstep.BI by fastforce
qed

lemma pidgin:
  assumes fin: "finite x"
      and set: "set s \<subseteq> x"
      and seq: "length s > card x"
    shows "\<exists>p q. p < length s \<and> q < length s \<and> p \<noteq> q \<and> s!p = s!q"
proof - {
    assume "\<forall>p q. p < length s \<and> q < length s \<and> p \<noteq> q \<longrightarrow> s!p \<noteq> s!q"
    hence a: "card (set s) \<ge> length s" by (simp add: distinct_card distinct_conv_nth)
    have b: "card (set s) \<le> card x" using set using card_mono fin by blast
    hence c: "card (set s) < length s" using seq using order_le_less_trans by blast
    have False using a c using linorder_not_le by blast
  } thus ?thesis by blast
qed

lemma history_states: "(s, x, s') \<in> history a \<Longrightarrow> set s' \<subseteq> states a"
proof (induction rule: history.induct)
  case (BB s c s')
  then show ?case unfolding states_def apply simp by blast
next
  case (BI s' c s'' s x t)
  then show ?case unfolding states_def apply simp by blast
qed

lemma list_decomp: "x = take m x @ drop m x"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case by simp
qed

lemma list_decomp2: "m < n \<Longrightarrow> x = take m x @ drop m (take n x) @ drop n x"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case
  proof (induction n)
    case 0
    then show ?case by blast
  next
    case (Suc n)
    then show ?case by (metis append_eq_appendI list_decomp min.absorb3 take_take)
  qed
qed

lemma droptakem: "\<lbrakk>m < n; n < length x\<rbrakk> \<Longrightarrow> x!m = drop m (take (Suc n) x)!0"
proof (induction x arbitrary: m n)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof (cases "m = 0")
    case True
    then show ?thesis using Cons.prems by fastforce
  next
    case False
    then show ?thesis using Cons.prems(1) Cons.prems(2) by force
  qed
qed

lemma droptaken: "\<lbrakk>m < n; n < length x\<rbrakk> \<Longrightarrow> x!n = drop m (take (Suc n) x)!(n-m)"
proof (induction x arbitrary: m n)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof (cases "m = 0")
    case True
    then show ?thesis by (metis diff_Suc_1' diff_Suc_Suc drop0 lessI nth_take)
  next
    case False
    then show ?thesis using Cons.prems(1) Cons.prems(2) by fastforce
  qed
qed

lemma bigstepwf_max:
  assumes wf: "folwf a"
      and ne: "a \<noteq> {}"
      and fin: "finite (states a)"
    shows "\<exists>ms. maxstepp a ms"
proof - {
    assume u: "\<forall>ms. \<not>maxstepp a ms"
    obtain n where a: "n = card (states a)" by blast
    then obtain s x s' where b: "(s, x, s') \<in> bigstep a" and c: "length x \<ge> Suc n"
      using u ne maxstepp_unbound by blast
    then obtain t where t: "(s, x, s'#t) \<in> history a" using bigstep_history by fastforce
    hence "Suc n \<le> length (s'#t)" by (metis c history_len)
    then obtain m k where d1: "m < length (s'#t)"
                      and d2: "k < length (s'#t)"
                      and d3: "m \<noteq> k"
                      and d4: "(s'#t)!m = (s'#t)!k"
      using a fin t history_states[of s x "s'#t" a] pidgin[of "states a" "s'#t"]
      apply simp by blast
    obtain m' k' where mk1: "m' < k'" and mk2: "{m', k'} \<subseteq> {m, k}"
      using d3 apply simp using nat_neq_iff by auto
    have mk3: "m' < length (s'#t)" using mk2 d1 d2 by blast
    have mk3: "k' < length (s'#t)" using mk2 d1 d2 by blast
    have st: "s'#t = take m' (s'#t) @ drop m' (take (Suc k') (s'#t)) @ drop (Suc k') (s'#t)"
      using list_decomp2[of "m'" "(Suc k')" "s'#t"] mk1 less_imp_diff_less less_Suc_eq by blast
    have "drop m' (take (Suc k') (s'#t))!0 = (s'#t)!m'" 
      using mk1 mk3 droptakem[of m' k' "s'#t"] by presburger
    have "drop m' (take (Suc k') (s'#t))!(k'-m') = (s'#t)!k'" 
      using mk1 mk3 droptaken[of m' k' "s'#t"] by presburger
    have False sorry
    } thus ?thesis by blast
qed

end