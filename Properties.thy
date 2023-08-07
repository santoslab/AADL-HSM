section \<open>Deductive Schemas\<close>

text \<open>Definitions in this section set up schema for reasoning about system execution
properties.  One role of the schema is to state how component-level properties to 
support system-level properties.
\<close>

theory Properties
  imports Behavior
begin

subsection \<open>Initialization Phase\<close>

text \<open>The following definition introduces a notion of a \emph{thread initialization 
property} for thread application logic (which abstracts thread entry point code).  
The property @{term P} holds for a thread's application logic 
if it holds for  all output variable states @{term vs'}
and output port states @{term ps'} that satisfy the thread's Initialize
entry point contract (@{term appInit}).\<close>

definition appInitProp :: "'a App \<Rightarrow> ('a VarState * 'a PortState \<Rightarrow> bool) \<Rightarrow> bool"
  where "appInitProp a P \<equiv> \<forall>vs' ps'. appInit a vs' ps' \<longrightarrow> P (vs', ps')"

text \<open>We introduce the notion a \emph{system initialization property}.  Currently,
the only system features that can be ``observed'' by a system property are the variable
states and application port states of a thread.  A system initialization property
makes observations about the results of ``executing'' the Initialization entry points
of each thread (which only constrain variable states and output application port states.
Therefore, the system initialization property is intuitively a family of properties 
indexed by component identifier @{term c} where each member of the family observes
the variables states and output application port states for a given component/thread @{term c}.

The following definition states that a system initialization property @{term P} 
holds for the app model @{term am} portion of a system when, for all threads (identifiers)
 @{term c}, if a thread can undergo an initialize step from thread state @{term t}
to thread state @{term t'}, then the @{term c}-relevant portion of the property
holds for the variable state @{term tvar} and output application port state @{term appo}
elements of thread state @{term t'}.\<close>

definition sysInitProp :: "'a AppModel \<Rightarrow> (CompId \<Rightarrow> ('a VarState * 'a PortState \<Rightarrow> bool)) => bool"
  where "sysInitProp am P \<equiv>
  \<forall>c \<in> appModelCIDs am. \<forall>t t'. stepInit (appModelApp am $ c) t t' \<longrightarrow> P c (tvar t', appo t')"

text \<open>Now, we set up a verification condition @{term sysInitVC} 
for a system initialization property @{term P}.
We intend to show that, to verify a system initialization property @{term P} (i.e., to show
that P holds for an app model @{term am}, it is sufficient to show that for every
thread component @{term c} in the model, the @{term c}-relevant portion of @{term P}
is an thread initialization property (@{term appInitProp}) for @{term c} (i.e., for
@{term c}'s application logic).\<close>

definition sysInitVC :: "'a AppModel \<Rightarrow> (CompId \<Rightarrow> ('a VarState * 'a PortState \<Rightarrow> bool)) => prop"
  where "sysInitVC am P \<equiv> 
  (\<And>c. c \<in> appModelCIDs am \<Longrightarrow> appInitProp (appModelApp am $ c) (P c))"

text \<open>The following lemma establishes that @{term sysInitVC} is a sound verification
condition for system initialization property P: for a well-formed app model @{term am},
if @{term sysInitVC} holds, then @{term sysInitProp} holds.\<close>

lemma initSysFromApps:
  assumes wf_am: "wf_AppModel am"
      and vc: "\<And>c. c \<in> appModelCIDs am \<Longrightarrow> appInitProp (appModelApp am $ c) (P c)"
    shows "sysInitProp am P"
proof (simp only: sysInitProp_def; clarify)
  fix c t t'
  assume a1: "c \<in> appModelCIDs am"
     and a2: "stepInit (appModelApp am $ c) t t'"
  thus "P c (tvar t', appo t')"
  proof -
    have "appInit (appModelApp am $ c) (tvar t') (appo t')" 
      using a2 stepInit_ruleinv[of "(appModelApp am $ c)" t t'] by blast
    thus ?thesis
      using a1 appInitProp_def vc by blast 
  qed
qed

text \<open>The follow definition will interpret a system initialization property
@{term P} in the context of a specific system state @{term s}.\<close>

definition sysAllInitProp :: "'a AppModel \<Rightarrow> 
  (CompId \<Rightarrow> ('a VarState * 'a PortState \<Rightarrow> bool)) \<Rightarrow> 
  ('u, 'a) SystemState \<Rightarrow> bool"
where "sysAllInitProp am P s \<equiv>
  \<forall>c \<in> appModelCIDs am. P c (tvar (systemThread s $ c), appo (systemThread s $ c))"

definition systemAppInit where "systemAppInit am c = { (v, p) | v p. appModelInit am c v p }"

definition varappo where "varappo x c = 
  (if c \<in> dom (systemThread x) 
    then Some (tvar (systemThread x $ c), appo (systemThread x $ c)) 
    else None)"

lemma varappo_te:
  assumes "c \<in> dom(systemThread x)"
  shows "varappo (x\<lparr>systemThread := 
    systemThread x(c \<mapsto> (systemThread x $ c)\<lparr>tvar := vs, appo := ps\<rparr>), systemExec := e\<rparr>) c = 
    Some (vs, ps)"
proof -
  have h1: "tvar(systemThread x(c \<mapsto> (systemThread x $ c)\<lparr>tvar := vs, appo := ps\<rparr>) $ c) = vs"
    by simp
  have h2: "appo(systemThread x(c \<mapsto> (systemThread x $ c)\<lparr>tvar := vs, appo := ps\<rparr>) $ c) = ps"
    by simp
  show ?thesis unfolding varappo_def by simp
qed

lemma sysInit_bw:
  shows "\<lbrakk>stepSys am com sch x y; systemExec y = Initialize cs \<rbrakk> \<Longrightarrow> systemExec x \<noteq> Initialize []"
proof (induction rule: stepSys.induct)
  case (initialize c cs t)
  then show ?case by simp
next
  case (switch c)
  then show ?case by simp
next
  case (push c t sb it)
  then show ?case by force
next
  case (pull c t sb it)
  then show ?case by simp
next
  case (execute c c' a t)
  then show ?case by simp
qed

lemma sysInit_seq_bw_neq:
  "\<lbrakk>(stepSys am com sch)\<^sup>*\<^sup>* x y; x \<noteq> y; systemExec y = Initialize cs \<rbrakk> \<Longrightarrow> systemExec x \<noteq> Initialize []"
proof (induction arbitrary: cs rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  have h1: "(stepSys am com sch)\<^sup>*\<^sup>* a b" using rtrancl_into_rtrancl.hyps(1) by blast
  have h2: "stepSys am com sch b c" using rtrancl_into_rtrancl.hyps(2) by blast
  have h3: "\<And>cs. a \<noteq> b \<Longrightarrow> systemExec b = Initialize cs \<Longrightarrow> systemExec a \<noteq> Initialize []"
    using rtrancl_into_rtrancl.IH by blast
  have h4: "a \<noteq> c" by (simp add: rtrancl_into_rtrancl.prems(1))
  have h5: "systemExec c = Initialize cs" using rtrancl_into_rtrancl.prems(2) by blast
  show ?case 
  proof (cases "a = b")
    case True
    then show ?thesis
      using rtrancl_into_rtrancl.hyps(2) rtrancl_into_rtrancl.prems(2) sysInit_bw by blast
  next
    case False
    then obtain cs' where "systemExec b = Initialize cs'" 
      using h2 h5 stepSysInit_sc_rev_ruleinv by blast
    then show ?thesis using False h3 by blast
  qed
qed

lemma sysInit_seq_bw_supseq:
  "\<lbrakk>(stepSys am com sch)\<^sup>*\<^sup>* x y; systemExec y = Initialize cs \<rbrakk> \<Longrightarrow> (\<exists>as. systemExec x = Initialize (as @ cs))"
proof (induction arbitrary: cs rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (metis append.assoc append_Cons append_Nil stepSysInit_sc_rev_ruleinv)
qed

lemma sysInit_none:
  "\<lbrakk>stepSys am com sch x y; systemExec y = Initialize cs; systemExec x = Initialize cs \<rbrakk> \<Longrightarrow> x = y"
  using stepSysInit_sc_rev_ruleinv by fastforce

lemma sysInit_seq_none:
  "\<lbrakk>(stepSys am com sch)\<^sup>*\<^sup>* x y; systemExec y = Initialize cs; systemExec x = Initialize cs \<rbrakk> \<Longrightarrow> x = y"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  obtain u where "systemExec b = Initialize (u#cs)"
    using rtrancl_into_rtrancl.hyps(2) rtrancl_into_rtrancl.prems(1) stepSysInit_sc_rev_ruleinv by blast
  then show ?case
    using rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems(2) sysInit_seq_bw_supseq by fastforce
qed

lemma sysInit_step_seq_set: 
  "\<lbrakk> stepSys am com sch x y; 
     isInitializing x;
     systemExec x = Initialize (c # cs) \<rbrakk> \<Longrightarrow> varappo y \<in> { (varappo x)(c\<mapsto>v) |v. v \<in> systemAppInit am c }"
proof (induction rule: stepSys.induct)
  case (initialize a cs t)
  have h1: "a = c" using initialize.hyps(2) initialize.prems(2) by fastforce
  then obtain vs ps where 
    h2: "varappo (x\<lparr>systemThread := systemThread x(a \<mapsto> t), systemExec := Initialize cs\<rparr>) c = Some (vs, ps)"
    using varappo_def
    by (metis SystemState.SystemState.select_convs(1) SystemState.SystemState.surjective 
        SystemState.SystemState.update_convs(1) SystemState.SystemState.update_convs(5) domI fun_upd_same)
  hence h3: "(vs, ps) \<in> systemAppInit am c" unfolding systemAppInit_def varappo_def apply clarify
    using h1 initialize.hyps(3) stepInit_ruleinv by fastforce
  have h4: "varappo (x\<lparr>systemThread := systemThread x(a \<mapsto> t), systemExec := Initialize cs\<rparr>) = varappo x(c \<mapsto> (vs, ps))"
  proof
    fix z
    show "varappo (x\<lparr>systemThread := systemThread x(a \<mapsto> t), systemExec := Initialize cs\<rparr>) z =
          (varappo x(c \<mapsto> (vs, ps))) z"
    proof (cases "z = c")
      case True
      then show ?thesis
        by (simp add: h2)
    next
      case False
      then show ?thesis by (simp add: h1 varappo_def)
    qed
  qed
  show ?case using initialize.prems h2 h3 using h1 h4 by fastforce
next
  case (switch c)
  then show ?case by simp
next
  case (push c t sb it)
  then show ?case by simp
next
  case (pull c t sb it)
  then show ?case by simp
next
  case (execute c c' a t)
  then show ?case by simp
qed

lemma sysInit_step_seq: 
  "\<lbrakk> stepSys am com sch x y; 
     systemExec x = Initialize (c # cs) \<rbrakk> \<Longrightarrow> varappo y \<in> map_Upd_seq (systemAppInit am) {varappo x} [c]"
proof (induction rule: stepSys.induct)
  case (initialize a as t)
  have h1: "a = c" using initialize.hyps(2) initialize.prems(1) by fastforce
  have h2: "as = cs" using initialize.hyps(2) initialize.prems(1) by fastforce
  have h3: "map_Upd_seq (systemAppInit am) {varappo x} [c] = { (varappo x)(c\<mapsto>v) |v. v \<in> systemAppInit am c }"
    by simp
  then show ?case apply (simp add: h3) 
    using h1 initialize.hyps stepSys.initialize sysInit_step_seq_set by fastforce
next
  case (switch c)
  then show ?case by simp
next
  case (push c t sb it)
  then show ?case by simp
next
  case (pull c t sb it)
  then show ?case by simp
next
  case (execute c c' a t)
  then show ?case by simp
qed

lemma sysInit_seq:
  "\<lbrakk> isInitializing x; stepsSys am com sch x y;
     systemExec x = Initialize xs; systemExec y = Initialize [] \<rbrakk> \<Longrightarrow> 
     varappo y \<in> map_Upd_seq (systemAppInit am) {varappo x} xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case unfolding varappo_def stepsSys_def using sysInit_seq_none by fastforce
next
  case (Cons a xs)
  obtain z where z1: "stepSys am com sch x z" 
             and z2: "stepsSys am com sch z y"
    using Cons.prems unfolding stepsSys_def
    by (metis Exec.inject(1) converse_rtranclpE list.distinct(1))
    have z3: "systemExec z = Initialize (xs)" using z1
      by (metis Cons.prems(1) Cons.prems(3) stepSysInit_redsch_ruleinv)
    have z4: "varappo z \<in> map_Upd_seq (systemAppInit am) {varappo x} [a]" 
      using sysInit_step_seq Cons.prems(3) z1 by fastforce
  show ?case using Cons.prems Cons.IH[of z] z1 z2 z3 z4
    by (metis (no_types, opaque_lifting) append_Cons append_Nil map_Upd_seq_comp_in stepSysInit_initInv_ruleinv)
qed

lemma sysInit_init_seq:
  assumes init: "isInitializing x"
      and steps: "stepsSys am com sch x y"
      and exec_x: "systemExec x = Initialize (scheduleInit sch)"
      and exec_y: "systemExec y = Initialize []"
    shows "varappo y \<in> map_Upd_seq (systemAppInit am) {varappo x} (scheduleInit sch)"
  using assms by (simp add: sysInit_seq)

lemma sysInit_init_merge:
  assumes wf_am: "wf_AppModel am"
      and wf_sch: "wf_SystemSchedule (appModel am) sch"
      and init: "isInitializing x"
      and steps: "stepsSys am com sch x y"
      and exec_x: "systemExec x = Initialize (scheduleInit sch)"
      and exec_y: "systemExec y = Initialize []"
    shows "varappo y \<in> 
    {varappo x} ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit am)) (scheduleInit sch))}"
proof -
  have h1: "card (set (scheduleInit sch)) = length (scheduleInit sch)"
    using wf_sch unfolding wf_SystemSchedule_def by simp
  have h2: "\<forall>c \<in> dom (modelCompDescrs (appModel am)). (\<exists>ws qs. (appModelInit am c) ws qs)"
    using wf_am unfolding wf_AppModel_def wf_App_def wf_CIDAppCIDAPP_def wf_CIDApp_def by simp
  hence h3: "\<forall>x \<in> set (scheduleInit sch). systemAppInit am x \<noteq> {}"
    using wf_sch unfolding wf_SystemSchedule_def systemAppInit_def by simp
  show ?thesis 
    using exec_x exec_y init steps h1 h3 
      sysInit_init_seq[of x am com sch y] 
      map_Upd_Merge[of "(scheduleInit sch)" "(systemAppInit am)" "{varappo x}"]
    by blast
qed

lemma sysInit_init_prop:
  assumes wf_am: "wf_AppModel am"
      and wf_sch: "wf_SystemSchedule (appModel am) sch"
      and wf_state: "dom (systemThread x) \<subseteq> appModelCIDs am" (* to be included in wf_Thread *)
      and init: "isInitializing x"
      and exec_x: "systemExec x = Initialize (scheduleInit sch)"
      and exec_y: "systemExec y = Initialize []"
      and steps: "stepsSys am com sch x y"
      and vc: "\<And>c. c \<in> appModelCIDs am \<Longrightarrow> appInitProp (appModelApp am $ c) (P c)"
    shows "sysAllInitProp am P y"
proof -
  have h0: "dom (varappo x) \<subseteq> appModelCIDs am" using wf_state unfolding varappo_def dom_def by auto
  have h1: "varappo y \<in> {varappo x} ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit am)) (scheduleInit sch))}"
    using exec_x exec_y init steps sysInit_init_merge wf_am wf_sch by blast
  have g0: "\<forall>m \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit am)) (scheduleInit sch))}. dom (varappo x) \<subseteq> dom m"
    using h0 wf_sch unfolding wf_SystemSchedule_def
    by (smt (verit, best) CollectD appModelCIDs.elims appModelCompDescrs.simps map_seq_merge_eq)
  have g1: "varappo y \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit am)) (scheduleInit sch))}"
    by (metis (no_types, lifting) g0 h1 map_Add_extend singleton_iff)
  hence h2: "\<And>c. c \<in> appModelCIDs am \<Longrightarrow> varappo y $ c \<in> systemAppInit am c"
  proof -
    fix c
    assume a1: "c \<in> appModelCIDs am"
    have "card (set (scheduleInit sch)) = length (scheduleInit sch)"
      using wf_SystemSchedule_def wf_sch by presburger
    show "varappo y $ c \<in> systemAppInit am c"
      using a1 g1 map_seq_merge_el wf_SystemSchedule_def wf_sch by fastforce
  qed
  hence h3: "\<forall>c \<in> appModelCIDs am. (tvar (systemThread y $ c), appo (systemThread y $ c)) \<in> systemAppInit am c"
    using g1 wf_sch unfolding wf_SystemSchedule_def
    by (smt (verit, ccfv_SIG) appModelCIDs.elims appModelCompDescrs.simps domIff map_seq_dom_dep 
        map_some_val_given mem_Collect_eq varappo_def)
  have h4: "\<forall>c \<in> appModelCIDs am. P c (tvar (systemThread y $ c), appo (systemThread y $ c))"
    by (smt (verit) appInitProp_def appModelInit.simps h3 mem_Collect_eq systemAppInit_def vc)
  thus ?thesis using sysAllInitProp_def by blast
qed

definition sysAppInvProp where "sysAppInvProp cids P I \<equiv> \<forall>c \<in> cids. \<forall>x p. P c (x, p) \<longrightarrow> I c x"

(* App computation invariant I on local variables and output port properties P. *)
(* All other port properties must be guaranteed on system level. *)
(* Also system-wide invariants must be dealt with globally, assume substrate properties. *)
definition appInvProp where "appInvProp a I P \<equiv> 
  \<forall>x x' d p p'. I x \<and> appCompute a x p d x' p' \<longrightarrow> I x' \<and> P (x', p')"

definition sysInvProp where "sysInvProp am sch I P \<equiv> 
  \<forall>c \<in> appModelCIDs am. 
    \<forall>t t'. I c (tvar t) \<and> 
      stepThread (computeDispatchStatus (appModel am) c) (appModelPortKind am) (appModelApp am $ c) sch t t' 
      \<longrightarrow> I c (tvar t) \<and> P c (tvar t, appo t)"

(*
lemma sysThreadInv:
  assumes wf_am: "wf_AppModel am"
      and valid: "c \<in> appModelCIDs am"
      and isat: "I c (tvar x)"
      and inv: "appInvProp (appModelApp am $ c) (I c) (P c)"
    shows "sysInvProp am sch I P"
  using wf_am unfolding wf_AppModel_def wf_CIDAppCIDAPP_def wf_CIDApp_def
  by blast


lemma sysThreadInv1:
  assumes wf_am: "wf_AppModel am"
      and vc: "\<And>c. \<lbrakk>c \<in> appModelCIDs am; I c (tvar x)\<rbrakk> \<Longrightarrow> appInvProp (appModelApp am $ c) (I c) (P c)"
      and step: "stepComp (computeDispatchStatus (appModel am) c) (appModelApp am $ c) sch x y"
    shows "sysInvProp am sch I P"
  using wf_am unfolding wf_AppModel_def wf_CIDAppCIDAPP_def wf_CIDApp_def
  by blast
*)
(*
lemma initIndProp:
  assumes inv: "initInvProp a P"
      and p0: "P s"
      and app: "(appInit a)\<^sup>*\<^sup>* s s'"
    shows "P s'"
  using inv p0 app unfolding initInvProp_def
  using rtranclp_induct[of "appInit a" s s' P]
  by blast

lemma initIndTrmProp:
  assumes inv: "initInvProp a P"
      and trm: "initTrmProp a P Q"
      and p0: "P s"
      and app: "(appInit a)\<^sup>*\<^sup>* s s'"
      and t0: "\<forall>s''. \<not>appInit a s' s''"
    shows "Q s'"
proof -
  have h1: "P s'"
    using app initIndProp inv p0 by blast
  show ?thesis
    using h1 trm t0 unfolding initTrmProp_def
    by blast
qed

lemma thread_wf_reach:
  assumes "wf_Model m"
      and "wf_App m a"
      and "reachP m a d t"
    shows "wf_ThreadState m c t"
  sorry (* by induction using the preceding two lemmata *)

lemma reachprop:
  assumes "wf_Model m"
      and "wf_App m a"
      and "cinitprop a (isModelCID m) P"
      and "cinvprop a (isModelCID m) P"
      and "reachP m a c t"
    shows "cthreadprop m t (isModelCID m) P"
  sorry
*)
end