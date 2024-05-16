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
entry point behavior (@{term appInit}).\<close>

definition appInitProp :: "'a AppBehavior \<Rightarrow> ('a PortState * 'a VarState  \<Rightarrow> bool) \<Rightarrow> bool"
  where "appInitProp a P \<equiv> \<forall>ao tvo. appInit a ao tvo \<longrightarrow> P (ao, tvo)"

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

definition sysInitProp :: "'a BehaviorModel \<Rightarrow> (CompId \<Rightarrow> ('a PortState * 'a VarState  \<Rightarrow> bool)) => bool"
  where "sysInitProp bm P \<equiv>
  \<forall>c \<in> modelCIDs (bmmodel bm). \<forall>(t::'a ThreadState) t'. stepInit (bmbehaviors bm $ c) t t' \<longrightarrow> P c (appo t', tvar t')"

text \<open>Now, we set up a verification condition \<open>sysInitVC\<close> 
for a system initialization property \<open>P\<close>.
We intend to show that, to verify a system initialization property \<open>P\<close> (i.e., to show
that \<open>P\<close> holds for an app model \<open>am\<close>, it is sufficient to show that for every
thread component \<open>c\<close> in the model, the \<open>c\<close>-relevant portion of \<open>P\<close>
is an thread initialization property (\<open>appInitProp\<close>) for \<open>c\<close> (i.e., for
\<open>c\<close>'s application logic).\<close>

definition sysInitVC :: "'a BehaviorModel \<Rightarrow> (CompId \<Rightarrow> ('a PortState * 'a VarState  \<Rightarrow> bool)) => prop"
  where "sysInitVC bm P \<equiv> 
  (\<And>c. c \<in> modelCIDs (bmmodel bm) \<Longrightarrow> appInitProp (bmbehaviors bm $ c) (P c))"

text \<open>The following lemma establishes that \<open>sysInitVC\<close> is a sound verification
condition for system initialization property \<open>P\<close>: for a well-formed app model \<open>am\<close>,
if \<open>sysInitVC\<close> holds, then \<open>sysInitProp\<close> holds.\<close>

lemma initSysFromApps:
  assumes wf_bm: "wf_BehaviorModel (bm::'a BehaviorModel)"
      and vc: "\<And>c. c \<in> modelCIDs (bmmodel bm) \<Longrightarrow> appInitProp (bmbehaviors bm $ c) (P c)"
    shows "sysInitProp bm P"
proof (simp only: sysInitProp_def; clarify)
  fix c
  fix t t'::"'a ThreadState"
  assume a1: "c \<in> modelCIDs (bmmodel bm)"
     and a2: "stepInit (bmbehaviors bm $ c) t t'"
  thus "P c (appo t', tvar t')"
  proof -
    have "appInit (bmbehaviors bm $ c) (appo t') (tvar t')" 
      using a2 stepInit_ruleinv[of "(bmbehaviors bm $ c)" t t'] by blast
    thus ?thesis
      using a1 appInitProp_def vc by blast 
  qed
qed

text \<open>The following definition will interpret a system initialization property
\<open>P\<close> in the context of a specific system state \<open>s\<close>.\<close>

definition sysStateProp :: "'a BehaviorModel \<Rightarrow> 
  (CompId \<Rightarrow> ('a PortState * 'a VarState \<Rightarrow> bool)) \<Rightarrow> 
  ('u, 'a) SystemState \<Rightarrow> bool"
where "sysStateProp bm P s \<equiv>
  \<forall>c \<in> modelCIDs (bmmodel bm). P c (appo (systemThread s $ c), tvar (systemThread s $ c))"

text \<open>The following definition forms the set of all possible Initialization Entrypoint
outputs of thread component \<open>c\<close>, where outputs are pairs of var states (\<open>tvar\<close>) \<open>v\<close> and application
output port states (\<open>appo\<close>) \<open>ao\<close>.\<close>

definition systemAppInit :: "'a BehaviorModel \<Rightarrow> CompId \<Rightarrow> ('a PortState \<times> 'a VarState ) set"
  where "systemAppInit bm c = { (ao, tvo) | ao tvo. appInit (bmbehaviors bm $ c) ao tvo }"

text \<open>The following definition projects a state to a tuple consisting of 
thread app output port states (\<open>appo\<close>) and thread variable states (\<open>tvar\<close>) 
-- the two thread state elements affected by thread initialisation.\<close>

(* From John: it might be a good idea at some point to group in one place a collection
    of definitions like this one that convert from a predicate view of a component behavior
    to a tuple/relational view of component behavior *)

definition appovar :: "('u, 'a) SystemState \<Rightarrow> CompId \<Rightarrow> ('a PortState \<times> 'a VarState) option"
 where "appovar x c = 
  (if c \<in> dom (systemThread x) 
    then Some (appo (systemThread x $ c), tvar (systemThread x $ c)) 
    else None)"

lemma appovar_te:
  assumes "c \<in> dom(systemThread x)"
  shows "appovar (x\<lparr>systemThread := 
    (systemThread x)(c \<mapsto> (systemThread x $ c)\<lparr>appo := ao, tvar := tvo\<rparr>), systemExec := e\<rparr>) c = 
    Some (ao, tvo)"
proof -
  have h1: "tvar((systemThread x)(c \<mapsto> (systemThread x $ c)\<lparr>appo := ao, tvar := tvo\<rparr>) $ c) = tvo"
    by simp
  have h2: "appo((systemThread x)(c \<mapsto> (systemThread x $ c)\<lparr>appo := ao, tvar := tvo\<rparr>) $ c) = ao"
    by simp
  show ?thesis unfolding appovar_def by simp
qed

lemma sysInit_bw:
  shows "\<lbrakk>stepSys bm com sc x y; systemExec y = Initialize cs \<rbrakk> \<Longrightarrow> systemExec x \<noteq> Initialize []"
  using stepSysInit_sc_rev_ruleinv by fastforce

lemma sysInit_seq_bw_neq:
  "\<lbrakk>(stepSys bm com sc)\<^sup>*\<^sup>* x y; x \<noteq> y; systemExec y = Initialize cs\<rbrakk> \<Longrightarrow> systemExec x \<noteq> Initialize []"
proof (induction arbitrary: cs rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  have h1: "(stepSys bm com sc)\<^sup>*\<^sup>* a b" using rtrancl_into_rtrancl.hyps(1) by blast
  have h2: "stepSys bm com sc b c" using rtrancl_into_rtrancl.hyps(2) by blast
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
  "\<lbrakk>(stepSys bm com sc)\<^sup>*\<^sup>* x y; systemExec y = Initialize cs \<rbrakk> \<Longrightarrow> (\<exists>as. systemExec x = Initialize (as @ cs))"
proof (induction arbitrary: cs rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (metis append.assoc append_Cons append_Nil stepSysInit_sc_rev_ruleinv)
qed

lemma sysInit_none:
  "\<lbrakk>stepSys bm com sc x y; systemExec y = Initialize cs; systemExec x = Initialize cs \<rbrakk> \<Longrightarrow> x = y"
  using stepSysInit_sc_rev_ruleinv by fastforce

lemma sysInit_seq_none:
  "\<lbrakk>(stepSys bm com sc)\<^sup>*\<^sup>* x y; systemExec y = Initialize cs; systemExec x = Initialize cs \<rbrakk> \<Longrightarrow> x = y"
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
  assumes step: "stepSys bm com sc x y"
      and exec: "systemExec x = Initialize (c # cs)"
    shows "appovar y \<in> { (appovar x)(c\<mapsto>v) |v. v \<in> systemAppInit bm c }"
proof -
  have "stepSys bm com sc x y = initStepSys bm com sc x y"
    using stepSys_initializing exec init_init by blast
  hence "initStepSys bm com sc x y" using step by force
  thus ?thesis using exec
  proof (induction rule: initStepSys.induct)
    case (initialize s c cs t)
    obtain ps vs where h2: "appovar (s\<lparr> systemThread := (systemThread s)(c \<mapsto> t), 
                                        systemExec := Initialize cs\<rparr>) c = Some (ps, vs)"
      using appovar_def domI fun_upd_same
      by (metis SystemState.SystemState.simps(1) SystemState.SystemState.simps(9) 
          SystemState.SystemState.surjective SystemState.SystemState.update_convs(1))
    hence h3: "(ps, vs) \<in> systemAppInit bm c" unfolding systemAppInit_def appovar_def apply clarify
      using initialize.hyps(3) stepInit_ruleinv by fastforce
    have h4: "appovar (s\<lparr>systemThread := (systemThread s)(c \<mapsto> t), 
                         systemExec := Initialize cs\<rparr>) = (appovar s)(c \<mapsto> (ps, vs))"
    proof
      fix z
      show "appovar (s\<lparr>systemThread := (systemThread s)(c \<mapsto> t), systemExec := Initialize cs\<rparr>) z =
            ((appovar s)(c \<mapsto> (ps, vs))) z"
      proof (cases "z = c")
        case True
        then show ?thesis
          by (simp add: h2)
      next
        case False
        then show ?thesis by (simp add: appovar_def)
      qed
    qed
    then show ?case using exec h3 using initialize.hyps(2) initialize.prems by auto
  next
    case (switch c)
    then show ?case by fastforce
  qed
qed

lemma sysInit_step_seq:
  assumes step: "stepSys bm com sc x y"
      and exec: "systemExec x = Initialize (c # cs)"
    shows "appovar y \<in> map_Upd_seq (systemAppInit bm) {appovar x} [c]"
proof -
  have "stepSys bm com sc x y = initStepSys bm com sc x y"
    using step stepSys_initializing exec init_init by blast
  hence h0: "initStepSys bm com sc x y" using step by force
  thus ?thesis using exec
  proof (induction rule: initStepSys.induct)
    case (initialize s a as t)
      have h1: "a = c" using initialize.hyps(2) initialize.prems(1) by fastforce
      have h2: "as = cs" using initialize.hyps(2) initialize.prems(1) by fastforce
      have h3: "map_Upd_seq (systemAppInit bm) {appovar s} [c] = { (appovar s)(c\<mapsto>v) |v. v \<in> systemAppInit bm c }"
        by simp
      show ?case
        using step exec h0 sysInit_step_seq_set[of bm com sc s y c cs] 
          initStepSys.initialize[of s c cs bm t] initialize.hyps(1) initialize.hyps(3)
        apply (simp add: h1 h2 h3) 
        using stepSys_initializing sysInit_step_seq_set
        by (smt (verit, best) \<open>\<And>sc cm. \<lbrakk>isInitializing s; systemExec s = Initialize (c # cs); stepInit (bmbehaviors bm $ c) (systemThread s $ c) t\<rbrakk> \<Longrightarrow> initStepSys bm cm sc s (s\<lparr>systemThread := (systemThread s) (c \<mapsto> t), systemExec := Initialize cs\<rparr>)\<close> h1 h2 initialize.hyps(1) initialize.hyps(2) initialize.hyps(3) mem_Collect_eq old.prod.exhaust)
    next
      case (switch c) 
        show ?case using exec switch.hyps(2) by (simp add: switch.prems)
    qed
qed

text \<open>Lemma {sysInit\_seq} is used to prove lemma {sysInit\_init\_seq} by induction.\<close>

lemma sysInit_seq:
  "\<lbrakk> stepsSys bm com sc x y;
     systemExec x = Initialize xs; systemExec y = Initialize [] \<rbrakk> \<Longrightarrow> 
     appovar y \<in> map_Upd_seq (systemAppInit bm) {appovar x} xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case unfolding appovar_def stepsSys_def using sysInit_seq_none by fastforce
next
  case (Cons a xs)
  have h1: "isInitializing x" by (simp add: Cons.prems(2))
  obtain z where z1: "stepSys bm com sc x z" 
             and z2: "stepsSys bm com sc z y"
    using Cons.prems unfolding stepsSys_def
    by (metis Exec.inject(1) converse_rtranclpE list.distinct(1))
    have z3: "systemExec z = Initialize (xs)" using z1 h1 Cons.prems(2) stepSysInit_redsch_ruleinv by blast
    have z4: "appovar z \<in> map_Upd_seq (systemAppInit bm) {appovar x} [a]" 
      using sysInit_step_seq Cons.prems(3) z1 Cons.prems(2) by blast
  show ?case using Cons.prems Cons.IH[of z] z1 z2 z3 z4
    by (metis (no_types, opaque_lifting) append_Cons append_Nil map_Upd_seq_comp_in)
qed

text \<open>Lemma {sysInit\_init\_seq} shows that the system initialisations can also be expressed by 
means of the recursive function \<open>map_Upd_seq\<close>.\<close>

lemma sysInit_init_seq:
  assumes steps: "stepsSys bm com sc x y"
      and exec_x: "systemExec x = Initialize (scheduleInit sc)"
      and exec_y: "systemExec y = Initialize []"
    shows "appovar y \<in> map_Upd_seq (systemAppInit bm) {appovar x} (scheduleInit sc)"
  using assms by (simp add: sysInit_seq)

text \<open>Lemma {sysInit\_init\_merge} shows that the order of initialisations does not matter.\<close>

lemma sysInit_init_merge:
  assumes wf_bm: "wf_BehaviorModel bm"
      and wf_sch: "wf_SystemSchedule (bmmodel bm) sc"
      and steps: "stepsSys bm com sc x y"
      and exec_x: "systemExec x = Initialize (scheduleInit sc)"
      and exec_y: "systemExec y = Initialize []"
    shows "appovar y \<in> 
    {appovar x} ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bm)) (scheduleInit sc))}"
proof -
  have h0: "isInitializing x" by (simp add: exec_x)
  have h1: "card (set (scheduleInit sc)) = length (scheduleInit sc)"
    using wf_sch unfolding wf_SystemSchedule_def by simp
  have h2: "\<forall>c \<in> modelCIDs (bmmodel bm). (\<exists>ws qs. appInit (bmbehaviors bm $ c) ws qs)"
    using wf_bm unfolding wf_BehaviorModel_def wf_AppBehaviors_def wf_AppBehavior_def wf_InitBehavior_Inhabited_def by auto
  hence h3: "\<forall>x \<in> set (scheduleInit sc). systemAppInit bm x \<noteq> {}"
    using wf_sch unfolding wf_SystemSchedule_def systemAppInit_def by simp
  show ?thesis 
    using exec_x exec_y h0 steps h1 h3 
      sysInit_init_seq[of bm com sc x y] 
      map_Upd_Merge[of "(scheduleInit sc)" "(systemAppInit bm)" "{appovar x}"]
    by blast
qed

text \<open>Lemma {sysInit\_init\_prop} describes that after initialisation in any well-formed order
all initialisation properties hold, given that the verification properties {vc} hold.
No assumption is made concerning the executed initialisations 
except that all of them must have been executed. This can also be seen as a consequence of lemma
{sysInit\_init\_merge} above that shows that any order of initialisations can be replaced by the
simultaneous execution of all initialisations.

The proof uses the following strategy.
Given the sequence of app initialisations \<open>scheduleInit sc\<close>, 
executing them with \<open>stepsSys\<close> \ldots \<open>y\<close>,
the property \<open>sysStateProp\<close> \ldots \<open>P y\<close>.
In order to show this, we first show that the effect of \<open>stepsSys\<close> \ldots \<open>y\<close> can be simulated
by \<open>appovar y \<in> map_Upd_seq\<close> \ldots\enspace. 
This is done by induction, replacing \<open>scheduleInit sc\<close> by 
a variable \<open>xs\<close>, in lemma {sysInit\_seq}.
The term \<open>appovar y \<in> map_Upd_seq\<close> \ldots can be shown to equal 
\<open>appovar y \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms\<close> \ldots \<open>(scheduleInit sc))}\<close>
using lemmas {map\_Upd\_Merge} and {map\_seq\_merge\_eq}.
This establishes that all initial states hold simultaneously.
Quantifying over the components \<open>c\<close> and using {vc}, we prove \<open>sysStateProp\<close> \ldots \<open>P y\<close>.
\<close>

lemma sysInit_state_prop:
  assumes wf_bm: "wf_BehaviorModel bm"
      and wf_sch: "wf_SystemSchedule (bmmodel bm) sc"
      and wf_state: "wf_SystemState (bmmodel bm) x"
      and exec_x: "systemExec x = Initialize (scheduleInit sc)"
      and exec_y: "systemExec y = Initialize []"
      and steps: "stepsSys bm com sc x y"
      and vc: "\<And>c. c \<in> modelCIDs (bmmodel bm) \<Longrightarrow> appInitProp (bmbehaviors bm $ c) (P c)"
    shows "sysStateProp bm P y"
proof -
  have i0: "isInitializing x" by (simp add: exec_x)
  have h0: "dom (appovar x) \<subseteq> modelCIDs (bmmodel bm)" 
    using wf_state unfolding appovar_def dom_def wf_SystemState_def by auto
  have h1: "appovar y \<in> {appovar x} ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bm)) (scheduleInit sc))}"
    using exec_x exec_y i0 steps sysInit_init_merge wf_bm wf_sch by blast
  have g0: "\<forall>m \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bm)) (scheduleInit sc))}. dom (appovar x) \<subseteq> dom m"
    using h0 wf_sch unfolding wf_SystemSchedule_def
     by (smt (verit) CollectD map_seq_merge_eq modelCIDs.simps)
  have g1: "appovar y \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bm)) (scheduleInit sc))}"
    by (metis (no_types, lifting) g0 h1 map_Add_extend singleton_iff)
  hence h2: "\<And>c. c \<in> modelCIDs (bmmodel bm) \<Longrightarrow> appovar y $ c \<in> systemAppInit bm c"
  proof -
    fix c
    assume a1: "c \<in> modelCIDs (bmmodel bm)"
    have "card (set (scheduleInit sc)) = length (scheduleInit sc)"
      using wf_SystemSchedule_def wf_sch by presburger
    show "appovar y $ c \<in> systemAppInit bm c"
      using a1 g1 map_seq_merge_el wf_SystemSchedule_def wf_sch by fastforce
  qed
  hence h3: "\<forall>c \<in> modelCIDs (bmmodel bm). 
               (appo (systemThread y $ c), tvar (systemThread y $ c)) \<in> systemAppInit bm c"
    using g1 wf_sch wf_state unfolding wf_SystemSchedule_def
    by (smt (verit, best) CollectD domIff map_seq_merge_eq map_some_val_given modelCIDs.simps appovar_def)
  have h4: "\<forall>c \<in> modelCIDs (bmmodel bm). P c (appo (systemThread y $ c), tvar (systemThread y $ c))"
    by (smt (verit, best) appInitProp_def h3 mem_Collect_eq systemAppInit_def vc)
  thus ?thesis using sysStateProp_def by blast 
qed

definition sysAppInvProp ::   "CompIds 
                            \<Rightarrow> (CompId \<Rightarrow> ('a PortState \<times> 'a VarState \<Rightarrow> bool))
                            \<Rightarrow> (CompId \<Rightarrow> 'a VarState \<Rightarrow> bool)
                            \<Rightarrow> bool"
  where "sysAppInvProp cids P I \<equiv> \<forall>c \<in> cids. \<forall>ao tvo. P c (ao, tvo) \<longrightarrow> I c tvo"

(* App computation invariant I on local variables and output port properties P. *)
(* All other port properties must be guaranteed on system level. *)
(* Also system-wide invariants must be dealt with globally, assume substrate properties. *)
definition appInvProp ::   
   " 'a AppBehavior \<Rightarrow> 
    ('a VarState \<Rightarrow> bool) \<Rightarrow>  \<comment> \<open>Invariant on variable states\<close> 
    (('a PortState \<times> 'a VarState) \<Rightarrow> bool) \<Rightarrow> 
    bool"
  where "appInvProp a I P \<equiv> 
   \<forall>ai tvi d ao tvo. (I tvi) \<and> ((appCompute a) ai tvi d ao tvo) \<longrightarrow> (I tvo) \<and> P (ao, tvo)"

definition sysInvProp ::
  "'a BehaviorModel
     \<Rightarrow> ScheduleState \<times> ScheduleState
        \<Rightarrow> (CompId \<Rightarrow> 'a VarState \<Rightarrow> bool)
           \<Rightarrow> (CompId \<Rightarrow> 'a PortState \<times> 'a VarState \<Rightarrow> bool) 
             \<Rightarrow> bool"
  where "sysInvProp bm sc I P \<equiv>
  \<forall>c \<in>  modelCIDs (bmmodel bm). 
    \<forall>(t:: 'a ThreadState) t'. I c (tvar t) \<and> 
      stepThread (computeDispatchStatus (bmmodel bm) c) 
                 (kindPID (bmmodel bm)) 
                 ((bmbehaviors bm) $ c) 
                 sc 
                 t t' 
      \<longrightarrow> I c (tvar t) \<and> P c (appo t, tvar t)"

lemma "\<lbrakk> (stepSys am cm sc)\<^sup>*\<^sup>* s s'; isInitializing s' \<rbrakk> \<Longrightarrow> (initStepSys am cm sc)\<^sup>*\<^sup>* s s'"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  have h: "isInitializing b"
    using rtrancl_into_rtrancl.hyps(2) rtrancl_into_rtrancl.prems stepSys_initializing_back by blast
  hence "(initStepSys am cm sc)\<^sup>*\<^sup>* a b" using rtrancl_into_rtrancl.IH by blast
  then show ?case by (meson h rtrancl_into_rtrancl.hyps(2) rtranclp.simps stepSys_initializing)
qed

lemma "\<lbrakk> (stepSys am cm sc)\<^sup>*\<^sup>* s s'; isComputing s \<rbrakk> \<Longrightarrow> (computeStepSys am cm sc)\<^sup>*\<^sup>* s s'"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  have h: "(computeStepSys am cm sc)\<^sup>*\<^sup>* a b" 
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems by blast
  have "isComputing b"
    using rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems 
    apply simp by (metis Exec.distinct(1) Exec.exhaust sysInit_seq_bw_supseq)
  then show ?case using initialize_not_compute
    by (meson h rtrancl_into_rtrancl.hyps(2) rtranclp.rtrancl_into_rtrancl stepSys_def)
qed

lemma stepSysDcmpL: "(stepSys am cm sc)\<^sup>*\<^sup>* s s' \<Longrightarrow> ((initStepSys am cm sc)\<^sup>*\<^sup>* OO (computeStepSys am cm sc)\<^sup>*\<^sup>*) s s'"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  obtain x where x1: "(initStepSys am cm sc)\<^sup>*\<^sup>* a x" and x2: "(computeStepSys am cm sc)\<^sup>*\<^sup>* x b"
    using rtrancl_into_rtrancl.IH by blast
  then show ?case
  proof (cases "x = b")
    case True
    then show ?thesis by (metis relcomppI rtrancl_into_rtrancl.hyps(2) rtranclp.simps stepSys_def x1)
  next
    case False
    have "isComputing x" using False compute_not_initialize
      by (metis Exec.exhaust converse_rtranclpE init_init isComputing.elims(3) x2)
    hence "computeStepSys am cm sc b c" 
      using stepSys_def stepSys_initializing_back x2 compute_not_initialize initialize_not_compute
      by (metis Exec.exhaust isComputing.simps isInitializing.elims(3) rtrancl_into_rtrancl.hyps(2) rtranclp.cases)
    then show ?thesis using x1 x2 by auto
  qed
qed

lemma stepSysDcmpR:
  assumes "((initStepSys am cm sc)\<^sup>*\<^sup>* OO (computeStepSys am cm sc)\<^sup>*\<^sup>*) s s'"
  shows "(stepSys am cm sc)\<^sup>*\<^sup>* s s'"
proof -
  have "((stepSys am cm sc)\<^sup>*\<^sup>* OO (stepSys am cm sc)\<^sup>*\<^sup>*) s s'"
    using stepSys_init_rtranclp stepSys_compute_rtranclp using assms by blast
  thus ?thesis by force
qed

lemma stepSysDcmp: "(stepSys am cm sc)\<^sup>*\<^sup>* = (initStepSys am cm sc)\<^sup>*\<^sup>* OO (computeStepSys am cm sc)\<^sup>*\<^sup>*"
proof -
  have "\<And>s s'. (stepSys am cm sc)\<^sup>*\<^sup>* s s' = ((initStepSys am cm sc)\<^sup>*\<^sup>* OO (computeStepSys am cm sc)\<^sup>*\<^sup>*) s s'"
    using stepSysDcmpL stepSysDcmpR by metis
  thus ?thesis by presburger
qed

lemma sysBehaviorDcmp:
  assumes wf_bm: "wf_BehaviorModel bm"
      and wf_sch: "wf_SystemSchedule (bmmodel bm) sc"
      and init: "initSys bm sc x"
      and steps: "stepsSys bm cm sc x z"
      and comp: "isComputing z"
      and vc: "\<And>c. c \<in> modelCIDs (bmmodel bm) \<Longrightarrow> appInitProp (bmbehaviors bm $ c) (P c)"
    shows "\<exists>y. initStepsSys bm cm sc x y \<and> sysStateProp bm P y \<and> computeStepsSys bm cm sc y z"
proof -
  obtain y where y1: "(initStepSys bm cm sc)\<^sup>*\<^sup>* x y" and y2: "(computeStepSys bm cm sc)\<^sup>*\<^sup>* y z"
    by (metis pick_middlep stepSysDcmpL steps stepsSys_def)
  have h1: "isInitializing x" using init initSys_def by auto
  have h2: "isComputing y" using y2 comp compute_compute compute_not_initialize
    by (metis Exec.exhaust converse_rtranclpE isInitializing.simps)
  have "x \<noteq> y" using compute_not_init h1 h2 by blast
  then obtain y' where y3: "(initStepSys bm cm sc)\<^sup>*\<^sup>* x y'" and y4: "initStepSys bm cm sc y' y"
    by (metis rtranclp.cases y1)
  have h3: "systemExec y' = Initialize []"
    by (meson compute_not_init h2 initStepSys.cases stepSysInit_initInv_ruleinv stepSys_init y4)
  have h4: "systemExec x = Initialize (scheduleInit sc)" using init initSys_def by blast
  have h5: "wf_SystemState (bmmodel bm) x" using init initSys_def by blast
  have "sysStateProp bm P y'"
    using sysInit_state_prop[of bm sc x y' cm P] using wf_bm wf_sch using h3 h4 vc y3 h5 
    by (metis stepSys_init_rtranclp stepsSys_def)
  hence "sysStateProp bm P y"
    using y4 h2 stepSys_init[of bm cm sc y' y] unfolding sysStateProp_def apply clarify
    using initStepSys.simps stepSysInit_initInv_ruleinv by fastforce
  then show ?thesis by (metis computeStepsSys_def initStepsSys_def y1 y2)
qed

(*
lemma sysThreadInv:
  assumes wf_am: "wf_AppModel am"
      and valid: "c \<in> appModelCIDs am"
      and isat: "I c (tvar x)"
      and inv: "appInvProp (appModelApp am $ c) (I c) (P c)"
    shows "sysInvProp am sc I P"
  using wf_am unfolding wf_AppModel_def wf_CIDAppCIDAPP_def wf_CIDApp_def
  by blast


lemma sysThreadInv1:
  assumes wf_am: "wf_AppModel am"
      and vc: "\<And>c. \<lbrakk>c \<in> appModelCIDs am; I c (tvar x)\<rbrakk> \<Longrightarrow> appInvProp (appModelApp am $ c) (I c) (P c)"
      and step: "stepComp (computeDispatchStatus (appModel am) c) (appModelApp am $ c) sc x y"
    shows "sysInvProp am sc I P"
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