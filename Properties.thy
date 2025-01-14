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

definition appInitProp :: "'a AppBehavior \<Rightarrow> ('a PortState * 'a VarState \<Rightarrow> bool) \<Rightarrow> bool"
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

definition sysInitProp :: "Model \<Rightarrow> 'a AppBehaviors \<Rightarrow> (CompId \<Rightarrow> ('a PortState * 'a VarState  \<Rightarrow> bool)) => bool"
  where "sysInitProp md bv P \<equiv>
  \<forall>c \<in> modelCIDs md. \<forall>(t::'a ThreadState) t'. stepInit (bv $ c) t t' \<longrightarrow> P c (appo t', tvar t')"

text \<open>Now, we set up a verification condition \<open>sysInitVC\<close> 
for a system initialization property \<open>P\<close>.
We intend to show that, to verify a system initialization property \<open>P\<close> (i.e., to show
that \<open>P\<close> holds for an app model \<open>am\<close>, it is sufficient to show that for every
thread component \<open>c\<close> in the model, the \<open>c\<close>-relevant portion of \<open>P\<close>
is an thread initialization property (\<open>appInitProp\<close>) for \<open>c\<close> (i.e., for
\<open>c\<close>'s application logic).\<close>

definition sysInitVC :: "Model \<Rightarrow> 'a AppBehaviors \<Rightarrow> (CompId \<Rightarrow> ('a PortState * 'a VarState  \<Rightarrow> bool)) => prop"
  where "sysInitVC md bv P \<equiv> 
  (\<And>c. c \<in> modelCIDs md \<Longrightarrow> appInitProp (bv $ c) (P c))"

text \<open>The following lemma establishes that \<open>sysInitVC\<close> is a sound verification
condition for system initialization property \<open>P\<close>: for a well-formed app model \<open>am\<close>,
if \<open>sysInitVC\<close> holds, then \<open>sysInitProp\<close> holds.\<close>

lemma initSysFromApps:
  assumes wf_bm: "wf_Model (md::Model)"
      and wf_bm: "wf_AppBehaviors md (bv::'a AppBehaviors)"
      and vc: "\<And>c. c \<in> modelCIDs md \<Longrightarrow> appInitProp (bv $ c) (P c)"
    shows "sysInitProp md bv P"
proof (simp only: sysInitProp_def; clarify)
  fix c
  fix t t'::"'a ThreadState"
  assume a1: "c \<in> modelCIDs md"
     and a2: "stepInit (bv $ c) t t'"
  thus "P c (appo t', tvar t')"
  proof -
    have "appInit (bv $ c) (appo t') (tvar t')" 
      using a2 stepInit_ruleinv[of "(bv $ c)" t t'] by blast
    thus ?thesis
      using a1 appInitProp_def vc by blast 
  qed
qed

text \<open>The following definition will interpret a system initialization property
\<open>P\<close> in the context of a specific system state \<open>s\<close>.\<close>

definition sysStateProp :: "Model \<Rightarrow> 
  (CompId \<Rightarrow> ('a PortState * 'a VarState \<Rightarrow> bool)) \<Rightarrow> 
  ('u, 'a) SystemState \<Rightarrow> bool"
where "sysStateProp md P s \<equiv>
  \<forall>c \<in> modelCIDs md. P c (appo (systemThread s $ c), tvar (systemThread s $ c))"

text \<open>The following definition forms the set of all possible Initialization Entrypoint
outputs of thread component \<open>c\<close>, where outputs are pairs of var states (\<open>tvar\<close>) \<open>v\<close> and application
output port states (\<open>appo\<close>) \<open>ao\<close>.\<close>

definition systemAppInit :: "'a AppBehaviors \<Rightarrow> CompId \<Rightarrow> ('a PortState \<times> 'a VarState ) set"
  where "systemAppInit bv c = { (ao, tvo) | ao tvo. appInit (bv $ c) ao tvo }"

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
  shows "\<lbrakk>stepSys md bv com sc x y; systemExec y = Initialize cs \<rbrakk> \<Longrightarrow> systemExec x \<noteq> Initialize []"
  using stepSysInit_sc_rev_ruleinv by fastforce

lemma sysInit_seq_bw_neq:
  "\<lbrakk>(stepSys md bv com sc)\<^sup>*\<^sup>* x y; x \<noteq> y; systemExec y = Initialize cs\<rbrakk> \<Longrightarrow> systemExec x \<noteq> Initialize []"
proof (induction arbitrary: cs rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  have h1: "(stepSys md bv com sc)\<^sup>*\<^sup>* a b" using rtrancl_into_rtrancl.hyps(1) by blast
  have h2: "stepSys md bv com sc b c" using rtrancl_into_rtrancl.hyps(2) by blast
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
  "\<lbrakk>(stepSys md bv com sc)\<^sup>*\<^sup>* x y; systemExec y = Initialize cs \<rbrakk> \<Longrightarrow> (\<exists>as. systemExec x = Initialize (as @ cs))"
proof (induction arbitrary: cs rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (metis append.assoc append_Cons append_Nil stepSysInit_sc_rev_ruleinv)
qed

lemma sysInit_none:
  "\<lbrakk>stepSys md bv com sc x y; systemExec y = Initialize cs; systemExec x = Initialize cs \<rbrakk> \<Longrightarrow> x = y"
  using stepSysInit_sc_rev_ruleinv by fastforce

lemma sysInit_seq_none:
  "\<lbrakk>(stepSys md bv com sc)\<^sup>*\<^sup>* x y; systemExec y = Initialize cs; systemExec x = Initialize cs \<rbrakk> \<Longrightarrow> x = y"
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
  assumes step: "stepSys md bv com sc x y"
      and exec: "systemExec x = Initialize (c # cs)"
    shows "appovar y \<in> { (appovar x)(c\<mapsto>v) |v. v \<in> systemAppInit bv c }"
proof -
  have "stepSys md bv com sc x y = initStepSys md bv com sc x y"
    using stepSys_initializing exec init_init by blast
  hence "initStepSys md bv com sc x y" using step by force
  thus ?thesis using exec
  proof (induction rule: initStepSys.induct)
    case (initialize s c cs t)
    obtain ps vs where h2: "appovar (s\<lparr> systemThread := (systemThread s)(c \<mapsto> t), 
                                        systemExec := Initialize cs\<rparr>) c = Some (ps, vs)"
      using appovar_def domI fun_upd_same
      by (metis SystemState.SystemState.simps(1) SystemState.SystemState.simps(9) 
          SystemState.SystemState.surjective SystemState.SystemState.update_convs(1))
    hence h3: "(ps, vs) \<in> systemAppInit bv c" unfolding systemAppInit_def appovar_def apply clarify
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
  assumes step: "stepSys md bv com sc x y"
      and exec: "systemExec x = Initialize (c # cs)"
    shows "appovar y \<in> map_Upd_seq (systemAppInit bv) {appovar x} [c]"
proof -
  have "stepSys md bv com sc x y = initStepSys md bv com sc x y"
    using step stepSys_initializing exec init_init by blast
  hence h0: "initStepSys md bv com sc x y" using step by force
  thus ?thesis using exec
  proof (induction rule: initStepSys.induct)
    case (initialize s a as t)
      have h1: "a = c" using initialize.hyps(2) initialize.prems(1) by fastforce
      have h2: "as = cs" using initialize.hyps(2) initialize.prems(1) by fastforce
      have h3: "map_Upd_seq (systemAppInit bv) {appovar s} [c] = { (appovar s)(c\<mapsto>v) |v. v \<in> systemAppInit bv c }"
        by simp
      show ?case
        using step exec h0 sysInit_step_seq_set[of md bv com sc s y c cs] 
          initStepSys.initialize[of s c cs bv t] initialize.hyps(1) initialize.hyps(3)
        apply (simp add: h1 h2 h3) 
        using stepSys_initializing sysInit_step_seq_set
        by (smt (verit, best) \<open>\<And>sc cm. \<lbrakk>isInitializing s; systemExec s = Initialize (c # cs); stepInit (bv $ c) (systemThread s $ c) t\<rbrakk> \<Longrightarrow> initStepSys md bv cm sc s (s\<lparr>systemThread := (systemThread s) (c \<mapsto> t), systemExec := Initialize cs\<rparr>)\<close> h1 h2 initialize.hyps(1) initialize.hyps(2) initialize.hyps(3) mem_Collect_eq old.prod.exhaust)
    next
      case (switch c) 
        show ?case using exec switch.hyps(2) by (simp add: switch.prems)
    qed
qed

text \<open>Lemma {sysInit\_seq} is used to prove lemma {sysInit\_init\_seq} by induction.\<close>

lemma sysInit_seq:
  "\<lbrakk> stepsSys md bv com sc x y;
     systemExec x = Initialize xs; systemExec y = Initialize [] \<rbrakk> \<Longrightarrow> 
     appovar y \<in> map_Upd_seq (systemAppInit bv) {appovar x} xs"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case unfolding appovar_def stepsSys_def using sysInit_seq_none by fastforce
next
  case (Cons a xs)
  have h1: "isInitializing x" by (simp add: Cons.prems(2))
  obtain z where z1: "stepSys md bv com sc x z" 
             and z2: "stepsSys md bv com sc z y"
    using Cons.prems unfolding stepsSys_def
    by (metis Exec.inject(1) converse_rtranclpE list.distinct(1))
    have z3: "systemExec z = Initialize (xs)" using z1 h1 Cons.prems(2) stepSysInit_redsch_ruleinv by blast
    have z4: "appovar z \<in> map_Upd_seq (systemAppInit bv) {appovar x} [a]" 
      using sysInit_step_seq Cons.prems(3) z1 Cons.prems(2) by blast
  show ?case using Cons.prems Cons.IH[of z] z1 z2 z3 z4
    by (metis (no_types, opaque_lifting) append_Cons append_Nil map_Upd_seq_comp_in)
qed

text \<open>Lemma {sysInit\_init\_seq} shows that the system initialisations can also be expressed by 
means of the recursive function \<open>map_Upd_seq\<close>.\<close>

lemma sysInit_init_seq:
  assumes steps: "stepsSys md bv com sc x y"
      and exec_x: "systemExec x = Initialize (scheduleInit sc)"
      and exec_y: "systemExec y = Initialize []"
    shows "appovar y \<in> map_Upd_seq (systemAppInit bv) {appovar x} (scheduleInit sc)"
  using assms by (simp add: sysInit_seq)

text \<open>Lemma {sysInit\_init\_merge} shows that the order of initialisations does not matter.\<close>

lemma sysInit_init_merge:
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and steps: "stepsSys md bv com sc x y"
      and exec_x: "systemExec x = Initialize (scheduleInit sc)"
      and exec_y: "systemExec y = Initialize []"
    shows "appovar y \<in> 
    {appovar x} ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bv)) (scheduleInit sc))}"
proof -
  have h0: "isInitializing x" by (simp add: exec_x)
  have h1: "card (set (scheduleInit sc)) = length (scheduleInit sc)"
    using wf_sch unfolding wf_SystemSchedule_def by simp
  have h2: "\<forall>c \<in> modelCIDs md. (\<exists>ws qs. appInit (bv $ c) ws qs)"
    using wf_bm wf_bv unfolding wf_Model_def wf_AppBehaviors_def wf_AppBehavior_def wf_InitBehavior_Inhabited_def
    by blast
  hence h3: "\<forall>x \<in> set (scheduleInit sc). systemAppInit bv x \<noteq> {}"
    using wf_sch unfolding wf_SystemSchedule_def systemAppInit_def by simp
  show ?thesis 
    using exec_x exec_y h0 steps h1 h3 
      sysInit_init_seq[of md bv com sc x y] 
      map_Upd_Merge[of "(scheduleInit sc)" "(systemAppInit bv)" "{appovar x}"]
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
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and wf_state: "wf_SystemState md x"
      and exec_x: "systemExec x = Initialize (scheduleInit sc)"
      and exec_y: "systemExec y = Initialize []"
      and steps: "stepsSys md bv com sc x y"
      and vc: "\<And>c. c \<in> modelCIDs md \<Longrightarrow> appInitProp (bv $ c) (P c)"
    shows "sysStateProp md P y"
proof -
  have i0: "isInitializing x" by (simp add: exec_x)
  have h0: "dom (appovar x) \<subseteq> modelCIDs md" 
    using wf_state unfolding appovar_def dom_def wf_SystemState_def by auto
  have h1: "appovar y \<in> {appovar x} ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bv)) (scheduleInit sc))}"
    using exec_x exec_y i0 steps sysInit_init_merge wf_bm wf_bv wf_sch by blast
  have g0: "\<forall>m \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bv)) (scheduleInit sc))}. dom (appovar x) \<subseteq> dom m"
    using h0 wf_sch unfolding wf_SystemSchedule_def
     by (smt (verit) CollectD map_seq_merge_eq modelCIDs.simps)
  have g1: "appovar y \<in> {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms (map (maps_of (systemAppInit bv)) (scheduleInit sc))}"
    by (metis (no_types, lifting) g0 h1 map_Add_extend singleton_iff)
  hence h2: "\<And>c. c \<in> modelCIDs md \<Longrightarrow> appovar y $ c \<in> systemAppInit bv c"
  proof -
    fix c
    assume a1: "c \<in> modelCIDs md"
    have "card (set (scheduleInit sc)) = length (scheduleInit sc)"
      using wf_SystemSchedule_def wf_sch by presburger
    show "appovar y $ c \<in> systemAppInit bv c"
      using a1 g1 map_seq_merge_el wf_SystemSchedule_def wf_sch by fastforce
  qed
  hence h3: "\<forall>c \<in> modelCIDs md. 
               (appo (systemThread y $ c), tvar (systemThread y $ c)) \<in> systemAppInit bv c"
    using g1 wf_sch wf_state unfolding wf_SystemSchedule_def
    by (smt (verit, best) CollectD domIff map_seq_merge_eq map_some_val_given modelCIDs.simps appovar_def)
  have h4: "\<forall>c \<in> modelCIDs md. P c (appo (systemThread y $ c), tvar (systemThread y $ c))"
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
  "Model
     \<Rightarrow> 'a AppBehaviors
        \<Rightarrow> ScheduleState \<times> ScheduleState
           \<Rightarrow> (CompId \<Rightarrow> 'a VarState \<Rightarrow> bool)
              \<Rightarrow> (CompId \<Rightarrow> 'a PortState \<times> 'a VarState \<Rightarrow> bool) 
                 \<Rightarrow> bool"
  where "sysInvProp md bv sc I P \<equiv>
  \<forall>c \<in>  modelCIDs md. 
    \<forall>(t:: 'a ThreadState) t'. I c (tvar t) \<and> 
      stepThread md c (bv $ c) sc t t' 
      \<longrightarrow> I c (tvar t) \<and> P c (appo t, tvar t)"

lemma "\<lbrakk> (stepSys md bv cm sc)\<^sup>*\<^sup>* s s'; isInitializing s' \<rbrakk> \<Longrightarrow> (initStepSys md bv cm sc)\<^sup>*\<^sup>* s s'"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  have h: "isInitializing b"
    using rtrancl_into_rtrancl.hyps(2) rtrancl_into_rtrancl.prems stepSys_initializing_back by blast
  hence "(initStepSys md bv cm sc)\<^sup>*\<^sup>* a b" using rtrancl_into_rtrancl.IH by blast
  then show ?case by (meson h rtrancl_into_rtrancl.hyps(2) rtranclp.simps stepSys_initializing)
qed

lemma "\<lbrakk> (stepSys md bv cm sc)\<^sup>*\<^sup>* s s'; isComputing s \<rbrakk> \<Longrightarrow> (computeStepSys md bv cm sc)\<^sup>*\<^sup>* s s'"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  have h: "(computeStepSys md bv cm sc)\<^sup>*\<^sup>* a b" 
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems by blast
  have "isComputing b"
    using rtrancl_into_rtrancl.hyps(1) rtrancl_into_rtrancl.prems 
    apply simp by (metis Exec.distinct(1) Exec.exhaust sysInit_seq_bw_supseq)
  then show ?case using initialize_not_compute
    by (meson h rtrancl_into_rtrancl.hyps(2) rtranclp.rtrancl_into_rtrancl stepSys_def)
qed

lemma stepSysDcmpL: "(stepSys md bv cm sc)\<^sup>*\<^sup>* s s' \<Longrightarrow> ((initStepSys md bv cm sc)\<^sup>*\<^sup>* OO (computeStepSys md bv cm sc)\<^sup>*\<^sup>*) s s'"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  obtain x where x1: "(initStepSys md bv cm sc)\<^sup>*\<^sup>* a x" and x2: "(computeStepSys md bv cm sc)\<^sup>*\<^sup>* x b"
    using rtrancl_into_rtrancl.IH by blast
  then show ?case
  proof (cases "x = b")
    case True
    then show ?thesis by (metis relcomppI rtrancl_into_rtrancl.hyps(2) rtranclp.simps stepSys_def x1)
  next
    case False
    have "isComputing x" using False compute_not_initialize
      by (metis Exec.exhaust converse_rtranclpE init_init isComputing.elims(3) x2)
    hence "computeStepSys md bv cm sc b c" 
      using stepSys_def stepSys_initializing_back x2 compute_not_initialize initialize_not_compute
      by (metis Exec.exhaust isComputing.simps isInitializing.elims(3) rtrancl_into_rtrancl.hyps(2) rtranclp.cases)
    then show ?thesis using x1 x2 by auto
  qed
qed

lemma stepSysDcmpR:
  assumes "((initStepSys md bv cm sc)\<^sup>*\<^sup>* OO (computeStepSys md bv cm sc)\<^sup>*\<^sup>*) s s'"
  shows "(stepSys md bv cm sc)\<^sup>*\<^sup>* s s'"
proof -
  have "((stepSys md bv cm sc)\<^sup>*\<^sup>* OO (stepSys md bv cm sc)\<^sup>*\<^sup>*) s s'"
    using stepSys_init_rtranclp stepSys_compute_rtranclp using assms by blast
  thus ?thesis by force
qed

lemma stepSysDcmp: "(stepSys md bv cm sc)\<^sup>*\<^sup>* = (initStepSys md bv cm sc)\<^sup>*\<^sup>* OO (computeStepSys md bv cm sc)\<^sup>*\<^sup>*"
proof -
  have "\<And>s s'. (stepSys md bv cm sc)\<^sup>*\<^sup>* s s' = ((initStepSys md bv cm sc)\<^sup>*\<^sup>* OO (computeStepSys md bv cm sc)\<^sup>*\<^sup>*) s s'"
    using stepSysDcmpL stepSysDcmpR by metis
  thus ?thesis by presburger
qed

lemma stepsSysDcmp: "stepsSys md bv cm sc x z = (\<exists>y. initStepsSys md bv cm sc x y \<and> computeStepsSys md bv cm sc y z)"
  by (simp add: computeStepsSys_def initStepsSys_def relcompp_apply stepSysDcmp stepsSys_def)

lemma sysBehaviorDcmp:
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and init: "initSys md sc x"
      and steps: "stepsSys md bv cm sc x z"
      and comp: "isComputing z"
      and vc: "\<And>c. c \<in> modelCIDs md \<Longrightarrow> appInitProp (bv $ c) (P c)"
    shows "\<exists>y. initStepsSys md bv cm sc x y \<and> sysStateProp md P y \<and> computeStepsSys md bv cm sc y z"
proof -
  obtain y where y1: "(initStepSys md bv cm sc)\<^sup>*\<^sup>* x y" and y2: "(computeStepSys md bv cm sc)\<^sup>*\<^sup>* y z"
    by (metis pick_middlep stepSysDcmpL steps stepsSys_def)
  have h1: "isInitializing x" using init initSys_def by auto
  have h2: "isComputing y" using y2 comp compute_compute compute_not_initialize
    by (metis Exec.exhaust converse_rtranclpE isInitializing.simps)
  have "x \<noteq> y" using compute_not_init h1 h2 by blast
  then obtain y' where y3: "(initStepSys md bv cm sc)\<^sup>*\<^sup>* x y'" and y4: "initStepSys md bv cm sc y' y"
    by (metis rtranclp.cases y1)
  have h3: "systemExec y' = Initialize []"
    by (meson compute_not_init h2 initStepSys.cases stepSysInit_initInv_ruleinv stepSys_init y4)
  have h4: "systemExec x = Initialize (scheduleInit sc)" using init initSys_def by blast
  have h5: "wf_SystemState md x" using init initSys_def by blast
  have "sysStateProp md P y'"
    using sysInit_state_prop[of md bv sc x y' cm P] using wf_bm wf_bv wf_sch using h3 h4 vc y3 h5 
    by (metis stepSys_init_rtranclp stepsSys_def)
  hence "sysStateProp md P y"
    using y4 h2 stepSys_init[of md bv cm sc y' y] unfolding sysStateProp_def apply clarify
    using initStepSys.simps stepSysInit_initInv_ruleinv by fastforce
  then show ?thesis by (metis computeStepsSys_def initStepsSys_def y1 y2)
qed

lemma sys_init_wf_ThreadState:
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and init: "initSys md sc x"
    shows "wf_SystemState md x"
  using init initSys_def by blast

lemma sys_initState_wf_ThreadState:
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and wf_x: "wf_SystemState md x"
      and init: "isInitializing x"
      and steps: "initStepsSys md bv cm sc x y"
    shows "wf_SystemState md y"
  using steps init wf_x unfolding initStepsSys_def
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl x)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl x y z)
  show ?case using rtrancl_into_rtrancl.hyps(2)
  proof cases
    case (initialize c cs t)
      have a1: "dom (systemThread y) \<subseteq> modelCIDs md" 
        using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems wf_SystemState_def by blast
      have a2: "wf_SystemState_ThreadStates md y" 
        using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems wf_SystemState_def by blast
      have a3: "wf_SystemState_ThreadStates_dom md y"
        using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems wf_SystemState_def by blast
      have a4: "wf_ThreadState md c (systemThread y $ c)"
        using wf_bv unfolding wf_AppBehaviors_def wf_AppBehavior_def
        using a2 a3 unfolding wf_SystemState_ThreadStates_def wf_SystemState_ThreadStates_dom_def 
        by simp
      have a5: "wf_AppBehavior md c (bv $ c)" using wf_AppBehaviors_def wf_bv by blast
      have a6: "wf_ThreadState md c t" using local.initialize(4)
      proof cases
        case (initialize ao tvo)
          have b1: "wf_ThreadState_infi md c (infi t)" 
            using a4 local.initialize(1) wf_ThreadState_def by auto
          have b2: "wf_ThreadState_appi md c (appi t)" 
            using a4 local.initialize(1) wf_ThreadState_def by auto
          have b3: "wf_ThreadState_appo md c (appo t)" 
            using a5 local.initialize unfolding wf_AppBehavior_def wf_InitBehavior_def
            using stepInit.simps stepInit_ruleinv by blast
          have b4: "wf_ThreadState_info md c (info t)"
            using a4 local.initialize(1) wf_ThreadState_def by auto
          have b5: "wf_ThreadState_tvar md c (tvar t)" 
            using a5 local.initialize unfolding wf_AppBehavior_def wf_InitBehavior_def
            by simp
          have b6: "wf_ThreadState_disp md c (disp t)" 
            using a4 local.initialize(1) wf_ThreadState_def by auto
        show ?thesis using b1 b2 b3 b4 b5 b6 unfolding wf_ThreadState_def by blast
      qed
      have a7: "wf_ThreadState md c ((systemThread y)(c \<mapsto> t) $ c)" by (simp add: a6)
      have a8: "wf_SystemState_ThreadStates md z"
        unfolding a2 a7 local.initialize(1) unfolding wf_SystemState_ThreadStates_def
        apply simp by (metis a2 a6 map_get_def wf_SystemState_ThreadStates_def)
      have a9: "wf_SystemState_ThreadStates_dom md z"
        using a3 wf_bv local.initialize(1) 
        unfolding wf_AppBehavior_def wf_AppBehaviors_def wf_SystemState_ThreadStates_dom_def
        apply simp by blast
    then show ?thesis
      by (simp add: a8 wf_SystemState_ThreadStates_dom_def wf_SystemState_def)
  next
    case (switch c)
    then show ?thesis
      using local.rtrancl_into_rtrancl(3) local.rtrancl_into_rtrancl(4) local.rtrancl_into_rtrancl(5)
      unfolding wf_SystemState_ThreadStates_def wf_SystemState_ThreadStates_dom_def wf_SystemState_def
      by simp
  qed
qed

lemma sys_initSteps_wf_ThreadState:
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and init: "initSys md sc x"
      and steps: "initStepsSys md bv cm sc x y"
    shows "wf_SystemState md y"
  using assms sys_initState_wf_ThreadState initSys_def init_init by blast

lemma sys_computeSteps_wf_ThreadState:
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and wf_cm: "wf_Communication md cm"
      and wf_x: "wf_SystemState md x"
      and comp: "isComputing x"
      and steps: "computeStepsSys md bv cm sc x y"
    shows "wf_SystemState md y"
proof -
  have f: "finite (dom (modelPortDescrs md))" 
    using wf_bm unfolding wf_Model_Finite_def wf_Model_def by blast
  show ?thesis using steps comp wf_x unfolding computeStepsSys_def
  proof (induction rule: rtranclp.induct)
    case (rtrancl_refl x)
    then show ?case by blast
  next
    case (rtrancl_into_rtrancl x y z)
    have a1: "dom (systemThread y) \<subseteq> modelCIDs md" 
      using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems wf_SystemState_def by blast
    have a2: "wf_SystemState_ThreadStates md y" 
      using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems wf_SystemState_def by blast
    have a3: "wf_SystemState_ThreadStates_dom md y"
      using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems wf_SystemState_def by blast
    show ?case using rtrancl_into_rtrancl.hyps(2)
    proof cases
      case (push c t sb it)
      have a4: "wf_ThreadState md c (systemThread y $ c)"
        using a2 local.push(3) domI unfolding wf_SystemState_ThreadStates_def by (meson domI)
      have "wf_ThreadState_info md c (info t)"
        using a4 local.push(3) wf_ThreadState_def by auto
      hence a5: "wf_ThreadState_info md c it" using wf_cm unfolding wf_Communication_def
        using local.push(4) wf_bv unfolding wf_AppBehavior_def wf_AppBehaviors_def
        apply simp by fastforce
      have a6: "wf_ThreadState md c (t\<lparr>info := it\<rparr>)" 
        using a4 a5 local.push(3) unfolding wf_ThreadState_def by fastforce
      have a7: "dom (systemThread z) \<subseteq> modelCIDs md"
        using wf_bv unfolding wf_AppBehavior_def wf_AppBehaviors_def by (simp add: subsetI)
      have a8: "wf_SystemState_ThreadStates md z"
        using a2 a3 a6 a7 
        unfolding wf_SystemState_ThreadStates_def wf_SystemState_ThreadStates_dom_def
        by (simp add: local.push(1))
      have a9: "wf_SystemState_ThreadStates_dom md z"
        using a3 local.push(1) local.push(3) unfolding wf_SystemState_ThreadStates_dom_def
        by auto
      then show ?thesis unfolding wf_SystemState_def using a7 a8 by auto
    next
      case (pull c t sb it)
      have a4: "wf_ThreadState md c (systemThread y $ c)"
        using a2 local.pull(3) domI unfolding wf_SystemState_ThreadStates_def by (meson domI)
      have "wf_ThreadState_infi md c (infi t)"
        using a4 local.pull(3) wf_ThreadState_def by auto
      hence a5: "wf_ThreadState_infi md c it" using wf_cm unfolding wf_Communication_def
        using local.pull(4) wf_bv unfolding wf_AppBehavior_def wf_AppBehaviors_def
        apply simp by fastforce
      have a6: "wf_ThreadState md c (t\<lparr>infi := it\<rparr>)" 
        using a4 a5 local.pull(3) unfolding wf_ThreadState_def by fastforce
      have a7: "dom (systemThread z) \<subseteq> modelCIDs md"
        using wf_bv unfolding wf_AppBehavior_def wf_AppBehaviors_def by (simp add: subsetI)
      have a8: "wf_SystemState_ThreadStates md z"
        using a2 a3 a6 a7 
        unfolding wf_SystemState_ThreadStates_def wf_SystemState_ThreadStates_dom_def
        by (simp add: local.pull(1))
      have a9: "wf_SystemState_ThreadStates_dom md z"
        using a3 local.pull(1) local.pull(3) unfolding wf_SystemState_ThreadStates_dom_def
        by auto
      then show ?thesis using a7 a8 wf_SystemState_def by blast
    next
      case (execute c c' a t)
      have a4: "wf_ThreadState md c (systemThread y $ c)"
        using a2 a3 wf_bv unfolding wf_AppBehavior_def wf_AppBehaviors_def 
          wf_SystemState_ThreadStates_def wf_SystemState_ThreadStates_dom_def 
        by simp
      have a5: "wf_AppBehavior md c (bv $ c)" using wf_AppBehaviors_def wf_bv by blast
      have a6: "wf_ThreadState md c t" using local.execute(5)
      proof cases
        case (dispatch dsp)
        have b1: "wf_ThreadState md c ((systemThread y $ c)\<lparr>disp := dsp\<rparr>)"
          using a4 a5 wf_computeDispatchStatus[of md c] wf_ThreadState_def wf_bm
          unfolding wf_AppBehavior_def using local.dispatch(2) by fastforce
        have b2: "inModelCID md c" using a5 unfolding wf_AppBehavior_def by simp
        have "dispatchInputPorts dsp \<subseteq> inPortsOfCID md c"
        proof (cases dsp)
          case NotEnabled
          then show ?thesis using local.dispatch(3) by blast
        next
          case (Periodic x2)
          then show ?thesis
            using b1 unfolding wf_ThreadState_def wf_ThreadState_disp_def by (simp add: subsetI)
        next
          case (Sporadic x3)
          then show ?thesis
            using b1 unfolding wf_ThreadState_def wf_ThreadState_disp_def
            apply (simp only: disp_elem.simps) by fastforce
        qed
        hence h1: "dispatchInputPorts dsp \<subseteq> dom (modelPortDescrs md)"
          using a5 wf_Model_def wf_bm 
          unfolding wf_AppBehavior_def wf_Model_CompDescrsContainedPortIds_def
          apply (simp add: subset_iff) by blast
        hence b3: "finite (dispatchInputPorts dsp)" by (simp add: f finite_subset)
        have b4: "\<forall>p\<in>dispatchInputPorts dsp. inModelPID md p" using h1 by auto
        then show ?thesis
          using receiveInputs_wf_ThreadState b1 b2 b3 local.dispatch(4) wf_bm by blast
      next
        case (compute ao tvo)
        have b1: "wf_ThreadState_appi md c (appi (systemThread y $ c))" 
          using a4 wf_ThreadState_def by blast
        have b2: "wf_ThreadState_appi md c 
                  (clearAll (dom (appi (systemThread y $ c))) (appi (systemThread y $ c)))"
          using b1 wf_clearAll_appi by blast
        have b3: "wf_ThreadState_appo md c ao" 
          using a5 local.compute(3) 
          unfolding wf_AppBehavior_def wf_ComputeBehavior_def by blast
        have b4: "wf_ThreadState_tvar md c tvo"
          using a5 local.compute(3) 
          unfolding wf_AppBehavior_def wf_ComputeBehavior_def by blast
        show ?thesis unfolding wf_ThreadState_def
          using a4 b2 b3 b4 local.compute(1) wf_ThreadState_def by auto
      next
        case (complete appo' info')
        have b1: "wf_ThreadState_appo md c (appo (systemThread y $ c))"
          using a4 wf_ThreadState_def by blast
        have b2: "wf_ThreadState_info md c (info (systemThread y $ c))"
          using a4 wf_ThreadState_def by blast
        have b3: "wf_ThreadState_appo md c appo' \<and> wf_ThreadState_info md c info'"
          using b1 b2 local.complete(3) sendOutput_wf_PortStates by blast
        then show ?thesis unfolding wf_ThreadState_def
          using a4 local.complete(1) wf_ThreadState_def wf_ThreadState_disp_NotEnabled by auto
      qed
      have a7: "dom (systemThread z) \<subseteq> modelCIDs md"
        using wf_bv unfolding wf_AppBehavior_def wf_AppBehaviors_def by (simp add: subsetI)
      have a8: "wf_SystemState_ThreadStates md z"
        using a2 a3 a6 a7 
        unfolding wf_SystemState_ThreadStates_def wf_SystemState_ThreadStates_dom_def
        by (simp add: local.execute(1))
      have a9: "wf_SystemState_ThreadStates_dom md z"
        using a3 a7 local.execute(1) unfolding wf_SystemState_ThreadStates_dom_def
        by auto
      then show ?thesis using a7 a8 wf_SystemState_def by blast
    qed
  qed
qed

lemma sys_steps_wf_ThreadState:
  assumes wf_bm: "wf_Model md"
      and wf_bv: "wf_AppBehaviors md bv"
      and wf_sch: "wf_SystemSchedule md sc"
      and wf_cm: "wf_Communication md cm"
      and reach: "reachSys md bv cm sc z"
    shows "wf_SystemState md z"  
proof -
  obtain x where x1: "initSys md sc x" and x2: "stepsSys md bv cm sc x z" 
    using reach unfolding reachSys_def by blast
  obtain y where y1: "initStepsSys md bv cm sc x y" and y2: "computeStepsSys md bv cm sc y z"
    using stepsSysDcmp x2 by blast
  have h1: "wf_SystemState md y" 
    using sys_initSteps_wf_ThreadState wf_bm wf_bv wf_sch x1 y1 by blast
  show ?thesis 
  proof (cases "isComputing z")
    case True
    then show ?thesis
      by (metis Exec.exhaust computeStepsSys_def compute_not_initialize 
          converse_rtranclpE h1 init_init isComputing.elims(3) sys_computeSteps_wf_ThreadState 
          wf_bm wf_bv wf_cm wf_sch y2)
  next
    case False
    then show ?thesis
      by (metis Exec.exhaust computeStepsSys_def compute_compute compute_not_initialize 
          converse_rtranclpE h1 isInitializing.simps sys_computeSteps_wf_ThreadState 
          wf_bm wf_bv wf_cm wf_sch y2)
  qed
qed

(* Incremental Invariant (Initialisation) *)
definition appInitIncProp :: "'a AppBehavior \<Rightarrow> ('a PortState * 'a VarState \<Rightarrow> bool) \<Rightarrow> ('a PortState * 'a VarState \<Rightarrow> bool) \<Rightarrow> bool"
  where "appInitIncProp a P Q \<equiv> \<forall>ao tvo. appInit a ao tvo \<and> P (ao, tvo) \<longrightarrow> Q (ao, tvo)"

(* Incremental Invariant (Application Step) *)
definition sysIncInvProp ::
  "Model
     \<Rightarrow> 'a AppBehaviors
        \<Rightarrow> ScheduleState \<times> ScheduleState
           \<Rightarrow> (CompId \<Rightarrow> 'a VarState \<Rightarrow> bool) \<Rightarrow> (CompId \<Rightarrow> 'a VarState \<Rightarrow> bool)
              \<Rightarrow> (CompId \<Rightarrow> 'a PortState \<times> 'a VarState \<Rightarrow> bool) 
                 \<Rightarrow> bool"
  where "sysIncInvProp md bv sc I J P \<equiv>
  \<forall>c \<in>  modelCIDs md. 
    \<forall>(t:: 'a ThreadState) t'. I c (tvar t) \<and> J c (tvar t)\<and> 
      stepThread md c (bv $ c) sc t t'
      \<longrightarrow> J c (tvar t) \<and> P c (appo t, tvar t)"

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