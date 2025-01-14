theory Behavior
  imports SetsAndMaps Model App ThreadState SystemState DispatchLogic RTSRules
begin

section \<open>Thread Execution\<close>

text \<open>The rules in this section reflect how a thread's state is transformed by 
executing the application logic for thread entry points.  The state transformation
for each entry point is determined by the transfer function (relation) derived from the
entry point contract as defined in App.thy. The application logic transfer relation
is defined on the portions of the thread state that are visible to the application code:
the application input port state @{term appi}, the application output port state 
@{term appo} and the thread variables @{term tvar}.   The rules in this section
"lift" the transfer relation from the application-code-visible portions of the state
to the entire thread state.  In addition, for Compute entry point execution,
the rules include invocations of AADL run-time services to manage the enqueuing
and dequeuing of port queues.\<close> 

subsection \<open>Initialize Entry Point\<close>
(* Initialization step *)
(* The well-formedness condition ensures that only the right variables and out-ports are modified. *)

text \<open>The Initialize entry point does not read any portion of the state; it only
gives initial values for output ports and thread variables.
Therefore, the app logic "transfer relation" @{term appInit} degenerates to a predicate
on the application output port state and thread variables.  The rule
below "lifts" that predicate to an "update" the entire thread state.  
Only the elements @{term vs} and @{term ps} are updated.  
The other elements of the thread state are unchanged.\<close>

inductive stepInit for a :: "'a AppBehavior" where
  initialize: "appInit a ao tvo \<Longrightarrow> stepInit a t (t\<lparr> appo:= ao, tvar:= tvo \<rparr>)"

text \<open>Below a rule inversion property is proved that states that if the
thread can do a @{term stepInit} step, it must be the case that the
execution of the thread Initialize application behavior @{term appInit} could produce the values
of the thread variable state and application output port state.\<close>

lemma stepInit_ruleinv:
  assumes "stepInit a t t'"
  shows "appInit a (appo t') (tvar t')"
proof -
  obtain ao tvo where h1: "t' = t\<lparr>appo := ao, tvar := tvo\<rparr>"
                 and h2: "appInit a ao tvo"
    using assms by (metis stepInit.cases)
  have h3: "tvo = tvar t'" using h1
    apply (drule_tac f = tvar in arg_cong)
    by simp
  have h4: "ao = appo t'" using h1
    apply (drule_tac f = appo in arg_cong)
    by simp
  thus ?thesis using h2 h3 h4 by blast
qed


(* Computing step *)
inductive stepThread for md :: "Model"
                     and c :: "CompId"
                     and app :: "'a AppBehavior" 
                     and cat :: "ScheduleState * ScheduleState" (* JH: Stefan says "the state of the control automaton for the thread" *)
                     where
  (* Copy to app input ports*)  (* JH: capturing notion of receive input *)
(* JH: "if there are some values on the infrastructure ports". 
   Stefan says this is a place that we can now improve the formalism by being more 
   precise what the "enabled" logic.  John says "This is related to the AADL dispatch logic" *)
 (* JH *URGENT* Stefan does it work if we move the clearAll from the 
   compute step to right before the receiveInputs, and if we clear both
   app inputs and app outputs?
   Rationale: it is conceptually a bit nicer if in the post-state of compute
   we can evaluate the contract, which references both the appi and appo.
   But now appi is getting cleared at that point.
   It is possible that for a temporary fix, we only need to clear appi immediately
   before the receiveInputs. *)
  dispatch: "\<lbrakk> cat = (Waiting, Ready); 
               dsp \<in> computeDispatchStatus md c (infi t); 
               dsp \<noteq> DispatchStatus.NotEnabled;
               receiveInputs md c (dispatchInputPorts dsp) (t \<lparr> disp:= dsp \<rparr>) t' \<rbrakk>
    \<Longrightarrow> stepThread md c app cat t t'"
  (* Compute next state of thread, reading and writing ports *)
  (* Stefan: appi needs to be updated OR all values get overwritten before the next iteration *)
  (* John: we need to discuss when to clear the port states.
   *)
| compute: "\<lbrakk> cat = (Ready, Running); appCompute app (appi t) (tvar t) (disp t) ao tvo \<rbrakk>
    \<Longrightarrow> stepThread md c app cat t (t\<lparr> appi:= clearAll (dom (appi t)) (appi t), 
                                         appo:= ao,
                                         tvar:= tvo \<rparr>)"
  (* Copy from app output ports *)
| complete: "\<lbrakk> cat = (Running, Waiting); sendOutput (appo t) (info t) appo' info' \<rbrakk>
    \<Longrightarrow> stepThread md c app cat t (t\<lparr> appo:= appo', info:= info', disp:= DispatchStatus.NotEnabled \<rparr>)"

section \<open>System Execution\<close>

(* Constrain allowed initial states *)
definition initSys where "initSys md sc s \<equiv>
  (wf_SystemState md s) \<and>
  (systemExec s = Initialize (scheduleInit sc)) \<and>
  (\<forall>c ts. inModelCID md c \<and> systemThread s c = Some ts \<longrightarrow> initial_ThreadState md c ts)"(* \<and>
  (\<forall>c x. systemState s c = Some x \<longrightarrow> x = Waiting) \<and>
  (systemComms s = {})"*)

(* System initialization step *)
inductive initStepSys for md :: "Model"
                and bv :: "'a AppBehaviors"
                and cm :: "('u, 'a) Communication"
                and sc :: "SystemSchedule" (* two schedulers: one for initialisation, one for computation *)
                (* (substrate state x ports to read), (updated substrate  *)
                where
  (* Carry out initialization steps while possible *)
  initialize: "\<lbrakk> isInitializing s; systemExec s = Initialize (c#cs);
                 stepInit (bv $ c) (systemThread s $ c) t \<rbrakk> \<Longrightarrow> 
  initStepSys md bv cm sc s (s\<lparr> systemThread:= (systemThread s)(c\<mapsto>t), systemExec:= Initialize cs \<rparr>)"
  (* When initialization has terminated, switch to computing phase *)
| switch: "\<lbrakk> isInitializing s; systemExec s = Initialize []; c \<in> scheduleFirst sc \<rbrakk>
    \<Longrightarrow> initStepSys md bv cm sc s (s\<lparr> systemExec:= Compute c \<rparr>)"

(* System computation step *)
inductive computeStepSys for md :: "Model"
                and bv :: "'a AppBehaviors"
                and cm :: "('u, 'a) Communication"
                and sc :: "SystemSchedule" (* two schedulers: one for initialisation, one for computation *)
                (* (substrate state x ports to read), (updated substrate  *)
                where
  (* Copy communication into substrate *)
  push: "\<lbrakk> isComputing s; systemThread s c = Some t; 
           (sb, it) \<in> comPush cm (systemComms s) (info t) (modelConns md) \<rbrakk>
    \<Longrightarrow> computeStepSys md bv cm sc s (s\<lparr>
          systemThread:= (systemThread s)(c\<mapsto>(t\<lparr> info:= it \<rparr>)),
          systemComms:= sb \<rparr>)"
  (* Copy communication from substrate *)
| pull: "\<lbrakk> isComputing s; systemThread s c = Some t; 
           (sb, it) \<in> comPull cm (systemComms s) (infi t) (modelConns md) \<rbrakk> 
    \<Longrightarrow> computeStepSys md bv cm sc s (s\<lparr>
          systemThread:= (systemThread s)(c\<mapsto>(t\<lparr> infi:= it \<rparr>)),
          systemComms:= sb \<rparr>)"
  (* Execute thread 
      - note: kindPID returns a function from PortIds to PortKinds *)
| execute: "\<lbrakk> isComputing s;
              systemExec s = Compute c;
              c' \<in> scheduleComp sc $ c;
              stepThread md c (bv $ c) (systemState s $ c, a) (systemThread s $ c) t \<rbrakk> 
    \<Longrightarrow> computeStepSys md bv cm sc s (s\<lparr> 
          systemThread:= (systemThread s)(c\<mapsto>t), 
          systemState:= (systemState s)(c\<mapsto>a),
          systemExec:= Compute c' \<rparr>)"

lemma compute_not_initialize:
  assumes comp: "computeStepSys md bv cm sc s s'"
  shows "\<not>isInitializing s"
  using assms computeStepSys.cases init_not_compute by blast

lemma initialize_not_compute:
  assumes init: "initStepSys md bv cm sc s s'"
  shows "\<not>isComputing s"
  using assms initStepSys.simps init_not_compute by blast

definition stepSys where
  "stepSys md bv cm sc s s' \<equiv> initStepSys md bv cm sc s s' \<or> computeStepSys md bv cm sc s s'"

lemma stepSys_init: "initStepSys md bv cm sc s s' \<Longrightarrow> stepSys md bv cm sc s s'" by (simp add: stepSys_def)

lemma stepSys_init_rtranclp: "(initStepSys md bv cm sc)\<^sup>*\<^sup>* s s' \<Longrightarrow> (stepSys md bv cm sc)\<^sup>*\<^sup>* s s'" 
  by (metis mono_rtranclp stepSys_init)

lemma stepSys_compute: "computeStepSys md bv cm sc s s' \<Longrightarrow> stepSys md bv cm sc s s'" by (simp add: stepSys_def)

lemma stepSys_compute_rtranclp: "(computeStepSys md bv cm sc)\<^sup>*\<^sup>* s s' \<Longrightarrow> (stepSys md bv cm sc)\<^sup>*\<^sup>* s s'" 
  by (metis mono_rtranclp stepSys_compute)

lemma stepSys_initializing:
  assumes init: "isInitializing s"
  shows "stepSys md bv cm sc s s' = initStepSys md bv cm sc s s'"
  unfolding stepSys_def
  using compute_not_initialize init by blast

lemma stepSys_initializing_back:
  assumes init: "isInitializing s'"
      and step: "stepSys md bv cm sc s s'"
    shows "isInitializing s"
proof -
  have "computeStepSys md bv cm sc s s' \<Longrightarrow> \<not>isInitializing s'"
  proof (induction rule: computeStepSys.induct)
    case (push c t sb it)
    then show ?case apply simp by fastforce
  next
    case (pull c t sb it)
    then show ?case apply simp by fastforce
  next
    case (execute c c' a t)
    then show ?case by simp
  qed
  hence "\<not>computeStepSys md bv cm sc s s'" using init by blast
  hence h2: "initStepSys md bv cm sc s s'" using step unfolding stepSys_def by blast
  thus ?thesis using initStepSys.simps by blast
qed

lemma stepSysInit_ruleinv:
  assumes init: "isInitializing s"
      and exec: "systemExec s = Initialize (x # xs)"
      and step: "stepSys md bv cm sc s s'"
    shows "stepInit (bv $ x) (systemThread s $ x) (systemThread s' $ x)"
proof - 
  \<comment> \<open>First show that @{term initStepSys} rule must have been applied, because the
     @{term Initialize} schedule is not empty.\<close>
  from assms have h1: "initStepSys md bv cm sc s s'" using stepSys_initializing by blast
  \<comment> \<open>Then the result follows by rule cases.\<close>
  from init exec h1 show ?thesis using initStepSys.cases by fastforce
qed

lemma stepSysInit_redsch_ruleinv:
  assumes init: "isInitializing s"
      and exec: "systemExec s = Initialize (x # xs)"
      and step: "stepSys md bv cm sc s s'"
    shows "systemExec s' = Initialize xs"
proof -
  \<comment> \<open>The @{term initStepSys} rule must have been applied, because the
     @{term Initialize} schedule is not empty.\<close>
  from assms have h1: "initStepSys md bv cm sc s s'" using stepSys_initializing by blast
  \<comment> \<open>Then the result follows by rule cases.\<close>
  from init exec h1 show ?thesis using initStepSys.cases by fastforce
qed
  
lemma stepSysInit_initInv_ruleinv:
  assumes init: "isInitializing s"
      and exec: "systemExec s = Initialize (x # xs)"
      and step: "stepSys md bv cm sc s s'"
    shows "isInitializing s'"
proof -
  \<comment> \<open>The @{term initStepSys} rule must have been applied, because the
     @{term Initialize} schedule is not empty.\<close>
  from assms have h1: "initStepSys md bv cm sc s s'" using stepSys_initializing by blast
  \<comment> \<open>Then the result follows by rule cases.\<close>
  from init exec h1 show ?thesis using initStepSys.cases by fastforce
qed

lemma stepSysInit_sc_rev_ruleinv:
  assumes step: "stepSys md bv cm sc s s'"
      and exec: "systemExec s' = Initialize xs"
    shows "\<exists>x. systemExec s = Initialize (x # xs)"
proof -
   \<comment> \<open>Since @{term s'} is initializing, and we took a step, then @{term s} is initializing.\<close>
  from assms have h1: "isInitializing s" using stepSys_initializing_back init_init by blast
   \<comment> \<open>We must have taken an init step from @{term s} to @{term s'}.\<close>
  from assms h1 have h2: "stepSys md bv cm sc s s' = initStepSys md bv cm sc s s'"
    using stepSys_initializing by blast
  from h2 have h3: "initStepSys md bv cm sc s s'" using step unfolding stepSys_def by simp
   \<comment> \<open>..and then the result follows by cases.\<close>
  from h1 h3 exec show ?thesis using initStepSys.cases by fastforce
qed

(* Transitive closure of steps; no traces *)
definition stepsSys where "stepsSys md bv cm sc = (stepSys md bv cm sc)\<^sup>*\<^sup>*"
definition initStepsSys where "initStepsSys md bv cm sc = (initStepSys md bv cm sc)\<^sup>*\<^sup>*"
definition computeStepsSys where "computeStepsSys md bv cm sc = (computeStepSys md bv cm sc)\<^sup>*\<^sup>*"

(* Reachable states from allowed initial states *)
definition reachSys where "reachSys md bv cm sc y \<equiv> 
  \<exists>x. initSys md sc x \<and> stepsSys md bv cm sc x y"

end