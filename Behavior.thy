theory Behavior
  imports SetsAndMaps Model App ThreadState SystemState DispatchLogic
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

inductive stepInit for a :: "'a App" and t :: "'a ThreadState" where
  initialize: "appInit a vs ps \<Longrightarrow> stepInit a t (t\<lparr> tvar:= vs, appo:= ps \<rparr>)"

text \<open>Below a rule inversion property is proved that states that if the
thread can do a @{term stepInit} step, it must be the case that the
execution of the thread Initialize entry logic could produce the values
of the thread variable state and application output port state as
specified by the Initialize application code transfer "relation" @{term appInit}.\<close>

lemma stepInit_ruleinv:
  assumes "stepInit a t t'"
  shows "appInit a (tvar t') (appo t')"
proof -
  obtain vs ps where h1: "t' = t\<lparr>tvar := vs, appo := ps\<rparr>"
                 and h2: "appInit a vs ps"
    using assms by (metis stepInit.cases)
  have h3: "vs = tvar t'" using h1
    apply (drule_tac f = tvar in arg_cong)
    by simp
  have h4: "ps = appo t'" using h1
    apply (drule_tac f = appo in arg_cong)
    by simp
  thus ?thesis using h2 h3 h4 by blast
qed

fun receiveInputSrc where
  "receiveInputSrc pki ps src dst p = (if p \<in> ps then 
  (case pki p of
    Data \<Rightarrow> Some (clear (src $ p))
  | Event \<Rightarrow> Some (tail (src $ p))
  | EventData \<Rightarrow> Some (clear (src $ p))
  )
  else None)"

fun receiveInputDst where
  "receiveInputDst pki ps src dst p = (if p \<in> ps then
  (case pki p of
    Data \<Rightarrow> Some (src $ p )
  | Event \<Rightarrow> Some (setBuffer (dst $ p) [head (src $ p)] )
  | EventData \<Rightarrow> Some (clear (dst $ p))
  )
  else None)"

inductive receiveInput for pki :: "PortId \<Rightarrow> PortKind"
                      and ps :: "PortIds"
                      and src :: "'a PortState"
                      and dst :: "'a PortState" where
  default: "receiveInput pki ps src dst 
              (receiveInputSrc pki ps src dst) 
              (receiveInputDst pki ps src dst)"

inductive sendOutput for src :: "'a PortState"
                      and dst :: "'a PortState" where
  default: "sendOutput src dst (clearAll (dom src) src) src"

(* Computing step *)
inductive stepThread for cds :: "'a PortState \<Rightarrow> DispatchStatus set"
                and pki :: "PortId \<Rightarrow> PortKind"
                and app :: "'a App" (* JH: this provides app "behavior" *)
                and cat :: "ScheduleState * ScheduleState" (* JH: Stefan says "the state of the control automaton for the thread" *)
                and t :: "'a ThreadState" where
  (* Copy to app input ports*)  (* JH: capturing notion of receive input *)
(* JH: "if there are some values on the infrastructure ports". 
   Stefan says this is a place that we can now improve the formalism by being more 
   precise what the "enabled" logic.  John says "This is related to the AADL dispatch logic" *)
  dispatch: "\<lbrakk> cat = (Waiting, Ready); 
               dsp \<in> cds (infi t); 
               dsp \<noteq> DispatchStatus.NotEnabled;
               receiveInput pki (dispatchInputPorts dsp) (infi t) (appi t) infi' appi' \<rbrakk>
    \<Longrightarrow> stepThread cds pki app cat t (t\<lparr> infi:= infi', appi:= appi', disp:= dsp \<rparr>)"
  (* Compute next state of thread, reading and writing ports *)
  (* Stefan: appi needs to be updated OR all values get overwritten before the next iteration *)
| compute: "\<lbrakk> cat = (Ready, Running); appCompute app (tvar t) (appi t) (disp t) ws qs \<rbrakk>
    \<Longrightarrow> stepThread cds pki app cat t (t\<lparr> tvar:= ws, 
                             appi:= clearAll (dom (appi t)) (appi t), 
                             appo:= qs \<rparr>)"
  (* Copy from app output ports *)
| complete: "\<lbrakk> cat = (Running, Waiting); sendOutput (appo t) (info t) appo' info' \<rbrakk>
    \<Longrightarrow> stepThread cds pki app cat t (t\<lparr> appo:= appo', info:= info', disp:= DispatchStatus.NotEnabled \<rparr>)"

(* Constrain allowed initial states *)
definition initSys where "initSys m s \<equiv>
  (isInitializing s) \<and>
  (\<forall>c ts. inModelCID m c \<and> systemThread s c = Some ts \<longrightarrow> initial_ThreadState m c ts) \<and>
  (\<forall>c x. systemState s c = Some x \<longrightarrow> x = Waiting) \<and>
  (systemComms s = {})"

(* System step *)
inductive stepSys for am :: "'a AppModel"
                and cm :: "('u, 'a) Communication"
                and sc :: "SystemSchedule" (* two schedulers: one for initialisation, one for computation *)
                (* (substrate state x ports to read), (updated substrate  *)
                and s :: "('u, 'a) SystemState" where
  (* Carry out initialization steps while possible *)
  initialize: "\<lbrakk> isInitializing s; systemExec s = Initialize (c#cs);
                 stepInit (appModelApp am $ c) (systemThread s $ c) t \<rbrakk> \<Longrightarrow> 
  stepSys am cm sc s (s\<lparr> systemThread:= (systemThread s)(c\<mapsto>t), systemExec:= Initialize cs \<rparr>)"
  (* When initialization has terminated, switch to computing phase *)
| switch: "\<lbrakk> isInitializing s; systemExec s = Initialize []; c \<in> scheduleFirst sc \<rbrakk>
    \<Longrightarrow> stepSys am cm sc s (s\<lparr> systemPhase:= Computing, systemExec:= Compute c \<rparr>)"
  (* Copy communication into substrate *)
| push: "\<lbrakk> isComputing s; systemThread s c = Some t; 
           (sb, it) \<in> comPush cm (systemComms s) (info t) (appModelConns am) \<rbrakk>
    \<Longrightarrow> stepSys am cm sc s (s\<lparr>
          systemThread:= (systemThread s)(c\<mapsto>(t\<lparr> info:= it \<rparr>)),
          systemComms:= sb \<rparr>)"
  (* Copy communication from substrate *)
| pull: "\<lbrakk> isComputing s; systemThread s c = Some t; 
           (sb, it) \<in> comPull cm (systemComms s) (infi t) (appModelConns am) \<rbrakk> 
    \<Longrightarrow> stepSys am cm sc s (s\<lparr>
          systemThread:= (systemThread s)(c\<mapsto>(t\<lparr> infi:= it \<rparr>)),
          systemComms:= sb \<rparr>)"
  (* Execute thread *)
| execute: "\<lbrakk> isComputing s;
              systemExec s = Compute c;
              c' \<in> scheduleComp sc $ c;
              stepThread (computeDispatchStatus (appModel am) c) 
                (appModelPortKind am)
                (appModelApp am $ c) 
                (systemState s $ c, a) 
                (systemThread s $ c) t \<rbrakk> 
    \<Longrightarrow> stepSys am cm sc s (s\<lparr> 
          systemThread:= (systemThread s)(c\<mapsto>t), 
          systemState:= (systemState s)(c\<mapsto>a),
          systemExec:= Compute c' \<rparr>)"

lemma stepSysInit_ruleinv:
  assumes init: "isInitializing s"
      and exec: "systemExec s = Initialize (x # xs)"
      and step: "stepSys am cm sc s s'"
    shows "stepInit (appModelApp am $ x) (systemThread s $ x) (systemThread s' $ x)"
proof -
  have "\<exists>c cs t.
        s' = s\<lparr>systemThread := (systemThread s)(c\<mapsto>t), systemExec := Initialize cs\<rparr> \<and>
        isInitializing s \<and>
        Initialize (x # xs) = Initialize (c # cs) \<and> stepInit (appModelApp am $ c) (systemThread s $ c) t"
    using exec step apply (simp add: stepSys.simps)
    apply (erule disjE)
     apply blast
    apply (erule disjE)
    using init apply force
    using init by force
  then obtain c cs t 
    where h1: "s' = s\<lparr>systemThread := (systemThread s)(c\<mapsto>t), systemExec := Initialize cs\<rparr>"
      and h2: "systemPhase s = Initializing"
      and h3: "systemExec s = Initialize (c # cs)"
      and h4: "stepInit (appModelApp am $ c) (systemThread s $ c) t"
    using exec isInitializing.elims by blast
  have h5: "c = x" using exec h3 by force
  have h6: "t = systemThread s' $ c" by (simp add: h1)
  show ?thesis
    using h4 by (simp add: h5 h6)
qed

lemma stepSysInit_redsch_ruleinv:
  assumes init: "isInitializing s"
      and exec: "systemExec s = Initialize (x # xs)"
      and step: "stepSys am cm sc s s'"
    shows "systemExec s' = Initialize xs"
proof -
  have "\<exists>c cs t.
        s' = s\<lparr>systemThread := (systemThread s)(c\<mapsto>t), systemExec := Initialize cs\<rparr> \<and>
        isInitializing s \<and>
        Initialize (x # xs) = Initialize (c # cs) \<and> stepInit (appModelApp am $ c) (systemThread s $ c) t"
    using exec step apply (simp add: stepSys.simps)
    apply (erule disjE)
     apply blast
    apply (erule disjE)
    using init apply force
    using init by force
  then obtain c cs t 
    where h1: "s' = s\<lparr>systemThread := (systemThread s)(c\<mapsto>t), systemExec := Initialize cs\<rparr>"
      and h2: "systemPhase s = Initializing"
      and h3: "systemExec s = Initialize (c # cs)"
      and h4: "stepInit (appModelApp am $ c) (systemThread s $ c) t"
    using exec isInitializing.elims by blast
  show ?thesis 
    using exec h1 h3 by fastforce
qed
  

lemma stepSysInit_initInv_ruleinv:
  assumes init: "isInitializing s"
      and exec: "systemExec s = Initialize (x # xs)"
      and step: "stepSys am cm sc s s'"
    shows "isInitializing s'"
proof -
  have "\<exists>c cs t.
        s' = s\<lparr>systemThread := (systemThread s)(c\<mapsto>t), systemExec := Initialize cs\<rparr> \<and>
        isInitializing s \<and>
        Initialize (x # xs) = Initialize (c # cs) \<and> stepInit (appModelApp am $ c) (systemThread s $ c) t"
    using exec step apply (simp add: stepSys.simps)
    apply (erule disjE)
     apply blast
    apply (erule disjE)
    using init apply force
    using init by force
  then obtain c cs t 
    where h1: "s' = s\<lparr>systemThread := (systemThread s)(c\<mapsto>t), systemExec := Initialize cs\<rparr>"
      and h2: "systemPhase s = Initializing"
      and h3: "systemExec s = Initialize (c # cs)"
      and h4: "stepInit (appModelApp am $ c) (systemThread s $ c) t"
    using exec isInitializing.elims by blast
  show ?thesis 
    by (simp add: h1 h2)
qed

(* Transitive closure of steps; no traces *)
definition stepsSys where "stepsSys am cm sc = (stepSys am cm sc)\<^sup>*\<^sup>*"

(* Reachable states from allowed initial states *)
definition reachSys where "reachSys am cm sc y \<equiv> 
  \<exists>x. initSys (appModel am) x \<and> stepsSys am cm sc x y"

end