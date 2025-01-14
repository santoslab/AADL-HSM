section \<open>System States\<close>

text \<open>An AADL runtime system state includes the state of each of the threads
in the system, the state of the inter-thread communication substrate, 
and the state of various system services associated with scheduling, etc.

This theory uses definitions ThreadState.thy (for representing the state
of threads) and Model.thy (for aligning the state elements with model 
information).\<close>

theory SystemState
  imports Main Model ThreadState
begin

subsection \<open>System Phase Structures\<close>

text \<open>AADL executions are separated into an \emph{Initializing} phase and a
\emph{Computing} phase (see the standard - Section 5.4.1 Clause (21), 
Section 13.3 Clause (7)).  

In the Initializing phase, each thread's
application code Initialize Entry Point executed once.  The application
developer designs this code to provide an initial value to each variable
in the thread's state and to put initial values on its output ports.

In the Computing phase, the Compute Entry Point application code for each thread
is executed repeated, according to the thread scheduling policy.

The two phases are associated with dedicated scheduling information.
See datatype @{term Exec} below.
\<close>

subsection \<open>Scheduling State Structures\<close>

text \<open>From the scheduler's perspective, each thread is either
\begin{itemize}
\item suspended awaiting dispatch,
\item dispatched and ready to be scheduled,
\item running.
\end{itemize}
This is a simplication of the AADL thread scheduling states reflected in
Section 5.4.1 ``Thread States and Actions'' and 5.4.2 ``Thread Dispatching'' of the standard 
and Figures 5 and 6.   In particular, we do not consider states related to modes, activation, 
deactivation, nor suspension due to resource acquisition or subprogram calls. 
\<close>

datatype ScheduleState = Waiting | Ready | Running

type_synonym Threadschedule = "(ScheduleState, ScheduleState) map" (* unused *)

text \<open>The AADL runtime is design to integrate with a scheduling infrastructure on the underlying platform.
The standard does not specify a particular scheduling strategy.   Our scheduling-related definitions
are set up (a) as a minimal abstract representation of scheduling, with (b) the ability to refine
the definition to a particular scheduling strategy.

Our abstract scheduling information indicates that the system is either initializing threads
(with a list of ids of threads remaining to be initialized), 
or is in the Computing phase and with @{term CompId} indicating the thread whose compute 
entry point will be executed next according to the underlying (unspecified) scheduling strategy.\<close>

datatype Exec = Initialize "CompId list" | Compute "CompId"

text \<open>Since Thread Initialize entry points do not read input ports, the ordering
of the execution of Initialize entry point is immaterial (see the standard Section 13.3 Clause (8).
We will subsequently prove that our semantics definitions support this independence property.\<close>

text \<open>For now, the notion of system schedule is instantiated to a static cyclic 
schedule.  @{term scheduleInit} provides a totally ordered thread schedule for the 
system's initialization phase. @{term scheduleFirst} indicates set the threads
that may be scheduled first in the system Compute phase.  For a given thread
t, @{term ScheduleComp} defines the set of threads whose execution may follow t.\<close>

record SystemSchedule =
  scheduleInit :: "CompId list"
  scheduleFirst :: "CompId set" (* to switch to the computation *)
  scheduleComp :: "(CompId, CompId set) map"

(*
During initialisation scheduling, each thread's initialisation is executed once
according to the order given in the list.
During computation scheduling, each scheduled thread has at least one successor.
This gives a minimal liveness guarantee.
*)

subsection \<open>System State Structures\<close>

text \<open>
The system state includes the following elements:
\begin{itemize}
\item a mapping from @{term CompId} to the thread states, 
\item an (abstract) representation of the state of the communication substrate,
\item a mapping from @{term CompId} to the scheduling state of each thread,
\item the current phase of the system (contained in @{term Exec}, 
\item the thread to be executed next. 
\end{itemize}
\<close>

(* From John to Stefan: 
        can we rename systemThread to systemThreadStates
        can we rename systemState to systemThreadSchedulingStates or 
                                     systemThreadSStates
                                     systemSchedulingStates
*)
record ('u, 'a) SystemState =
  systemThread :: "(CompId, 'a ThreadState) map" \<comment> \<open>states of each thread\<close>
  systemComms :: "'u" \<comment> \<open>state of communication substrate\<close>
  systemState :: "(CompId, ScheduleState) map" \<comment> \<open>schedule state of each thread\<close>
  systemExec :: "Exec" \<comment> \<open>system state and thread to be executed next\<close>


text \<open>Define an instantiation of the system state in which the communication substrate
structure is defined as a set of communication packets with a source @{term PortId} 
a payload, and a target @{term PortId}.\<close>

type_synonym 'a CommonState = "('a, (PortId * 'a * PortId * nat) set) SystemState"


text \<open>The following helper function uses the map @{term ran} (range) operation
to retreive the set of thread states associated with all threads in the system 
state @{term s}.\<close>

fun systemThreadStates :: "('u, 'a) SystemState \<Rightarrow> 'a ThreadState set"
  where "systemThreadStates s = ran (systemThread s)"


text \<open>The following helper predicates can be used to determine the current
phase of the system.
\<close>

text \<open>The system is in the initialization phase when the @{term systemPhase} field is 
set to @{term Initializing} and the execution schedule field is set to an 
initialization schedule.\<close>

(* consider making these well-formedness properties, i.e., if the phase is Initializing,
then the systemExec field references an initialization schedule *)

fun isInitializing :: "('a, 'u) SystemState \<Rightarrow> bool"
  where "isInitializing s = (\<exists>cs. systemExec s = Initialize cs)"

text \<open>The system is in the compute phase when the @{term systemPhase} field is 
set to @{term Computing} and the execution schedule field indicates that component
@{term c} is the next to execute.\<close>

fun isComputing :: "('a, 'u) SystemState \<Rightarrow> bool"
  where "isComputing s = (\<exists>c. systemExec s = Compute c)"

lemma init_not_compute: "isInitializing s \<Longrightarrow> \<not>isComputing s"
  apply simp
  by fastforce

lemma compute_not_init: "isComputing s \<Longrightarrow> \<not>isInitializing s"
  apply simp
  by fastforce

lemma init_init: "systemExec s = Initialize cs \<Longrightarrow> isInitializing s"
  by simp

lemma compute_compute: "systemExec s = Compute c \<Longrightarrow> isComputing s"
  by simp

subsection \<open>Well-formedness Definitions\<close>

text \<open>
This section define a notion of well-formed system state.  This
is organized in terms of well-formedness properties for each system state element.  
\<close>


subsubsection \<open>Well-formedness Definitions for Thread States\<close>

text \<open>
The system state's thread state map is well-formed if each thread
state in the map is well-formed and if the domain of the map
equals the set of thread ids in the model.\<close>

definition wf_SystemState_ThreadStates :: "Model \<Rightarrow> ('u, 'a) SystemState \<Rightarrow> bool"
  where  "wf_SystemState_ThreadStates m ss \<equiv>
           let threadStates = systemThread ss in 
            \<forall>c \<in> dom threadStates . wf_ThreadState m c (threadStates $ c)" 

definition wf_SystemState_ThreadStates_dom :: "Model \<Rightarrow> ('u, 'a) SystemState \<Rightarrow> bool"
  where  "wf_SystemState_ThreadStates_dom m ss \<equiv> 
           let threadStates = systemThread ss in
            dom threadStates = modelCIDs m" 

text \<open>
***** ToDo ****** communication state.
\<close>

text \<open>
The system state's thread schedule state map is well-formed if the domain of the map
equals the set of thread ids in the model.\<close>

definition wf_SystemState_ScheduleStates_dom :: "Model \<Rightarrow> ('u, 'a) SystemState \<Rightarrow> bool"
  where  "wf_SystemState_ScheduleStates_dom m ss \<equiv> 
           let scheduleStates = systemState ss in
            dom scheduleStates = modelCIDs m" 


(* From John to Stefan: is there any reason why we should not have equality below,
   i.e., dom of systemThreads is equal to modelCIDs? *)

(* The following is a candidate for elimination, because it is subsumed by the 
   broader system state well-formed properties *)

definition wf_SystemState :: "Model \<Rightarrow> ('u, 'a) SystemState \<Rightarrow> bool" 
  where "wf_SystemState m x \<equiv> 
    dom (systemThread x) \<subseteq> modelCIDs m \<and>
    wf_SystemState_ThreadStates m x \<and>
    wf_SystemState_ThreadStates_dom m x"

text \<open>Well-formedness for @{type Exec} indicates that (a) when in the Initializing
phase the list of thread ids yet to be initialized are found in the thread ids of the model.
and (b) when in the Compute phase the id of the next thread to execute is found in the
thread ids of the model.\<close>

definition wf_Exec :: "Model \<Rightarrow> Exec \<Rightarrow> bool"
  where "wf_Exec m e \<equiv> 
          case e of 
           Initialize cs \<Rightarrow> set cs \<subseteq> (modelCIDs m)
         | Compute c \<Rightarrow> c \<in> (modelCIDs m)"


text \<open>
Well-formedness of the system state is the conjunction of the well-formed properties
above.
\<close>

definition wf_SystemStateJohn :: "Model \<Rightarrow> ('u, 'a) SystemState \<Rightarrow> bool"
  where "wf_SystemStateJohn m ss \<equiv> 
          wf_SystemState_ThreadStates m ss
        \<and> wf_SystemState_ThreadStates_dom m ss
        \<and> wf_SystemState_ScheduleStates_dom m ss
        \<and> wf_Exec m (systemExec ss)"


text \<open>The following definition gives well-formed conditions for system schedules:
\begin{itemize}
\item the thread ids referenced in the initialization phase schedule, must match
exactly the set of thread ids in the model (i.e., those for which a model descriptor
is declared), and
\item the length of the initialization phase schedule must be equal to the number of 
threads (along with the first condition, this implies that every thread appears exactly
once in the initialization phase schedule, 
\item there must be at least one thread given in the @{term scheduleFirst} set for the computing phase
scheduling,
\item the thread ids in @{term scheduleFirst} set are ``valid'' (i.e., they appear
in the model declarations), and
\item each thread id declared in the model is accounted for in the @{term scheduleComp}
``next to schedule'' map (i.e., the map is total on the model-declared threads)
and every model-declared thread has an entry in the map. 
\end{itemize}
\<close>

(* ToDo: 
    - add a constraint that each element in the range of scheduleComp is in 
   dom (modelCompDescrs md) 
    - do we need to require that the set of successors for each thread in
    the scheduleComp map is non-empty? or do we want the flexibility of 
    saying that certain threads don't have a successor.  *)

definition wf_SystemSchedule :: "Model \<Rightarrow> SystemSchedule \<Rightarrow> bool"
  where "wf_SystemSchedule md sc \<equiv> 
  (set (scheduleInit sc) = dom (modelCompDescrs md)) \<and>
  (length (scheduleInit sc) = card (dom (modelCompDescrs md))) \<and>
  (scheduleFirst sc \<noteq> {}) \<and>
  (scheduleFirst sc \<subseteq> dom (modelCompDescrs md)) \<and>
  (dom (scheduleComp sc) = dom (modelCompDescrs md))"

(* Should we move the communication definitions into their own theory? *)

subsection \<open>Communication\<close>

record ('u,'a) Communication =
  comPush :: "'u \<Rightarrow> 'a PortState \<Rightarrow> Conns \<Rightarrow> ('u \<times> 'a PortState) set" 
  comPull :: "'u \<Rightarrow> 'a PortState \<Rightarrow> Conns \<Rightarrow> ('u \<times> 'a PortState) set"

definition wf_Communication where
  "wf_Communication md cm \<equiv> 
    (\<forall>sb ps. \<forall>c\<in>dom (modelCompDescrs md).
      wf_ThreadState_info md c ps \<longrightarrow> 
        (\<forall>(tb, qs)\<in>comPush cm sb ps (modelConns md). wf_ThreadState_info md c qs)) \<and>
    (\<forall>sb ps. \<forall>c\<in>dom (modelCompDescrs md).
      wf_ThreadState_infi md c ps \<longrightarrow> 
        (\<forall>(tb, qs)\<in>comPull cm sb ps (modelConns md). wf_ThreadState_infi md c qs))"

fun commonPushItems where
  "commonPushItems _ _ [] _ = {}"
| "commonPushItems p q (x#xs) mx = {(p, x, q, Suc mx)} \<union> commonPushItems p q xs (Suc mx)"

fun commonPushSubstrate where
  "commonPushSubstrate cn ps pids mx pf = (\<Union>p \<in> pids. \<Union>q \<in> cn $ p. (commonPushItems p q (pf p) mx))"

fun commonPushQueues where
  "commonPushQueues ps pf p = 
    (if p \<in> dom ps 
      then Some (drop (length (pf p)) (ps $ p))
      else None)"

fun commonPush where
  "commonPush sb ps cn =
  {(tb, qs) | tb qs pids pf. 
    pids \<subseteq> dom ps \<and> 
    (\<forall>p \<in> pids. pf p \<le> buffer (ps $ p)) \<and>
    tb = commonPushSubstrate cn ps pids (Max {n | p x q n. (p, x, q, n) \<in> sb}) pf \<and>
    qs = commonPushQueues ps pf}"

fun commonPullSubstrate where
  "commonPullSubstrate sb qf = sb - (\<Union>q. (qf q))"

fun exact where 
  "exact [] s = (s = {})"
| "exact (x#xs) s = (\<exists>(p, v, q, n) \<in> s. v = x \<and> exact xs (s - {(p, v, q, n)}))"

fun commonPullItems where "commonPullItems p s = 
  { p\<lparr> buffer:= buffer p @ ys \<rparr> | ys. ys \<in> lists {v | p' v q n. (p', v, q, n) \<in> s} \<and> exact ys s }"

fun commonPullQueues where
  "commonPullQueues ps qf = 
    { qs | qs. (dom qs = dom ps \<and> (\<forall>pid \<in> dom ps. qs $ pid \<in> commonPullItems (ps $ pid) (qf pid)))}"

fun commonPull where
  "commonPull sb ps cn = 
  { (tb, qs) | tb qs qids qf.
    qids \<subseteq> dom ps \<and>
    (\<forall>q \<in> qids. qf q \<subseteq> { (p, x, q', n) \<in> sb . q = q'}) \<and>
    (\<forall>q \<in> UNIV - qids. qf q = {}) \<and>
    (\<forall>q \<in> qids. card (qf q) + length (buffer (ps $ q)) \<le> qsize (ps $ q)) \<and>
    tb = commonPullSubstrate sb qf \<and>
    qs \<in> commonPullQueues ps qf}"

definition CommonComm :: "((PortId * 'a::equal * PortId * nat) set, 'a) Communication" where
  "CommonComm = \<lparr>
    comPush= commonPush,
    comPull= commonPull
\<rparr>"

end