section "Port States"

text \<open>An AADL thread communicates with other threads over ports.  Each port has some
type of storage associated with it: a data port has a memory slot to hold a single
value, an event data port has a queue/buffer to hold messages, and an event port
has a queue/buffer to hold signals (null messages) indicating the presence of an event.
To simplify the semantics, we represent the storage for every kind of port using
a queue defined in Queue.thy.  Queues associated with data ports
will be constrained to always have size one.

The runtime needs to be able to associate a model-declared port to 
storage storage for the port.  In HAMR, this is implemented by associating
a @{term PortId} to a queue data structure.  In this semantics mechanization,
we introduce the type @{term PortState} -- a mapping from @{term PortId} 
to @{term Queue} to realize that association for each thread.   
For simplicity, we provide separate @{term PortState}s for input and output ports.  
Further, Hatcliff-al:ISOLA22 argued that the AADL runtime semantics implies that
there is a distinction between the application's view of a port's state,
and the communication infrastructure's view of a port's state (see, for example,  
Section 8.3.1 (7) of the standard).  Thus,
a @{term ThreadState} will include four @{term PortState} structures:
\begin{itemize}
\item @{term iin} - infrastructure input port state (representing the infrastructure's view of input ports)
\item @{term ain} - application input port state (representing the thread application logic's view of input ports) 
\item @{term aout} - application output port state (representing the thread application logic's view of output ports)
\item @{term iout} - infrastructure output port state (representing the infrastructure's view of output ports)
\end{itemize}

The PortState.thy theory provides:
\begin{itemize}
\item the definition of a port state data structure
\item definitions of well-formed port states
\item operations on port states
\item properties/proofs that operations preserve well-formedness
\end{itemize}

The theory depends on SetsAndMaps.thy for the map type that implements the port state,
Queue.thy for storage for each port, and Model.thy to provide the basis for well-formedness
(i.e., the contents of the port states are aligned with the port declarations in the model).
\<close>

theory PortState
  imports Main SetsAndMaps Queue Model
begin

subsection "Structures"

text \<open>A @{term PortState} maps @{term PortId}s to queues.  
Intuitively, each port state applies to a particular set of 
@{term PortId}s (e.g., the input ports of a particular thread).
We will use the Isabelle Map type @{term dom} (domain) operation
to determine the set of @{term PortId}s that the port state
supports. "Unsupported"/"Non-applicable" ports are not in the 
domain, while "supported" ports are always bound to a queue
value.\<close>

type_synonym 'a PortState = "(PortId, 'a Queue) map"

subsection "Well-formedness Definitions"

text \<open>A @{term PortState} is well-formed wrt some set of PortIds if its domain is equal
   to the set of PortIds.  This concept is used to show that common operations
   on port state maintain a domain that is aligned with a set of ports
   declared in a component (e.g., all input ports of the component).\<close>

definition wf_PortState_dom :: "'a PortState \<Rightarrow> PortId set \<Rightarrow> bool" where 
  "wf_PortState_dom ps pids \<equiv> (dom ps) = pids"

text \<open>A @{term PortState} is well-formed if every @{term PortId} in the port state
is associated with a well-formed @{term Queue} (as defined in Queue.thy).\<close>

definition wf_PortState_queues :: "'a PortState \<Rightarrow> bool" where 
  "wf_PortState_queues ps \<equiv> \<forall>p \<in> dom ps. wf_Queue (ps $ p)"

text \<open>The following definition conjoins the well-formedness properties above.\<close>

definition wf_PortState :: "'a PortState \<Rightarrow> PortId set \<Rightarrow> bool" where 
  "wf_PortState ps pids \<equiv>   wf_PortState_dom ps pids
                          \<and> wf_PortState_queues ps"

subsection "Operations"

text \<open>We define a number of helper functions for working with port
states.  As a naming convention, operations with "PID" in the name
take a @{term PortId} argument as a reference to a port;
operations with "PD" in the name to a @{term PortDescr} as a reference
to a port.\<close>

text \<open>Does port state @{term ps} map port identifier @{term PortId} to some queue?\<close>
fun portDefinedPID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> bool" 
  where "portDefinedPID ps p = (p \<in> dom ps)"

text \<open>Does port state @{term ps} associate a non-empty queue with 
port identifier @{term PortId}? (i.e., is data available in the port storage?)\<close>

fun dataAvailablePID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> bool" (* formerly davail *)
  where "dataAvailablePID ps p = (\<exists>q . ps p = Some(q) \<and> \<not>isEmpty q)"

text \<open>Given a port state @{term ps}, return the set of port ids for which there is 
data available (i.e., the set of port ids that are associated with non-empty queues.\<close>

fun dataAvailablePorts :: "'a PortState \<Rightarrow> PortId set" 
  where "dataAvailablePorts ps = {p . dataAvailablePID ps p}"

text \<open>Does the port state @{term ps} have any queues that have data available?\<close>

fun dataUnavailable :: "'a PortState \<Rightarrow> bool" (* formerly pempty *)
  where "dataUnavailable ps = (\<forall>p \<in> dom ps. \<forall>q. ps p = Some(q) \<longrightarrow> isEmpty q)"

(* ToDo: John: Should reconcile the name of readyPIDs with dataAvailable *)

text \<open>Does the port state @{term ps} have data available on all ports in the
set @{term pids}?\<close>

fun readyPIDs :: "'a PortState \<Rightarrow> PortId set \<Rightarrow> bool" (* formerly pready *)
  where "readyPIDs ps pids = (\<forall>p \<in> pids. dataAvailablePID ps p)"

text \<open>Transform the port state @{term ps} by dequeuing one value from 
each of the ports in the set @{term pids}?\<close>

fun portDequeuePIDs :: "'a PortState \<Rightarrow> PortId set \<Rightarrow> 'a PortState" 
  where "portDequeuePIDs ps pids = ps ++ (\<lambda>p. if p \<in> pids then Some (tail (ps $ p)) else None)"

text \<open>Transform the port state @{term ps} by dequeuing one value from 
the port @{term p}?\<close>

fun portDequeuePID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a PortState" 
  where "portDequeuePID ps p = ps(p \<mapsto> tail (ps $ p))"

text \<open>Return the first value from @{term p}'s queue within port state @{term ps}.\<close>

fun portHeadPID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a"
  where "portHeadPID ps p = head (ps $ p)"

text \<open>Return the entire buffer of @{term p}'s queue with port state @{term ps}.\<close>
fun portBufferPID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a list"  
  where "portBufferPID ps p = buffer (ps $ p)"

text \<open>Transform the port state @{term ps} by enqueueing a value @{term v} 
into @{term p}'s queue.\<close>
fun portEnqueuePID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a \<Rightarrow> 'a PortState" 
  where "portEnqueuePID ps p v = ps(p \<mapsto> push (ps $ p) v)"

text \<open>Transform the port state @{term ps} by replacing @{term p}'s queue
with queue @{term q}.\<close>
fun portReplacePID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a Queue \<Rightarrow> 'a PortState" 
  where "portReplacePID (ps::'a PortState) p q = ps(p \<mapsto> q)"

text \<open>Transform the port state @{term ps} by clearing 
all the queue buffers in the set of ports @{term pids}'s.\<close>

fun clearAll :: "PortId set \<Rightarrow> 'a PortState \<Rightarrow> 'a PortState"
  where "clearAll pids ps = (\<lambda>p. if p \<in> pids then Some (clear (ps $ p)) else ps p)"

text \<open>The following property provides a "sanity check" on a couple of the opeations
above: enqueueing a value and then dequeueing yields an identical queue value.\<close>

lemma portEnqueueDequeue_empty:
  assumes avail: "portDefinedPID ps p"
      and capa: "capacity (ps $ p) > 0"
      and empty: "isEmpty (ps $ p)"
    shows "portDequeuePID (portEnqueuePID ps p x) p = ps"
proof -
  have "\<forall>q \<in> dom ps. portDequeuePID (portEnqueuePID ps p x) p q = ps q"
  proof
    fix q
    assume "q \<in> dom ps"
    show "portDequeuePID (portEnqueuePID ps p x) p q = ps q"
    proof (cases "p = q")
      case True
      obtain e b c s where h0: "ps p = Some \<lparr> error= e, buffer= b, capacity= c, strategy = s \<rparr>"
        by (metis Queue.cases avail domD portDefinedPID.elims(2))
      have h1: "b = []"
        using empty h0 by fastforce
      have h6: "length [] < capacity (ps $ p)"
        using capa by fastforce
      have h4: "buffer (push (ps $ p) x) = [x]"
        by (metis append_Nil capa empty isEmpty.elims(2) list.size(3) push_within_capacity)
      have h5: "error (push (ps $ p) x) = error (ps $ p)"
        by (metis capa empty isEmpty.simps list.size(3) push_no_error)
      have h7: "error (ps $ p) = e"
        by (simp add: h0)
      have h2: "portEnqueuePID ps p x p = Some(push (ps $ p) x)"
        by simp
      have h2: "portEnqueuePID ps p x p = Some \<lparr> error= e, buffer= [x], capacity= c, strategy = s \<rparr>"
        using h0 h1 h2 h4 h5 
          map_some_val_given[of ps p "\<lparr> error= e, buffer= b, capacity= c, strategy = s \<rparr>"]
        by (smt (verit, ccfv_threshold) Queue.equality Queue.select_convs(1) Queue.select_convs(2) 
           Queue.select_convs(3) Queue.select_convs(4) old.unit.exhaust push_frame_capacity 
           push_frame_strategy)
      have h3: "portDequeuePID (portEnqueuePID ps p x) p p = 
                Some \<lparr> error= e, buffer= b, capacity= c, strategy = s \<rparr>"
        using h1 h2 by auto
      then show ?thesis
        using h0 by force
    next
      case False
      then show ?thesis
        by simp
    qed
  qed
  thus ?thesis
  by (metis avail fun_upd_triv fun_upd_upd portDefinedPID.elims(2) portDequeuePID.elims portEnqueuePID.elims)
qed

subsection "Operation Properties"

subsubsection \<open>@{term portReplacePID} operation preserves well-formedness\<close>

text \<open>If we perform @{term portReplacePID} for port id @{term p} that already exists 
      within port state @{term ps}, 
      then the resulting port state has the same domain.\<close>

lemma portReplacePID_preserves_wf_PortState_dom:
  assumes wf_ps_dom:   "wf_PortState_dom ps dom_pids" 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_dom (portReplacePID ps p q) dom_pids"
using wf_ps_dom p_in_dom 
  by (auto simp add: wf_PortState_dom_def)

text \<open>@{term portReplacePID} preserves port state well-formedness.\<close>

lemma pset_preserves_wf_PortState:
  assumes wf_ps:   "wf_PortState ps dom_pids" 
      and p_in_dom: "p \<in> dom_pids"
      and wf_queue: "wf_Queue q"
    shows "wf_PortState (portReplacePID ps p q) dom_pids"
  using wf_ps
        p_in_dom  
        portReplacePID_preserves_wf_PortState_dom  
        wf_PortState_def
  by (smt (verit) fun_upd_other fun_upd_same map_get_def map_some_val_given portReplacePID.elims 
     wf_PortState_dom_def wf_PortState_queues_def wf_queue)


subsubsection \<open>@{term portDequeuePID} operation preserves well-formedness\<close>

text \<open>If we perform @{term portDequeuePID} for port id @{term p} that already exists 
      within port state @{term ps}, 
      then the resulting port state has the same domain.\<close>

lemma pdeq_preserves_wf_PortState_dom: 
  assumes wf_ps_dom:   "wf_PortState_dom ps dom_pids" 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_dom (portDequeuePID ps p) dom_pids"
  using wf_ps_dom p_in_dom 
  by (auto simp add: wf_PortState_dom_def)

text \<open>@{term portDequeuePID} preserves port state well-formedness.\<close>

lemma pdeq_preserves_wf_PortState: 
 assumes wf_ps:   "wf_PortState ps dom_pids" 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState (portDequeuePID ps p) dom_pids"
proof -
  have h1: "dom (portDequeuePID ps p) = dom_pids"
    using p_in_dom wf_ps apply (simp add: wf_PortState_def wf_PortState_dom_def)
    by blast
  have h2: "(\<forall>q\<in>dom (portDequeuePID ps p). wf_Queue (portDequeuePID ps p $ q))"
    using wf_ps p_in_dom apply (simp add: wf_Queue_def wf_PortState_def wf_PortState_dom_def wf_PortState_queues_def)
    using diff_le_self le_trans by blast
  thus ?thesis
    apply (simp add: wf_PortState_def wf_PortState_dom_def wf_PortState_queues_def)
    using h1 by force
qed
end