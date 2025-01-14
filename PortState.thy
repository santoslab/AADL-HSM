section \<open>Port States \label{sec:port-states}\<close>

text \<open>An AADL thread communicates with other threads over ports.  Each port has some
type of storage associated with it: a data port has a memory slot to hold a single
value, an event data port has a queue/buffer to hold messages, and an event port
has a queue/buffer to hold signals (null messages) indicating the presence of an event.
To simplify the semantics, we adopt a uniform representation the storage for 
every kind of port using queues defined in Queue.thy (Section~\ref{sec:queues}).  
This is further justified
by the language in Section 8.3 (3) of the AADL standard: "Data ports are event data
ports with a queue size of one in which the newest arrival is kept" and 
"Event ports are event data ports with empty message content".

The runtime needs to be able to associate a model-declared port to 
storage storage for the port.  In HAMR, this is implemented by associating
a @{term PortId} to a queue data structure.  In this semantics mechanization,
we introduce the type @{term PortState} -- a mapping from @{term PortId} 
to @{term Queue} to realize that association for each thread.   
For simplicity, we provide separate @{term PortState}s for input and output ports.  
Further, \cite{Hatcliff-al:ISOLA22} argued that the AADL runtime semantics implies that
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

This theory provides:
\begin{itemize}
\item the definition of a port state data structure
\item definitions of well-formed port states
\item operations on port states
\item properties/proofs that operations preserve well-formedness
\end{itemize}

The theory depends on SetsAndMaps.thy for the map type that implements the port state,
Queue.thy (Section~\ref{sec:queues}) for storage for each port, and Model.thy to provide the basis for well-formedness
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

definition wf_PortState_dom :: "Model \<Rightarrow> PortId set \<Rightarrow> 'a PortState \<Rightarrow> bool" where 
  "wf_PortState_dom m pids ps \<equiv> ((dom ps) = pids) \<and> (dom ps) \<subseteq> modelPIDs m"

text \<open>A @{term PortState} is well-formed if every @{term PortId} in the port state
is associated with a well-formed @{term Queue} @{term q} (as defined in Queue.thy -- Section~\ref{sec:queues}),
the capacity of the @{term q} is equal to the model-declared size of the
queue as found in the model @{term PortDescr} @{term pd},
and the overflow handling protocol in @{term q} matches
the model-declared value in @{term pd}.\<close>

definition wf_PortState_queue :: "Model \<Rightarrow> PortId \<Rightarrow> 'a Queue \<Rightarrow> bool" where
  "wf_PortState_queue m p q \<equiv> 
    (wf_Queue q \<and> qsize q = queueSize ((modelPortDescrs m) $ p) \<and> 
                    qohp q = ohp ((modelPortDescrs m) $ p))"
    (* proof automation (e.g., fastforce) works less well when this nicer
       version with let below is used 
     let pd = (modelPortDescrs m) $ p 
                in (wf_Queue q \<and> qsize q = queueSize pd \<and> qohp q = ohp pd)
     I wish I could figure out how to fix this.
     *)

definition wf_PortState_queues :: "Model \<Rightarrow> PortId set \<Rightarrow> 'a PortState \<Rightarrow> bool" where 
(* Old definition
  "wf_PortState_queues m pids ps \<equiv> \<forall>p \<in> dom ps. wf_Queue (ps $ p)" *)
  "wf_PortState_queues m pids ps \<equiv> 
    \<forall>p \<in> pids. let q = (ps $ p)  
                in wf_PortState_queue m p q"

text \<open>The following definition conjoins the well-formedness properties above.\<close>

definition wf_PortState :: "Model \<Rightarrow> PortId set \<Rightarrow> 'a PortState \<Rightarrow> bool" where 
  "wf_PortState m pids ps  \<equiv>   wf_PortState_dom m pids ps
                             \<and> wf_PortState_queues m pids ps"

text \<open>The following helper lemmas establish properties of elements (queues, buffers)
that below to well-formed port states.  These are used in proofs that operations
on port states preserve well-formedness.\<close>

lemma wf_PortState_implies_wf_PortState_queue:
  assumes wf_ps: "wf_PortState m dom_pids ps"
  and p_in_dom: "p \<in> dom_pids"
shows "wf_PortState_queue m p (ps $ p)"
  using wf_ps p_in_dom
  by (simp add: wf_PortState_def wf_PortState_queues_def)


(*==================================================================
   O p e r a t i o n s
 ===================================================================*)

subsection "Operations"

text \<open>We define a number of helper functions for working with port
states.  As a naming convention, operations with ``PID'' in the name
take a @{term PortId} argument as a reference to a port;
operations with ``PD'' in the name to a @{term PortDescr} as a reference
to a port.\<close>

subsubsection \<open>Accessor Operations\<close>

text \<open>Accessor operators implement queries about the aggregate port state
or individual ports.  These do not perform logical updates of the port state.\<close>

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

(* ToDo: John: Should reconcile the name of readyPIDs with dataAvailablePorts and dataAvailable *)

text \<open>Does the port state @{term ps} have data available on all ports in the
set @{term pids}?\<close>

fun readyPIDs :: "'a PortState \<Rightarrow> PortId set \<Rightarrow> bool" (* formerly pready *)
  where "readyPIDs ps pids = (\<forall>p \<in> pids. dataAvailablePID ps p)"

text \<open>Return the first value from @{term p}'s queue within port state @{term ps}.\<close>

fun portHeadPID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a"
  where "portHeadPID ps p = head (ps $ p)"

text \<open>Return the entire buffer of @{term p}'s queue with port state @{term ps}.\<close>
fun portBufferPID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a list"  
  where "portBufferPID ps p = buffer (ps $ p)"

subsubsection \<open>Transformer Operations\<close>

text \<open>Transformer operation perform logical updates of the port states.
Sections that follow will prove well-formedness preservation properties for these.\<close>

text \<open>Transform the port state @{term ps} by replacing @{term p}'s queue
with queue @{term q}.\<close>

fun portReplacePID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a Queue \<Rightarrow> 'a PortState"
  where "portReplacePID (ps::'a PortState) p q = ps(p \<mapsto> q)"

text \<open>Transform the port state @{term ps} by replacing @{term p}'s buffer
with queue @{term b}, leaving the rest of queue (the static properties and error state) unchanged.\<close>

fun portReplaceBufferPID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a list \<Rightarrow> 'a PortState"
  where "portReplaceBufferPID (ps::'a PortState) p b = 
    (let q_pre = (ps $ p) in \<comment> \<open>get the current q\<close>
       let q_post = setBuffer q_pre b in \<comment> \<open>update the queue with a new buffer\<close>
         ps(p \<mapsto> q_post))"

text \<open>Transform the port state @{term ps} by dequeuing one value from 
each of the ports in the set @{term pids}?\<close>

fun portDequeuePIDs :: "'a PortState \<Rightarrow> PortId set \<Rightarrow> 'a PortState" 
  where "portDequeuePIDs ps pids = ps ++ (\<lambda>p. if p \<in> pids then Some (tail (ps $ p)) else None)"

text \<open>Transform the port state @{term ps} by dequeuing one value from 
the port @{term p}?\<close>

fun portDequeuePID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a PortState" 
  where "portDequeuePID ps p = ps(p \<mapsto> tail (ps $ p))"

text \<open>Transform the port state @{term ps} by enqueueing a value @{term v} 
into @{term p}'s queue.\<close>
fun portEnqueuePID :: "'a PortState \<Rightarrow> PortId \<Rightarrow> 'a \<Rightarrow> 'a PortState" 
  where "portEnqueuePID ps p v = ps(p \<mapsto> push (ps $ p) v)"


text \<open>Transform the port state @{term ps} by clearing 
all the queue buffers in the set of ports @{term pids}'s.\<close>

fun clearAll :: "PortId set \<Rightarrow> 'a PortState \<Rightarrow> 'a PortState"
  where "clearAll pids ps = (\<lambda>p. if p \<in> pids then Some (clear (ps $ p)) else ps p)"

text \<open>The following property provides a ``sanity check'' on a couple of the operations
above: enqueueing a value and then dequeueing yields an identical queue value.\<close>

lemma portEnqueueDequeue_empty:
  assumes avail: "portDefinedPID ps p"
      and capa: "qsize (ps $ p) > 0"
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
      obtain e b c s where h0: "ps p = Some \<lparr> error= e, buffer= b, qsize= c, qohp = s \<rparr>"
        by (metis Queue.cases avail domD portDefinedPID.elims(2))
      have h1: "b = []"
        using empty h0 by fastforce
      have h6: "length [] < qsize (ps $ p)"
        using capa by fastforce
      have h4: "buffer (push (ps $ p) x) = [x]"
        by (metis append_Nil capa empty isEmpty.elims(2) list.size(3) push_within_qsize)
      have h5: "error (push (ps $ p) x) = error (ps $ p)"
        by (metis capa empty isEmpty.simps list.size(3) push_no_error)
      have h7: "error (ps $ p) = e"
        by (simp add: h0)
      have h2: "portEnqueuePID ps p x p = Some(push (ps $ p) x)"
        by simp
      have h2: "portEnqueuePID ps p x p = Some \<lparr> error= e, buffer= [x], qsize= c, qohp = s \<rparr>"
        using h0 h1 h2 h4 h5 
          map_some_val_given[of ps p "\<lparr> error= e, buffer= b, qsize= c, qohp = s \<rparr>"]
        by (smt (verit, ccfv_threshold) Queue.equality Queue.select_convs(1) Queue.select_convs(2) 
           Queue.select_convs(3) Queue.select_convs(4) old.unit.exhaust push_frame_qsize 
           push_frame_qohp)
      have h3: "portDequeuePID (portEnqueuePID ps p x) p p = 
                Some \<lparr> error= e, buffer= b, qsize= c, qohp = s \<rparr>"
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

(*==================================================================
   O p e r a t i o n    P r o p e r t i e s
 ===================================================================*)

subsection "Operation Properties"

(*--------------------------
    R e p l a c e
  --------------------------*)

subsubsection \<open>@{term portReplacePID} operation preserves well-formedness\<close>

text \<open>If we perform @{term portReplacePID} for port id @{term p} that exists 
      within port state @{term ps}, 
      then the resulting port state has the same domain.\<close>

lemma portReplacePID_preserves_wf_PortState_dom:
  assumes wf_ps_dom:   "wf_PortState_dom m dom_pids ps" 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_dom m dom_pids (portReplacePID ps p q) "
using wf_ps_dom p_in_dom 
  by (auto simp add: wf_PortState_dom_def)

text \<open>If we perform @{term portReplacePID} for port id @{term p} that exists 
      within well-formed port state @{term ps} and the new queue is also well-formed 
      with respect to the model, 
      then the queues in the resulting port state all well-formed
      with respect to the model.\<close>

lemma portReplacePID_preserves_wf_PortState_queues:
  assumes wf_ps: "wf_PortState m dom_pids ps"
      and p_in_dom: "p \<in> dom_pids"
      and wf_ps_queue: "wf_PortState_queue m p q"
     shows "wf_PortState_queues m dom_pids (portReplacePID ps p q)"
  using wf_ps  \<comment> \<open>assume we start with well-formed port states\<close>  
        p_in_dom 
        wf_ps_queue \<comment> \<open>assume the new value of the queue is well-formed\<close>
        wf_PortState_queue_def  \<comment> \<open>well-formedness definitions and associated properties\<close>
        wf_PortState_queues_def
        wf_PortState_implies_wf_PortState_queue 
  by fastforce


text \<open>@{term portReplacePID} preserves port state well-formedness.\<close>

lemma portReplacePID_preserves_wf_PortState:
  assumes wf_ps:   "wf_PortState m dom_pids ps" 
      and p_in_dom: "p \<in> dom_pids"
      and wf_ps_queue: "wf_PortState_queue m p q"
    shows "wf_PortState m dom_pids (portReplacePID ps p q)"
  using wf_ps \<comment> \<open>assume we start with well-formed port states\<close>
        p_in_dom 
        wf_ps_queue \<comment> \<open>assume the new value of the queue is well-formed\<close>
        portReplacePID_preserves_wf_PortState_dom \<comment> \<open>previous theorems\<close> 
        portReplacePID_preserves_wf_PortState_queues 
        wf_PortState_def \<comment> \<open>primary definition\<close>
     by blast

(*--------------------------
    R e p l a c e B u f f e r
  --------------------------*)

subsubsection \<open>@{term portReplaceBufferPID} operation preserves well-formedness\<close>

text \<open>If we perform @{term portReplaceBufferPID} for port id @{term p} that exists 
      within port state @{term ps}, 
      then the resulting port state has the same domain.\<close>

lemma portReplaceBufferPID_preserves_wf_PortState_dom:
  assumes wf_ps_dom:   "wf_PortState_dom m dom_pids ps" 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_dom m dom_pids (portReplaceBufferPID ps p b) "
using wf_ps_dom p_in_dom 
  by (auto simp add: wf_PortState_dom_def)

text \<open>Given a well-formed port state @{term ps}, and a pid @{term p} that is in the
      domain of the port state, and a buffer @{term b} that is well-formed (it's length
      does not exceed the maximum capacity declared for the port),
      if we perform @{term portReplaceBufferPID} 
      then the queues in the resulting port state all well-formed
      with respect to the model.\<close>

lemma portReplaceBufferPID_preserves_wf_PortState_queues:
  assumes wf_ps: "wf_PortState m dom_pids ps"
      and p_in_dom: "p \<in> dom_pids"
      and b_wf: "length b \<le> (queueSizePID m p)"
    shows "wf_PortState_queues m dom_pids (portReplaceBufferPID ps p b)"
  using wf_ps  \<comment> \<open>assume we start with well-formed port states\<close>  
        p_in_dom 
        b_wf \<comment> \<open>assume the new value of the buffer is well-formed\<close>
        wf_PortState_queue_def  \<comment> \<open>well-formedness definitions and associated properties\<close>
        wf_PortState_queues_def
        wf_PortState_implies_wf_PortState_queue 
         setBuffer_wf \<comment> \<open>setting wf buffer within wf queue produces wf queue\<close>
        setBuffer_frame_qsize \<comment> \<open>setBuffer frame conditions\<close>
        setBuffer_frame_qohp 
  by fastforce


text \<open>@{term portReplacePID} preserves port state well-formedness.\<close>

lemma portReplaceBufferPID_preserves_wf_PortState:
  assumes wf_ps:   "wf_PortState m dom_pids ps" 
      and p_in_dom: "p \<in> dom_pids"
      and b_wf: "length b \<le> (queueSizePID m p)"
    shows "wf_PortState m dom_pids (portReplaceBufferPID ps p b)"
  using wf_ps \<comment> \<open>assume we start with well-formed port states\<close>
        p_in_dom 
        b_wf \<comment> \<open>assume the new buffer is well-formed wrt queue capacity\<close>
        portReplaceBufferPID_preserves_wf_PortState_dom \<comment> \<open>previous theorems\<close> 
        portReplaceBufferPID_preserves_wf_PortState_queues 
        wf_PortState_def \<comment> \<open>primary definition\<close>
     by blast


(*--------------------------
    D e q u e u e 
  --------------------------*)

subsubsection \<open>@{term portDequeuePID} operation preserves well-formedness\<close>

text \<open>If we perform @{term portDequeuePID} for port id @{term p} that exists 
      within port state @{term ps}, 
      then the resulting port state has the same domain.\<close>

lemma portDequeuePID_preserves_wf_PortState_dom: 
  assumes wf_ps_dom:   "wf_PortState_dom m dom_pids ps" 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_dom m dom_pids (portDequeuePID ps p)"
  using wf_ps_dom p_in_dom 
  by (auto simp add: wf_PortState_dom_def)

text \<open>If we perform @{term portDequeuePID} for port id @{term p} that exists 
      within port state @{term ps}, 
      then the resulting queue is well-formed.\<close>

lemma portDequeuePID_preserves_wf_PortState_queue:
  assumes wf_ps: "wf_PortState m dom_pids ps"
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_queue m p ((portDequeuePID ps p) $ p)"
proof -
  from wf_ps p_in_dom have wf_operand_queue: "wf_PortState_queue m p (ps $ p)" 
    by (rule wf_PortState_implies_wf_PortState_queue)
  show ?thesis
    using wf_operand_queue (* well-formed input to the dequeue operation *)
          tail_wf (* properties of tail used in the dequeue operation *)
          wf_PortState_queue_def  
          tail_wf 
       by force
    (* ToDo: I'm surprised I don't need the frame conditions on tail to prove this.
        I would expect something like what is given below
    using 
      tail_wf tail_frame_error tail_frame_capacity tail_frame_strategy (* tail properties *)
      wf_operand_queue (* well-formed input to the dequeue operation *) 
      wf_PortState_queue_def     *)      
   qed

text \<open>All the other queues within the port state @{term ps}
      not operated on by @{term portDequeuePID} are unchanged.\<close>

lemma portDequeuePID_frame:
  assumes wf_ps: "wf_PortState m dom_pids ps"
      and p_in_dom: "p \<in> dom_pids"
    shows "\<forall>p'\<in> dom_pids - {p} .  ((portDequeuePID ps p) $ p') = ps $ p'"
  by simp

text \<open>If we perform @{term portDequeuePID} for port id @{term p} that exists 
      within port state @{term ps}, 
      then all the queues in the resulting port state are well-formed.\<close>

lemma portDequeuePID_preserves_wf_PortState_queues:
  assumes wf_ps: "wf_PortState m dom_pids ps"
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_queues m dom_pids (portDequeuePID ps p)"
  using wf_ps \<comment> \<open>assume we start with well-formed port states\<close>
        wf_PortState_queues_def \<comment> \<open>..which implies that we have well-formed queues\<close>
        wf_PortState_implies_wf_PortState_queue  \<comment> \<open>..which implies that the argument to dequeue is well-formed\<close>
        portDequeuePID_preserves_wf_PortState_queue \<comment> \<open>..and dequeue produces a well-formed queue\<close>
  by fastforce


text \<open>@{term portDequeuePID} preserves port state well-formedness.\<close>

lemma portDequeuePID_preserves_wf_PortState: 
 assumes wf_ps:   "wf_PortState m dom_pids ps " 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState m dom_pids (portDequeuePID ps p)"
  using wf_ps p_in_dom \<comment> \<open>assumptions\<close>
        portDequeuePID_preserves_wf_PortState_dom \<comment> \<open>lemmas showing subproperties of wf preserved\<close>
        portDequeuePID_preserves_wf_PortState_queues 
        wf_PortState_def \<comment> \<open>definition of well-formedness\<close> 
     by blast

(* old proof
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
*)

(*--------------------------
    E n q u e u e
  --------------------------*)

subsubsection \<open>@{term portEnqueuePID} operation preserves well-formedness\<close>

text \<open>If we perform @{term portEnqueuePID} for port id @{term p} that exists 
      within port state @{term ps}, 
      then the resulting port state has the same domain.\<close>

lemma portEnqueuePID_preserves_wf_PortState_dom:
  assumes wf_ps_dom:   "wf_PortState_dom m dom_pids ps" 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_dom m dom_pids (portEnqueuePID ps p v) "
using wf_ps_dom p_in_dom 
  by (auto simp add: wf_PortState_dom_def)

text \<open>If we perform @{term portEnqueuePID} for port id @{term p} that exists 
      within port state @{term ps}, 
      then the resulting queue is well-formed.\<close>

lemma portEnqueuePID_preserves_wf_PortState_queue:
  assumes wf_ps: "wf_PortState m dom_pids ps"
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState_queue m p ((portEnqueuePID ps p v) $ p)"
proof -
  \<comment> \<open>Introduce names for original and updated queue.\<close>
  let ?orgq = "ps $ p"
  let ?newq = "(portEnqueuePID ps p v) $ p"
  \<comment> \<open>Since the original port state is wf (assumption), 
      we know the original queue for @{term p} is wf\<close>
  from wf_ps p_in_dom have wf_operand_portstate_queue: "wf_PortState_queue m p ?orgq" 
    by (rule wf_PortState_implies_wf_PortState_queue)
  \<comment> \<open>Since @{term push} preserves wf, we know the new queue is wf.\<close>
  from p_in_dom wf_operand_portstate_queue
  have wf_result_push_queue: "wf_Queue (push ?orgq v)"
    using push_wf wf_PortState_queue_def
    by metis
  \<comment> \<open>Restate new queue (and well-formedness) in terms of the entire port state.\<close>
  from p_in_dom wf_result_push_queue 
  have wf_result_queue: "wf_Queue ?newq"
    using push_wf p_in_dom wf_operand_portstate_queue
    by simp
  \<comment> \<open>frame condition for @{term qsize}.\<close>
  have qsize_preserved: "qsize ?newq = qsize ?orgq"
    using p_in_dom push_frame_qsize
    by (metis fun_upd_same map_some_val_given portEnqueuePID.simps) (* ToDo *)
  \<comment> \<open>frame condition for @{term qohp}.\<close>
  have qohp_preserved: "qohp ?newq = qohp ?orgq"
    using p_in_dom push_frame_qohp
    by (metis fun_upd_same map_some_val_given portEnqueuePID.simps) (* ToDo *)
  \<comment> \<open>..prove thesis\<close>
  from p_in_dom 
       wf_operand_portstate_queue \<comment> \<open>input queue is wf\<close>
       wf_result_queue  \<comment> \<open>output queue is wf\<close>
       qsize_preserved \<comment> \<open>frame conditions on portEnqueue\<close>
       qohp_preserved
  show ?thesis
    by (metis wf_PortState_queue_def)
qed   

text \<open>If we perform @{term portEnqueuePID} for port id @{term p} that exists 
      within well-formed port state @{term ps}, 
      then the queues in the resulting port state all well-formed
      with respect to the model.\<close>


lemma portEnqueuePID_preserves_wf_PortState_queues:
  assumes wf_ps: "wf_PortState m dom_pids ps"
      and p_in_dom: "p \<in> dom_pids"
     shows "wf_PortState_queues m dom_pids (portEnqueuePID ps p v)"
  using wf_ps  \<comment> \<open>assume we start with well-formed port states\<close>  
        p_in_dom 
        portEnqueuePID_preserves_wf_PortState_queue
        wf_PortState_def
        wf_PortState_queues_def  \<comment> \<open>well-formedness definitions and associated properties\<close> 
  by (smt (verit, best) fun_upd_apply map_get_def portEnqueuePID.simps) 

(* ToDo (from John): Try getting rid of the smt in the proof above and simpifying
  proofs above using portEnqueuePID.simps.   This seems to give the one-level
  unfolding of function definition 

  Also, if you take a look at what keeps showing up in the metis and smt proofs,
  it is things related to map (map_get_def) and (fun_upd_apply).  It is likely
  possible to engineer the defs/functions/lemmas so that those things don't keep
  coming up and blocking things. *)

text \<open>@{term portEnqueuePID} preserves port state well-formedness.\<close>

lemma portEnqueuePID_preserves_wf_PortState: 
 assumes wf_ps:   "wf_PortState m dom_pids ps " 
      and p_in_dom: "p \<in> dom_pids"
    shows "wf_PortState m dom_pids (portEnqueuePID ps p v)"
  using wf_ps p_in_dom \<comment> \<open>assumptions\<close>
        portEnqueuePID_preserves_wf_PortState_dom \<comment> \<open>lemmas showing subproperties of wf preserved\<close>
        portEnqueuePID_preserves_wf_PortState_queues 
        wf_PortState_def \<comment> \<open>definition of well-formedness\<close> 
  by metis

end