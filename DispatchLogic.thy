section \<open>Thread Dispatch Logic \label{sec:dispatch-logic}\<close>

text \<open>The specifications in this formalize AADL's rules for thread
dispatching (as specified in Section 5.3.2 of the standard).  Since
our formalization does not yet consider time, some aspects of AADL's
policies are not fully specified.  

This theory imports basic set and map definitions, Model (to access
basic structures as well as declared thread and port properties related to
dispatching, and ThreadState run time state to access the current state
of infrastructure ports when considering sporadic thread dispatch.\<close>

theory DispatchLogic
  imports SetsAndMaps Model ThreadState
begin

datatype EnabledStatus = 
    Periodic (* Periodic Thread is enabled *)
  | Sporadic PortId  (* Sporadic Thread is enabled by the arrival on triggering port PortId *)

text \<open>
 A periodic thread is enabled if the model-declared period of the thread
 (to be recorded in @{term CompDesc}) is appropriately related to current time
 (currently omitted).  See the AADL Standard Section 5.3.2 (33). 

 This method is a placeholder.  Its current implementation simply returns a 
 value indicating that it is enabled
\<close>

(* ToDo: we currently assume periodic components are always enabled. *)
fun periodicIsEnabled :: "CompDescr \<Rightarrow> bool"
  where "periodicIsEnabled cd = True" 

(* ToDo: we currently assume periodic components are always enabled. *)
fun periodicEnabledStatus :: "CompDescr \<Rightarrow> EnabledStatus set"
  where "periodicEnabledStatus cd = {EnabledStatus.Periodic}" 

text \<open>
 A sporadic thread is enabled if two types of conditions are satisfied:
\begin{enumerate}
\item timing: the time interval since the last dispatch of the thread exceeds
       the model-declared "period" of the thread (the "period" attribute is
       slightly misnamed and actually reflects a minimum separation time).
       In the current state of the formalization, time is omitted and this
       condition is taken to be trivially true.
\item event arrival: at least one message/value has arrived on a port
       declared in the model as a dispatch trigger.  By default (if no
       event triggers are explicitly declared in the model),
       all event and event data ports (see Section 5.4 (6))
\end{enumerate}
\<close>

text \<open>Placeholder for to check if the minimum separation time for a sporadic thread
is achieved.\<close>

fun minSeparationAchieved :: "Model \<Rightarrow> CompId \<Rightarrow> bool"
  where "minSeparationAchieved m c = True"

text \<open>
@{term selectMaximumUrgencyPorts} returns the set of port ids from thread c in m that
have the highest urgency among the 
given set of ports @{term candidateDispatchPort}.  This function
is intended to be called with the @{term candidateDispatchPorts} parameter
instantiated to a set of input ports from c that have non-empty 
infrastructure queues (i.e., messages pending).\<close>

fun selectMaximumUrgencyPorts :: "Model \<Rightarrow> PortId set \<Rightarrow> PortId set"
  (* buggy 
  where "selectMaximumUrgencyPorts m c candidateDispatchPorts = 
      {p \<in> portsOfCID m c .\<forall>p' \<in> candidateDispatchPorts . urgencyPID m p \<ge> urgencyPID m p'}"
  *)
  where "selectMaximumUrgencyPorts m candidateDispatchPorts = 
      {p \<in> candidateDispatchPorts .\<forall>p' \<in> candidateDispatchPorts . urgencyPID m p \<ge> urgencyPID m p'}"

lemma selectMaximumUrgencyPorts_subset:
  "selectMaximumUrgencyPorts m candidateDispatchPorts \<subseteq> candidateDispatchPorts"
  by simp

text \<open>
@{term getDispatchablePorts} returns the set of port ids from thread c in m 
are candidates for sporadic dispatching according to AADL's dispatching specification.
Intuitively, a candidate most be declared (implicitly or explicitly in the AADL model)
as a dispatch trigger, it must have data available in its infrastructure port state queue,
and it must have the highest urgency among other candidate ports.
Currently, if more than one port is declared with the same urgency, it is possible
to have multiple dispatchable ports (whereas the standard specifies that there
is at most one port available for dispatch).  We still need to add the notion
of AADL Queue\_Processing\_Protocol property, which would "break the tie" among
multiple dispatchable ports.  For now, we just return a set of ports and assume
non-deterministic tie-breaking.\<close>

fun getSporadicDispatchablePorts :: "Model \<Rightarrow> CompDescr \<Rightarrow> 'a PortState \<Rightarrow> PortId set"
  where "getSporadicDispatchablePorts m cd ps = 
        (let declaredDispatchTriggers = CompDescr.dispatchTriggers cd
     in let dataAvailableTriggers = {p \<in> declaredDispatchTriggers . dataAvailablePID ps p}
     in selectMaximumUrgencyPorts m dataAvailableTriggers)"


text \<open>The following two methods are not used directly in the semantics at the 
moment but are presented to enable traceability to the current version of the 
Slang reference semantics.\<close>

text \<open>@{term sporadicEnabledStatus} returns a set of @{term EnabledStatus} values
indicating which ports have triggered a sporadic dispatch.  The fact that a set
is currently returned instead of an indicator of a single port is a result of
our currently not emphasizing the timestamp tie-breaking for sporadic dispatch
candidates as reflected in AADL Queue Processing Protocol policy option.
Our intention in HAMR is to eventually implement the FIFO option for the Queue Processing Protocol,
which would return a single value that arrived earliest across all the non-empty ports
which have the same urgency (see Section 8.3.2 (36)).  
For now, we assume that the client system semantics transitions non-deterministically
pick from among the returned set values.  Note that AADL does allow a set
of triggering ports to be made available to the Compute Entry Point user code
(see Section 5.4.2 (39)). \<close>

(* Regarding the "{es . ..}" set comprehension below,
   for the general strategy of converting set comprehensions where the set
   element expression is a pattern into an alternative where the element expression
   is a simple variable, see Isabelle Tutorial Section 6.1.2 *)
fun sporadicEnabledStatus :: "Model \<Rightarrow> CompId \<Rightarrow> CompDescr \<Rightarrow> 'a PortState \<Rightarrow> EnabledStatus set"
  where "sporadicEnabledStatus m c cd c_infi 
    = (if (minSeparationAchieved m c)
       then (let dispatchablePorts = getSporadicDispatchablePorts m cd c_infi
          in {es . \<exists>p \<in> dispatchablePorts . es = Sporadic p})
       else {})"

text \<open>@{term computeEnabledStatus} returns a set of @{term EnabledStatus} values
indicating if a thread is dispatchable.  We first fetch the thread's dispatch
protocol from the thread descriptor.  Then, the return value is computed by calling
helper methods for both Periodic and Sporadic dispatch protocol cases.\<close>

fun computeEnabledStatus :: "Model \<Rightarrow> CompId \<Rightarrow> 'a PortState \<Rightarrow> EnabledStatus set"
  where "computeEnabledStatus m c ps = 
   (   let compDescr = ((modelCompDescrs m) $ c) 
    in let dp = CompDescr.dispatchProtocol compDescr
        in (case dp of 
              DispatchProtocol.Periodic \<Rightarrow> periodicEnabledStatus compDescr  
            | DispatchProtocol.Sporadic \<Rightarrow> sporadicEnabledStatus m c compDescr ps))"


subsection \<open>Determining Ports to Freeze\<close>

text \<open>
Once it is determined that a thread is dispatchable (enabled), we also determine
which ports should be frozen in the dispatch action, because the information 
used to determine freeze ports is coupled to the information used to determine
dispatch.
 
The functions/definitions in this section help compute the set of ports to freeze
for a particular dispatch.  This information is included in the @{term DispatchStatus}
structure for both periodic and sporadic dispatches.\<close>

text \<open>The rules for determining which ports to freeze are given primarily
in Section 8.3.2, but also Section 5.4 (7), 5.4.2 (e.g., clauses 7,37), 
Section 8.3 (e.g., clause 2) of the standard.
In general, the idea of AADL is that, upon dispatch, application
code can only read (a) ports that are either non-dispatch triggers 
(see Section 8.3.2 (20)
or (b) the port that was
selected for sporadic dispatch. 
It is these ports that must be frozen on dispatch (we only support the
Dispatch Time option for the AADL property Input Time, which indicates
the point in time at which ports or frozen).
The following is helpful intuition.
\begin{itemize}
\item Periodic threads -- The notion of dispatch trigger is not relevant for Periodic threads
(dispatch is only triggered by time-out, not event arrival).  Therefore,
all input ports are frozen (see e.g., Section 5.4.2 (33)).
\item Sporadic threads -- HAMR makes a few simplifying assumptions for Sporadic threads.  
First, it assumes that data ports can never
be dispatch triggers (i.e., only event and event data ports can be triggers).  
The AADL standard actually allows data ports to be declared as 
dispatch triggers (i.e., triggered when fresh data arrives, see Section 5.4 (6), 5.4.2 (31)) 
but this is not currently implemented in HAMR.
Then, following the AADL standard for sporadic components, 
unless dispatch triggers are explictly declared as
a thread property, all event and event data ports are assumed to be dispatch triggers
in sporadic components.
Practically speaking, this means that for Sporadic threads in HAMR, the typical situation
is that all data ports will be frozen along with the event-like port that triggered the
dispatch (see the AADL Standard Section 5.3.2 (30).  
In the non-typical situation that only a subset of event-like ports are
declared to be dispatch triggers, then all data ports, all non-trigger declared ports,
and trigger-declared port that actually triggered the dispatch will be frozen. 
Intuitively, the application should not read non-frozen input ports.  Right now,
we have no way of enforcing that in the semantics, and we assume that this property
is enforced at the code level (e.g., by static analysis). 
\end{itemize}
\<close>

(* 8.3.2 (20) The input of other ports that can trigger dispatch is not frozen. Input of the remaining
ports is frozen according to the specified input time.

(21) If a dispatch condition is specified then the logic expression determines the combination of event and event data
ports that trigger a dispatch, and whose input is frozen as part of the dispatch. The input of other ports that can
trigger dispatch is not frozen. The input of other ports that can trigger dispatch is not frozen. Input of the remaining
ports is frozen according to the specified input time.
*)

text \<open>For periodic threads, the following function states which input ports are to be frozen.
Our interpretation of the AADL standard is that all input ports are frozen.  This
is based on the following language: 
\begin{itemize}
\item "By default, input of ports is frozen for all 
ports that are not candidates for thread dispatch triggering" (Section 5.4 (7))." 
\item "By default arrival of data at data ports does not trigger a dispatch." (Section 8.3 (3))
\end{itemize}
HAMR always enforces the "default" mentioned above -- no data ports are dispatch triggers.
Moreover, since in a periodic thread, no port triggers a dispatch,
this implies that by default all input ports are frozen.
\<close>

fun getPeriodicPortsToFreeze :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set"
  where "getPeriodicPortsToFreeze m c = inPortsOfCID m c"

(* doc below has been updated with refs to new version of standard *)
text \<open>For sporadic threads, the following function states work together to indicate
which input ports are to be frozen. Our interpretation is based on the following
language in the AADL standard: 
\begin{itemize}
\item "By default, input of ports is frozen for all ports that are not 
candidates for thread dispatch triggering" (Section 5.4 (7))."  Since HAMR 
adopts the "default" scenario, this means that all data ports and all
non-dispatch trigger declared event-like ports will always be frozen.
\item "The input of other ports that can trigger dispatch is not frozen" (New Section 8.3.2 (20)).
and "for dispatch trigger candidates, only those port(s) actually triggering a 
specific dispatch is frozen" (Section 5.4 (7)).  
This means from among the declared dispatch triggers, only the
port that actually triggered the dispatch will be frozen.
\end{itemize}
\<close>

text \<open>The following helper function returns the event-like ports that are
not declared to be dispatch triggers (i.e., to match the language from the 
standard above, they are "not candidates for dispatch triggering".  
Event arrival at these ports never triggers a dispatch, and they will always
be frozen (along with all data ports).\<close>

fun getNonTriggeringEventLikePorts :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set"
  where "getNonTriggeringEventLikePorts m c 
    = (inEventLikePortsOfCID m c) - (dispatchTriggersOfCID m c)"

text \<open>Data ports are always frozen (HAMR assumes they can never be dispatch triggers), 
and any non-dispatch trigger ports are always frozen.\<close>

fun getSporadicAlwaysFreezePorts :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set"
  where "getSporadicAlwaysFreezePorts m c 
    = (inDataPortsOfCID m c) \<union> (getNonTriggeringEventLikePorts m c)"

text \<open>In addition to the ports that are always frozen, also freeze the port that
triggered the dispatch.\<close>

fun getSporadicPortsToFreeze :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> PortId set"
  where "getSporadicPortsToFreeze m c triggeringPort 
   = (getSporadicAlwaysFreezePorts m c) \<union> {triggeringPort}"


(* ToDo: For a specific system, consider generating specialized (short-cut)
lemmas and associated proofs that indicate that, e.g., a sporadic
thread is enabled when there is an event on a specific port. *)

subsection \<open>Computing Dispatch Status\<close>

fun computePeriodicDispatchStatus :: "Model \<Rightarrow> CompId \<Rightarrow> CompDescr \<Rightarrow> (DispatchStatus set)"
  where "computePeriodicDispatchStatus m c cd = 
    (if periodicIsEnabled cd
     then (let portsToFreeze = getPeriodicPortsToFreeze m c
            in {DispatchStatus.Periodic portsToFreeze})
     else {DispatchStatus.NotEnabled})"

fun computeSporadicDispatchStatus :: 
  "Model \<Rightarrow> CompId \<Rightarrow> CompDescr \<Rightarrow> 'a PortState \<Rightarrow> (DispatchStatus set)"
  where "computeSporadicDispatchStatus m c cd c_infi = 
    (let dispatchablePorts = getSporadicDispatchablePorts m cd c_infi
      in {ds . \<exists>p \<in> dispatchablePorts . 
                   ds = (DispatchStatus.Sporadic (p, getSporadicPortsToFreeze m c p))})"


fun computeDispatchStatus :: "Model \<Rightarrow> CompId \<Rightarrow> 'a PortState \<Rightarrow> (DispatchStatus set)"
  where "computeDispatchStatus m c c_infi = 
   (   let compDescr = ((modelCompDescrs m) $ c) 
    in let dp = CompDescr.dispatchProtocol compDescr
        in (case dp of 
              DispatchProtocol.Periodic \<Rightarrow> computePeriodicDispatchStatus m c compDescr
            | DispatchProtocol.Sporadic \<Rightarrow> computeSporadicDispatchStatus m c compDescr c_infi))"


subsection \<open>Well-formedness Properties\<close>

text \<open>One of the key goals of well-formedness for the computed dispatch status for
thread component c is to show that the triggering ports and ports-to-freeze in the 
dispatch status are input ports.   The following helper lemmas show that this
property holds for the helper functions used to construct the port id sets used
in the dispatch status.\<close>

lemma nonTriggeringEventLikePorts_are_inPorts: 
  "getNonTriggeringEventLikePorts m c \<subseteq> inPortsOfCID m c"
  using DiffD1 by fastforce 

lemma sporadicAlwaysFreezePorts_are_inPorts:
  "getSporadicAlwaysFreezePorts m c \<subseteq> inPortsOfCID m c"
   using DiffD1 by fastforce 

text \<open>In this helper function, @{term p} represents triggering port.\<close>

lemma sporadicPortsToFreeze_are_inPorts:
 "isInCIDPID m c p \<Longrightarrow> getSporadicPortsToFreeze m c p \<subseteq> inPortsOfCID m c"
  using sporadicAlwaysFreezePorts_are_inPorts by auto

text \<open>From model well-formedness, we can concluded that all ports in dispatch
trigger declarations are in ports.\<close>

lemma dispatchTriggers_are_inPorts:
  assumes wf_m: "wf_Model m"
      and c_in_m: "inModelCID m c"
    shows "dispatchTriggersOfCID m c \<subseteq> inPortsOfCID m c"
proof -
  \<comment> \<open>Since the model is well-formed, we know all of the dispatch trigger declarations
         in the model are well-formed.\<close>
  from wf_m have wf_m_DispatchTriggers: "wf_Model_CompDescrsDispatchTriggers m" 
    unfolding wf_Model_def by blast
   \<comment> \<open>Since dispatch trigger declarations are well-formed for component c in the model,
       we know that the declared dispatch triggers for c are all input ports.\<close>
  from c_in_m wf_m_DispatchTriggers 
  show "dispatchTriggersOfCID m c \<subseteq> inPortsOfCID m c" 
  unfolding wf_Model_CompDescrsDispatchTriggers_def
        (* ToDo: fix ugly proof *)
        by (metis inEventLikePortsOfCID.simps inModelCID.elims(2) 
                  inPortsOfCID.simps isInCDPID.simps isInCIDPID.simps 
                  isInEventLikeCDPID.simps isInEventLikeCIDPID.simps 
                  mem_Collect_eq modelCIDs.simps subsetD subsetI) 
qed

text "And from the above, we can conclude that the @{term getSporadicDispatchablePorts}
      function returns only in ports (plus we need a basic relation between the
      component id and component descriptor)."

lemma sporadicDispatchablePorts_are_inPorts:
  assumes wf_m: "wf_Model m"
      and c_in_m: "inModelCID m c" 
      and c_mapsTo_cd: "(modelCompDescrs m) $ c = cd"
    shows "getSporadicDispatchablePorts m cd ps \<subseteq> inPortsOfCID m c"
proof -
  from assms dispatchTriggers_are_inPorts
  have h1: "dispatchTriggersOfCID m c \<subseteq> inPortsOfCID m c" by blast
  from c_mapsTo_cd 
  have h2: "CompDescr.dispatchTriggers cd = dispatchTriggersOfCID m c" by simp
  from h1 h2 
  have h3: "CompDescr.dispatchTriggers cd  \<subseteq> inPortsOfCID m c" by blast
  hence h4: "\<forall>p \<in> CompDescr.dispatchTriggers cd . dataAvailablePID ps p \<longrightarrow> p \<in> inPortsOfCID m c"
    by blast
  have h5: "selectMaximumUrgencyPorts m {p\<in>CompDescr.dispatchTriggers cd . dataAvailablePID ps p} \<subseteq> inPortsOfCID m c"
    using h3 by auto
  thus ?thesis apply (simp only: getSporadicDispatchablePorts.simps) by meson
qed
 
text \<open>Now, we proof the overall well-formedness preservation property for
@{term wf_computeDispatchStatus}.\<close>

lemma wf_computeDispatchStatus:
  assumes wf_md: "wf_Model md" \<comment> \<open>model is well-formed.\<close>
      and c_in_md: "inModelCID md c" \<comment> \<open>thread id belongs to model.\<close>
       \<comment> \<open>infi portion of thread state is well-formed.\<close>
      and wf_ThreadState_infi: "wf_ThreadState_infi md c ps"
       \<comment> \<open>@{term d} is new dispatch status to be included in thread state.\<close>
      and d: "d \<in> computeDispatchStatus md c ps"
  \<comment> \<open>new dispatch status portion of thread state is well-formed.\<close>
  shows "wf_ThreadState_disp md c d"
  unfolding wf_ThreadState_disp_def
proof - {
    fix p
    assume a: "disp_elem d p"
    obtain dp where dp: "dp = CompDescr.dispatchProtocol ((modelCompDescrs md) $ c)"  by simp
    hence "isInCIDPID md c p"
    proof (cases dp)
      case Periodic
      hence "d \<in> computePeriodicDispatchStatus md c ((modelCompDescrs md) $ c)"
        using d dp by auto
      then show ?thesis using a by auto
    next
      case Sporadic
      hence s1: "d \<in> computeSporadicDispatchStatus md c ((modelCompDescrs md) $ c) ps"
        using d dp apply clarify
        by (metis DispatchProtocol.simps(4) computeDispatchStatus.elims)
      have s2: "getSporadicDispatchablePorts md ((modelCompDescrs md) $ c) ps \<subseteq> inPortsOfCID md c"
        using c_in_md sporadicDispatchablePorts_are_inPorts wf_md by blast
      show ?thesis 
      proof (cases d)
        case NotEnabled
        then show ?thesis using a by auto
      next
        case (Periodic qs)
        then show ?thesis using s1 by force
      next
        case (Sporadic qqs)
        obtain q qs where q: "qqs = (q, qs)" by fastforce
        have s4: "isInCIDPID md c q" using Sporadic q s1 s2 by fastforce
        have s5: "\<forall>q\<in>qs. isInCIDPID md c q"
          using DispatchStatus.inject(2) Sporadic q s1 s4 sporadicPortsToFreeze_are_inPorts 
          by fastforce
        show ?thesis using a apply simp
          using Sporadic q s4 s5 by fastforce
      qed
    qed
  } thus "\<forall>p. disp_elem d p \<longrightarrow> isInCIDPID md c p" by blast
qed

end