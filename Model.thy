(* chapter "Representing AADL Model Information" *)

text \<open>This chapter provides definitions for representing AADL 
static model information and associated model well-formedness specifications.

The static model structure is designed to represent HAMR-relevant content from a
AADL system instance model \cite[Section 2.2]{Feiler2013}.  The system instance model is 
a rather complicated structure and an external representation for it has not
yet been standardized.  When HAMR code generation executes, it generates a 
JSON instance model representation that also includes model annex information, e.g., 
including GUMBO contract information.\footnote{The HAMR instance model
definition is an extension of the XML instance model representation in the 
Ocarina AADL code generation framework
(whose development was led by Jerome Hugues).}

Subsequently in the HAMR code generation tool chain, the JSON instance model
representation is converted into a simplified Slang data structure, which 
in the HAMR code base is held in the {\tt ArchDescription.scala} file.  It is 
this data structure that forms the basis of the HAMR Isabelle model representation
in this theory file.

In summary, given a system model in the AADL sublanguage processed by HAMR, 
HAMR can generate instances of the types defined in this theory.  This provides the
basis for proving properties about system's structure and behavior. 

The theory uses Isabelle's Set and Map theories to represent model structures,
but includes some additional helper functions in the SetsAndMaps theory.\<close>

theory Model
  imports Main SetsAndMaps
begin

section "Identifiers"

text \<open>This section includes types for representing different types of identifiers.\<close>

subsection "Port Identifiers @{term PortId}"

text \<open>Port is the main category of feature appearing on the interface of AADL software components.
AADL tools typicially will need some concise way of uniquely refering to ports.
When generating a model representation
from AADL source, HAMR will generate a unique natural number identifier for each port, which is used throughout the HAMR 
run-time infrastructure. 

\edcomment{ToDo: add remark about new representation using Slang range types.
That is, Slang range types are used to restrict the ranges of portIds and similar
ranges. Should the translation generate a constraint corresponding to that range? 
}
\<close>

datatype PortId = PortId nat

text \<open>Sets of port identifiers are frequently used in the model representation, so we introduce an
appropriate type synonym.\<close>

type_synonym PortIds = "PortId set"

subsection "Component Identifiers @{term CompId}"

text \<open>Component identifier definitions are similar to those for port identifiers.  {\bf Note:} 
      In the current AADL formalization, 
      threads are the only category of components represented.\<close>

datatype CompId = CompId nat

type_synonym CompIds = "CompId set"

subsection "Variable Identifiers @{term VarId}"

text \<open>Variable identifiers are also similar to port identifiers, except that strings are used 
     for readability instead of numbers. \<close>


datatype VarId = VarId string

type_synonym VarIds = "VarId set"

section "Ports Descriptors"

text \<open>Port descriptors combine pieces of information from the AADL instance model
into a single structure that provides attributes of a component port.  
The descriptor includes the port's direction 
(in or out), kind (Event, Data, or Event Data), size (i.e., the size
of the buffer associated with the port) and other user-specified 
properties of the port that are recognized by HAMR.\<close>

text \<open>@{term PortDirection} indicates the directionality of the port.  
Note that HAMR only accepts unidirectional ports.  AADL's bi-directional {\tt in out} ports are
disallowed because they complicate analysis, semantics, and code generation.\<close>

datatype PortDirection = 
  In | Out

text \<open>@{term PortKind} indicates the possible AADL port category.  
\emph{Event} ports  model interrupt signals
or other notification-oriented messages without payloads.
\emph{Data} ports model shared memory between components or
distributed memory services where an update to a distributed memory
cell is automatically propagated to other components that declare
access to the cell.  \emph{Event data} ports model
asynchronous messages with payloads, such as in publish-subscribe
frameworks).  Definitions in Section~\ref{sec:port-states} specify
the state representation for storage associated with ports.  
Inputs to event and event data ports are buffered. The
buffer sizes and overflow policies can be configured per port using
standardized AADL properties.  Inputs to data ports are not buffered;
newly arriving data overwrites the previous value.\<close>

datatype PortKind = 
  Event | Data | EventData

text \<open>The @{term PortDescr} includes the following fields
\begin{itemize}
\item name - the printable name of the port for reporting and debugging purposes,
\item id - the unique identifier for the port, as generated by the HAMR code generator,
\item compId - the unique identifier for the component to which this port belongs,
\item direction - the direction of the port (in or out)
\item kind - the AADL port category for the port (event, data, or eventdata),
\item queueSize - the capacity (maximum number of items) of the buffer 
  associated with the port, as declared by the Queue\_Size 
port property in the AADL model (see the AADL standard Section 8.3).  When a size is not specified in the AADL model, 
the size value defaults to 1).  Data ports always have a size of 1.
\item ohp - corresponds to the AADL standard property {\tt Overflow\_Handling\_Protocol}
 (see the AADL standard Section 8.3).  This policy choice determines the behavior of an
enqueue operation when the port queue is full.
\end{itemize}
\<close>

text \<open>Define an enumerated type to represent the possible values of the 
AADL {\tt Overflow\_Handling\_Protocol} (see the AADL standard Section 8.3.3 (35))
indicating the behavior of an enqueue operation when the port queue is full.\<close>

datatype OverflowHandlingProtocol = DropNewest | DropOldest | Error | Unbounded

text \<open>
\begin{itemize}
\item {\tt DropNewest} - the newly arriving item is dropped (not enqueued).
\item {\tt DropOldest} - the oldest item in the queue is dequeued and the newly arriving
item is enqueued.
\item {\tt Error} - This option can be declared in the semantics currently, but it is 
not fully specified because the AADL standard underspecifies the intended semantics.
The AADL standard states that a thread error state results and a 
thread may  determine the port that caused the error by consulting the thread state 
Dispatch Status value (Section 8.3.3 (35)).  Section A.4 also adds ``the
thread’s error recovery to be invoked''.
\item {\tt Unbounded} -- not a valid AADL standard concept, but allowed to support 
prototyping in HAMR and this formalization.
\end{itemize}
The default setting (enforced by the HAMR translation into Isabelle) is {\tt DropOldest}.
This is relevant for data ports because it achieves the desired data port semantics of 
overwriting the currently held value.
\<close>


record PortDescr =
  name :: "string" 
  id :: "PortId" 
  compId :: "CompId" 
  direction :: PortDirection
  kind :: PortKind
  queueSize :: "nat"  \<comment> \<open>Corresponds to standard AADL property {\tt Queue\_Size}.\<close>
  urgency :: "nat"  \<comment> \<open>Corresponds to standard AADL property {\tt Urgency}.\<close>
  ohp :: OverflowHandlingProtocol  \<comment> \<open>Corresponds to standard AADL property 
                                         {\tt Overflow\_Handling\_Protocol}.\<close>
  
subsection \<open>Port Descriptor Well-formedness\<close>

text \<open>A port descriptor is well-formed iff
\begin{itemize}
\item the queue size specified in the port descriptor is greater than 0.
\item if the port is a data port, then its queue size must be equal to 1 (as specified 
in the AADL standard Section 8.3 (3)).
\end{itemize}

\edcomment{The AADL standard has a global properties {\tt Max\_Queue\_Size} {\tt Max\_Urgency} to bound all
port-specific {\tt Queue\_Size} and {\tt Urgency} values.  
We do not need that in the semantics now, but it could be added and enforced in 
well-formedness checks.}
\<close>


definition wf_PortDescr :: "PortDescr \<Rightarrow> bool"
  where "wf_PortDescr pd \<equiv> (PortDescr.queueSize pd > 0) 
                         \<and> (PortDescr.kind pd = Data \<longrightarrow> PortDescr.queueSize pd = 1)"

subsection \<open>Helper Functions for Working with Ports and Port Descriptors\<close>

text \<open>The following function can be used to abbreviate the declaration of 
port descriptors.\<close>

fun mkPortDescr where "mkPortDescr n i ci d k s u op
      = \<lparr> name= n, id=i, compId= ci, direction=d, kind= k, queueSize= s, urgency= u, ohp= op\<rparr>"

text \<open>The following helper functions query properties of ports as captured in port descriptors.\<close>

text \<open>Is the port an input port?\<close>

fun isInPD :: "PortDescr \<Rightarrow> bool" where
 "isInPD pd = (direction pd = In)"

text \<open>Is the port an output port?\<close>

fun isOutPD :: "PortDescr \<Rightarrow> bool" where
 "isOutPD pd = (direction pd = Out)"

text \<open>Is the port a data port?\<close>

fun isDataPD :: "PortDescr \<Rightarrow> bool" where
 "isDataPD pd = (kind pd = Data)"

text \<open>Is the port an event port?\<close>

fun isEventPD :: "PortDescr \<Rightarrow> bool" where
 "isEventPD pd = (kind pd = Event)"

text \<open>Is the port an event data port?\<close>

fun isEventDataPD :: "PortDescr \<Rightarrow> bool" where
 "isEventDataPD pd = (kind pd = EventData)"

text \<open>Is the port an event-like port? Note: we use the term \emph{event-like}
to refer to ports that are either event ports or event data ports.  
This combined reference is useful because event-like ports are queued
and have similar port update semantics, whereas data ports are not queued.
\<close>

fun isEventLikePD :: "PortDescr \<Rightarrow> bool" where
 "isEventLikePD pd = ((kind pd = Event) \<or> (kind pd = EventData))"


section "Component Descriptors"

text \<open>Similar to port descriptors, Component Descriptors 
combine pieces of information from the AADL instance model
into a single structure that provides attributes of a component.  
In the current formalization, only Thread components are represented.
Therefore, properties included in the component descriptor pertain to 
AADL Thread components.\<close>

text \<open>The following data type represents possible values of 
the AADL Dispatch\_Protocol Thread property (See the AADL standard Section 5.4.2 (45). 
Periodic threads are dispatched at regular intervals as defined by the 
AADL Period property (time and associated timing properties are not represented
currently).   Sporadic threads are dispatched up the arrival of messages
on event-like ports.  The specific conditions for thread dispatching are formalized
in Chapter~\ref{chap:dispatch-logic}. 
HAMR currently does not support the remaining AADL dispatch protocols (Aperiodic, 
Timed, Hybrid).\<close>

datatype DispatchProtocol = 
  Periodic | Sporadic

text \<open>The @{term CompDescr} includes the following fields
\begin{itemize}
\item name - the printable name of the component for reporting and debugging purposes,
\item id - the unique identifier for the component, as generated by the HAMR code generator,
\item portIds - set of unique identifiers for the ports that are declared on the interface
      of the component,  for the component to which this port belongs,
\item dispatchProtocol - the value of the AADL property Dispatch\_Protocol for this (thread) component,
\item dispatchTriggers - the set of identifiers for event-like input ports that can act as dispatch
triggers for this thread (for a longer discussion, see Chapter~\ref{chap:dispatch-logic}),
\item compVars - the set of identifiers for variables that contribute to the behavior
of the component, as specified by GUMBO contract declarations.
\end{itemize}
\<close>

record CompDescr = 
  name :: "string"
  id :: "CompId" (* unique id for component *)
  portIds :: "PortIds" (* ports belonging to this component *)
  dispatchProtocol :: "DispatchProtocol"  
  dispatchTriggers :: "PortIds" (* ids of ports that can trigger a dispatch *)
  varIds :: "VarIds"

subsection \<open>Helper Functions for Working with Components and Component Descriptors\<close>

text \<open>The following function can be used to abbreviate the declaration of 
component descriptors.\<close>

fun mkCompDescr where "mkCompDescr n i pis dp dts v = 
  \<lparr> name= n,  id=i, portIds= pis, dispatchProtocol= dp, dispatchTriggers= dts, varIds= v \<rparr>"

text \<open>The following helper functions query properties of components as captured in 
      component descriptors.\<close>

text \<open>Is the component a periodic thread?\<close>

fun isPeriodicCD :: "CompDescr \<Rightarrow> bool" where
 "isPeriodicCD cd = (dispatchProtocol cd = Periodic)"

text \<open>Is the component a sporadic thread?\<close>

fun isSporadicCD :: "CompDescr \<Rightarrow> bool" where
 "isSporadicCD cd = (dispatchProtocol cd = Sporadic)"


section "Connections"

text \<open>Connections are represented as a map from a connection source @{term PortId} 
 to a set of one or more target @{term PortIds}.\<close>

type_synonym Conns = "(PortId, PortIds) map"

section "Models"

text \<open>The complete static model consists of three maps (lookup tables):
\begin{itemize}
\item modelCompDescrs: associates component ids to component descriptors,
\item modelPortDescrs: associates port ids to port descriptors,
\item modelConns: associates each source port id to a set of target port ids to which it is connected.
\end{itemize}
\<close>

record Model =
  modelCompDescrs :: "(CompId, CompDescr) map" 
  modelPortDescrs :: "(PortId, PortDescr) map" 
  modelConns :: "Conns"
 
text \<open>A helper function for abbreviating the construction of model structures.\<close>

fun mkModel where "mkModel compdescrs portdescrs conns = 
  \<lparr> modelCompDescrs= compdescrs,  modelPortDescrs= portdescrs,  
    modelConns= conns \<rparr>"


(*================ H e l p e r     F u n c t i o n s ===================*)

section "Model Helper Functions"

text \<open>
This section defines helper function for accessing model elements.
\<close>

subsection \<open>Model-wide Queries About Components and Ports\<close>

text \<open>
The first set of helper functions are queries across an entire
model (not limited to a particular component).
\<close>

text \<open>Return the component identifiers in model m.\<close>
fun modelCIDs:: "Model \<Rightarrow> CompId set"
  where "modelCIDs m = dom (modelCompDescrs m)"

text \<open>Return the port identifiers in model m.\<close>
fun modelPIDs:: "Model \<Rightarrow> PortId set"
  where "modelPIDs m = dom (modelPortDescrs m)"

text \<open>Does model m include a component (id) c?\<close>
fun inModelCID :: "Model \<Rightarrow> CompId \<Rightarrow> bool"
  where "inModelCID m c = (c \<in> modelCIDs m)"

text \<open>Does model m include a port (id) p?\<close>
fun inModelPID :: "Model \<Rightarrow> PortId \<Rightarrow> bool" 
  where "inModelPID m p = (p \<in> modelPIDs m)"

text \<open>Does model m include a input port (id) p?\<close>
fun isInPID :: "Model \<Rightarrow> PortId \<Rightarrow> bool" 
  where "isInPID m p = (direction (modelPortDescrs m $ p) = In)"

text \<open>Does model m include an output port (id) p?\<close>
fun isOutPID :: "Model \<Rightarrow> PortId \<Rightarrow> bool"
  where "isOutPID m p = (direction (modelPortDescrs m $ p) = Out)"

text \<open>Does model m include a port (id) p with queue capacity n?\<close>
fun isQueueSizePID :: "Model \<Rightarrow> PortId \<Rightarrow> nat \<Rightarrow> bool"
  where "isQueueSizePID m p n = (queueSize (modelPortDescrs m $ p) = n)"

text \<open>Return the queue capacity of port (id) p in model m.\<close>
fun queueSizePID :: "Model \<Rightarrow> PortId \<Rightarrow> nat"
  where "queueSizePID m p = (queueSize (modelPortDescrs m $ p))"

text \<open>Return the kind (data, event, event data) of port (id) p in model m.\<close>
fun kindPID :: "Model \<Rightarrow> PortId \<Rightarrow> PortKind"
  where "kindPID m p = (kind (modelPortDescrs m $ p))"

text \<open>Does model m include a data port (id) p?\<close>
fun isDataPID :: "Model \<Rightarrow> PortId \<Rightarrow> bool"
  where "isDataPID m p = (kindPID m p = Data)"

text \<open>Does model m include an event port (id) p?\<close>
fun isEventPID :: "Model \<Rightarrow> PortId \<Rightarrow> bool"
  where "isEventPID m p = (kindPID m p = Event)"

text \<open>Does model m include an event data port (id) p?\<close>
fun isEventDataPID :: "Model \<Rightarrow> PortId \<Rightarrow> bool"
  where "isEventDataPID m p = (kindPID m p = EventData)"

text \<open>Does model m include an event-like port (id) p?\<close>
fun isEventLikePID :: "Model \<Rightarrow> PortId \<Rightarrow> bool"
  where "isEventLikePID m p = ((kindPID m p = Event) \<or> (kindPID m p = EventData))"

text \<open>Return the urgency of port (id) p in model m.\<close>
fun urgencyPID :: "Model \<Rightarrow> PortId \<Rightarrow> nat"
  where "urgencyPID m p = (urgency (modelPortDescrs m $ p))"

text \<open>Is source port (id) p1 connected to target port (id) p2?\<close>
fun connectedPIDs :: "Model \<Rightarrow> PortId \<Rightarrow> PortId \<Rightarrow> bool"
  where "connectedPIDs m p1 p2 = (p2 \<in> ((modelConns m) $ p1))"

subsection \<open>Queries About Ports Associated With a Specific Component\<close>

text \<open>
The second set of helper functions support queries about
properties of a particular component, which can be indicated
by its id (i.e. @{term CompId}) or component descriptor (i.e. @{term CompDescr})
\<close>

text \<open>In model m, does component (id) c have a data port (id) p?\<close>
fun isPortOfCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool" 
  where "isPortOfCIDPID  m c p = (p \<in> (portIds ((modelCompDescrs m) $ c)))"

text \<open>In model m, does component (descriptor) cd have a var (id) v?\<close>
fun isVarOfCD :: "Model \<Rightarrow> CompDescr \<Rightarrow> VarId \<Rightarrow> bool"
  where "isVarOfCD m cd v = (v \<in> (varIds cd))"

text \<open>In model m, does component (id) c have a var (id) v?\<close>
fun isVarOfCID :: "Model \<Rightarrow> CompId \<Rightarrow> VarId \<Rightarrow> bool"
  where "isVarOfCID m c v = isVarOfCD m ((modelCompDescrs m) $ c) v"

text \<open>In model m, does component (descriptor) cd have an input port (id) p?\<close>
fun isInCDPID :: "Model \<Rightarrow> CompDescr \<Rightarrow> PortId \<Rightarrow> bool"
  where "isInCDPID m cd p = (p \<in> (portIds cd) \<and> isInPD ((modelPortDescrs m) $ p))"

text \<open>In model m, does component (id) c have an input port (id) p?\<close>
fun isInCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool"
  where "isInCIDPID m c = isInCDPID m ((modelCompDescrs m) $ c)"

text \<open>In model m, does component (descriptor) cd have an output port (id) p?"\<close>
fun isOutCDPID :: "Model \<Rightarrow> CompDescr \<Rightarrow> PortId \<Rightarrow> bool"
  where "isOutCDPID m cd p = (p \<in> (portIds cd) \<and> isOutPD ((modelPortDescrs m) $ p))"

text \<open>In model m, does component (id) c have an output port (id) p?"\<close>
fun isOutCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool"
  where "isOutCIDPID m c = isOutCDPID m ((modelCompDescrs m) $ c)"

text \<open>In model m, does component (descriptor) cd have a data port (id) p?"\<close>
fun isDataCDPID :: "Model \<Rightarrow> CompDescr \<Rightarrow> PortId \<Rightarrow> bool"
  where "isDataCDPID m cd p = (p \<in> (portIds cd) \<and> isDataPD ((modelPortDescrs m) $ p))"

text \<open>In model m, does component (id) c have a data port (id) p?"\<close>
fun isDataCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool"
  where "isDataCIDPID m c = isDataCDPID m (modelCompDescrs m $ c)"

text \<open>In model m, does component (descriptor) cd have an event port (id) p?"\<close>
fun isEventCDPID :: "Model \<Rightarrow> CompDescr \<Rightarrow> PortId \<Rightarrow> bool"
  where "isEventCDPID m cd p = (p \<in> (portIds cd) \<and> isEventPD ((modelPortDescrs m) $ p))"

text \<open>In model m, does component (id) c have an event port (id) p?"\<close>
fun isEventCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool"
  where "isEventCIDPID m c = isEventCDPID m ((modelCompDescrs m) $ c)"

text \<open>In model m, does component (descriptor) cd have an event-like port (id) p?"\<close>
fun isEventLikeCDPID :: "Model \<Rightarrow> CompDescr \<Rightarrow> PortId \<Rightarrow> bool"
  where "isEventLikeCDPID m cd p = (p \<in> (portIds cd) \<and> isEventLikePD ((modelPortDescrs m) $ p))"

text \<open>In model m, does component (id) c have an event-like port (id) p?"\<close>
fun isEventLikeCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool"
  where "isEventLikeCIDPID m c = isEventCDPID m ((modelCompDescrs m) $ c)"

(* new - need to test *)

text \<open>In model m, does component (descriptor) cd have a input data port (id) p?"\<close>
fun isInDataCDPID :: "Model \<Rightarrow> CompDescr \<Rightarrow> PortId \<Rightarrow> bool"
  where "isInDataCDPID m cd p = (p \<in> (portIds cd) 
                                \<and> (let pd = ((modelPortDescrs m) $ p)
                                   in (isInPD pd \<and> isDataPD pd)))"

text \<open>In model m, does component (id) c have an input data port (id) p?"\<close>
fun isInDataCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool"
  where "isInDataCIDPID m c = isInDataCDPID m ((modelCompDescrs m) $ c)"

text \<open>In model m, does component (descriptor) cd have an input event-like port (id) p?"\<close>
fun isInEventLikeCDPID :: "Model \<Rightarrow> CompDescr \<Rightarrow> PortId \<Rightarrow> bool"
  where "isInEventLikeCDPID m cd p = (p \<in> (portIds cd) 
                                \<and> (let pd = ((modelPortDescrs m) $ p)
                                   in (isInPD pd \<and> isEventLikePD pd)))"

text \<open>In model m, does component (id) c have an input event-like port (id) p?"\<close>
fun isInEventLikeCIDPID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> bool"
  where "isInEventLikeCIDPID m c = isInEventLikeCDPID m ((modelCompDescrs m) $ c)"

text \<open>Return the ports belonging to component (id) c in model m.\<close>
fun portsOfCID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set" 
  where "portsOfCID  m c = portIds ((modelCompDescrs m) $ c)"

text \<open>Return the input ports belonging to component (id) c in model m.\<close>
fun inPortsOfCID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set"
  where "inPortsOfCID m c = {p . isInCIDPID m c p}"

text \<open>Return the input data ports belonging to component (id) c in model m.\<close>
fun inDataPortsOfCID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set"
  where "inDataPortsOfCID m c = {p . isInDataCIDPID m c p}"

text \<open>Return the input event-like ports belonging to component (id) c in model m.\<close>
fun inEventLikePortsOfCID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set"
  where "inEventLikePortsOfCID m c = {p . isInEventLikeCIDPID m c p}"

text \<open>Return the output ports belonging to component (id) c in model m.\<close>
fun outPortsOfCID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set"
  where "outPortsOfCID m c = {p . isOutCIDPID m c p}"

text \<open>Return the dispatch triggers (port ids)belonging to component (id) c in model m.\<close>
fun dispatchTriggersOfCID :: "Model \<Rightarrow> CompId \<Rightarrow> PortId set" 
  where "dispatchTriggersOfCID  m c = dispatchTriggers ((modelCompDescrs m) $ c)"

(*========= M o d e l   W e l l f o r m e d n e s s   P r o p e r t i e s  ===========*)

section \<open>Model Well-formedness Properties\<close>

text \<open>
We now define a collection of well-formedness properties for models. 
The notion of well-formed model (@{term wf_Model}) is defined as the 
conjunction of all of these properties.

When HAMR generates an Isabelle representation of an AADL, all
of these properties are automatically proven.
\<close>


(*
 To Add
   * no reuse of var ids across components (may not need to this -- does Stefan need it?)
   * add constraints on Urgency ?
*)

text \<open>The model is finite, i.e., the sets of descriptors are finite.\<close> 
definition wf_Model_Finite :: "Model \<Rightarrow> bool" 
  where "wf_Model_Finite m \<equiv> 
    finite (dom (modelCompDescrs m)) \<and> 
    finite (dom (modelPortDescrs m))"

text \<open>Each port descriptor in the modelPortDescrs map is well-formed.\<close> 
definition wf_Model_PortDescr :: "Model \<Rightarrow> bool" 
  where "wf_Model_PortDescr m \<equiv> 
  (\<forall>p \<in> dom (modelPortDescrs m). wf_PortDescr ((modelPortDescrs m) $ p))"

text \<open>For each entry (p:: PortId, pd:: PortDescr) in the port descriptors map, 
   the port id in the descriptor pd matches p.\<close> 
definition wf_Model_PortDescrsIds :: "Model \<Rightarrow> bool" 
  where "wf_Model_PortDescrsIds m \<equiv> 
  (\<forall>p \<in> dom (modelPortDescrs m). p = PortDescr.id ((modelPortDescrs m) $ p))"

text \<open>For each entry (c:: CompId, cd:: CompDescr) in the component descriptors map, 
   the comp id in the descriptor cd matches c.\<close> 
definition wf_Model_CompDescrsIds :: "Model \<Rightarrow> bool" 
  where "wf_Model_CompDescrsIds m \<equiv> 
  (\<forall>c \<in> dom (modelCompDescrs m) . c = CompDescr.id ((modelCompDescrs m) $ c))"

text \<open>For each entry (p:: PortId, pd:: PortDescr) in the port descriptors map, 
   the comp id indicating the enclosing component for the port is in the
   domain of the component descriptors map.\<close>

(* ToDo: it may be best to use the "inModel" predicate here as an abstraction 
   for dom (..) *)
definition wf_Model_PortDescrsCompId :: "Model \<Rightarrow> bool" 
  where "wf_Model_PortDescrsCompId m \<equiv> 
  (\<forall>p \<in> dom (modelPortDescrs m). PortDescr.compId ((modelPortDescrs m) $ p) \<in> dom (modelCompDescrs m))"

text \<open>For each entry (c:: CompId, cd:: CompDescr) in the component descriptors map, 
   the port ids of component's contained ports are contained in the domain of the 
   port descriptor map.\<close>
definition wf_Model_CompDescrsContainedPortIds :: "Model \<Rightarrow> bool" 
  where "wf_Model_CompDescrsContainedPortIds m \<equiv> 
  (\<forall>c \<in> dom (modelCompDescrs m).  (CompDescr.portIds ((modelCompDescrs m) $ c)) \<subseteq> dom (modelPortDescrs m))"

text \<open>For each pair of component ids c, d in the model,
      the sets of ids of ports belonging to those components are disjoint.\<close>
definition wf_Model_DisjointPortIds :: "Model \<Rightarrow> bool"
  where "wf_Model_DisjointPortIds m \<equiv>
  (\<forall>c \<in> dom (modelCompDescrs m). 
   \<forall>d \<in> dom (modelCompDescrs m). 
   (c \<noteq> d \<longrightarrow> ((CompDescr.portIds ((modelCompDescrs m) $ c) \<inter> CompDescr.portIds ((modelCompDescrs m) $ d)) = {})))"

text \<open>For each entry (p:: PortId, s:: PortId set) in the connections map,  
   the port id p and the port ids s = {p1, ..., pn} are in the domain of the 
   port descriptor map.\<close>
definition wf_Model_ConnsPortIds :: "Model \<Rightarrow> bool" 
  where "wf_Model_ConnsPortIds m \<equiv> 
  (\<forall>p \<in> dom (modelConns m).   (p \<in> dom (modelPortDescrs m))
                            \<and> ((modelConns m) $ p) \<subseteq> dom (modelPortDescrs m))"

text \<open>For each entry (p:: PortId, s:: PortId set) in the connections map,  
      p is an output port and the ports in p' in s are input ports
      and the port kinds of p and p' match.\<close>
definition wf_Model_ConnsPortCategories :: "Model \<Rightarrow> bool" 
  where "wf_Model_ConnsPortCategories m \<equiv> 
  (\<forall>p \<in> dom (modelConns m).(isOutPID m p) \<and> 
   (\<forall>p'\<in> ((modelConns m) $ p).(isInPID m p') \<and> (kindPID m p = kindPID m p')))"

text \<open>No ``fan in'' for data ports:  for each p1, p2 that are connection sources 
      in the connections map,  if p1 and p2 both connect to a target port q and q is a data port, 
      then p1 and p2 must be identical (see AADL standard Section 9.1 (L11)), and also
      Section 9.2.2 (20) -- ``Data ports are restricted to 1-n connectivity, i.e., a data port 
      can have multiple outgoing connections, but only one incoming connection per mode. 
      Since data ports hold a single data state value, multiple incoming connections
      would result in multiple sources overwriting each other’s values in the destination 
      port variable.''\<close>

definition wf_Model_ConnsNoDataPortFanIn :: "Model \<Rightarrow> bool" 
  where "wf_Model_ConnsNoDataPortFanIn m \<equiv> 
  (\<forall>p1 \<in> dom (modelConns m).\<forall>p2 \<in> dom (modelConns m).
   \<forall>q. connectedPIDs m p1 q \<and> connectedPIDs m p2 q \<and> isDataPID m q
    \<longrightarrow> p1 = p2)"


text \<open>For each entry (c:: CompId, cd:: CompDescr) in the component descriptors map, 
   the port ids of the declared dispatch triggers must be input event-like ports belonging to 
   the components.\<close>

definition wf_Model_CompDescrsDispatchTriggers :: "Model \<Rightarrow> bool"
  where "wf_Model_CompDescrsDispatchTriggers m \<equiv> 
  (\<forall>c \<in> dom (modelCompDescrs m).  
    (dispatchTriggersOfCID m c \<subseteq> inEventLikePortsOfCID m c))"

text \<open>For each entry (c:: CompId, cd:: CompDescr) in the component descriptors map, 
if c is Sporadic, then cd's dispatchTriggers is non-empty.
HAMR currently ignores dispatch trigger declarations in periodic ports.
NOTE: the AADL standard does not require that dispatch triggers are declared in
Sporadic threads.  The standard specifies that, in the absence of dispatch
trigger declarations in Sporadic threads, ALL event-like ports are treated
as dispatch triggers by default.  We do not include the logic for ``by default''.
Instead, we assume that the HAMR Isabelle model generation strategy will
look for any dispatch trigger declarations for the thread in the AADL model,
and if no such declarations exist, the translation will 
explicitly insert in dispatchTriggers field in the CompDescr, a set containing
the set of all event-like input ports for the thread.  This simplifies the logic
in the Isabelle model and HAMR code-base.
\<close>

definition wf_Model_SporadicComp :: "Model \<Rightarrow> bool"
  where "wf_Model_SporadicComp m \<equiv>
  (\<forall>c \<in> dom (modelCompDescrs m). (isSporadicCD (modelCompDescrs m $ c)) 
    \<longrightarrow> (dispatchTriggers (modelCompDescrs m $ c)) \<noteq> empty)"


text \<open>For each entry (c:: CompId, cd:: CompDescr) in the component descriptors map, 
if c is Periodic, then cd's dispatchTriggers is empty.\<close>

definition wf_Model_PeriodicComp :: "Model \<Rightarrow> bool"
  where "wf_Model_PeriodicComp m \<equiv>
  (\<forall>c \<in> dom (modelCompDescrs m). (isPeriodicCD (modelCompDescrs m $ c)) 
    \<longrightarrow> (dispatchTriggers (modelCompDescrs m $ c)) = empty)"


text \<open>
The following top-level definition for well-formed models
is the conjunction of the properties above.\<close>

definition wf_Model :: "Model \<Rightarrow> bool"
  where "wf_Model m \<equiv>
           wf_Model_Finite m
         \<and> wf_Model_PortDescr m
         \<and> wf_Model_PortDescrsIds m
         \<and> wf_Model_CompDescrsIds m
         \<and> wf_Model_PortDescrsCompId m
         \<and> wf_Model_CompDescrsContainedPortIds m 
         \<and> wf_Model_DisjointPortIds m
         \<and> wf_Model_ConnsPortIds m
         \<and> wf_Model_ConnsPortCategories m
         \<and> wf_Model_ConnsNoDataPortFanIn m 
         \<and> wf_Model_CompDescrsDispatchTriggers m
         \<and> wf_Model_SporadicComp m
         \<and> wf_Model_PeriodicComp m"

text \<open>
Finiteness of models is implied by other wf conditions, e.g. @{term wf_SystemSchedule}, but
might occasionally needed to be assumed explicitly.\<close>

definition finite_Model :: "Model \<Rightarrow> bool"
  where "finite_Model m \<equiv> finite (dom (modelCompDescrs m)) \<and> finite (dom (modelPortDescrs m))"

(*========= M o d e l   W e l l f o r m e d n e s s   P r o p e r t i e s  ===========*)

section \<open>Properties Derived from Well-formedness\<close>

text \<open>The following helper lemmas lift constraints on queue capacity 
specified in the lower-level port descriptors to the top-level model abstractions.\<close>

lemma wf_model_implies_data_ports_capacity: 
  assumes wf_m: "wf_Model m"
      and p_in_m: "p \<in> dom (modelPortDescrs m)"
      and p_is_dataport: "isDataPID m p"
    shows "(queueSizePID m p) = 1"
proof - 
  from p_is_dataport have h1: "(kind (modelPortDescrs m $ p)) = Data" by auto 
  from wf_m have h2: "wf_Model_PortDescr m" unfolding wf_Model_def by auto
  from h2 have h3: "wf_PortDescr ((modelPortDescrs m) $ p)" by (simp add: p_in_m wf_Model_PortDescr_def)
  from h3 h1 show ?thesis by (simp add: wf_PortDescr_def)
qed

lemma  
  assumes wf_m: "wf_Model m"
      and p_in_m: "p \<in> dom (modelPortDescrs m)"
      and p_is_dataport: "isDataPID m p"
    shows "(queueSizePID m p) = 1"
proof - 
  from p_is_dataport have h1: "(kind (modelPortDescrs m $ p)) = Data" by auto 
  from wf_m have h3: "wf_PortDescr ((modelPortDescrs m) $ p)" 
    by (auto simp add: p_in_m wf_Model_def wf_Model_PortDescr_def wf_PortDescr_def)
  from h3 h1 show ?thesis by (simp add: wf_PortDescr_def)
qed

(*
lemma  
 "\<lbrakk>wf_Model m; isDataPID m p\<rbrakk> \<Longrightarrow> p \<in> dom (modelPortDescrs m)"
  apply (simp only: wf_Model_def wf_Model_PortDescr_def wf_PortDescr_def) 
  sledgehammer
  sorry
*)

lemma wf_model_implies_port_capacity_ge_one: 
  assumes wf_m: "wf_Model m"
      and p_in_m: "inModelPID m p"
    shows "1 \<le> (queueSizePID m p)"
proof -
  \<comment> \<open>Unfold well-formedness properties.\<close>
  from wf_m have h1: "wf_Model_PortDescr m" unfolding wf_Model_def by auto
  from h1 have h2: "wf_PortDescr ((modelPortDescrs m) $ p)" using wf_Model_PortDescr_def p_in_m by simp
   \<comment> \<open>The definition of well-formedness for port descriptors includes the condition that
      the maximum queue capacity is greater than 0.\<close>
  from h2 have h3: "0 < queueSize ((modelPortDescrs m) $ p)" by (simp add: wf_PortDescr_def)
  \<comment> \<open>..and from this we can show that the capacity is greater than or equal to 1.\<close>
  from h3 show ?thesis by auto
qed


lemma isInCIDPID_implies_p_in_m:
  assumes wf_m:  "wf_Model m"
      and p_assm: "isInCIDPID m t p"
      and t_in_m: "t \<in> modelCIDs m" (* can this be derived from the property above? *)
    shows "inModelPID m p"
proof - 
  from assms show ?thesis 
    using wf_Model_def wf_Model_CompDescrsContainedPortIds_def 
    by auto
(*
  from p_assm have h1: "p \<in> (portIds ((modelCompDescrs m) $ t))" by simp
  from wf_m have h3: "CompDescr.portIds ((modelCompDescrs m) $ t) \<subseteq> dom (modelPortDescrs m)"
    using wf_Model_def wf_Model_CompDescrsContainedPortIds_def t_in_m by simp
  from h1 h3 show ?thesis by auto
*)
qed

end