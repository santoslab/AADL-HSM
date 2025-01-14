chapter \<open>GUMBO Contract Representation\<close>

text \<open>This chapter presents a representation of contracts.\<close>


theory Contracts
  imports Main Model SetsAndMaps App PortState ThreadState SystemState
begin

(* Check CAmkES formalization to see if they tended to use records or data type more *)
(* Possible classroom activity is to define well-formedness conditions for contracts *)

section \<open>Shallow Embedding Representation of Contracts\<close>

subsection \<open>Data Type Invariants\<close>

text \<open>Each HAMR datatype may have one or more invariants associated with it.  
The semantic requirement is that all values of these data types conform 
to corresponding invariants.

HAMR datatypes are used to type values flowing between components on ports.  
These values are value-based in that they do not contain references (which would generate
semantics dependences on underlying memory representations, etc.).  
Further, when generating code for HAMR-supported programming languages, values
of HAMR types are considered immutable.

At what points in execution should datatype invariants be enforced?
This is not immediately easy to answer since a common issue when
dealing with invariants is that they may be violated during intermediate
computations in which the subject of the invariant is being manipulated,
then they must be reestablished again.  

Practically, what happens with values of HAMR types during component computation
is outside the scope of HAMR semantics -- it is the programming language's 
decision about how such invariants are treated.  From the HAMR semantics point 
of view, we only require that a value satisfy its data type invariant as it is 
communicated between components, i.e., when it appears on an input or output port.
This also implies that the invariant is maintained during communication since 
no values are modified during intercomponent communication.

Moreover, the invariants also apply to state variable values in the component's
pre and post-state.
\<close>

text \<open>Semanticly, a datatype is a predicate on values (i.e., 
values of the HAMR universal value type).  Conceptually, the 
invariant is also indexed by a HAMR type (has some knowledge
of the type), but we ignore that issue for now since we currently
do not have a representation of types within the semantics.\<close>

type_synonym 'a DIContractSem = "'a \<Rightarrow> bool"

text \<open>Since PortState queues accumulate multiple values as they are 
flowing through a port, it will often be necessary to semantically lift the
datatype invariant from a single value to a queue of values.\<close>

fun DIContractLiftToQueue :: "'a DIContractSem \<Rightarrow> 'a Queue \<Rightarrow> bool" where
 "DIContractLiftToQueue ic q = (\<forall>v \<in> set (buffer q). ic v)"

subsection \<open>Integration Constraints\<close>

text \<open>Each component port may have \emph{integration constraints} associated with it.
Each integration constraint can be understood as an invariant for values flowing 
through the port.\<close>  

text \<open>Semanticly, an Integration Constraint is a predicate on values (i.e., 
values of the HAMR universal value type).\<close>

type_synonym 'a ICContractSem = "'a \<Rightarrow> bool"

text \<open>Since PortState queues accumulate multiple values as they are 
flowing through a port, it will often be necessary to semantically lift the
integration constraint from a single value to a queue of values.\<close>

fun ICContractLiftToQueue :: "'a ICContractSem \<Rightarrow> 'a Queue \<Rightarrow> bool" where
 "ICContractLiftToQueue ic q = (\<forall>v \<in> set (buffer q). ic v)"

text \<open>Integration constraints do not specify the presence or absence
of values at the port.  Nor can they capture relationships between component
inputs and outputs.   Instead, they only state that when a value is put into or 
taken from a port at runtime, it must satisfy all stated integration 
constraints for the port (this is the semantic interpretation of the constraint).

Absence of integration constraint violations can be verified statically by requiring
stronger conditions that guarantee that no runtime violations occur. 

When dealing with an input port Q in the verification process:
\begin{itemize}
\item A VC is generated to require that all output ports connected to Q produce 
only values that satisfy Q's integration constraints.  To enable a compositional 
approach, the necessity of the VCs are recognized when each output port is 
connected to the input port Q, i.e., when the sending and receiving components are 
\emph{integrated}.  
\item An assumption condition (AC) is generated when the receiving component 
retrieves a value from port Q specifying that all its integration constraints 
are satisfied.
\end{itemize}

There are at least two approaches for generating VCs sufficient for guaranteeing 
no run-time violations.  The easier and more restrictive approach is as follows:
\begin{itemize}
\item When an output port P is connected to Q, require that for each Q integration 
constraint I, the conjunction of P's integration constraints entails I.
\end{itemize}

This approach requires all of the constraints necessary for P output values to 
satisfy I be specified via P integration constraints.   However, if the
entry point contracts for the component C of P are sufficiently strong, it is possible 
for output values that satisfy C's contract to satisfy I even when P's integration
constraints do not entail I.  Intuitively, this is because some constraints necessary
to satisfy I are not achieved by P integration constraints, but rather by C entry
point contracts.  A verification strategy aligned with this alternate principle would 
need to generate a VC requiring that C's Compute entry point contract, conjoined
with P's integration constraints entails I (similarly for C's Initialization
Entry Point contract).

The above discussion reveals that integration constraints are not technically 
necessary -- the same constraints may be achieved via entry point contracts.
However, integration constraints are useful to developers for the following reasons:
\begin{itemize}
\item Compute entry point contract structure typically depends on the specified
dispatch protocol for the component (e.g., Periodic or Sporadic).  The integration
constraint format is independent of the dispatch protocol and enables the developer
to specify initial simple value constraints on ports before a dispatch protocol 
is specified (and they do not need to be changed when a dispatch protocol is changed).
\item Integration constraints introduce invariants that must hold for both initialize
and compute entry points.  Thus, the desired constraint does not need to be 
restated in each entry point.
\end{itemize}
\<close>

subsection \<open>Compute Entry Point Contracts -- Preconditions\<close>

text \<open>Each thread component may multiple preconditions (assume clauses)
that place constraints on input port states (big question: do these
contracts apply to the application port state or to the infrastructure
port state?  I'm inclined to answer "application" -- because they 
are constraints that you apply to the component's prestate when it is 
dispatched.  But then we composing
components, we may need some way of deriving contracts for infrastructure
port states.\<close>

text \<open>In addition to user-defined contracts, there are other constraints
that must hold due to AADL semantics.
\begin{itemize}
\item For a sporadic component, exactly one trigger port can have a value
in it (and for now, we assume that we only dequeue one value at a time).
\item There must always be exactly one value present in an input data port.
\end{itemize}
\<close>

text \<open>Compute Entry Point Preconditions are similar to Integration Constraints
on input ports and that they both place constraints on the pre-state 
of a component. There are several differences between the two:
\begin{itemize}
\item preconditions can detect the presence or absence of events/values in the
queues of event-like port states 
\item conceptually, preconditions apply not to value but to queue states,
and they need to guard against empty queues before extract a queue value.
\item whereas a IC is associated with a single port, preconditions are
associated with the entire pre-state of a component.  Thus, they can state
relationships between values of input application port states as well as 
thread local state values.
\end{itemize}
\<close>

text \<open>Therefore, we can interpret the semantics of an precondition 
as a predicate on the component's input application state and local 
variable state.  Intuitively, the domain of PortState matches the 
declared component input ports and the domain of VarState matches
the components declared state variables.  These conditions are 
enforced by system well-formedness conditions.\<close>

type_synonym 'a CEPPreContractSem = "'a PortState \<Rightarrow> 'a VarState \<Rightarrow> bool"

subsection \<open>Compute Entry Point Contracts -- PostConditions\<close>


type_synonym 'a CEPPostContract = "('a PortState \<Rightarrow> 'a VarState \<Rightarrow> 
                                     DispatchStatus \<Rightarrow> 
                                     'a PortState \<Rightarrow> 'a VarState \<Rightarrow> bool)" 



subsection \<open>Compute Entry Point Contracts -- Frame Conditions (implicit Post Conditions)\<close>


subsection \<open>Effective Pre/Post-Condition Construction\<close>

record 'a ThreadContract =
  appInit :: "'a InitBehavior"
  appCompute :: "'a ComputeBehavior" 



text \<open>In contrast to integration constraints, pr\<close>

section \<open>Deep Embedding Representation of Contracts\<close>

datatype Exp = Dummy (* may want to separate GExps which can contain In(..) *)
datatype Name = Dummy
datatype DataId = Dummy

type_synonym Exps = "Exp set" (* could divide these into pre and post-expressions *)
type_synonym NamedExps = "(Name, Exp) map"
type_synonym PortExp = "PortId \<times> Exp"
type_synonym NamedPortExps = "(Name, PortExp) map"

record IEPContract =
  imodifies :: Vars
  iguarantees :: NamedExps

record IntegrationContract = 
  ins :: NamedPortExps
  outs :: NamedPortExps

record HandlesContract =
  hmodifies :: Vars
  hassumes :: NamedExps
  hguarantees :: NamedExps

record CaseContract =
  sname :: Name
  sassumes :: Exp  (* case expressions inherit the identifier of the case clause *)
  sguarantees :: Exp

record CEPContract =
  cmodifies :: Vars
  cassumes :: NamedExps
  cguarantees :: NamedExps
  ccases :: "CaseContract list" (* order matters for case contracts, so instead of a map we use a list *)
  chandles :: "(PortId,HandlesContract) map" 

record DataContract = 
  invs :: NamedExps

record ThreadContract = 
  stateDecls :: Vars
  (* ToDo: add var invariants here *)
  intcontract :: IntegrationContract
  iepcontract :: IEPContract
  cepcontract :: CEPContract
  
record Contracts =
  threadContracts :: "(CompId,ThreadContract) map"
  dataContracts :: "(DataId, DataContract) map"
 

end
