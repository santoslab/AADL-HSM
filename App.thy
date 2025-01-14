section \<open>Relational Behavior of Thread Application Logic\<close>

theory App
  imports Main VarState PortState ThreadState Model
begin

subsection \<open>Application Logic Relations \label{subsec:app-logic-relations}\<close>

text \<open>The application code for an AADL Thread component is organized into entry points.
This semantics currently supports the Initialization and Compute entry points.
In the HAMR/GUMBO framework, GUMBO contracts are attached to AADL Thread component
interfaces, and then thread entry point code is shown to conform to the contracts
via SMT-based verification in Logika or via testing.

Roughly speaking, each entry point contract specifies a 
a relation between component input ports and output ports and also characterizes how
the thread's local variable state is transformed.  GUMBO contracts are
automatically generated (planned) by HAMR into Isabelle as predicates
on thread/port state elements.  These predicates are represented as a shallow
embedding as reflected in the  @{text "InitContract"} and @{text "ComputeContract"}
types shown below.  These predicates are then lifted to set-based definitions
of component behaviors reflected in the @{text "InitRelation"} and 
@{text "ComputeRelation"} types shown below.

Intuitively, the Initialize entry point takes as inputs the initial var state for
the thread, where the value of each variable is set to an unspecified system default value, 
and it gives each thread value an initial value.  In addition, it gives each
output data port a value, and may optionally give each event-like port a value.

Discuss / To Do:
 - it's likely that as a simplifying assumption, we should require each output
   data port to be given a value.  This should be stated in the well-formed condition.

The Compute entry point takes as inputs the current var state, application input 
port state, and dispatch status.  The dispatch status information is produced by
the AADL RunTime dispatch logic and indicates what triggered the dispatch of the
thread.  This is most relevant for Sporadic threads where the dispatch status
indicates the port that triggered the dispatch due to event arrival on that port.
Conceptually, this allows the application logic to select behavior specific
to the triggering event, e.g., in code corresponding to an event handler.
The Compute entry point produces an updated var state where individual
variables are optionally updated and where output ports are optionally given values.
\<close>

text \<open>
Below are the types for the shallow embedding predicate-based representations of GUMBO
contracts.
\<close>

type_synonym 'a InitContract = "('a PortState \<Rightarrow> 'a VarState \<Rightarrow> bool)" 
type_synonym 'a ComputeContract = "('a PortState \<Rightarrow> 'a VarState \<Rightarrow> 
                                     DispatchStatus \<Rightarrow> 
                                     'a PortState \<Rightarrow> 'a VarState \<Rightarrow> bool)" 

text \<open>
Below are the types for the set-based representations of component behaviors (which
will be derived from the predicate representation of the contracts).
\<close>

type_synonym 'a InitBehavior = "('a PortState  \<Rightarrow> 'a VarState \<Rightarrow> bool)" 
type_synonym 'a ComputeBehavior = "('a PortState \<Rightarrow> 'a VarState \<Rightarrow> 
                                    DispatchStatus \<Rightarrow> 
                                    'a PortState \<Rightarrow> 'a VarState \<Rightarrow> bool)" 

text \<open>The following type represents (abstractly) the behavior of the 
thread component's application code as derived from its contracts. 
\<close>

record 'a AppBehavior =
  appInit :: "'a InitBehavior"
  appCompute :: "'a ComputeBehavior" 


(* add outPorts to domain of compute if necessary; it needs to be ensured that all outPorts are defined at the end *)

text \<open>
The following definitions "lift" the predicate/contract-based representation 
into a set-based representation.  

The strategy for handling contract well-formedness issues is important and was the 
subject of much deliberation. From a practical/implementation point of view,
HAMR will check that each GUMBO contract is well-formed in the sense that:
\begin{itemize}
\item it only reference features (ports, variables) from component to which it belongs,
\item it doesn't confuse input and output ports,
\item it doesn't confuse types associated with ports and variables.
\end{itemize}

With a shallow embedding representation of contracts, there is no way to directly
check (confirm) those properties in the Isabelle representation.  For example, 
to check type correctness, we would need a formalization of predicate expression
ASTs and an associated type checker.

Ultimately, we desire that, given a well-formed input @{term ThreadState}, the
relational app behavior of a component will yield well-formed output 
@{term ThreadState}s.  This will enable us support the fundamental run-time
property that each thread execution step in the semantics preserves
well-formed thread-states.  Note that HAMR should also guarantee this, and
we eventually want to demonstrate this by showing HAMR state logs conform
with Isabelle system execution steps.

In any case, the following definitions are currently designed so that,
in lifting from the predicate representations of the contracts, the
predicates are only applied to well-formed input and output thread states.

Therefore, we would expect that the presence of mal-formed HAMR contracts
(manifested in mal-formed predicates) would give rise to empty relations.

An alternative approach that needs to be investigated is that we only
assume input states are well-formed, and we prove that, for a given
contract, output states are well-formed.  This will require that we
add frame-conditions to the contracts (intuitively, capturing 
implicit properties that HAMR ensures during entry point execution).
\<close>

(* infrastructure / well-formedness conditions on initialize app behavior.
   We need to be able to establish that the output of the InitEP is a well-formed
   thread state. *)

definition initInfrastructureContract :: "Model \<Rightarrow> CompId \<Rightarrow> 'a InitContract"
  where "initInfrastructureContract m cid ao tv \<equiv> 
              wf_ThreadState_appo m cid ao
          \<and>   wf_ThreadState_tvar m cid tv"


(* infrastructure conditions on compute app behavior.
   Basically, the idea is that we need to show that well-formed properties are preserved.
   That might be derived from frame conditions on the different portions of the thread state.
   For now, simply use the existing well-formedness on both the input and outputs. *)

definition computeInfrastructureContract :: "Model \<Rightarrow> CompId \<Rightarrow> 'a ComputeContract"
  where "computeInfrastructureContract m cid ai tvi ds ao tvo \<equiv> 
           wf_ThreadState_appi m cid ai 
        \<and>  wf_ThreadState_tvar m cid tvi
        \<and>  wf_ThreadState_disp m cid ds
        \<and>  wf_ThreadState_appo m cid ao 
        \<and>  wf_ThreadState_tvar m cid tvo"


fun mk_InitBehaviorFromContract :: "Model \<Rightarrow> CompId \<Rightarrow> 
   'a InitContract \<Rightarrow> 'a InitBehavior" where
  "mk_InitBehaviorFromContract m cid initContract ao tvo =
             (initContract ao tvo 
          \<and>  initInfrastructureContract m cid ao tvo)"

fun mk_ComputeBehaviorFromContract :: "Model \<Rightarrow> CompId \<Rightarrow> 
    'a ComputeContract
 \<Rightarrow> 'a ComputeBehavior" where
  "mk_ComputeBehaviorFromContract m cid computeContract ai tvi d ao tvo  =  
           (computeContract ai tvi d ao tvo
        \<and>  computeInfrastructureContract m cid ai tvi d ao tvo)"

fun mk_AppBehaviorFromContracts ::
  "Model \<Rightarrow> CompId \<Rightarrow> 'a InitContract \<Rightarrow> 'a ComputeContract \<Rightarrow> 'a AppBehavior" where
  "mk_AppBehaviorFromContracts m cid initUserContract computeUserContract = \<lparr>
    appInit = mk_InitBehaviorFromContract m cid initUserContract,
    appCompute = mk_ComputeBehaviorFromContract m cid computeUserContract \<rparr>"

                              
(**** The plan is to refactor the wf_ThreadState properties to properly address
      queue sizes before continuing with the definitions below. ****)

text \<open>An @{term App} @{term a} is well-formed wrt a @{term Model} @{term m} and @{term CompId} @{term c} iff 
the thread state elements associated with the relations (transfer functions) of @{term a} are well-formed wrt @{term m} 
and @{term c}.\<close>

(* The following property should probably be moved directly into the definitions
   wf_ThreadState_appi and wf_ThreadState_appo *)

definition wf_ThreadState_dataPorts :: "Model \<Rightarrow> CompId \<Rightarrow> 'a PortState \<Rightarrow> bool"
  where "wf_ThreadState_dataPorts m c ps \<equiv>
          \<forall>p \<in> dom ps . isDataPID m p \<longrightarrow> isOneElement (ps $ p)"

definition wf_InitBehavior:: "Model \<Rightarrow> CompId \<Rightarrow> 'a InitBehavior \<Rightarrow> bool" 
  where "wf_InitBehavior m c initBehavior \<equiv>
    (\<forall>ao tvo . initBehavior ao tvo \<longrightarrow> 
      (  wf_ThreadState_appo m c ao
       \<and> wf_ThreadState_tvar m c tvo
       \<and> wf_ThreadState_dataPorts m c ao))"

definition wf_InitBehavior_Inhabited:: "Model \<Rightarrow> CompId \<Rightarrow> 'a InitBehavior \<Rightarrow> bool" 
  where "wf_InitBehavior_Inhabited m c initBehavior \<equiv>
    (\<exists>ao tvo . initBehavior ao tvo)"

(* Stefan: We should change this into an implication where
         wf_ThreadState_appi m c ai
       \<and> wf_ThreadState_dataPorts m c ai 
       \<and> wf_ThreadState_tvar m c tvi
are added on the left-hand side of the implication.
This will express that the semantics guarantees wf given that the apps preserve it,
a contract between the app code and the AADL infrastructure.
  Operation clearAll must be changed to incorporate the data port constraints.
*)

definition wf_ComputeBehavior:: "Model \<Rightarrow> CompId \<Rightarrow> 'a ComputeBehavior \<Rightarrow> bool" 
  where "wf_ComputeBehavior m c computeBehavior \<equiv>
    (\<forall>ai tvi ds ao tvo . computeBehavior ai tvi ds ao tvo \<longrightarrow> 
      (  wf_ThreadState_appi m c ai
       \<and> wf_ThreadState_dataPorts m c ai 
       \<and> wf_ThreadState_tvar m c tvi
       \<and> wf_ThreadState_disp m c ds  
       \<and> wf_ThreadState_appo m c ao
       \<and> wf_ThreadState_dataPorts m c ao
       \<and> wf_ThreadState_tvar m c tvo
       ))"

definition wf_ComputeBehavior_Inhabited:: "Model \<Rightarrow> CompId \<Rightarrow> 'a ComputeBehavior \<Rightarrow> bool" 
  where "wf_ComputeBehavior_Inhabited m c computeBehavior \<equiv>
    (\<exists>ai tvi ds ao tvo . computeBehavior ai tvi ds ao tvo)"

definition wf_AppBehavior:: "Model \<Rightarrow> CompId \<Rightarrow> 'a AppBehavior \<Rightarrow> bool" 
  where "wf_AppBehavior m c a \<equiv>
    c \<in> dom (modelCompDescrs m)
  \<and> wf_InitBehavior m c (appInit a)
  \<and> wf_InitBehavior_Inhabited m c (appInit a)
  \<and> wf_ComputeBehavior m c (appCompute a)
  \<and> wf_ComputeBehavior_Inhabited m c (appCompute a)"


text \<open>
Each thread component is associated with its application logic via 
an @{term AppBehaviors} structure -- a map from component identifiers to 
application code behaviors.
\<close>

type_synonym 'a AppBehaviors = "(CompId, 'a AppBehavior) map" 

text \<open>
A @{term AppBehaviors} structure is well-formed, 
if each @{term AppBehavior} is well-formed wrt the associated component.
\<close>

(* NOTE: this should probably constrain the domain of the map to match the set of 
   Thread IDs declared in the model. *)

definition wf_AppBehaviors where "wf_AppBehaviors m cb \<equiv> \<forall>c. wf_AppBehavior m c (cb $ c)"

(* Need to move this remark from the AADL standard Section 8.3.1 (6) to the appropriate place
  (6) Event and event data ports may dispatch a port specific Compute_Entrypoint. This permits threads with
multiple event or event data ports to execute different source text sequences for events arriving at different event
ports.  *)

end