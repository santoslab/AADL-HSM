text \<open>The theory in this chapter formalizes the representation of thread application logic.
The theory depends static model information (e.g., to determine domains of state
representations such as the port identifiers may be referenced as input and output ports)
as well as thread state specifications.\<close>

theory App
  imports Main Model ThreadState 
begin

section \<open>Relational Behavior of Thread Application Logic\<close>

text \<open>The AADL standard specifies that the application code for a Thread component 
is organized into code "entry points" that are invoked by the AADL run time.
Our semantics currently supports the Initialize and Compute entry points.

While a thread's application logic could be formalized in a variety of ways, e.g., 
an automata based on the AADL Behavioral Annex (BA) or its adaptation in BLESS,
our representation is geared toward making a strong connection to behavioral
contract languages used to specify the behavior of threads coded in a programming
language.

In the GUMBO AADL contract language, contracts are attached to AADL Thread component
interfaces, and then thread entry point code is shown to conform to the contracts
using other techniques.  As part of our broader work, we have shown how
SMT-based verification in the Logika tool can prove that thread application code
written in Slang (a safety-critical subset of Scala) conforms to Logika contracts
automatically derived from AADL-level GUMBO contracts.  In addition, we 
have developed an approach for automated property-based testing to demonstrate
Slang code conformance with executable versions of GUMBO contracts.

Our semantics is not hard-wired to GUMBO contracts. However, HAMR, GUMBO, and 
this semantics are all designed to work "hand in glove":
\begin{itemize}
\item we aim to (eventually) prove the soundness of GUMBO with respect to this semantics, and
\item we aim to support a formal methods tool chain by which HAMR thread application code is 
proved to conform to GUMBO contracts using Logika, and then GUMBO contracts (which summarize
thread application logic behaviors) are translated
into the definitions in this theory to support Isabelle-based proofs of end-to-end system
behavior (experience with this approach will drive the design of a more automated system
verification in Logika that uses rules proven sound in this framework).  
\end{itemize}

Here are the key technical points.  Roughly speaking, each GUMBO entry point contract specifies a 
a relation between component input ports and output ports and also characterizes how
the thread's local variable state is updated during a thread activation. We represent
each relation as a predicate on application input port states @{term appi}, 
application output port states @{term appo}, dispatch status, and thread variable state.  We aggregate
each entry point contract representation for a thread into a record as defined below.  Hereafter,
for simplicity, we refer to a predicate providing the representation of a contract as the "contract" 
when no confusion results.\<close>

record 'a App =
  appInit :: "'a VarState \<Rightarrow> 'a PortState \<Rightarrow> bool"
  appCompute :: "'a VarState \<Rightarrow> 'a PortState \<Rightarrow> DispatchStatus \<Rightarrow> 'a VarState \<Rightarrow> 'a PortState \<Rightarrow> bool"

text \<open>Intuitively, a thread's Initialize entry point code 
provides initial values for the variables in the thread @{term VarState}
and initial values for the thread application output ports @{term PortState}
(according to the AADL standard,
values for output data ports are required; values for output event-like ports are optional).
Thus, an Initialize entry point contract puts constraints on a thread's variables and output
port values, and such contracts are formalized as a predicates on @{term VarState} and
output application @{term PortState}.  Intuitively, a thread state's @{term tvar} and
@{term appo} fields will be constrained by these predicates in the thread and system semantics
rules.

According to the AADL standard, a thread \emph{does not} provide initial values for its 
input ports.  Rather, input port initial values are obtained by an initial communication phase
after executing Initialize entry points that propagates output port values to connected input
port values.  This is why we omit input ports in the @{term appInit} predicate above. 

The Compute entry point takes as inputs the current var state, application input 
port state, and dispatch status.  The dispatch status information is produced by
the AADL RunTime dispatch logic and indicates what triggered the dispatch of the
thread.  This is most relevant for Sporadic threads where the dispatch status
indicates the port that triggered the dispatch due to event arrival on that port.
Conceptually, this allows the application logic to select behavior specific
to the triggering event, e.g., in code corresponding to an event handler for the arriving event.
The Compute entry point produces an updated var state in which individual
variables are optionally updated and an updated output application port state
in which output ports are optionally given values.
\<close>

text \<open>Each thread is associated to its application logic behavior via a 
      mapping from @{term CompId}s to @{term App}s.\<close>

type_synonym 'a CIDApp = "(CompId, 'a App) map" 

text \<open>We wish to distinguish the specifications that the developer 
supplies for an application (e.g., model information and thread application logic) 
from the state and execution logic of the AADL run-time and underlying 
execution platform.  Accordingly, we introduce a record type @{term AppModel} 
for developer-supplied information that aggregates the structural model
information (@{term Model}) and behavior specifications for each thread (@{term CIDApp}).
Further separating the developer's structural specifications and behavior 
specifications as in the record below permits the semantics to 
support an approach for model refinement where the structural model remains unchanged 
but the application logic can be considered at different abstraction levels.
\<close>

record 'a AppModel =
  appModel :: "Model"
  appModelApp :: "'a CIDApp"

text \<open>The following helper functions are defined to access elements of an @{term AppModel}.\<close>

fun appModelCompDescrs where "appModelCompDescrs am = modelCompDescrs (appModel am)"
fun appModelPortDescrs where "appModelPortDescrs am = modelPortDescrs (appModel am)"
fun appModelPortKind where "appModelPortKind am p = kind ((appModelPortDescrs am) $ p)"
fun appModelConns where "appModelConns am = modelConns (appModel am)"
fun appModelCIDs where "appModelCIDs am = dom (appModelCompDescrs am)"
fun appModelPIDs where "appModelPIDs am = dom (appModelPortDescrs am)"
fun appModelInit where "appModelInit am c = appInit (appModelApp am $ c)"
fun appModelCompute where "appModelCompute am c = appCompute (appModelApp am $ c)"

section \<open>Thread Application Logic Well-formedness Properties\<close>

text \<open>This section presents several well-formedness properties for application logic
predicates.  This properties are \<close>

text \<open>
The first property states basic constraints on app logic predicates with
respect to the general model, but without
regard to the model thread specifications associated with the app logic.  
This is a weaker property that may be strengthened by other properties below
when needed.   The constraints are:
\begin{itemize}
\item The port states constrained by @{term appInit} belong to output ports,
\item @{term appCompute} relates input port states to output port states,
\item All data ports from the model are constrained to have a non-empty value
by @{term appCompute}.  
\end{itemize}
\<close>

definition wf_App :: "Model \<Rightarrow> 'a App \<Rightarrow> bool"
  where "wf_App m a \<equiv> 
    (\<exists>ws qs. appInit a ws qs) \<and>
    (\<forall>ws qs. appInit a ws qs \<longrightarrow> (\<forall>p \<in> dom qs. isOutPID m p)) \<and>
    (\<forall>vs ps d ws qs. appCompute a vs ps d ws qs \<longrightarrow> 
      (\<forall>p \<in> dom ps. isInPID m p) \<and> (\<forall>p \<in> dom qs. isOutPID m p)) \<and>
    (\<forall>vs ps d ws qs. appCompute a vs ps d ws qs \<longrightarrow> 
      (\<forall>q. isDataPD (modelPortDescrs m $ q) \<longrightarrow> \<not>isEmpty (qs $ q)))" (* added *)

(* From John:  Suggested refinements
    - dom ca = dom (modelCompDescrs m)
    - [informal] \<forall>c \<in> dom ca .  wf_ThreadState_appi m c [app input ports](ca $ c)
    - [informal] \<forall>c \<in> dom ca .  wf_ThreadState_appo m c [app output ports](ca $ c)
    - [informal] \<forall>c \<in> dom ca .  wf_ThreadState_vars m c [app vars](ca $ c)
*)

text \<open>The following property further constrains app logic predicates to the
features of a specific thread @{term c}:
\begin{itemize}
\item any variable state that satisfies @{term appInit} must only contain
variable ids from thread @{term c}
\item any port state that satisfies @{term appInit} must only contain
port ids from thread @{term c}
\item any variable state that satisfies @{term appCompute} must only contain
variable ids from thread @{term c}
\item any port state that satisfies @{term appCompute} must only contain
port ids from thread @{term c}
\item any port state that satisfies the @{term appCompute} on output port states
must only contain output port ids from thread @{term c}.
\end{itemize}
\<close>

definition wf_CIDAppCIDAPP where "wf_CIDAppCIDAPP m c a \<equiv> 
  (wf_App m a) \<and>
  (\<forall>ws qs. appInit a ws qs \<longrightarrow> 
    (\<forall>v. v \<in> dom ws \<longrightarrow> isVarOfCID m c v) \<and>
    (\<forall>p. p \<in> dom qs \<longrightarrow> isPortOfCIDPID m c p)) \<and>
  (\<forall>vs ps d ws qs. appCompute a vs ps d ws qs \<longrightarrow>  
    (\<forall>v. v \<in> dom vs \<union> dom ws \<longrightarrow> isVarOfCID m c v) \<and>
    (\<forall>p. p \<in> dom ps \<union> dom qs \<longrightarrow> isPortOfCIDPID m c p) \<and>
    (\<forall>q. q \<in> dom qs \<longleftrightarrow> isPortOfCIDPID m c q \<and> isOutPID m q))" 

text \<open>A model's thread application logic is well-formed if each individual
thread's app logic is well-formed.\<close>

definition wf_CIDApp where "wf_CIDApp m ca \<equiv> \<forall>c. wf_CIDAppCIDAPP m c (ca $ c)"

(* ToDo: In the definition above, probably want to say that the domain of CIDApp matches the domain of the models compDescrs. *)

text \<open>A model integrated with app logic is well-formed if the model is well-formed
and if the app logic is well-formed with respect to the model.\<close>

definition wf_AppModel where 
  "wf_AppModel am \<equiv> wf_Model (appModel am) 
                  \<and> wf_CIDApp (appModel am) (appModelApp am)"

(* ToDo: If the following definitions in comments below are no longer needed, we can
remove them in the cleanup before the public release of the model artifacts. *)

(*
fun init_seq_fw where
  "init_seq_fw app i [] = i"
| "init_seq_fw app i (c#cs) = 
    init_seq_fw app 
      (\<Union>(vs, vs', ps') \<in> i. { (vs, vs' ++ vs'', ps' ++ ps'') | vs'' ps'' . (vs, (vs', ps')) \<in> app c }) cs"

fun init_seq where
  "init_seq app [] vp = vp"
| "init_seq app (c#cs) vp = 
    init_seq app cs (\<Union>(vs, ps) \<in> vp. { (vs', ps ++ ps') | vs' ps' . (vs, (vs', ps')) \<in> app c })"
*)
(*
fun init_seq where
  "init_seq app [] vp = vp"
| "init_seq app (c#cs) vp = 
    init_seq app cs (\<Union>(vs, ps) \<in> vp. { (vs', ps ++ ps') | vs' ps' . (vs, (vs', ps')) \<in> app c })"
*)
(*
lemma appInitParallel:
  assumes wf_am: "wf_AppModel am"
      and cs_cid: "cs \<subseteq> appModelCIDs am"
    shows "\<lbrakk> set cseq = cs; length cseq = card cs \<rbrakk> \<Longrightarrow> 
      init_seq (\<lambda>c. appInit (appModelApp am $ c)) cseq {s} \<subseteq> 
        ({ (\<Uplus>\<^sub>m {y c | c. c \<in> cs}, \<Uplus>\<^sub>m {z c | c. c \<in> cs}) 
          | x y z c. c \<in> cs \<and> (x, y c, z c) \<in> appInit (appModelApp am $ c) })"
proof (standard; induction cseq arbitrary: cs)
  case Nil
  then show ?case sorry
next
  case (Cons a cseq)
  then show ?case sorry
qed
*)
(*
lemma appInitParallel:
  assumes wf_am: "wf_AppModel am"
      and cs_cid: "cs \<subseteq> appModelCIDs am"
      and cs_1: "cs1 \<in> lists cs"
    shows "init_seq (\<lambda>c. appInit (appModelApp am $ c)) cs1 {s} = 
      ({ (\<Uplus>\<^sub>m {y c | c. c \<in> cs}, \<Uplus>\<^sub>m {z c | c. c \<in> cs}) 
            | x y z c. c \<in> cs \<and> (x, y c, z c) \<in> appInit (appModelApp am $ c) })"
proof
  show "init_seq (\<lambda>c. appInit (appModelApp am $ c)) cs1 {s} \<subseteq> 
      ({ (\<Uplus>\<^sub>m {y c | c. c \<in> cs}, \<Uplus>\<^sub>m {z c | c. c \<in> cs}) 
            | x y z c. c \<in> cs \<and> (x, y c, z c) \<in> appInit (appModelApp am $ c) })"
  
next
  show "({ (\<Uplus>\<^sub>m {y c | c. c \<in> cs}, \<Uplus>\<^sub>m {z c | c. c \<in> cs}) 
          | x y z c. c \<in> cs \<and> (x, y c, z c) \<in> appInit (appModelApp am $ c) }) \<subseteq>
            init_seq (\<lambda>c. appInit (appModelApp am $ c)) cs1 {s}" sorry
qed
*)
(*
lemma appInitSetNonIntereference:
  assumes wf_am: "wf_AppModel am"
      and cs_cid: "cs \<subseteq> appModelCIDs am"
      and c_cid: "c \<in> appModelCIDs am - cs"
    shows ""
*)

end