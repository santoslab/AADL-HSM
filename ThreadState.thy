section \<open>Thread States\<close>

text \<open>The state of a thread includes the state of its ports, local variables, and its 
dispatch status (a structure indicating what caused the dispatch of the thread and
what input ports are currently frozen).

A thread's state changes due to:
\begin{itemize}
\item execution of the thread's entry points, with the semantics of execution being
reflected in the application logic (see App.thy) for each entry point. Entry point
execution may change the application view of the input and output port states and local variables.
\item communication actions in the communication infrastructure.  This may change the 
infrastructure view of the input ports (e.g., as messages arrive at the thread's inputs)
and output ports (e.g., as messages are released from the thread onto the communication substrate).
\item execution of AADL run-time services as the thread changes its scheduling state.
This includes the transfer port values from infrastructure input ports to application input ports via
the ReceiveInput RTS -- ``freezing'' the application's view of the input ports, as well as the 
transfer of port values from application output ports to infrastructure output ports via
the SendOutput RTS.
\end{itemize}
Other theories will prove that, regardless of state changes, the thread state will always
be well-formed according to the definitions in this theory.

This theory defines:
\begin{itemize}
\item the structure of a thread state,
\item notions of well-formedness for a thread state, and
\item a characterization of the valid initial states for a thread.
\end{itemize}

The theory imports SetsAndMaps.thy to represent basic structures, Models.thy to supply
variable and port identifiers and to the align the variable states and port states with model
declarations to achieve well-formedness, and VarState.thy and PortState.thy to provide
the representations of variable state and port state.
\<close>

theory ThreadState
  imports Main SetsAndMaps Model VarState PortState
begin

subsection \<open>Structures\<close>

text \<open>The AADL standard presents "dispatch status" as information
that the thread application code can access to find out what triggered the dispatch of the thread
(in particular, for sporadic dispatch protocol, which input event-like port had an event arrival
that triggered the dispatch). However, the standard does not fully specify the concept.  

The following datatype defines our interpretation of the dispatch status.\<close>

datatype DispatchStatus = 
    NotEnabled  (* Thread is not enabled *) 
  | Periodic "PortIds" (* Periodic Thread is enabled with a set of input ports to be frozen *)
  | Sporadic "PortId * PortIds" (* Sporadic Thread is enabled by dispatch trigger Port  with a set of input ports to be frozen *)

text \<open>The "Periodic" alternate of the datatype indicates that the thread is currently
executing due to a periodic dispatch and the accompanying @{term PortIds} indicates
the set of input ports that have had their values frozen (by the invocation of the
ReceiveInput RTS). 
The "Sporadic" alternate of the datatype indicates that the thread is currently
executing due to a sporadic dispatch that has been triggered
by the arrival of a message on the port indicated by @{term PortId} 
and the accompanying @{term PortIds} indicates
the set of input ports that have had their values frozen.
According to the AADL standard, the thread application code should never
access any port whose values are not frozen (the rationale is that such
an access could result in a race condition).  The condition that the thread
(and, in HAMR, an accompanying GUMBO contract) must not access an unfrozen
port should be enforced by static checks on the program code and contract specification.
For more information about how this semantics interprets the standard's 
approach to "freezing input ports", see DispatchLogic.thy.

The "NotEnabled" alternate is more a technical choice of the semantics design.
The thread application code would never see this alternate since if the thread
is not enabled, the application code would not be running.  We have added
this alternative to give the runtime system a value that the dispatch status field
of the thread state can be set to when the thread is not executing. Another alterative
might be to have the status field set to the most recent dispatch status value or
some other default value.\<close>

text \<open>Given a dispatch status value, the following helper function returns the set of 
input ports whose values are frozen.  These form the conceptual "port inputs" to the 
application logic during that particular dispatch of the thread.\<close>

fun dispatchInputPorts :: "DispatchStatus \<Rightarrow> PortIds" where
  "dispatchInputPorts NotEnabled = {}"
| "dispatchInputPorts (Periodic ps) = ps"
| "dispatchInputPorts (Sporadic (_, ps)) = ps"

text \<open>The following helper predicate is used in thread state well-formedness definitions.
It holds when @{term p} is a port id mentioned any where in the dispatch status.
Such a port id should appear in the set of input port ids for a thread.\<close>

fun disp_elem:: "DispatchStatus \<Rightarrow> PortId \<Rightarrow> bool" where
  "disp_elem ds p = (case ds of
                       NotEnabled \<Rightarrow> False
                     | Periodic portset \<Rightarrow> p \<in> portset  
                     | Sporadic (p',portset) \<Rightarrow> ((p = p') \<or> p \<in> portset))" 

(* ToDo: John: refactor or rename these two helper functions.  For example, it
should be the case for Sporadic that is p triggers a dispatch then p is also frozen.
We may not need both of these functions. *)

text \<open>The runtime state of the thread consists of the following elements.  For further motivation
and rationale, see Hatcliff-al:ISOLA22. The justification for the @{term PortState} fields 
of the @{term ThreadState} is also summarized in PortState.thy.

\begin{itemize}
\item @{term tvar} - the state of the thread's local variables 
\item @{term iin} - infrastructure input port state (representing the infrastructure's view of input ports)
\item @{term ain} - application input port state (representing the thread application logic's view of input ports) 
\item @{term aout} - application output port state (representing the thread application logic's view of output ports)
\item @{term iout} - infrastructure output port state (representing the infrastructure's view of output ports)
\item @{term disp} - the current dispatch status of the thread
\end{itemize}
\<close>
record 'a ThreadState = 
  infi :: "'a PortState"
  appi :: "'a PortState"
  appo :: "'a PortState"
  info :: "'a PortState"
  tvar :: "'a VarState"
  disp :: DispatchStatus

text \<open>The following function helps abbreviate the construction of a thread state.\<close>

fun tstate where "tstate ii ai ao io tv ds = 
 \<lparr> infi= ii, appi= ai, appo= ao, info= io, tvar= tv, disp= ds \<rparr>"


subsection \<open>Well-formedness Definitions\<close>

text \<open>In general, thread state well-formedness definitions 
    specify that the things (vars, ports) that we are manipulating
    in the state for a thread {\em t} are aligned with things that we declared in the model for {\em t}.
    (e.g., the thread state does not include a queue for a port that was not declared
    for the thread in the model, and conversely, every port that was declared for this 
    thread in the model has a queue associated with it).
    First, well-formedness conditions for each of the thread state elements are specified.
    Then, the well-formedness condition for the entire thread state is defined as a conjunction of 
    these properties.\<close> 

(*
  Note: eventually, we would also need
   - type compatibility for values associated with ports
   - conformance of queue sizes to declared queue size properties
      (for now, we can simplify by just hardwiring the well-formedness predicate
       to a maximum queue size of 1)
*)

subsubsection \<open>Well-formed Thread State Elements\<close>

definition wf_ThreadState_tvar:: "Model \<Rightarrow> CompId \<Rightarrow> ('a VarState) \<Rightarrow> bool" where
 "wf_ThreadState_tvar m c vs \<equiv> wf_VarState vs {v . isVarOfCID m c v}"  

text \<open>The infi component of a ThreadState (input infrastructure port map) 
   is well formed when the domain of the infi port map is equal to the set of 
   input ports for the thread declared in the model. 
   Intuitively, each of the declared "in" ports for the thread (according to the model)
   is associated with a infrastructure message queue, 
   (and there are no "extra" ports in the map). \<close>

(* ToDo: add constraint to port size and policy -- probably need to pass the port
   descriptor down to port well-formedness *)

definition wf_ThreadState_infi:: "Model \<Rightarrow> CompId \<Rightarrow> ('a PortState) \<Rightarrow> bool" where
 "wf_ThreadState_infi m c ps \<equiv> wf_PortState m {p . isInCIDPID m c p} ps" 

text \<open>The definitions below for other port-state elements are similar.\<close>

definition wf_ThreadState_appi:: "Model \<Rightarrow> CompId \<Rightarrow> ('a PortState) \<Rightarrow> bool" where
 "wf_ThreadState_appi m c ps \<equiv> wf_PortState m {p . isInCIDPID m c p} ps"


definition wf_ThreadState_appo:: "Model \<Rightarrow> CompId \<Rightarrow> ('a PortState) \<Rightarrow> bool" where
 "wf_ThreadState_appo m c ps \<equiv> wf_PortState m {p . isOutCIDPID m c p} ps"

definition wf_ThreadState_info:: "Model \<Rightarrow> CompId \<Rightarrow> ('a PortState) \<Rightarrow> bool" where
 "wf_ThreadState_info m c ps \<equiv> wf_PortState m {p . isOutCIDPID m c p} ps"

text \<open>If p is mentioned in the dispatch status of ts, then it must be an input port of c.
      ToDo: constrain to dispatch triggers, also check the relationship between 
      p' and portset in the Sporadic case.\<close>

definition wf_ThreadState_disp:: "Model \<Rightarrow> CompId \<Rightarrow> DispatchStatus \<Rightarrow> bool" where
 "wf_ThreadState_disp m c ds \<equiv> (\<forall>p. disp_elem ds p \<longrightarrow> isInCIDPID m c p)" 

subsubsection \<open>Well-formed Thread States\<close>

definition wf_ThreadState:: "Model \<Rightarrow> CompId \<Rightarrow> ('a ThreadState) \<Rightarrow> bool"  
  where "wf_ThreadState m t ts \<equiv>
   (wf_ThreadState_infi m t (infi ts)) \<and>
   (wf_ThreadState_appi m t (appi ts)) \<and>
   (wf_ThreadState_appo m t (appo ts)) \<and>
   (wf_ThreadState_info m t (info ts)) \<and>
   (wf_ThreadState_tvar m t (tvar ts)) \<and>
   (wf_ThreadState_disp m t (disp ts))"


subsection \<open>Initial Thread States\<close>

text \<open>Characterizing system execution, e.g., in terms of traces, requires some notion of 
initial system state, which in turn requires some notion of initial thread state.
This section provides definitions characterizing initial thread states.
Following AADL's philosophy of a system Initialization phase, the Initialize
entry point for each thread {\em should} provide the initial state of the
thread that will be seen in the ``normal'' AADL system Compute phase 
by the thread's application code. However, from a technical standpoint
in the semantics, we need an initial state for the Initialization phase
(which is what is provided in this section).  Since the code of an 
thread Initialize entry point should never read the initial values
of thread local variables nor the initial values of ports, the semantics
of the thread's application logic should not be dependent on the 
initial thread state.  Thus, we have some freedom regarding what
we choose as the initial state (particular for variables).
The AADL standard implicitly assumes that all port queues 
start out empty.  So that is reflected in the definitions below.
For variables, we currently choose an arbitrary default value
for variables.  This implies that the current definitions will
yield a single unique initial state.  However, since Initialize
entry point application code should initialize all local variables,
it would also be appropriate in the semantics to leave the @{term tvar}
thread state component with arbitrary values for each of the local
variables declared for the thread (yielding a family of initial states
for a thread).

Other aspects of the initial state predicates reference the well-formed
state predicates to ensure that the domains used in variable value
and port value maps match the model declarations.
\<close>

text \<open>Currently, we instantiate the universal data type to @{type int} and
use @{term 0} for the default variable value.\<close>

definition default_value:: "int" where "default_value \<equiv> 0"

text \<open>The @{term tvar} component of an initial state is well-formed
wrt the model, and the value of each variable is the default value.\<close>

definition initial_ThreadState_tvar:: "Model \<Rightarrow> CompId \<Rightarrow> int ThreadState \<Rightarrow> bool" where
  "initial_ThreadState_tvar m c ts \<equiv> 
      (wf_ThreadState_tvar m c (tvar ts)) 
   \<and> (\<forall>v \<in> dom (tvar ts) . (tvar ts) v = Some(default_value))"

text \<open>For each port state component of the thread state, 
the port state should be well-formed wrt the model and should be associated
with an empty queue.\<close>

(* ToDo: John: when the well-formedness requirements for port states is extended to 
say that data ports always have a value in them, these definitions might need to 
reflect that -- or we can simply let the initialization phase establish a basic 
system invariant that all data port queues have exactly one value in them. *)

definition initial_ThreadState_infi:: "Model \<Rightarrow> CompId \<Rightarrow> int ThreadState \<Rightarrow> bool" where
  "initial_ThreadState_infi m c ts \<equiv> (wf_ThreadState_infi m c (infi ts)) \<and> dataUnavailable (infi ts)"

definition initial_ThreadState_appi:: "Model \<Rightarrow> CompId \<Rightarrow> int ThreadState \<Rightarrow> bool" where
  "initial_ThreadState_appi m c ts \<equiv> (wf_ThreadState_appi m c (appi ts)) \<and> dataUnavailable (appi ts)"

definition initial_ThreadState_appo:: "Model \<Rightarrow> CompId \<Rightarrow> int ThreadState \<Rightarrow> bool" where
  "initial_ThreadState_appo m c ts \<equiv> (wf_ThreadState_appo m c (appo ts)) \<and> dataUnavailable (appo ts)"

definition initial_ThreadState_info:: "Model \<Rightarrow> CompId \<Rightarrow> int ThreadState \<Rightarrow> bool" where
  "initial_ThreadState_info m c ts \<equiv> (wf_ThreadState_info m c (info ts)) \<and> dataUnavailable (info ts)"

text \<open>The initial dispatch status of the thread is @{term NotEnabled}.\<close>

definition initial_ThreadState_disp:: "Model \<Rightarrow> CompId \<Rightarrow> int ThreadState \<Rightarrow> bool" where
  "initial_ThreadState_disp m c ts \<equiv> (wf_ThreadState_disp m c (disp ts)) \<and> (disp ts = NotEnabled)"

text \<open>We take the conjunction of the conditions for components of the thread state to
get the overall predicate for a valid initial thread state.\<close>

definition initial_ThreadState:: "Model \<Rightarrow> CompId \<Rightarrow> (int ThreadState) \<Rightarrow> bool"  
  where "initial_ThreadState m t ts \<equiv>
   (initial_ThreadState_infi m t ts) \<and>
   (initial_ThreadState_appi m t ts) \<and>
   (initial_ThreadState_appo m t ts) \<and>
   (initial_ThreadState_info m t ts) \<and>
   (initial_ThreadState_tvar m t ts) \<and>
   (initial_ThreadState_disp m t ts)
  "

text \<open>The following lemma states that any initial thread state is well-formed.\<close>

lemma initial_implies_wf:
  "\<lbrakk>initial_ThreadState m t ts\<rbrakk> \<Longrightarrow> wf_ThreadState m t ts"
  unfolding  initial_ThreadState_def  
             initial_ThreadState_infi_def initial_ThreadState_appi_def 
             initial_ThreadState_appo_def initial_ThreadState_info_def 
             initial_ThreadState_tvar_def initial_ThreadState_disp_def
             wf_ThreadState_def
  by blast


end