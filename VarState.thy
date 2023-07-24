section "Variable States"

text \<open>Real-time tasks often have local state (e.g., variables declared within the 
source code of a thread) that are used to store values of input devices and intermediate
results of task calculations.   Because the AADL standard focus on architectural 
specifications it has no specification notation for thread-local variables.  However, the 
BLESS AADL behavioral specification language has the ability to specify thread-local variables
for threads, and the GUMBO contract language continues and extends the concept.

In GUMBO, thread entry point contracts specify real-time task behaviors in terms
of pre/post-conditions that semantically are \emph{relations} between input port values and values of thread-local variables 
at the time of thread dispatch to output port values and (possibly updated) values of 
thread-local variables at the time at which the thread completes its entry point computation.

In this Isabelle formalization, specifications of thread application logic 
are not ``hard-wired'' to GUMBO style contracts, but they are designed 
to be sufficient for representing GUMBO contracts.  Accordingly, 
thread application logic behavior is defined in terms of relations as described above
(see XXXX App.thy XXXX).

To support the above concepts, the representation of thread's state includes
values of thread-local variables, e.g., as declared in GUMBO state declarations.
When HAMR generates the Isabelle representation of threads, it will automatically
generate from GUMBO state declarations a listing of thread-local variables 
in each threads @{term CompDescr}.   Intuitively, each thread state includes a 
@{term VarState} field representing a ``store'' that maps
each @{term CompDescr} specified local variables to values.  
\<close>

theory VarState
  imports Main Model SetsAndMaps
begin

text \<open>A @{term VarState} is used to represent the state of a thread's local variables
  whose value persist between thread dispatches.\<close>

text \<open>A @{term VarState} is a map, associating a var id with 
  a value of type 'a, representing the value of the variable.
The notion of application variable type and value is not fully
developed at this point, so we parameterize the @{term VarState}
of a type \emph{a} representing a universal value type.
\<close>

type_synonym 'a VarState = "(Var, 'a) map"

text \<open>Currently, we do not have any conditions for well-formedness
for a VarState.  Later on, we will need to add conditions, e.g., to indicate
stored values match a variable's type.  So leave a placeholder for well-formedness.\<close>

definition wf_VarState_dom :: "'a VarState \<Rightarrow> Var set \<Rightarrow> bool" where 
  "wf_VarState_dom vs vars \<equiv> (dom vs) = vars"

definition wf_VarState :: "'a VarState \<Rightarrow> Var set \<Rightarrow> bool" where 
  "wf_VarState vs vars \<equiv> wf_VarState_dom vs vars"

end