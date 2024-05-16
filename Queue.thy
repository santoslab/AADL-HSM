section \<open>Queues\<close>

text \<open>In the AADL runtime, buffered storage for event and event data ports is represented
using queues. To obtain a uniform storage representation for ports (which simplifies the semantics), 
our semantics also represents data port storage using queues, but well-formed properties will 
constrain data port queues to always have one element.

AADL port queues are of bounded size -- the bound is specified using the Queue\_Size port 
property in the AADL model, and this value is stored in the port descriptor data
structure (the field @{term size}) defined in Model.thy.

This theory defines a @{term Queue} data type representation for 
AADL queues using Isabelle lists.  The data type implements 
AADL's different \emph{overflow handling protocols} that
indicate what the semantics should be when clients attempt
to insert a value into a full queue.
\<close>

theory Queue
  imports Main
begin

subsection \<open>Structures\<close>

text \<open>Define a datatype to represent the three options for 
AADL's port Overflow\_Handling\_Protocol (OHP) property.  Add an additional
Unbounded option for simplicity to be used when prototyping various 
aspects of the semantics.\<close>

datatype Strategy = DropEarliest | DropLatest | Error | Unbounded

text \<open>\edcomment{ToDo: reconcile the terms "Strategy", "Overflow Handling Protocol"}\<close>


text \<open>Define a record type to represent queue values with the following fields:
\begin{itemize}
\item error -- when the OHP is set to Error, this field is used to indicate
      that the queue is in an error state.
\item buffer -- the representation of queue storage
\item capacity -- [static] the maximum number of elements that the buffer 
                  (queue) can hold.  The value for this field should be equal to the 
                  Queue\_Size port property in the AADL model (default is 1), which
                  is held in the @{term PortDescr} from Model.thy.   If the OHP is 
                  unbounded, this value is ignored.
\item strategy -- [static] the OHP for the queue.  The value for this field should be equal to the 
                  OHP port property in the AADL model (default is DropEarliest), which
                  is held in the @{term PortDescr} from Model.thy 
\end{itemize}

Fields marked \emph{static} are set at the creation time for the record and do not "change"
(are preserved as copies are made of the record) during system execution.  An alternative
design for the formalism would be to always have the Model/PortDescr available and reference
the static fields directly from the model information.
\<close>

record 'a Queue =
  error :: bool
  buffer :: "'a list"
  capacity :: nat
  strategy :: Strategy

text \<open>\edcomment{ToDo: double-check the terminology in the AADL standard and
reconcile the terms "capacity", "size", "maxsize", etc. used
in AADL standard, Model.thy, Queue.thy}\<close>

text \<open>Create a queue initialised with given buffer, capacity and strategy\<close>
fun mk_queue :: "'a list \<Rightarrow> nat \<Rightarrow> Strategy \<Rightarrow> 'a Queue"
  where "mk_queue b c s = \<lparr> error= False, buffer= b, capacity= c, strategy= s \<rparr>"

text \<open>Create a queue initialised with an empty buffer, capacity and strategy\<close>
fun mk_empty_queue :: "nat \<Rightarrow> Strategy \<Rightarrow> 'a Queue"
  where "mk_empty_queue c s = \<lparr> error= False, buffer= [], capacity= c, strategy= s \<rparr>"

text \<open>The following definitions define an order on list values.\<close>

instantiation list :: (equal) order
begin

fun less_eq_list where "less_eq_list x y = (\<exists>z. x @ z = y)"
fun less_list where "less_list x y = (\<exists>z. x @ z = y \<and> z \<noteq> [])"

instance
proof
  fix x y z :: "'a list"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by force
  show "x \<le> x" by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by fastforce
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by fastforce
qed

end

text \<open>
\edcomment{ToDo Stefan: indicate ordering on lists are used in theory/proofs.
Also explain what the Isabelle constructs above are, e.g., is this an instantiation
of a type class?}
\<close>


subsection \<open>Well-formedness Definitions\<close>

text \<open>A queue is well-formed if the length of the buffer conforms to the capacity
value.\<close>

definition wf_Queue 
  where "wf_Queue q \<equiv> (0 < capacity q) \<and> 
                      (strategy q \<noteq> Unbounded \<longrightarrow> length (buffer q) \<le> capacity q)"

subsection \<open>Operations\<close>

text \<open>This section defines operations on queues.  Generally, the operations
work on the buffer field of the record representing the queue.\<close>

text \<open>Check if the queue is empty.\<close>

fun isEmpty :: "'a Queue \<Rightarrow> bool" 
  where "isEmpty q = (buffer q = [])"

text \<open>Check if the queue has exactly one element.\<close>

fun isOneElement :: "'a Queue \<Rightarrow> bool" 
  where "isOneElement q = (length (buffer q) = 1)"

text \<open>Return the head (first value) from the queue.\<close>
fun head :: "'a Queue \<Rightarrow> 'a" 
  where "head q = hd (buffer q)"

text \<open>Take the tail of a queue.\<close>

fun tail :: "'a Queue \<Rightarrow> 'a Queue"
  where "tail q = q \<lparr> buffer:= tl (buffer q) \<rparr>"

text \<open>Enqueue a single value.\<close>

fun push :: "'a Queue \<Rightarrow> 'a \<Rightarrow> 'a Queue" where 
  "push q a = 
    (case strategy q of
      DropEarliest \<Rightarrow> 
        (if length (buffer q) < capacity q 
          then q \<lparr> buffer:= buffer q @ [a] \<rparr> 
          else q \<lparr> buffer:= tl (buffer q) @ [a] \<rparr>) 
    | DropLatest \<Rightarrow> 
        (if length (buffer q) < capacity q 
          then q \<lparr> buffer:= buffer q @ [a] \<rparr> 
          else q)
    | Error \<Rightarrow> 
        (if length (buffer q) < capacity q 
          then q \<lparr> buffer:= buffer q @ [a] \<rparr> 
          else q \<lparr> error:= True, buffer:= [] \<rparr>)
    | Unbounded \<Rightarrow> q \<lparr> buffer:= buffer q @ [a] \<rparr>)"

text \<open>Enqueue a list of values.\<close>

fun pushQueue :: "'a Queue \<Rightarrow> 'a list \<Rightarrow> 'a Queue" where 
  "pushQueue q q' = 
    (case strategy q of
      DropEarliest \<Rightarrow> 
        q \<lparr> buffer:= drop (length (buffer q @ q') - capacity q) (buffer q @ q') \<rparr>
    | DropLatest \<Rightarrow> 
        q \<lparr> buffer:= take (capacity q) (buffer q @ q') \<rparr>
    | Error \<Rightarrow> 
        (if length (buffer q @ q') \<le> capacity q 
          then q \<lparr> buffer:= buffer q @ q' \<rparr> 
          else q \<lparr> error:= True, buffer:= [] \<rparr>)
    | Unbounded \<Rightarrow> q \<lparr> buffer:= buffer q @ q' \<rparr>)"

text \<open>Drop the first (head-side) n values from the queue.\<close>

fun drop :: " nat \<Rightarrow> 'a Queue \<Rightarrow> 'a Queue"
  where "drop n q = q \<lparr> buffer:= List.drop n (buffer q) \<rparr>"

text \<open>Remove all values from the queue.\<close>

fun clear :: "'a Queue \<Rightarrow> 'a Queue"
  where "clear q = q\<lparr> buffer:= [] \<rparr>"

text \<open>Set the queue buffer to a specific list of values (head corresponding to the
first item in the list.\<close>

fun setBuffer :: "'a Queue \<Rightarrow> 'a list \<Rightarrow> 'a Queue"
  where "setBuffer q b = q \<lparr> buffer:= b \<rparr>"

subsection \<open>Operation Properties\<close>

text \<open>{\bf head} Properties\<close>

lemma single_queue_head: "buffer q = [a] \<Longrightarrow> head q = a"
  by simp

(*------------------------
   t a i l   properties
 ------------------------*)

text \<open>{\bf tail} Properties\<close>

text \<open>@{term tail} frame properties.  The @{term tail} doesn't change the @{term error},
@{term capacity}, or @{term strategy} fields.\<close>

lemma tail_frame_error: "error (tail q) = error q"
  by simp

lemma tail_frame_capacity: "capacity (tail q) = capacity q"
  by simp

lemma tail_frame_strategy: "strategy (tail q) = strategy q"
  by simp

text \<open>@{term tail} preserves well-formedness.\<close>

lemma tail_wf:
  assumes "wf_Queue q"
  shows "wf_Queue (tail q)"
  using assms by (auto simp add: wf_Queue_def)
 
lemma single_queue_tail: "buffer q = [a] \<Longrightarrow> buffer (tail q) = []"
  by simp

(*------------------------
   p u s h    properties
 ------------------------*)

text \<open>{\bf push} Properties\<close>

text \<open>@{term push} doesn't change the @{term capacity} field.\<close>

lemma push_frame_capacity: "capacity (push q a) = capacity q"
  by (cases "(strategy q)"; simp)

(*
  apply (simp; rule conjI)
   apply (metis (no_types, lifting) Strategy.exhaust Strategy.simps(13) Strategy.simps(14) 
         Strategy.simps(15) Strategy.simps(16) select_convs(3) surjective update_convs(2))
  by (metis (no_types, lifting) Strategy.exhaust Strategy.simps(13) Strategy.simps(14) 
     Strategy.simps(15) Strategy.simps(16) select_convs(3) surjective update_convs(1) update_convs(2))
*)

text \<open>@{term push} doesn't change the @{term strategy} field.\<close>

lemma push_frame_strategy: "strategy (push q a) = strategy q"
  by (cases "(strategy q)"; simp)

text \<open>Express the transformation of @{term push} on the buffer when the operation won't 
cause the capacity to be exceeded.\<close>

lemma push_within_capacity:
  assumes "length (buffer q) < capacity q"
  shows "buffer (push q a) = buffer q @ [a]"
  using assms by (cases "(strategy q)"; simp)

(*
  apply (simp; rule conjI)
   apply (metis (no_types, lifting) Strategy.exhaust Strategy.simps(13) Strategy.simps(14) 
         Strategy.simps(15) Strategy.simps(16) select_convs(2) surjective update_convs(2))
  using assms by blast
*)

text \<open>Express the transformation of @{term push} on the error flag when the operation won't 
cause the capacity to be exceeded.\<close>

lemma push_no_error:
  assumes "length (buffer q) < capacity q"
  shows "error (push q a) = error q"
  using assms by (cases "(strategy q)"; simp)

(*
  apply (simp; rule conjI; clarify)
   apply (smt (verit, best) Strategy.exhaust Strategy.simps(13) Strategy.simps(14) 
         Strategy.simps(15) Strategy.simps(16) ext_inject surjective update_convs(2))
  using assms by blast
*)

(* 
   Historical note: (from John):  
   I was originally trying to prove the following
   property (push preserves wf) 

    lemma push_wf:
    assumes "wf_Queue q"
    shows "wf_Queue (push q v)"

   without the capacity q > 0 condition
   in wf_Queue. This fails for the DropEarliest case, because tail [] = []
   so pushing a value on an empty queue will exceed the capacity of 0. 

   Interestingly, this issue was revealed to me by QuickCheck as shown below.

proof (prove)
goal (1 subgoal):
 1. wf_Queue (push q v) 
Auto Quickcheck found a counterexample:
  q = \<lparr>error = True, buffer = [], capacity = 0, strategy = DropEarliest\<rparr>
  v = a\<^sub>1
 *)

lemma push_wf:
  assumes "wf_Queue q"
  shows "wf_Queue (push q v)"
using assms by (cases "(strategy q)"; auto simp add: wf_Queue_def)

(*------------------------
   d r o p    properties
 ------------------------*)

text \<open>{\bf drop} Properties\<close>

text \<open>@{term drop} frame properties.  The @{term drop} operation doesn't change the @{term error},
@{term capacity}, or @{term strategy} fields.\<close>

lemma drop_frame_error: "error (drop n q) = error q"
  by simp

lemma drop_frame_capacity: "capacity (drop n q) = capacity q"
  by simp

lemma drop_frame_strategy: "strategy (drop n q) = strategy q"
  by simp

text \<open>@{term tail} preserves well-formedness.\<close>

lemma drop_wf:
  assumes "wf_Queue q"
  shows "wf_Queue (drop n q)"
  using assms by (auto simp add: wf_Queue_def)

(*------------------------
  c l e a r    properties
 ------------------------*)

text \<open>{\bf clear} Properties\<close>

text \<open>@{term clear} frame properties.  The @{term clear} operation doesn't change the @{term error},
@{term capacity}, or @{term strategy} fields.\<close>

lemma clear_frame_error: "error (clear q) = error q"
  by simp

lemma clear_frame_capacity: "capacity (clear q) = capacity q"
  by simp

lemma clear_frame_strategy: "strategy (clear q) = strategy q"
  by simp

text \<open>@{term tail} preserves well-formedness.\<close>

lemma clear_wf:
  assumes "wf_Queue q"
  shows "wf_Queue (clear q)"
  using assms by (simp add: wf_Queue_def)
  

(*----------------------------------
   s e t B u f f e r    properties
 -----------------------------------*)

text \<open>{\bf setBuffer} Properties\<close>

text \<open>@{term setBuffer} frame properties.  The @{term setBuffer} operation doesn't change the @{term error},
@{term capacity}, or @{term strategy} fields.\<close>

lemma setBuffer_frame_error: "error (setBuffer q b) = error q"
  by simp

lemma setBuffer_frame_capacity: "capacity (setBuffer q b) = capacity q"
  by simp

lemma setBuffer_frame_strategy: "strategy (setBuffer q b) = strategy q"
  by simp

text \<open>@{term setBuffer} preserves well-formedness.\<close>

lemma setBuffer_wf:
  assumes "wf_Queue q"
     and  "length b \<le> capacity q"
   shows "wf_Queue (setBuffer q b)"
  using assms by (simp add: wf_Queue_def)


end