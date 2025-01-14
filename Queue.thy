section \<open>Queues \label{sec:queues}\<close>

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
  imports Main Model
begin

subsection \<open>Structures\<close>


text \<open>Define a record type to represent queue values with the following fields:
\begin{itemize}
\item error -- when the OHP is set to Error, this field is used to indicate
      that the queue is in an error state.
\item buffer -- the representation of queue storage
\item qsize -- [static] the maximum number of elements that the buffer 
                  (queue) can hold.  The value for this field should be equal to the 
                  Queue\_Size port property in the AADL model (default is 1), which
                  is held in the @{term PortDescr} from Model.thy.   If the OHP is 
                  unbounded, this value is ignored.
\item qohp -- [static] the OHP for the queue.  The value for this field should be equal to the 
                  OHP port property in the AADL model (default is DropOldest), which
                  is held in the @{term PortDescr} from Model.thy 
\end{itemize}

Fields marked \emph{static} are set at the creation time for the record and do not ``change''
(are preserved as copies are made of the record) during system execution.  An alternative
design for the formalism would be to always have the Model/PortDescr available and reference
the static fields directly from the model information.
\<close>

record 'a Queue =
  error :: bool
  buffer :: "'a list"
  qsize :: nat
  qohp :: OverflowHandlingProtocol

text \<open>Create a queue initialised with given buffer, capacity and strategy\<close>
fun mk_queue :: "'a list \<Rightarrow> nat \<Rightarrow> OverflowHandlingProtocol \<Rightarrow> 'a Queue"
  where "mk_queue b qs op = \<lparr> error= False, buffer= b, qsize= qs, qohp= op \<rparr>"

text \<open>Create a queue initialised with an empty buffer, capacity and strategy\<close>
fun mk_empty_queue :: "nat \<Rightarrow> OverflowHandlingProtocol \<Rightarrow> 'a Queue"
  where "mk_empty_queue qs op = \<lparr> error= False, buffer= [], qsize= qs, qohp= op \<rparr>"

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
  where "wf_Queue q \<equiv> (0 < qsize q) \<and> 
                      (qohp q \<noteq> Unbounded \<longrightarrow> length (buffer q) \<le> qsize q)"

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

text \<open>Return the tail of a queue.\<close>

fun tail :: "'a Queue \<Rightarrow> 'a Queue"
  where "tail q = q \<lparr> buffer:= tl (buffer q) \<rparr>"

text \<open>Enqueue a single value.\<close>

fun push :: "'a Queue \<Rightarrow> 'a \<Rightarrow> 'a Queue" where 
  "push q a = 
    (case qohp q of
      DropOldest \<Rightarrow> 
        (if length (buffer q) < qsize q 
          then q \<lparr> buffer:= buffer q @ [a] \<rparr> 
          else q \<lparr> buffer:= tl (buffer q) @ [a] \<rparr>) 
    | DropNewest \<Rightarrow> 
        (if length (buffer q) < qsize q 
          then q \<lparr> buffer:= buffer q @ [a] \<rparr> 
          else q)
    | Error \<Rightarrow> 
        (if length (buffer q) < qsize q 
          then q \<lparr> buffer:= buffer q @ [a] \<rparr> 
          else q \<lparr> error:= True, buffer:= [] \<rparr>)
    | Unbounded \<Rightarrow> q \<lparr> buffer:= buffer q @ [a] \<rparr>)"

text \<open>Enqueue a list of values.\<close>

fun pushQueue :: "'a Queue \<Rightarrow> 'a list \<Rightarrow> 'a Queue" where 
  "pushQueue q q' = 
    (case qohp q of
      DropOldest \<Rightarrow> 
        q \<lparr> buffer:= drop (length (buffer q @ q') - qsize q) (buffer q @ q') \<rparr>
    | DropNewest \<Rightarrow> 
        q \<lparr> buffer:= take (qsize q) (buffer q @ q') \<rparr>
    | Error \<Rightarrow> 
        (if length (buffer q @ q') \<le> qsize q 
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

lemma tail_frame_qsize: "qsize (tail q) = qsize q"
  by simp

lemma tail_frame_qohp: "qohp (tail q) = qohp q"
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

text \<open>@{term push} doesn't change the @{term qsize} field.\<close>

lemma push_frame_qsize: "qsize (push q a) = qsize q"
  by (cases "(qohp q)"; simp)


text \<open>@{term push} doesn't change the @{term qohp} field.\<close>

lemma push_frame_qohp: "qohp (push q a) = qohp q"
  by (cases "(qohp q)"; simp)

text \<open>Express the transformation of @{term push} on the buffer when the operation doesn't 
cause the capacity to be exceeded.\<close>

lemma push_within_qsize:
  assumes "length (buffer q) < qsize q"
  shows "buffer (push q a) = buffer q @ [a]"
  using assms by (cases "(qohp q)"; simp)

text \<open>Show that @{term push} preserves the state of the 
error flag when the operation doesn't cause the capacity to be exceeded.\<close>

lemma push_no_error:
  assumes "length (buffer q) < qsize q"
  shows "error (push q a) = error q"
  using assms by (cases "(qohp q)"; simp)


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

text \<open>Prove that @{term push} preserves well-formedness.\<close>

lemma push_wf:
  assumes "wf_Queue q"
  shows "wf_Queue (push q v)"
using assms by (cases "(qohp q)"; auto simp add: wf_Queue_def)

(*------------------------
   d r o p    properties
 ------------------------*)

text \<open>{\bf drop} Properties\<close>

text \<open>@{term drop} frame properties.  The @{term drop} operation doesn't change the @{term error},
@{term capacity}, or @{term strategy} fields.\<close>

lemma drop_frame_error: "error (drop n q) = error q"
  by simp

lemma drop_frame_qsize: "qsize (drop n q) = qsize q"
  by simp

lemma drop_frame_qohp: "qohp (drop n q) = qohp q"
  by simp

text \<open>@{term drop} preserves well-formedness.\<close>

lemma drop_wf:
  assumes "wf_Queue q"
  shows "wf_Queue (drop n q)"
  using assms by (auto simp add: wf_Queue_def)

(*------------------------
  c l e a r    properties
 ------------------------*)

text \<open>{\bf clear} Properties\<close>

text \<open>@{term clear} frame properties.  The @{term clear} operation doesn't change the @{term error},
@{term qsize}, or @{term qohp} fields.\<close>

lemma clear_frame_error: "error (clear q) = error q"
  by simp

lemma clear_frame_qsize: "qsize (clear q) = qsize q"
  by simp

lemma clear_frame_qohp: "qohp (clear q) = qohp q"
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
@{term qsize}, or @{term qohp} fields.\<close>

lemma setBuffer_frame_error: "error (setBuffer q b) = error q"
  by simp

lemma setBuffer_frame_qsize: "qsize (setBuffer q b) = qsize q"
  by simp

lemma setBuffer_frame_qohp: "qohp (setBuffer q b) = qohp q"
  by simp

text \<open>@{term setBuffer} preserves well-formedness.\<close>

lemma setBuffer_wf:
  assumes "wf_Queue q"
     and  "length b \<le> qsize q"
   shows "wf_Queue (setBuffer q b)"
  using assms by (simp add: wf_Queue_def)


end