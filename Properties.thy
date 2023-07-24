theory Properties
  imports Behavior
begin

text \<open>
\<close>

(* Initialisation property P *)
definition appInitProp where "appInitProp a P \<equiv> \<forall>s' p'. appInit a s' p' \<longrightarrow> P (s', p')"

definition sysInitProp where "sysInitProp am P \<equiv> 
  \<forall>c \<in> appModelCIDs am. \<forall>t t'. stepInit (appModelApp am $ c) t t' \<longrightarrow> P c (tvar t', appo t')"

definition sysInitVC where "sysInitVC am P \<equiv> 
  (\<And>c. c \<in> appModelCIDs am \<Longrightarrow> appInitProp (appModelApp am $ c) (P c))"

lemma initSysFromApps:
  assumes wf_am: "wf_AppModel am"
      and vc: "\<And>c. c \<in> appModelCIDs am \<Longrightarrow> appInitProp (appModelApp am $ c) (P c)"
    shows "sysInitProp am P"
proof (simp only: sysInitProp_def; clarify)
  fix c t t'
  assume a1: "c \<in> appModelCIDs am"
     and a2: "stepInit (appModelApp am $ c) t t'"
  thus "P c (tvar t', appo t')"
  proof -
    have "appInit (appModelApp am $ c) (tvar t') (appo t')" 
      using a2 stepInit_ruleinv[of "(appModelApp am $ c)" t t'] by blast
    thus ?thesis
      using a1 appInitProp_def vc by blast 
  qed
qed

definition sysAllInitProp where "sysAllInitProp am P s \<equiv> 
  \<forall>c \<in> appModelCIDs am. P c (tvar (systemThread s $ c), appo (systemThread s $ c))"

(*
lemma sysInit_upd_seq:
  assumes wf_am: "wf_AppModel am"
      and init: "isInitializing x"
      and step: "stepsSys am com sch x y"
      and exec_x: "systemExec x = Initialize (scheduleInit sch)"
      and exec_y: "systemExec y = Initialize []"
    shows "systemThread y = map_upd_seq (appModelInit am) (systemThread x) (scheduleInit sch)"
*)
(*
lemma initSysTermInduction:
  assumes wf_am: "wf_AppModel am"
      and props: "sysInitProp am P"
    shows "\<lbrakk> isInitializing x;
            set (xs @ ys) \<subseteq> appModelCIDs am;
            systemExec x = Initialize (xs @ ys);
            systemExec y = Initialize ys;
            stepsSys am com sch x y \<rbrakk> 
              \<Longrightarrow> \<forall>c \<in> set xs. P c (tvar (systemThread y $ c), appo (systemThread y $ c))"
(*  using props unfolding sysInitProp_def*)
proof (induction xs arbitrary: x)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  have h1: "systemExec x = Initialize (a # xs @ ys)" by (simp add: Cons.prems(3))
  obtain z where h2: "stepSys am com sch x z"
             and h3: "stepsSys am com sch z y"
    by (metis Cons.prems(4) Cons.prems(5) Cons_eq_appendI Exec.inject(1) append_self_conv2 
          converse_rtranclpE h1 list.distinct(1) stepsSys_def)
  have h4: "systemExec z = Initialize (xs @ ys)" 
    using h1 h2 h3 stepSysInit_redsch_ruleinv[of x a "xs @ ys" am com sch z] Cons.prems(1) by blast
  have h5: "isInitializing z" using stepSysInit_initInv_ruleinv[of x a "xs @ ys" am com sch z]
    using Cons.prems(1) h1 h2 by blast
  have h6: "\<forall>c\<in>set xs. P c (tvar (systemThread y $ c), appo (systemThread y $ c))"
    using Cons.IH Cons.prems(2) Cons.prems(4) h3 h4 h5 by simp
  have h7: "a \<in> appModelCIDs am" 
    using Cons.prems(2) by simp
  have h8: "stepInit (appModelApp am $ a) (systemThread x $ a) (systemThread z $ a)"
    using stepSysInit_ruleinv[of x a "xs @ ys" am com sch z]
    using Cons.prems(1) h1 h2 by fastforce
  have h9: "P a (tvar (systemThread z $ a), appo (systemThread z $ a))"
    using h7 h8 props unfolding sysInitProp_def by blast
  (*have g1: ""*)
  then show ?case
    by blast
qed

lemma initSysTerm:
  assumes wf_am: "wf_AppModel am"
      and wf_sch: "wf_SystemSchedule (appModel am) sch"
      and init: "isInitializing x"
      and exec_x: "systemExec x = Initialize (scheduleInit sch)"
      and exec_y: "systemExec y = Initialize []"
      and steps: "stepsSys am com sch x y"
      and props: "sysInitProp am P"
    shows "sysAllInitProp am P y"
proof -
  have "set (scheduleInit sch) = dom (modelCompDescrs (appModel am))"
    using wf_SystemSchedule_def wf_sch by blast
  thus ?thesis
  using initSysTermInduction[of am P x "(scheduleInit sch)" "[]" y com sch]
  unfolding appInitProp_def sysAllInitProp_def 
  apply simp
  using exec_x exec_y init isInitializing.simps props steps wf_am by blast
qed
*)
definition sysAppInvProp where "sysAppInvProp cids P I \<equiv> \<forall>c \<in> cids. \<forall>x p. P c (x, p) \<longrightarrow> I c x"

(* App computation invariant I on local variables and output port properties P. *)
(* All other port properties must be guaranteed on system level. *)
(* Also system-wide invariants must be dealt with globally, assume substrate properties. *)
definition appInvProp where "appInvProp a I P \<equiv> 
  \<forall>x x' d p p'. I x \<and> appCompute a x p d x' p' \<longrightarrow> I x' \<and> P (x', p')"

definition sysInvProp where "sysInvProp am sch I P \<equiv> 
  \<forall>c \<in> appModelCIDs am. 
    \<forall>t t'. I c (tvar t) \<and> 
      stepThread (computeDispatchStatus (appModel am) c) (appModelPortKind am) (appModelApp am $ c) sch t t' 
      \<longrightarrow> I c (tvar t) \<and> P c (tvar t, appo t)"

(*
lemma sysThreadInv:
  assumes wf_am: "wf_AppModel am"
      and valid: "c \<in> appModelCIDs am"
      and isat: "I c (tvar x)"
      and inv: "appInvProp (appModelApp am $ c) (I c) (P c)"
    shows "sysInvProp am sch I P"
  using wf_am unfolding wf_AppModel_def wf_CIDAppCIDAPP_def wf_CIDApp_def
  by blast


lemma sysThreadInv1:
  assumes wf_am: "wf_AppModel am"
      and vc: "\<And>c. \<lbrakk>c \<in> appModelCIDs am; I c (tvar x)\<rbrakk> \<Longrightarrow> appInvProp (appModelApp am $ c) (I c) (P c)"
      and step: "stepComp (computeDispatchStatus (appModel am) c) (appModelApp am $ c) sch x y"
    shows "sysInvProp am sch I P"
  using wf_am unfolding wf_AppModel_def wf_CIDAppCIDAPP_def wf_CIDApp_def
  by blast
*)
(*
lemma initIndProp:
  assumes inv: "initInvProp a P"
      and p0: "P s"
      and app: "(appInit a)\<^sup>*\<^sup>* s s'"
    shows "P s'"
  using inv p0 app unfolding initInvProp_def
  using rtranclp_induct[of "appInit a" s s' P]
  by blast

lemma initIndTrmProp:
  assumes inv: "initInvProp a P"
      and trm: "initTrmProp a P Q"
      and p0: "P s"
      and app: "(appInit a)\<^sup>*\<^sup>* s s'"
      and t0: "\<forall>s''. \<not>appInit a s' s''"
    shows "Q s'"
proof -
  have h1: "P s'"
    using app initIndProp inv p0 by blast
  show ?thesis
    using h1 trm t0 unfolding initTrmProp_def
    by blast
qed

lemma thread_wf_reach:
  assumes "wf_Model m"
      and "wf_App m a"
      and "reachP m a d t"
    shows "wf_ThreadState m c t"
  sorry (* by induction using the preceding two lemmata *)

lemma reachprop:
  assumes "wf_Model m"
      and "wf_App m a"
      and "cinitprop a (isModelCID m) P"
      and "cinvprop a (isModelCID m) P"
      and "reachP m a c t"
    shows "cthreadprop m t (isModelCID m) P"
  sorry
*)
end