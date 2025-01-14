theory RuntimeExamples
  imports VarState PortState ThreadState ModelExamples
begin

(*

definition ADescr where
  "ADescr =
    mkCompDescr
     ''compA''
     AId
     (mkCSet {AOut0Id, AOut1Id})
     Periodic
     (mkCSet {})
     (mkCSet {})"
*)

(*
In this example, all of our ports have size 1.
So make a single empty port queue to use to create the initial values for 
port states below.
*) 

definition emptyq:: "int Queue" where [simp add]:
 "emptyq = mk_empty_queue 1 DropOldest"

(* Comp A has no variables *)
definition compA_tvar_initial:: "int VarState" where [simp add]:
  "compA_tvar_initial = Map.empty"

(* Comp A has no input ports, so mapping from input port ids to queues is empty *)
definition compA_infi_initial:: "int PortState" where [simp add]:
  "compA_infi_initial = Map.empty"

(* Comp A has no input ports, so mapping from input port ids to queues is empty *)
definition compA_appi_initial:: "int PortState" where [simp add]:
  "compA_appi_initial = Map.empty"

(* Associate Comp A's two output ports with empty queues *)
definition compA_appo_initial:: "int PortState" where [simp add]:
  "compA_appo_initial = map_of [(AOut0Id, emptyq), (AOut1Id, emptyq)]"

(* Associate Comp A's two output ports with empty queues *)
definition compA_info_initial:: "int PortState" where [simp add]:
  "compA_info_initial = map_of [(AOut0Id, emptyq), (AOut1Id, emptyq)]"

definition compA_disp_initial:: "DispatchStatus" where [simp add]:
  "compA_disp_initial = NotEnabled"

definition compA_initial:: "int ThreadState" where [simp add]:
 "compA_initial = 
   (tstate compA_infi_initial compA_appi_initial compA_appo_initial compA_info_initial
           compA_tvar_initial 
           compA_disp_initial)"

(*
definition BDescr where
  "BDescr =
    mkCompDescr
     ''compB''
     BId
     (mkCSet {BIn2Id, BIn3Id})
     Sporadic
     (mkCSet {BIn2Id, BIn3Id})
     (mkCSet {localVarB})"
*)

(* Comp B has one variable localVarB *)
definition compB_tvar_initial:: "int VarState" where [simp add]:
  "compB_tvar_initial = map_of [(localVarB, default_value)]"

(* Associate Comp B's two intput ports with empty queues *)

definition compB_infi_initial:: "int PortState" where [simp add]:
  "compB_infi_initial = map_of [(BIn2Id, emptyq), (BIn3Id, emptyq)]"

(* Comp A has no input ports, so mapping from input port ids to queues is empty *)
definition compB_appi_initial:: "int PortState" where [simp add]:
  "compB_appi_initial = map_of [(BIn2Id, emptyq), (BIn3Id, emptyq)]"

(* Comp B has no output ports, so mapping from input port ids to queues is empty *)
definition compB_appo_initial:: "int PortState" where [simp add]:
  "compB_appo_initial = Map.empty"

(* Comp B has no output ports, so mapping from input port ids to queues is empty *)
definition compB_info_initial:: "int PortState" where [simp add]:
  "compB_info_initial = Map.empty"

definition compB_disp_initial:: "DispatchStatus" where [simp add]:
  "compB_disp_initial = NotEnabled"

definition compB_initial:: "int ThreadState" where [simp add]:
 "compB_initial = 
   (tstate compB_infi_initial compB_appi_initial compB_appo_initial compB_info_initial 
           compB_tvar_initial
           compB_disp_initial)"

lemma compA_initial_prop: "initial_ThreadState sysModel AId compA_initial" 
  by  (auto simp add: 
                    wf_VarState_def wf_VarState_dom_def 
                    wf_PortState_def wf_PortState_dom_def wf_PortState_queue_def wf_PortState_queues_def
                    wf_Queue_def
                    initial_ThreadState_def 
                    initial_ThreadState_tvar_def wf_ThreadState_tvar_def 
                    initial_ThreadState_infi_def wf_ThreadState_infi_def
                    initial_ThreadState_appi_def wf_ThreadState_appi_def
                    initial_ThreadState_appo_def wf_ThreadState_appo_def
                    initial_ThreadState_info_def wf_ThreadState_info_def
                    initial_ThreadState_disp_def wf_ThreadState_disp_def
                    )


end

