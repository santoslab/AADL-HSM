theory ModelExamples
  imports Model
begin

(********************************************
  Examples of Basic Syntactic Domains

   PortId, PortId CSet
   CompId, CompId CSet
   Var,    Var CSet

 ********************************************)

(* ------------------ Port Ids -------------------- *)

(* datatype PortId = PortId nat *)

value  "PortId 0 :: PortId"  (* syntax for PortId value *)

(* Introduce Port Id names to be used in system model *)

definition AOut0Id :: PortId  (* define a name for PortId *)
  where "AOut0Id = PortId 0"

definition AOut1Id :: PortId  
  where "AOut1Id = PortId 1"

definition BIn2Id :: PortId  
  where "BIn2Id = PortId 2"

definition BIn3Id :: PortId  
  where "BIn3Id = PortId 3"

(* type_synonym PortIds = "PortId CSet" *)

value "{ PortId 0, PortId 1 }  :: PortIds"  (* illustrate set of PortId *)

value "{ AOut0Id, AOut1Id, BIn2Id, BIn3Id }  :: PortIds"  (* use names instead *)

(* Introduce name for Port Ids to be used in system model *)

definition sysPortIds :: PortIds
  where "sysPortIds = { AOut0Id, AOut1Id, BIn2Id, BIn3Id }"

(* ------------------ Comp Ids -------------------- *)

(* datatype CompId = CompId nat *)

value  "CompId 0 :: CompId"

(* Introduce Comp Id names to be used in system model *)

definition AId :: CompId  
  where "AId = CompId 0"

definition BId :: CompId  
  where "BId = CompId 1"

(* type_synonym CompIds = "CompId CSet" *)

value "{ CompId 0, CompId 1 }  :: CompIds"

(* Introduce name for Comp Ids to be used in system model *)

definition sysCompIds :: CompIds
  where "sysCompIds = { AId, BId }"


(* ------------------ Var Ids -------------------- *)

(* datatype Var = Var string *)

value  "Var ''myVar'' :: Var"

(* type_synonym Vars = Var CSet *)

value "{ Var ''a'', Var ''b'' }  :: Vars"

(* Introduce name for Var Ids to be used in system model *)

definition localVarB :: Var  
  where "localVarB = Var ''localVarB''"

(********************************************
  Examples of Representing Port Descriptors

record PortDescr = 
  name :: "string"
  id :: "PortId" (* unique id for port *)
  compId :: "CompId" (* component id for owner of this port *)
  direction :: PortDirection
  kind :: PortKind
  size :: "nat"  

 ********************************************)

(* portAOut0: out data port *)

definition AOut0Descr where
  "AOut0Descr =
    mkPortDescr
     ''portAOut0''
     AOut0Id
     AId
     Out
     Data
     1
     0"

(* portAOut1: out event data port *)

definition AOut1Descr where
  "AOut1Descr =
    mkPortDescr
     ''portAOut1''
     AOut1Id
     AId
     Out
     EventData
     1
     0"

definition BIn2Descr :: PortDescr where (* an explicit PortDescr type can be added *)
  "BIn2Descr =
    mkPortDescr
     ''portBIn2''
     BIn2Id
     BId
     In
     Data
     1
     0"

definition BIn3Descr where
  "BIn3Descr =
    mkPortDescr
     ''portBIn3''
     BIn3Id
     BId
     In
     EventData
     1
     0"

(********************************************
  Examples of Representing Component Descriptors

(* Comp descriptor *)
record CompDescr = 
  name :: "string"
  id :: "CompId" (* unique id for component *)
  portIds :: "PortIds" (* ports belonging to this component *)
  dispatchProtocol :: "DispatchProtocol"  
  dispatchTriggers :: "PortIds" (* ids of ports that can trigger a dispatch *)
  compVars :: "Vars" 

 ********************************************)



definition ADescr where
  "ADescr =
    mkCompDescr
     ''compA''
     AId
     {AOut0Id, AOut1Id}
     Periodic
     {}
     {}"



definition BDescr where
  "BDescr =
    mkCompDescr
     ''compB''
     BId
     {BIn2Id, BIn3Id}
     Sporadic
     {BIn2Id, BIn3Id}
     {localVarB}"


(********************************************
  Examples of Representing Connections
 ********************************************)

definition AtoBdata :: "Conns" where
  "AtoBdata = map_of [(PortId 0,  {PortId 2})]"

definition AtoBeventdata :: "Conns" where
  "AtoBeventdata = map_of [(PortId 1,  {PortId 3})]"

(* To Do: combining the connection info for individual ports *)
(* To Do: establishing that the Conns connection crel is a function *)

definition AtoB :: "Conns" where
  "AtoB = map_of [(PortId 0,  {PortId 2}),
                  (PortId 1,  {PortId 3})]"

(* illustrate connection definitions using port name definitions *)

definition sysConns :: "Conns" where
  "sysConns = map_of [(AOut0Id,  {BIn2Id}),
                      (AOut1Id,  {BIn3Id})]"


(********************************************
  Examples of model descriptor tables
 ********************************************)

definition sysPortDescrs :: "(PortId, PortDescr) map" where
 "sysPortDescrs = map_of [(AOut0Id, AOut0Descr),
                          (AOut1Id, AOut1Descr),
                          (BIn2Id, BIn2Descr),
                          (BIn3Id, BIn3Descr)]"

definition sysCompDescrs :: "(CompId, CompDescr) map" where 
 "sysCompDescrs = map_of [(AId, ADescr),
                          (BId, BDescr)]"


(********************************************
  Examples of System Model
 ********************************************)

(*
record Model =
  modelCompDescrs :: "(CompId, CompDescr) map" 
  modelPortDescrs :: "(PortId, PortDescr) map" 
  modelConns :: "Conns"
*)

definition sysModel :: "Model" where
  "sysModel = (mkModel sysCompDescrs sysPortDescrs sysConns)"


(************************************************************************************
 
   W e l l - f o r m e d n e s s     P r o o f s

 ************************************************************************************)

(* instruct the simplifier to unfold all definitions used to
   give names (for convenience and readability) to model elements *)

declare AOut0Id_def [simp add]
declare AOut1Id_def [simp add]
declare BIn2Id_def [simp add]
declare BIn3Id_def [simp add]

declare AOut0Descr_def [simp add]
declare AOut1Descr_def [simp add]
declare BIn2Descr_def [simp add]
declare BIn3Descr_def [simp add]

declare AId_def [simp add]
declare BId_def [simp add]

declare ADescr_def [simp add]
declare BDescr_def [simp add]

declare sysCompDescrs_def [simp add]
declare sysPortDescrs_def [simp add]
declare sysConns_def [simp add]
declare sysModel_def [simp add]

(* Each PortDescr is well-formed -  no longer used 

lemma AOut0Descr_wf [simp]: "wf_PortDescr AOut0Descr"
  apply (simp add: wf_PortDescr_def) (* well-formedness property definition *) 
  done

lemma AOut1Descr_wf [simp]: "wf_PortDescr AOut1Descr"
  apply (simp add: wf_PortDescr_def) 
  done

lemma BIn2Descr_wf [simp]: "wf_PortDescr BIn2Descr"
  apply (simp add: wf_PortDescr_def) 
  done

lemma BIn3Descr_wf [simp]: "wf_PortDescr BIn3Descr"
  apply (simp add: wf_PortDescr_def) 
  done
*)

(*
declare AOut0Descr_def [simp del]
declare AOut1Descr_def [simp del]
declare BIn2Descr_def [simp del]
declare BIn3Descr_def [simp del]
*)



(* The following was proving before adding any of the simplifier declarations
lemma sysModel_wf_Model_PortDescr: "wf_Model_PortDescr sysModel"
  apply (simp add: wf_Model_PortDescr_def sysModel_def sysPortDescrs_def)
  done
*)


lemma sysModel_wf_Model_PortDescr: "wf_Model_PortDescr sysModel"
  by (simp add: wf_Model_PortDescr_def wf_PortDescr_def) 

lemma sysModel_wf_Model_PortDescrsIds:  "wf_Model_PortDescrsIds sysModel"
  by (simp add: wf_Model_PortDescrsIds_def)                     
 
lemma sysModel_wf_Model_CompDescrsIds:  "wf_Model_CompDescrsIds sysModel"
  by (simp add: wf_Model_CompDescrsIds_def)                     

lemma sysModel_wf_Model_PortDescrsCompId: "wf_Model_PortDescrsCompId sysModel"
  by (simp add: wf_Model_PortDescrsCompId_def)
  
lemma sysModel_wf_Model_CompDescrsContainedPortIds: "wf_Model_CompDescrsContainedPortIds sysModel"
  by (simp add: wf_Model_CompDescrsContainedPortIds_def)

lemma sysModel_wf_Model_ConnsPortIds: "wf_Model_ConnsPortIds sysModel"
  by (simp add: wf_Model_ConnsPortIds_def)

lemma sysModel_wf_Model_DisjointPortIds: "wf_Model_DisjointPortIds sysModel"
  by (simp add: wf_Model_DisjointPortIds_def)

lemma sysModel_wf_Model_ConnsPortCategories: "wf_Model_ConnsPortCategories sysModel"
  by (simp add: wf_Model_ConnsPortCategories_def)

lemma sysModel_wf_Model_InDataPorts: "wf_Model_InDataPorts sysModel"
  by (simp add: wf_Model_InDataPorts_def)

lemma sysModel_wf_Model_SporadicComp: "wf_Model_SporadicComp sysModel"
  by (simp add: wf_Model_SporadicComp_def)

end

