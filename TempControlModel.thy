theory TempControlModel
  imports Model VarState PortState ThreadState
begin

(*===============================================================*
 *   C o m p o n e n t: TempControlSoftwareSystem_s_Instance_tcproc_tempSensor [id = (CompId 0)] ---
 *===============================================================*)

(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_currentTemp [id = (PortId 0)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_currentTemp where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_currentTemp =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_currentTemp''
     (PortId 0)
     (CompId 0)
     Out
     Data
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_currentTemp_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_tempChanged [id = (PortId 1)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_tempChanged where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_tempChanged =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_tempChanged''
     (PortId 1)
     (CompId 0)
     Out
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_tempChanged_def [simp add]


(* -- Comp: TempControlSoftwareSystem_s_Instance_tcproc_tempSensor [id = (CompId 0)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempSensor where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempSensor =
     mkCompDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempSensor''
     (CompId 0)
     {(PortId 0),(PortId 1)}
     DispatchProtocol.Periodic
     {}
     {}"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_def [simp add]



(*===============================================================*
 *   C o m p o n e n t: TempControlSoftwareSystem_s_Instance_tcproc_fan [id = (CompId 1)] ---
 *===============================================================*)

(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_fan_fanCmd [id = (PortId 2)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_fan_fanCmd where
  "TempControlSoftwareSystem_s_Instance_tcproc_fan_fanCmd =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_fan_fanCmd''
     (PortId 2)
     (CompId 1)
     In
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_fan_fanCmd_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_fan_fanAck [id = (PortId 3)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_fan_fanAck where
  "TempControlSoftwareSystem_s_Instance_tcproc_fan_fanAck =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_fan_fanAck''
     (PortId 3)
     (CompId 1)
     Out
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_fan_fanAck_def [simp add]


(* -- Comp: TempControlSoftwareSystem_s_Instance_tcproc_fan [id = (CompId 1)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_fan where
  "TempControlSoftwareSystem_s_Instance_tcproc_fan =
     mkCompDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_fan''
     (CompId 1)
     {(PortId 2),(PortId 3)}
     DispatchProtocol.Sporadic
     {(PortId 2)}
     {}"
declare TempControlSoftwareSystem_s_Instance_tcproc_fan_def [simp add]



(*===============================================================*
 *   C o m p o n e n t: TempControlSoftwareSystem_s_Instance_tcproc_tempControl [id = (CompId 2)] ---
 *===============================================================*)

(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_tempControl_currentTemp [id = (PortId 4)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempControl_currentTemp where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempControl_currentTemp =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempControl_currentTemp''
     (PortId 4)
     (CompId 2)
     In
     Data
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempControl_currentTemp_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanAck [id = (PortId 5)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanAck where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanAck =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanAck''
     (PortId 5)
     (CompId 2)
     In
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanAck_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_tempControl_setPoint [id = (PortId 6)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempControl_setPoint where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempControl_setPoint =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempControl_setPoint''
     (PortId 6)
     (CompId 2)
     In
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempControl_setPoint_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_tempControl_tempChanged [id = (PortId 8)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempControl_tempChanged where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempControl_tempChanged =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempControl_tempChanged''
     (PortId 8)
     (CompId 2)
     In
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempControl_tempChanged_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanCmd [id = (PortId 7)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanCmd where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanCmd =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanCmd''
     (PortId 7)
     (CompId 2)
     Out
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanCmd_def [simp add]


(* -- Comp: TempControlSoftwareSystem_s_Instance_tcproc_tempControl [id = (CompId 2)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_tempControl where
  "TempControlSoftwareSystem_s_Instance_tcproc_tempControl =
     mkCompDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_tempControl''
     (CompId 2)
     {(PortId 4),(PortId 5),(PortId 6),(PortId 8),(PortId 7)}
     DispatchProtocol.Sporadic
     {(PortId 5),(PortId 6),(PortId 8)}
     {}"
declare TempControlSoftwareSystem_s_Instance_tcproc_tempControl_def [simp add]



(*===============================================================*
 *   C o m p o n e n t: TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface [id = (CompId 3)] ---
 *===============================================================*)

(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_currentTemp [id = (PortId 9)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_currentTemp where
  "TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_currentTemp =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_currentTemp''
     (PortId 9)
     (CompId 3)
     In
     Data
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_currentTemp_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_tempChanged [id = (PortId 11)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_tempChanged where
  "TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_tempChanged =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_tempChanged''
     (PortId 11)
     (CompId 3)
     In
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_tempChanged_def [simp add]


(* -- Port: TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_setPoint [id = (PortId 10)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_setPoint where
  "TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_setPoint =
    mkPortDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_setPoint''
     (PortId 10)
     (CompId 3)
     Out
     Event
     1
     0"
declare TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_setPoint_def [simp add]


(* -- Comp: TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface [id = (CompId 3)] -- *)
definition TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface where
  "TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface =
     mkCompDescr
     ''TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface''
     (CompId 3)
     {(PortId 9),(PortId 11),(PortId 10)}
     DispatchProtocol.Periodic
     {}
     {}"
declare TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_def [simp add]



(*===============================================================*
 *   S Y S T E M   C O N N E C T I O N S
 *===============================================================*)

definition sysConns
  where "sysConns = map_of [
    ((PortId 0), {(PortId 4),(PortId 9)}),
    ((PortId 1), {(PortId 8),(PortId 11)}),
    ((PortId 3), {(PortId 5)}),
    ((PortId 7), {(PortId 2)}),
    ((PortId 10), {(PortId 6)})
  ]"
declare sysConns_def [simp add]

(*===============================================================*
*   P O R T   D E S C R I P T O R S
*===============================================================*)

definition sysPortDescrs
  where "sysPortDescrs = map_of [
    ((PortId 0), TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_currentTemp),
    ((PortId 1), TempControlSoftwareSystem_s_Instance_tcproc_tempSensor_tempChanged),
    ((PortId 2), TempControlSoftwareSystem_s_Instance_tcproc_fan_fanCmd),
    ((PortId 3), TempControlSoftwareSystem_s_Instance_tcproc_fan_fanAck),
    ((PortId 4), TempControlSoftwareSystem_s_Instance_tcproc_tempControl_currentTemp),
    ((PortId 5), TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanAck),
    ((PortId 6), TempControlSoftwareSystem_s_Instance_tcproc_tempControl_setPoint),
    ((PortId 8), TempControlSoftwareSystem_s_Instance_tcproc_tempControl_tempChanged),
    ((PortId 7), TempControlSoftwareSystem_s_Instance_tcproc_tempControl_fanCmd),
    ((PortId 9), TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_currentTemp),
    ((PortId 11), TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_tempChanged),
    ((PortId 10), TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface_setPoint)
  ]"
declare sysPortDescrs_def [simp add]

(*===============================================================*
*   C O M P O N E N T   D E S C R I P T O R S
*===============================================================*)

definition sysCompDescrs
  where "sysCompDescrs = map_of [
    ((CompId 0), TempControlSoftwareSystem_s_Instance_tcproc_tempSensor),
    ((CompId 1), TempControlSoftwareSystem_s_Instance_tcproc_fan),
    ((CompId 2), TempControlSoftwareSystem_s_Instance_tcproc_tempControl),
    ((CompId 3), TempControlSoftwareSystem_s_Instance_tcproc_operatorInterface)
  ]"
declare sysCompDescrs_def [simp add]

(*===============================================================*
*   T O P - L E V E L  S Y S T E M   M O D E L
*===============================================================*)

definition sysModel
  where "sysModel = mkModel sysCompDescrs sysPortDescrs sysConns"
declare sysModel_def [simp add]

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
