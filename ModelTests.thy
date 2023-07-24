theory ModelTests
  imports ModelExamples
begin

(*************************************************************
  Uses "test" lemmas to test/validate model helper functions,
  using the example models in ModelExamples.
 *************************************************************)

(* Port Descriptor helper functions *)

lemma "isInPD BIn2Descr"
  by auto
  
lemma "\<not>(isInPD AOut0Descr)"
  by auto
 
(* Abdullah: continue with port descriptor operations:
    isOutPD
    isDataPD
    isEventPD
    isEventLikePD
 
  You DO NOT have to illustrate negation on each.
  You may have to construct some additional PortDescr examples
  (and instruct the simplifier accordingly)
 *)

lemma "isOutPD AOut0Descr"
  by auto

lemma "isOutPD AOut1Descr"
  by auto

lemma "isDataPD AOut0Descr"
  by auto

lemma "isDataPD BIn2Descr"
  by auto

lemma "isEventLikePD AOut1Descr"
  by auto

lemma "isEventLikePD BIn3Descr"
  by auto

lemma "isPeriodicCD ADescr"
  by auto
  

(* Abdullah: address isSporadicCD *)
lemma "isSporadicCD BDescr"
  by auto

(* helper functions for retreiving information from complete models *)
lemma "isOutPID sysModel AOut0Id"
  by auto


lemma "\<not> (isInPID sysModel AOut0Id)"
  by auto

(* Abdullah: address isSizePID *)

lemma "isPortOfCIDPID sysModel AId AOut0Id "
  by auto

(* Abdullah: address similar helper functions *)

lemma "isOutCDPID sysModel ADescr AOut0Id "
  by auto

(* Abdullah: address similar helper functions *)



end

