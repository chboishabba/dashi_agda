module DASHI.Control.ZhangDaibingUAVControlFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Control.ZhangDaibingUAVControlBidiExact as Zhang

------------------------------------------------------------------------
-- FINITE AUTONOMOUS-CONTROL RECONSTRUCTION
--
-- A small finite tracking carrier exercises the source-backed stage family.
-- Numbers are DASHI reconstruction values, not a reproduction of any one DOI
-- paper's vehicle, gains, trajectory or field-test errors.
------------------------------------------------------------------------

record FiniteZhangDaibingControlWitness : Set where
  constructor finite-zhang-daibing-control-witness
  field
    sourceReferences : String
    stages : List Zhang.UAVControlStage
    sensorSamples : Nat
    fusedStateSamples : Nat
    referenceWaypoints : Nat
    commandUpdates : Nat
    maximumSyntheticTrackingErrorMilliUnits : Nat
    syntheticReconstruction : Bool
    sourceTestReproduced : Bool
    nextExactLeaf : String

open FiniteZhangDaibingControlWitness public

finiteZhangDaibingControlWitness : FiniteZhangDaibingControlWitness
finiteZhangDaibingControlWitness = finite-zhang-daibing-control-witness
  "DOI 10.11887/j.cn.201801023; DOI 10.13700/j.bh.1001-5965.2016.0679; DOI 10.13973/j.cnki.robot.2017.0160"
  (Zhang.stateSensing ∷ Zhang.multisensorFusion ∷ Zhang.localisation ∷
   Zhang.referenceGeneration ∷ Zhang.guidanceCommand ∷ Zhang.flightControl ∷
   Zhang.landingOrPathDecision ∷ Zhang.formationCoordination ∷ Zhang.fieldTestResidual ∷ [])
  8
  8
  4
  8
  25
  true
  false
  "select one exact DOI object and replace synthetic counts with source dynamics, control law, gains, sensor model, geometry and error/robustness measurements"

finiteWitnessTouchesControlFamily : Bool
finiteWitnessTouchesControlFamily = true

finiteWitnessIsSpecificFlightReplication : Bool
finiteWitnessIsSpecificFlightReplication = false

finiteWitnessPaysDeployment : Bool
finiteWitnessPaysDeployment = false
