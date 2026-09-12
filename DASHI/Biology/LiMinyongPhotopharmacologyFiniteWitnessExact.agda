module DASHI.Biology.LiMinyongPhotopharmacologyFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.LiMinyongPhotopharmacologyBidiExact as Li

------------------------------------------------------------------------
-- FINITE PHOTOCONTROL RECONSTRUCTION
--
-- This finite carrier demonstrates a reversible light-control/readout path.
-- Wavelengths, affinities and kinetics below are not source claims; the witness
-- remains synthetic until one exact compound/probe object is selected.
------------------------------------------------------------------------

data FinitePhotoState : Set where darkState litState recoveredState : FinitePhotoState

record FiniteLiMinyongPhotopharmWitness : Set where
  constructor finite-li-minyong-photopharm-witness
  field
    sourceReferences : String
    stages : List Li.PhotoControlStage
    initialState : FinitePhotoState
    illuminatedState : FinitePhotoState
    recoveredStateValue : FinitePhotoState
    illuminationSteps : Nat
    bindingReadoutObserved : Bool
    reverseReadoutObserved : Bool
    syntheticReconstruction : Bool
    sourceCompoundReproduced : Bool
    nextExactLeaf : String

open FiniteLiMinyongPhotopharmWitness public

finiteLiMinyongPhotopharmWitness : FiniteLiMinyongPhotopharmWitness
finiteLiMinyongPhotopharmWitness = finite-li-minyong-photopharm-witness
  "DOI 10.1002/med.22120; CN201110101082.5; CN201110100874.0"
  (Li.photonInput ∷ Li.photoswitchStateChange ∷ Li.targetEncounter ∷ Li.targetBinding ∷
   Li.molecularOrPhysiologicalReadout ∷ Li.recoveryOrReverseSwitch ∷ [])
  darkState
  litState
  recoveredState
  2
  true
  true
  true
  false
  "select one exact compound/probe and replace this mechanism-shape witness with source wavelengths, photostationary fractions, affinity/selectivity, dose, readout calibration and reversibility kinetics"

finiteWitnessIsReversibleMechanismShape : Bool
finiteWitnessIsReversibleMechanismShape = true

finiteWitnessIsClinicalEfficacyEvidence : Bool
finiteWitnessIsClinicalEfficacyEvidence = false

finiteWitnessPaysAnyTargetControllable : Bool
finiteWitnessPaysAnyTargetControllable = false
