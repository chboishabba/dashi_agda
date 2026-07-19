module DASHI.Physics.QuantumVacuum.ConjectureLedger where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface
import DASHI.Physics.QuantumVacuum.FullDASHIFormalism as Full

------------------------------------------------------------------------
-- Useful physics extracted from the report, represented as conjectures with
-- explicit premises and promotion targets rather than prose conclusions.
------------------------------------------------------------------------

data Conjecture : Set where
  boundaryConditionsAlterStress : Conjecture
  geometryAmplifiesNoiseCoupling : Conjecture
  materialSwitchingMayYieldStrokeMargin : Conjecture
  cavityModesMayShiftGroundStates : Conjecture
  nonlinearMixingMayDownconvert : Conjecture
  operationalVacuumReservoirMayDegrade : Conjecture
  vacuumCouplingMayTransferMomentum : Conjecture

record ConjectureEntry : Set₁ where
  constructor conjectureEntry
  field
    conjecture : Conjecture
    mechanism  : Surface.Mechanism
    Premise    : Set
    PredictedObservable : Set
    NullHypothesis : Set
    promotionTarget : Full.ClaimStage
    presentlyPromoted : Bool

record TestedConjecture (entry : ConjectureEntry) : Set₁ where
  constructor testedConjecture
  field
    premiseReceipt : ConjectureEntry.Premise entry
    observableReceipt : ConjectureEntry.PredictedObservable entry
    NullControl : ConjectureEntry.NullHypothesis entry → Set
    nullControlReceipt :
      (h : ConjectureEntry.NullHypothesis entry) → NullControl h

-- A test receipt is not a continuous-power receipt.

testDoesNotRewritePromotionStatus :
  (entry : ConjectureEntry) → TestedConjecture entry →
  ConjectureEntry.presentlyPromoted entry ≡
  ConjectureEntry.presentlyPromoted entry
testDoesNotRewritePromotionStatus entry test = refl

record PhysicsConjectureAtlas : Set₁ where
  constructor physicsConjectureAtlas
  field
    boundaryStress : ConjectureEntry
    coilNoise      : ConjectureEntry
    tunableMaterial : ConjectureEntry
    groundState    : ConjectureEntry
    downconversion : ConjectureEntry
    reservoir      : ConjectureEntry
    propulsion     : ConjectureEntry
