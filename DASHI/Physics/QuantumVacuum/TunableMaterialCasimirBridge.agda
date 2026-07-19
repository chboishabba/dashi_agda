module DASHI.Physics.QuantumVacuum.TunableMaterialCasimirBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- A tunable Casimir machine needs two measured material-response states and a
-- derived stroke-work difference.  Merely naming conductor/dielectric states
-- does not establish a positive cycle.
------------------------------------------------------------------------

record MaterialResponse : Set₁ where
  constructor mkMaterialResponse
  field
    ResponseCarrier : Set
    permittivity       : Q.Frequency → ResponseCarrier
    permeability       : Q.Frequency → ResponseCarrier
    reflectionResponse : Q.Frequency → ResponseCarrier

record ForceCurve : Set where
  constructor mkForceCurve
  field
    sample : Q.Length → Q.Pressure

record MaterialForceModel : Set₁ where
  constructor mkMaterialForceModel
  field
    material : MaterialResponse
    curve    : ForceCurve
    responseDeterminesCurve : Set

record TunableCasimirStroke : Set₁ where
  constructor mkTunableCasimirStroke
  field
    strongState weakState : MaterialForceModel
    inwardWorkStrong : Q.Work
    resetWorkWeak    : Q.Work
    switchingCost   : Q.Work
    dissipation     : Q.Work

cycleCostMagnitude : TunableCasimirStroke → Nat
cycleCostMagnitude s =
  Q.Work.magnitude (TunableCasimirStroke.resetWorkWeak s) +
  (Q.Work.magnitude (TunableCasimirStroke.switchingCost s) +
   Q.Work.magnitude (TunableCasimirStroke.dissipation s))

record PositiveMaterialStroke (s : TunableCasimirStroke) : Set where
  constructor mkPositiveMaterialStroke
  field
    margin : Nat
    closes :
      Q.Work.magnitude (TunableCasimirStroke.inwardWorkStrong s) ≡
      suc (cycleCostMagnitude s + margin)

record MeasuredMaterialComparison (s : TunableCasimirStroke) : Set where
  constructor mkMeasuredMaterialComparison
  field
    strongCurveObserved : Set
    weakCurveObserved   : Set
    switchingPathObserved : Set
    strokePositive : PositiveMaterialStroke s

-- The comparison bridge yields a positive fully charged material stroke, but
-- independent replication and long-run reservoir closure are still external.

comparisonYieldsPositiveStroke :
  (s : TunableCasimirStroke) →
  MeasuredMaterialComparison s →
  PositiveMaterialStroke s
comparisonYieldsPositiveStroke s comparison =
  MeasuredMaterialComparison.strokePositive comparison
