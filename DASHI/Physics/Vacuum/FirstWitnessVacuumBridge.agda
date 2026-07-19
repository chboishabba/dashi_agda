module DASHI.Physics.Vacuum.FirstWitnessVacuumBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Foundations.FirstWitnessConstraintAlgebra as Witness

------------------------------------------------------------------------
-- Vacuum candidate semantics.
--
-- `firstFailure = nothing` means the candidate survives every represented
-- admissibility depth: it is saturated relative to this finite model.
-- `firstFailure = just d` means depth d is the unique first decisive witness
-- that removes the candidate.  This is the vacuum analogue of the Euler
-- kill-key lock, but it does not by itself derive physical gravity.
------------------------------------------------------------------------

record VacuumCandidate : Set where
  constructor vacuumCandidate
  field
    firstFailure : Maybe Nat

natEqual? : Nat → Nat → Bool
natEqual? zero    zero    = true
natEqual? zero    (suc n) = false
natEqual? (suc m) zero    = false
natEqual? (suc m) (suc n) = natEqual? m n

applyDepth : Nat → VacuumCandidate → Witness.Status → Witness.Status
applyDepth depth candidate Witness.dead = Witness.dead
applyDepth depth candidate Witness.alive with VacuumCandidate.firstFailure candidate
... | nothing = Witness.alive
... | just decisive with natEqual? depth decisive
...   | true  = Witness.dead
...   | false = Witness.alive

record Saturated (candidate : VacuumCandidate) : Set where
  constructor saturated
  field
    noFirstFailure : VacuumCandidate.firstFailure candidate ≡ nothing

record ResidueAt (depth : Nat) (candidate : VacuumCandidate) : Set where
  constructor residueAt
  field
    decisiveFailure : VacuumCandidate.firstFailure candidate ≡ just depth

saturatedSurvivesEveryDepth :
  (candidate : VacuumCandidate) →
  Saturated candidate →
  (depth : Nat) →
  applyDepth depth candidate Witness.alive ≡ Witness.alive
saturatedSurvivesEveryDepth candidate proof depth rewrite
  Saturated.noFirstFailure proof = refl

constraintDepthsCommute :
  (left right : Nat) →
  (candidate : VacuumCandidate) →
  (status : Witness.Status) →
  applyDepth left candidate (applyDepth right candidate status) ≡
  applyDepth right candidate (applyDepth left candidate status)
constraintDepthsCommute left right candidate Witness.dead = refl
constraintDepthsCommute left right candidate Witness.alive with
  VacuumCandidate.firstFailure candidate
... | nothing = refl
... | just decisive with natEqual? left decisive | natEqual? right decisive
...   | true  | true  = refl
...   | true  | false = refl
...   | false | true  = refl
...   | false | false = refl

------------------------------------------------------------------------
-- Interpretation boundary.
--
-- The finite first-witness model establishes schedule-independent survival
-- and an exact saturated/residue split.  Promotion to an Einstein or quantum
-- gravity claim requires the following independent mathematical bridges.
------------------------------------------------------------------------

record EinsteinPromotionObligations : Set₁ where
  field
    BaseManifold : Set
    MetricCarrier : Set
    admissibleDiffeomorphismAction : Set
    localFiniteJetAction : Set
    leadingSecondOrderEquations : Set
    valuationToMetricMap : Set
    residueToStressEnergyMap : Set
    microscopicToValuationClosure : Set
    bianchiCompatibility : Set

record QuantumGravityPromotionObligations : Set₁ where
  field
    classicalBridge : EinsteinPromotionObligations
    fluctuationCarrier : Set
    gaugeFixedQuadraticAction : Set
    positiveNormPhysicalSector : Set
    spinTwoModeDerivation : Set
    microscopicUnitarityCompatibility : Set

record VacuumEinsteinCandidate (candidate : VacuumCandidate) : Set₁ where
  field
    saturationReceipt : Saturated candidate
    promotionObligations : EinsteinPromotionObligations

record VacuumQuantumGravityCandidate (candidate : VacuumCandidate) : Set₁ where
  field
    saturationReceipt : Saturated candidate
    promotionObligations : QuantumGravityPromotionObligations

------------------------------------------------------------------------
-- No constructor is supplied from Saturated alone.  This deliberately blocks
-- the invalid inference "closed shell, therefore Einstein gravity".
------------------------------------------------------------------------

saturationIsWeakerThanEinsteinPromotion :
  (candidate : VacuumCandidate) → Saturated candidate → Set₁
saturationIsWeakerThanEinsteinPromotion candidate proof =
  EinsteinPromotionObligations
