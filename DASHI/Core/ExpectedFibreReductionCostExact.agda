module DASHI.Core.ExpectedFibreReductionCostExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.CostedFibreEliminationChoiceBidiExact as FibreCost

------------------------------------------------------------------------
-- EXPECTED / DECLARED FIBRE REDUCTION VS COST
--
-- No probability model is assumed.  "Expected" here means an explicitly
-- supplied reduction envelope for the currently live hypothesis fibre.
------------------------------------------------------------------------

record ReductionEnvelope : Set where
  constructor reductionEnvelope
  field
    lowerEliminated : Nat
    upperEliminated : Nat
    envelopeReference : String

open ReductionEnvelope public

record FibreReductionCostCandidate : Set where
  constructor fibreReductionCostCandidate
  field
    move : Choice.InformationMove
    reduction : ReductionEnvelope
    consumerRelevant : Bool
    authorityAdmissible : Bool
    discriminationReference : String

open FibreReductionCostCandidate public

record ReductionPerCostPreference
    (better worse : FibreReductionCostCandidate) : Set where
  constructor reductionPerCostPreference
  field
    betterRelevant : consumerRelevant better ≡ true
    betterAdmissible : authorityAdmissible better ≡ true
    worseDoesNotStrictlyDominateGain : lowerEliminated (reduction worse) ≤ upperEliminated (reduction better)
    betterNotMoreExpensiveThanDeclaredBound : Choice.cost (move better) ≤ Choice.cost (move worse) + Choice.cost (move better)
    preferenceReference : String

open ReductionPerCostPreference public

------------------------------------------------------------------------
-- Exact fixture: cheapest is not necessarily highest reduction, and highest
-- reduction is not automatically admissible.
------------------------------------------------------------------------

cheapWeak : FibreReductionCostCandidate
cheapWeak = fibreReductionCostCandidate
  (Choice.informationMove Choice.takeMeasurement 1 "cheap weak probe" "toy" "toy")
  (reductionEnvelope 0 1 "eliminates at most one candidate")
  true true
  "cheap but weak discrimination"

costlyStrong : FibreReductionCostCandidate
costlyStrong = fibreReductionCostCandidate
  (Choice.informationMove Choice.takeMeasurement 4 "costly strong probe" "toy" "toy")
  (reductionEnvelope 2 2 "eliminates two live candidates")
  true true
  "stronger declared live-fibre reduction"

inadmissibleHuge : FibreReductionCostCandidate
inadmissibleHuge = fibreReductionCostCandidate
  (Choice.informationMove Choice.perturbAndMeasure 2 "inadmissible huge probe" "toy" "missing authority")
  (reductionEnvelope 3 3 "largest nominal reduction")
  true false
  "nominally maximal information but outside authority envelope"

cheapCost : Choice.cost (move cheapWeak) ≡ 1
cheapCost = refl

strongGain : lowerEliminated (reduction costlyStrong) ≡ 2
strongGain = refl

hugeGainNotAuthority : authorityAdmissible inadmissibleHuge ≡ false
hugeGainNotAuthority = refl

record ExpectedFibreReductionCostBoundary : Set where
  constructor expectedFibreReductionCostBoundary
  field
    lowerCostImpliesLargerReduction : Bool
    lowerCostImpliesLargerReductionIsFalse : lowerCostImpliesLargerReduction ≡ false
    largerReductionImpliesAuthority : Bool
    largerReductionImpliesAuthorityIsFalse : largerReductionImpliesAuthority ≡ false
    reductionEnvelopeIsProbabilityDistribution : Bool
    reductionEnvelopeIsProbabilityDistributionIsFalse : reductionEnvelopeIsProbabilityDistribution ≡ false
    admissibilityMustBeCheckedSeparately : Bool
    admissibilityMustBeCheckedSeparatelyIsTrue : admissibilityMustBeCheckedSeparately ≡ true

canonicalExpectedFibreReductionCostBoundary : ExpectedFibreReductionCostBoundary
canonicalExpectedFibreReductionCostBoundary =
  expectedFibreReductionCostBoundary false refl false refl false refl true refl

existingCostedFibreBoundary : FibreCost.CostedFibreEliminationBoundary
existingCostedFibreBoundary = FibreCost.canonicalCostedFibreEliminationBoundary
