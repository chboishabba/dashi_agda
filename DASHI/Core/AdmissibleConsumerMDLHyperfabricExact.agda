module DASHI.Core.AdmissibleConsumerMDLHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REPO-NATIVE DASHI EXTENSION
--
-- Description length is a ranking coordinate only after hard admissibility and
-- consumer-sufficiency obligations are inhabited. This module therefore does
-- not identify lower MDL with physical truth, empirical support, authority, or
-- universal optimality.
------------------------------------------------------------------------

record ConsumerMDLProblem : Set₁ where
  constructor consumerMDLProblem
  field
    Model : Set
    Admissible : Model → Set
    ConsumerAdequate : Model → Set
    descriptionLength : Model → Nat
    Refines : Model → Model → Set
    modelReference : Model → String
    codingConventionReference : String
    consumerReference : String

open ConsumerMDLProblem public

Eligible : (problem : ConsumerMDLProblem) → Model problem → Set
Eligible problem model =
  Admissible problem model × ConsumerAdequate problem model

record AdmissibleStratumPoint
    (problem : ConsumerMDLProblem) : Set where
  constructor admissibleStratumPoint
  field
    model : Model problem
    admissible : Admissible problem model
    adequate : ConsumerAdequate problem model

open AdmissibleStratumPoint public

record MinimalEligibleDescription
    (problem : ConsumerMDLProblem)
    (selected : Model problem) : Set₁ where
  constructor minimalEligibleDescription
  field
    selectedAdmissible : Admissible problem selected
    selectedAdequate : ConsumerAdequate problem selected
    noLongerThanAnyEligible :
      (candidate : Model problem) →
      Admissible problem candidate →
      ConsumerAdequate problem candidate →
      descriptionLength problem selected ≤ descriptionLength problem candidate
    searchReference : String

open MinimalEligibleDescription public

minimalDescriptionIsEligible :
  ∀ {problem selected} →
  MinimalEligibleDescription problem selected →
  Eligible problem selected
minimalDescriptionIsEligible receipt =
  selectedAdmissible receipt , selectedAdequate receipt

------------------------------------------------------------------------
-- Counterexample/local-repair surface.
------------------------------------------------------------------------

record ConsumerCounterexample
    (problem : ConsumerMDLProblem)
    (candidate : Model problem) : Set₁ where
  constructor consumerCounterexample
  field
    Witness : Set
    witness : Witness
    candidateInsufficient : ConsumerAdequate problem candidate → ⊥
    erasedDistinctionReference : String
    counterexampleReference : String

open ConsumerCounterexample public

counterexampleExcludesEligibility :
  ∀ {problem candidate} →
  ConsumerCounterexample problem candidate →
  Eligible problem candidate → ⊥
counterexampleExcludesEligibility failure eligible =
  candidateInsufficient failure (proj₂ eligible)

record LocalRefinementRepair
    (problem : ConsumerMDLProblem)
    (coarse fine : Model problem) : Set₁ where
  constructor localRefinementRepair
  field
    failure : ConsumerCounterexample problem coarse
    refinement : Refines problem coarse fine
    repairedAdmissibility : Admissible problem fine
    repairedConsumerAdequacy : ConsumerAdequate problem fine
    reopenedResidualReference : String

open LocalRefinementRepair public

repairProvidesEligibleRefinement :
  ∀ {problem coarse fine} →
  LocalRefinementRepair problem coarse fine →
  Eligible problem fine
repairProvidesEligibleRefinement repair =
  repairedAdmissibility repair , repairedConsumerAdequacy repair

------------------------------------------------------------------------
-- Multi-axis cost / Pareto layer over the admissible stratum.
------------------------------------------------------------------------

record CostHyperfabric
    (problem : ConsumerMDLProblem) : Set₁ where
  constructor costHyperfabric
  field
    Axis : Set
    cost : Axis → Model problem → Nat
    axisReference : Axis → String

open CostHyperfabric public

WeaklyDominates :
  ∀ {problem} →
  (costs : CostHyperfabric problem) →
  Model problem → Model problem → Set
WeaklyDominates costs left right =
  (axis : Axis costs) → cost costs axis left ≤ cost costs axis right

record ParetoAdmissible
    {problem : ConsumerMDLProblem}
    (costs : CostHyperfabric problem)
    (selected : Model problem) : Set₁ where
  constructor paretoAdmissible
  field
    selectedEligible : Eligible problem selected
    noStrictlyCheaperEligibleWitness :
      (candidate : Model problem) →
      Eligible problem candidate →
      WeaklyDominates costs candidate selected →
      WeaklyDominates costs selected candidate
    paretoReference : String

open ParetoAdmissible public

------------------------------------------------------------------------
-- Optional recursive/refinement neighbourhood.
------------------------------------------------------------------------

record RefinementNeighbourhood
    (problem : ConsumerMDLProblem) : Set₁ where
  constructor refinementNeighbourhood
  field
    Address : Set
    address : Model problem → Address
    sameNeighbourhood : Address → Address → Set
    refinementLocality :
      (coarse fine : Model problem) →
      Refines problem coarse fine →
      sameNeighbourhood (address coarse) (address fine)
    neighbourhoodReference : String

open RefinementNeighbourhood public

repairStaysInDeclaredNeighbourhood :
  ∀ {problem coarse fine} →
  (neighbourhood : RefinementNeighbourhood problem) →
  LocalRefinementRepair problem coarse fine →
  sameNeighbourhood neighbourhood
    (address neighbourhood coarse)
    (address neighbourhood fine)
repairStaysInDeclaredNeighbourhood neighbourhood repair =
  refinementLocality neighbourhood _ _ (refinement repair)

record AdmissibleConsumerMDLBoundary : Set where
  constructor admissibleConsumerMDLBoundary
  field
    lowerDescriptionLengthIsPhysicalTruth : Bool
    lowerDescriptionLengthIsPhysicalTruthIsFalse :
      lowerDescriptionLengthIsPhysicalTruth ≡ false
    inadmissibleModelMayWinByShortCode : Bool
    inadmissibleModelMayWinByShortCodeIsFalse :
      inadmissibleModelMayWinByShortCode ≡ false
    consumerInadequateModelMayWinByShortCode : Bool
    consumerInadequateModelMayWinByShortCodeIsFalse :
      consumerInadequateModelMayWinByShortCode ≡ false
    richerModelExistenceRefutesCompactModel : Bool
    richerModelExistenceRefutesCompactModelIsFalse :
      richerModelExistenceRefutesCompactModel ≡ false
    counterexampleMayDriveLocalRefinement : Bool
    counterexampleMayDriveLocalRefinementIsTrue :
      counterexampleMayDriveLocalRefinement ≡ true
    paretoAxesAreApplicationDeclared : Bool
    paretoAxesAreApplicationDeclaredIsTrue :
      paretoAxesAreApplicationDeclared ≡ true
    recursiveAddressAutomaticallyMeansPAdicPhysics : Bool
    recursiveAddressAutomaticallyMeansPAdicPhysicsIsFalse :
      recursiveAddressAutomaticallyMeansPAdicPhysics ≡ false

canonicalAdmissibleConsumerMDLBoundary : AdmissibleConsumerMDLBoundary
canonicalAdmissibleConsumerMDLBoundary =
  admissibleConsumerMDLBoundary
    false refl false refl false refl false refl true refl true refl false refl
