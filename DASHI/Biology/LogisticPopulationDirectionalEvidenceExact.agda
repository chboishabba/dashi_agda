module DASHI.Biology.LogisticPopulationDirectionalEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural
import DASHI.Statistics.DirectionalEvidenceTritExact as Evidence

------------------------------------------------------------------------
-- LOGISTIC POPULATION / DIRECTIONAL-EVIDENCE ADAPTER
--
-- Reuses the finite logistic population fixture already owned by
-- NaturalSystemsHyperfabricExact.  The balanced trit is only a coarse
-- observation of one-step population direction; it is not the population
-- state itself, and it carries no agency or abiogenesis semantics.
------------------------------------------------------------------------

growthDirection : Natural.LogisticPopulationState → Trit
growthDirection Natural.populationZero = zer
growthDirection Natural.populationOne = pos
growthDirection Natural.populationTwo = pos
growthDirection Natural.populationThree = zer
growthDirection Natural.populationFour = neg

populationZeroStationary :
  growthDirection Natural.populationZero ≡ zer
populationZeroStationary = refl

populationOneGrows :
  growthDirection Natural.populationOne ≡ pos
populationOneGrows = refl

populationTwoGrows :
  growthDirection Natural.populationTwo ≡ pos
populationTwoGrows = refl

populationThreeStationary :
  growthDirection Natural.populationThree ≡ zer
populationThreeStationary = refl

populationFourDeclines :
  growthDirection Natural.populationFour ≡ neg
populationFourDeclines = refl

------------------------------------------------------------------------
-- Exact witness that the coarse trit is not injective.  Distinct population
-- states can share the same visible growth direction, so the state remains an
-- explicit residual coordinate.
------------------------------------------------------------------------

populationOneNotPopulationTwo :
  Natural.populationOne ≡ Natural.populationTwo → ⊥
populationOneNotPopulationTwo ()

positiveDirectionCollision :
  growthDirection Natural.populationOne ≡ growthDirection Natural.populationTwo
positiveDirectionCollision = refl

record LogisticGrowthResidual : Set where
  constructor logistic-growth-residual
  field
    state : Natural.LogisticPopulationState
    next : Natural.LogisticPopulationState
    nextIsCanonical : next ≡ Natural.logisticFour state
    direction : Trit
    directionIsCanonical : direction ≡ growthDirection state

open LogisticGrowthResidual public

canonicalGrowthResidual :
  (state : Natural.LogisticPopulationState) → LogisticGrowthResidual
canonicalGrowthResidual state =
  logistic-growth-residual state (Natural.logisticFour state) refl
    (growthDirection state) refl

------------------------------------------------------------------------
-- Generic statistical interpretation boundary for a measured/estimated growth
-- effect.  The statistics layer remains separate from the exact finite fixture:
-- a domain adapter must supply actual positive/negative/underdetermined
-- evidence predicates for its estimator or confidence procedure.
------------------------------------------------------------------------

record PopulationGrowthEvidenceSemantics (Result : Set) : Set₁ where
  constructor population-growth-evidence-semantics
  field
    PositiveGrowthEvidence : Result → Set
    NegativeGrowthEvidence : Result → Set
    UnderdeterminedGrowthEvidence : Result → Set

open PopulationGrowthEvidenceSemantics public

asDirectionalEvidenceSemantics :
  ∀ {Result : Set} →
  PopulationGrowthEvidenceSemantics Result →
  Evidence.DirectionalEvidenceSemantics Result ⊤
asDirectionalEvidenceSemantics semantics =
  Evidence.directional-evidence-semantics
    (λ result _ → PositiveGrowthEvidence semantics result)
    (λ result _ → NegativeGrowthEvidence semantics result)
    (λ result _ → UnderdeterminedGrowthEvidence semantics result)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameGrowthTritMeansSamePopulationPermission : Set where

data NotPositiveGrowthMeansNegativeGrowthPermission : Set where

data StationaryObservationMeansCarryingCapacityPermission : Set where

data LogisticGrowthMeansAgencyPermission : Set where

sameGrowthTritDoesNotMeanSamePopulation :
  SameGrowthTritMeansSamePopulationPermission → ⊥
sameGrowthTritDoesNotMeanSamePopulation ()

notPositiveDoesNotMeanNegativeGrowth :
  NotPositiveGrowthMeansNegativeGrowthPermission → ⊥
notPositiveDoesNotMeanNegativeGrowth ()

stationaryObservationDoesNotByItselfIdentifyCarryingCapacity :
  StationaryObservationMeansCarryingCapacityPermission → ⊥
stationaryObservationDoesNotByItselfIdentifyCarryingCapacity ()

logisticGrowthDoesNotCreateAgency :
  LogisticGrowthMeansAgencyPermission → ⊥
logisticGrowthDoesNotCreateAgency ()

record LogisticPopulationDirectionalBoundary : Set where
  constructor logistic-population-directional-boundary
  field
    tritIsCoarseObservation : Bool
    sameTritImpliesSamePopulation : Bool
    failedPositiveEvidenceImpliesNegativeEvidence : Bool
    stationaryObservationIdentifiesUniquePhysicalEquilibrium : Bool
    logisticPopulationDynamicsCreateAgency : Bool
    residualPopulationStateRemainsExplicit : Bool

canonicalLogisticPopulationDirectionalBoundary :
  LogisticPopulationDirectionalBoundary
canonicalLogisticPopulationDirectionalBoundary =
  logistic-population-directional-boundary
    true false false false false true
