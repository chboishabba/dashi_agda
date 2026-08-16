module DASHI.Governance.GenericSocialAttractor where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Generic discrete attractor algebra.
--
-- This module deliberately contains no named social or political case.  It is
-- the common theorem layer for trauma/exploitation, epistemic closure,
-- externality/punitive-restoration and engagement-optimisation specialisations.
------------------------------------------------------------------------

record DiscreteSystem : Set₁ where
  field
    State : Set
    step : State → State

open DiscreteSystem public

record FixedPoint (S : DiscreteSystem) : Set where
  field
    point : State S
    fixed : step S point ≡ point

open FixedPoint public

record InvariantRegion (S : DiscreteSystem) : Set₁ where
  field
    Region : State S → Set
    closedUnderStep :
      (x : State S) →
      Region x →
      Region (step S x)

open InvariantRegion public

record AbsorbingRegion
  (S : DiscreteSystem)
  (R : InvariantRegion S) : Set₁ where
  field
    enters : State S → Set
    entryIsInRegion :
      (x : State S) →
      enters x →
      InvariantRegion.Region R (step S x)

open AbsorbingRegion public

record IdempotentDynamics (S : DiscreteSystem) : Set where
  field
    stepIdempotent :
      (x : State S) →
      step S (step S x) ≡ step S x

open IdempotentDynamics public

------------------------------------------------------------------------
-- Positive theorem: every image point of an idempotent step is a fixed point.
------------------------------------------------------------------------

imagePointIsFixed :
  (S : DiscreteSystem) →
  IdempotentDynamics S →
  (x : State S) →
  step S (step S x) ≡ step S x
imagePointIsFixed S dynamics x =
  stepIdempotent dynamics x

fixedPointFromImage :
  (S : DiscreteSystem) →
  IdempotentDynamics S →
  State S →
  FixedPoint S
fixedPointFromImage S dynamics x =
  record
    { point = step S x
    ; fixed = stepIdempotent dynamics x
    }

------------------------------------------------------------------------
-- A closed invariant region remains closed after two steps as well.
------------------------------------------------------------------------

closedUnderTwoSteps :
  (S : DiscreteSystem) →
  (R : InvariantRegion S) →
  (x : State S) →
  InvariantRegion.Region R x →
  InvariantRegion.Region R (step S (step S x))
closedUnderTwoSteps S R x inRegion =
  InvariantRegion.closedUnderStep R
    (step S x)
    (InvariantRegion.closedUnderStep R x inRegion)

------------------------------------------------------------------------
-- Interventions are not automatically repairs.  A repair must provide an
-- explicit escape witness from the original step at the intervention point.
------------------------------------------------------------------------

record Intervention (S : DiscreteSystem) : Set₁ where
  field
    intervene : State S → State S

record EscapingIntervention
  (S : DiscreteSystem)
  (I : Intervention S) : Set₁ where
  field
    witness : State S
    escapesStep :
      Intervention.intervene I witness ≡ step S witness → ⊥

------------------------------------------------------------------------
-- Claim boundary: fixed-point existence says nothing by itself about value,
-- diagnosis, legality, political authority or inevitability.
------------------------------------------------------------------------

record GenericAttractorBoundary : Set where
  constructor genericAttractorBoundary
  field
    fixedPointImpliesNormativeApproval : Bool
    fixedPointImpliesClinicalDiagnosis : Bool
    fixedPointImpliesLegalConclusion : Bool
    fixedPointImpliesHistoricalInevitability : Bool
    namedCaseRequiresExternalInstantiation : Bool

canonicalGenericAttractorBoundary : GenericAttractorBoundary
canonicalGenericAttractorBoundary =
  genericAttractorBoundary false false false false true
