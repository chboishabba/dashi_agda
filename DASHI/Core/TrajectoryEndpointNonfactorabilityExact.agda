module DASHI.Core.TrajectoryEndpointNonfactorabilityExact where

------------------------------------------------------------------------
-- TRAJECTORY / ENDPOINT NON-FACTORABILITY
--
-- INTERNAL THEOREM-PATTERN PROVENANCE
--
-- Several live DASHI lanes independently require the same distinction:
--
-- * PR #606: two histories with the same start/goal can carry different
--   effort, stress, barrier and optionality-loss cost;
-- * PR #613: a present coarse endpoint can hide path-deposited residue;
-- * PR #621: local transition contributions accumulate on finite histories;
-- * PR #624: two trade routes with the same endpoint role can have different
--   turnover/risk/optionality cost.
--
-- Those draft branches are inspiration only.  This owner imports none of them.
-- It extracts the domain-neutral information theorem already supported by the
-- existing `IntersectionalNonFactorability` machinery:
--
--   same endpoint observation + different trajectory consumer
--   => the consumer does not factor through endpoints alone
--   => no post-processing of endpoints can reconstruct the erased path data.
--
-- This is not a least-action theorem and does not assert that every meaningful
-- path quantity is additive, scalar, or Nat-valued.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- Generic endpoint-indexed trajectory carrier.
------------------------------------------------------------------------

record EndpointTrajectorySystem : Set₁ where
  constructor endpoint-trajectory-system
  field
    State Trajectory : Set
    start : Trajectory → State
    finish : Trajectory → State
    trajectoryCode : Trajectory → Nat
    trajectoryReading : String

open EndpointTrajectorySystem public

endpointObserver :
  (system : EndpointTrajectorySystem) →
  Trajectory system → State system × State system
endpointObserver system trajectory =
  start system trajectory , finish system trajectory

------------------------------------------------------------------------
-- Exact witness: endpoints collide while a trajectory-valued consumer splits.
------------------------------------------------------------------------

record SameEndpointDifferentTrajectoryCode
    (system : EndpointTrajectorySystem) : Set where
  constructor same-endpoint-different-trajectory-code
  field
    leftRoute rightRoute : Trajectory system
    sameStart :
      start system leftRoute ≡ start system rightRoute
    sameFinish :
      finish system leftRoute ≡ finish system rightRoute
    routeCodesDiffer :
      trajectoryCode system leftRoute
      ≡ trajectoryCode system rightRoute →
      ⊥

open SameEndpointDifferentTrajectoryCode public

sameEndpoints :
  {system : EndpointTrajectorySystem} →
  (witness : SameEndpointDifferentTrajectoryCode system) →
  endpointObserver system (leftRoute witness)
  ≡ endpointObserver system (rightRoute witness)
sameEndpoints witness =
  cong₂ _,_ (sameStart witness) (sameFinish witness)

endpointCollisionGivesTrajectoryNonfactorability :
  {system : EndpointTrajectorySystem} →
  SameEndpointDifferentTrajectoryCode system →
  NF.NonFactorabilityWitness
    (endpointObserver system)
    (trajectoryCode system)
endpointCollisionGivesTrajectoryNonfactorability witness =
  NF.nonFactorabilityWitness
    (leftRoute witness)
    (rightRoute witness)
    (sameEndpoints witness)
    (routeCodesDiffer witness)

endpointOnlyDecoderImpossible :
  {system : EndpointTrajectorySystem} →
  SameEndpointDifferentTrajectoryCode system →
  NF.FactorsThrough
    (endpointObserver system)
    (trajectoryCode system) →
  ⊥
endpointOnlyDecoderImpossible witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (endpointCollisionGivesTrajectoryNonfactorability witness)

postprocessedEndpointStillCannotRecoverTrajectoryCode :
  {system : EndpointTrajectorySystem} →
  ∀ {Chart : Set} →
  (rechart : State system × State system → Chart) →
  SameEndpointDifferentTrajectoryCode system →
  NF.FactorsThrough
    (λ route → rechart (endpointObserver system route))
    (trajectoryCode system) →
  ⊥
postprocessedEndpointStillCannotRecoverTrajectoryCode rechart witness =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart
    (endpointCollisionGivesTrajectoryNonfactorability witness)

------------------------------------------------------------------------
-- Concrete finite regression.
------------------------------------------------------------------------

data DemoState : Set where
  demoStart demoGoal : DemoState

data DemoRoute : Set where
  lowCostRoute highCostRoute : DemoRoute

demoStartOf : DemoRoute → DemoState
demoStartOf lowCostRoute = demoStart
demoStartOf highCostRoute = demoStart

demoFinishOf : DemoRoute → DemoState
demoFinishOf lowCostRoute = demoGoal
demoFinishOf highCostRoute = demoGoal

demoTrajectoryCode : DemoRoute → Nat
demoTrajectoryCode lowCostRoute = 3
demoTrajectoryCode highCostRoute = 8

demoSystem : EndpointTrajectorySystem
demoSystem =
  endpoint-trajectory-system
    DemoState
    DemoRoute
    demoStartOf
    demoFinishOf
    demoTrajectoryCode
    "Two finite routes share start and finish while retaining different path-sensitive codes."

demoSameEndpointDifferentCode :
  SameEndpointDifferentTrajectoryCode demoSystem
demoSameEndpointDifferentCode =
  same-endpoint-different-trajectory-code
    lowCostRoute
    highCostRoute
    refl
    refl
    (λ ())

demoTrajectoryDoesNotFactorThroughEndpoints :
  NF.NonFactorabilityWitness
    (endpointObserver demoSystem)
    (trajectoryCode demoSystem)
demoTrajectoryDoesNotFactorThroughEndpoints =
  endpointCollisionGivesTrajectoryNonfactorability
    demoSameEndpointDifferentCode

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record TrajectoryEndpointBoundary : Set where
  constructor trajectory-endpoint-boundary
  field
    endpointEqualityImpliesTrajectoryEquality : Bool
    endpointEqualityImpliesTrajectoryEqualityIsFalse :
      endpointEqualityImpliesTrajectoryEquality ≡ false

    endpointEqualityImpliesEqualTrajectoryCost : Bool
    endpointEqualityImpliesEqualTrajectoryCostIsFalse :
      endpointEqualityImpliesEqualTrajectoryCost ≡ false

    postprocessingEndpointsCanRecoverErasedPathCoordinate : Bool
    postprocessingEndpointsCanRecoverErasedPathCoordinateIsFalse :
      postprocessingEndpointsCanRecoverErasedPathCoordinate ≡ false

    everyTrajectoryConsumerIsAdditive : Bool
    everyTrajectoryConsumerIsAdditiveIsFalse :
      everyTrajectoryConsumerIsAdditive ≡ false

    finiteTrajectoryCodeImpliesLeastActionPrinciple : Bool
    finiteTrajectoryCodeImpliesLeastActionPrincipleIsFalse :
      finiteTrajectoryCodeImpliesLeastActionPrinciple ≡ false

canonicalTrajectoryEndpointBoundary : TrajectoryEndpointBoundary
canonicalTrajectoryEndpointBoundary =
  trajectory-endpoint-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
