module DASHI.Physics.Chemistry.ChiralFutureFactorisationSpineExact where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Core.FactorisationSpineCrosswalkExact as Spine
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics

------------------------------------------------------------------------
-- CANONICAL CONSUMER/NON-DESCENT CROSSWALK
--
-- The first chemistry owner contained a local no-factor theorem.  This module
-- pays the repo-wide integration debt by expressing the same witnessed failure
-- through the canonical ProjectionCollision / ConsumerNonDescentWitness spine.
------------------------------------------------------------------------

futureSeedCollision :
  Coarse.ProjectionCollision
    Dynamics.coarseChemicalChart
    Dynamics.futureAfterStep
futureSeedCollision =
  Coarse.projectionCollision
    Dynamics.leftSeed
    Dynamics.rightSeed
    Dynamics.sameCoarseSeeds
    Dynamics.futureSeedsSeparate

futureConsumerNonDescent :
  Descent.ConsumerNonDescentWitness
    Dynamics.coarseChemicalChart
    Dynamics.futureAfterStep
futureConsumerNonDescent =
  Spine.projectionCollisionToNonDescent futureSeedCollision

futureCollisionBlocksEveryCanonicalFactorisation :
  (coarseReadout : Dynamics.CoarseChemicalChart → Dynamics.FutureBranchReadout) →
  ((x : Dynamics.ChiralBiasState) →
    Dynamics.futureAfterStep x
      ≡ coarseReadout (Dynamics.coarseChemicalChart x)) →
  ⊥
futureCollisionBlocksEveryCanonicalFactorisation =
  Coarse.consumerCannotFactorThroughProjection futureSeedCollision

anySufficientRepairMustSeparateChiralSeeds :
  ∀ {Refinement : Set}
    {refine : Dynamics.ChiralBiasState → Refinement} →
  Repair.RefinementRepairs
    Dynamics.coarseChemicalChart
    refine
    Dynamics.futureAfterStep →
  refine Dynamics.leftSeed ≡ refine Dynamics.rightSeed →
  ⊥
anySufficientRepairMustSeparateChiralSeeds =
  Spine.projectionCollisionRepairRequiresSeparation futureSeedCollision

record ChiralFutureFactorisationBoundary : Set where
  constructor chiralFutureFactorisationBoundary
  field
    localChemistryNoFactorWitnessCrosswalkedToCore : Bool
    predictiveSufficiencyIsConsumerRelative : Bool
    everySufficientRepairMustSeparateWitnessedSeeds : Bool
    seedSeparationAloneProvesGlobalPredictiveSufficiency : Bool
    coarseCompositionConnectivityChargeIsGloballyUseless : Bool

canonicalChiralFutureFactorisationBoundary : ChiralFutureFactorisationBoundary
canonicalChiralFutureFactorisationBoundary =
  chiralFutureFactorisationBoundary true true true false false
