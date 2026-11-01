module DASHI.Biology.WorldRegularityHyperformalismCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.WorldRepresentationSeparationExact as World
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerRelativeCoarseGrainingBidiExact as Coarse
import DASHI.Core.SituatedFormalisationBoundaryExact as Situated
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as WrongType
import DASHI.Biology.NaturalSystemsHyperfabricExact as Natural

------------------------------------------------------------------------
-- WORLD REGULARITY x WRONGTYPE x FACTORISATION x HYPERFABRIC
--
-- A hyperfabric cell carries distinct world, observation, representation and
-- consumer coordinates.  No scalar "truth" field collapses those coordinates.
------------------------------------------------------------------------

record WorldTheoryHyperfabricCell : Set where
  constructor world-theory-hyperfabric-cell
  field
    worldCoordinate : World.GravityWorldState
    observationCoordinate : World.FallObservation
    theoryCoordinate : World.GravityTheory
    naturalLayer : Natural.NaturalLayer
    coupling : Natural.CouplingKind
    admissibleForDeclaredUse : Bool
    consumerAdequateForDeclaredUse : Bool
    provenanceReference : String

open WorldTheoryHyperfabricCell public

birdFlightGravityCell : WorldTheoryHyperfabricCell
birdFlightGravityCell =
  world-theory-hyperfabric-cell
    World.lowCurvatureFall
    World.observedFall
    World.preFormalRegularity
    Natural.organismLayer
    Natural.mechanicalCoupling
    true
    true
    "World coupling precedes or bypasses explicit propositional gravity theory."

newtonianGravityCell : WorldTheoryHyperfabricCell
newtonianGravityCell =
  world-theory-hyperfabric-cell
    World.lowCurvatureFall
    World.observedFall
    World.newtonianRepresentation
    Natural.symbolicLayer
    Natural.mechanicalCoupling
    true
    true
    "A symbolic representation shares a world coordinate with non-symbolic world coupling."

relativisticGravityCellSameWorld : WorldTheoryHyperfabricCell
relativisticGravityCellSameWorld =
  world-theory-hyperfabric-cell
    World.lowCurvatureFall
    World.observedFall
    World.relativisticRepresentation
    Natural.symbolicLayer
    Natural.mechanicalCoupling
    true
    true
    "Theory delta does not entail world delta."

------------------------------------------------------------------------
-- Imported boundaries certify the cross-pollination direction.
------------------------------------------------------------------------

worldBoundary : World.WorldRepresentationBoundary
worldBoundary = World.canonicalWorldRepresentationBoundary

naturalBoundary : Natural.NaturalSystemsBoundary
naturalBoundary = Natural.canonicalNaturalSystemsBoundary

mdlBoundary : MDL.AdmissibleConsumerMDLBoundary
mdlBoundary = MDL.canonicalAdmissibleConsumerMDLBoundary

coarseBoundary : Coarse.ConsumerRelativeCoarseGrainingBoundary
coarseBoundary = Coarse.canonicalConsumerRelativeCoarseGrainingBoundary

situatedBoundary : Situated.SituatedFormalisationBoundary
situatedBoundary = Situated.canonicalSituatedFormalisationBoundary

wrongTypeBoundary : WrongType.CrossPollinationBoundary
wrongTypeBoundary = WrongType.canonicalCrossPollinationBoundary

gravityNonFactorability :
  INF.NonFactorabilityWitness
    World.coarseFallObservation
    World.gravityRegularity
gravityNonFactorability = World.gravityObservationNonFactorability

record WorldTheoryHyperfabricBoundary : Set where
  constructor world-theory-hyperfabric-boundary
  field
    hyperfabricKeepsOnticAndRepresentationalCoordinatesDistinct : Bool
    hyperfabricKeepsOnticAndRepresentationalCoordinatesDistinctIsTrue :
      hyperfabricKeepsOnticAndRepresentationalCoordinatesDistinct ≡ true
    admissibilityIsNotPhysicalTruth : Bool
    admissibilityIsNotPhysicalTruthIsTrue :
      admissibilityIsNotPhysicalTruth ≡ true
    singleObservationMayBeConsumerUsefulWithoutBeingWorldComplete : Bool
    singleObservationMayBeConsumerUsefulWithoutBeingWorldCompleteIsTrue :
      singleObservationMayBeConsumerUsefulWithoutBeingWorldComplete ≡ true
    intersectionalNonFactorabilitySuppliesCollisionTest : Bool
    intersectionalNonFactorabilitySuppliesCollisionTestIsTrue :
      intersectionalNonFactorabilitySuppliesCollisionTest ≡ true
    wrongTypePreventsTheoryWorldCollapse : Bool
    wrongTypePreventsTheoryWorldCollapseIsTrue :
      wrongTypePreventsTheoryWorldCollapse ≡ true
    organismCouplingCanPrecedeSymbolicTheory : Bool
    organismCouplingCanPrecedeSymbolicTheoryIsTrue :
      organismCouplingCanPrecedeSymbolicTheory ≡ true

open WorldTheoryHyperfabricBoundary public

canonicalWorldTheoryHyperfabricBoundary : WorldTheoryHyperfabricBoundary
canonicalWorldTheoryHyperfabricBoundary =
  world-theory-hyperfabric-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
