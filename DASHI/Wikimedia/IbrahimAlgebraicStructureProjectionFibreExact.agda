module DASHI.Wikimedia.IbrahimAlgebraicStructureProjectionFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionFibre as Fibre
import DASHI.Wikimedia.IbrahimAbstractAlgebraStructureFactorsThroughSnowballExact as Algebra
import DASHI.Wikimedia.IbrahimAlgebraicStructureNDimHyperfabricSnowballExact as Hyper
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- Q205464 ALGEBRAIC STRUCTURE -> REPO-NATIVE PROJECTION FIBRE
--
-- ProjectionFibre already owns the exact generic geometry needed here:
--   Carrier --pi--> Observable
-- with fibres of hidden carrier states collapsing to one observable point.
-- The algebraic-structure snowball specializes the reading:
--   whole structure -> carrier-only observable
-- where operation/law/representation/character coordinates may be hidden.
--
-- This module deliberately does not claim that Wikidata constructs a formal
-- forgetful functor.  The external graph discovers the carrier/operation
-- distinction; the projection/fibre mathematics comes from DASHI.
------------------------------------------------------------------------

record AlgebraicProjectionFibreReading : Set where
  constructor algebraic-projection-fibre-reading
  field
    externalSubject : String
    externalQid : String
    repoProjectionOwner : String
    carrierCoordinateVisible : Bool
    operationCoordinateMayBeHidden : Bool
    lawCoordinateMayBeHidden : Bool
    representationCoordinateMayBeHidden : Bool
    characterCoordinateMayBeHidden : Bool
    sameObservablePermitsDistinctCarrierStates : Bool
    observationalEquivalenceCreatesIdentity : Bool
open AlgebraicProjectionFibreReading public

canonicalAlgebraicProjectionFibreReading : AlgebraicProjectionFibreReading
canonicalAlgebraicProjectionFibreReading = algebraic-projection-fibre-reading
  "algebraic structure"
  "Q205464"
  "DASHI.Core.ProjectionFibre"
  true true true true true true false

------------------------------------------------------------------------
-- Existing repo-native projection witness is retained as the abstraction
-- source. It is intentionally the trivial canonical instance; this module is
-- a semantic specialization boundary, not a fabricated concrete category of
-- all algebraic structures.
------------------------------------------------------------------------

projectionFibreOwner : Fibre.ProjectionFibre PC.canonicalProjectionCategory
projectionFibreOwner = Fibre.canonicalProjectionFibre

record ConsumerFibreStatus : Set where
  constructor consumer-fibre-status
  field
    cardinalityQueryMayUseCarrierProjection : Bool
    operationQueryNeedsOperationAxis : Bool
    lawQueryNeedsLawAxis : Bool
    representationQueryNeedsRepresentationAxis : Bool
    characterQueryNeedsCharacterAxis : Bool
    hiddenFibreCanWitnessNonfactorability : Bool
    failedFactorisationCanSnowballMissingAxis : Bool
    projectionFibreCreatesWholeStructure : Bool
open ConsumerFibreStatus public

canonicalConsumerFibreStatus : ConsumerFibreStatus
canonicalConsumerFibreStatus = consumer-fibre-status
  true true true true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameObservableCreatesSameAlgebra : Set where
data UnderlyingCarrierRecoversOperation : Set where
data ProjectionFibreCreatesExternalQidSemantics : Set where
data ExternalUnderlyingSetRelationCreatesFormalFunctor : Set where

sameObservableDoesNotCreateSameAlgebra : SameObservableCreatesSameAlgebra → ⊥
sameObservableDoesNotCreateSameAlgebra ()

carrierDoesNotRecoverOperation : UnderlyingCarrierRecoversOperation → ⊥
carrierDoesNotRecoverOperation ()

projectionDoesNotCreateQidSemantics : ProjectionFibreCreatesExternalQidSemantics → ⊥
projectionDoesNotCreateQidSemantics ()

qidRelationDoesNotCreateFunctor : ExternalUnderlyingSetRelationCreatesFormalFunctor → ⊥
qidRelationDoesNotCreateFunctor ()

algebraBoundary : Algebra.AbstractAlgebraStructureBoundary
algebraBoundary = Algebra.canonicalAbstractAlgebraStructureBoundary

hyperfabricBoundary : Hyper.AlgebraicHyperformBoundary
hyperfabricBoundary = Hyper.canonicalAlgebraicHyperformBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
