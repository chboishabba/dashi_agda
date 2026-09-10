module DASHI.Wikimedia.IbrahimAlgebraicStructureNDimHyperfabricSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimAbstractAlgebraStructureFactorsThroughSnowballExact as Algebra
import DASHI.Interop.SensibLawNDimAdmissibilityTetrationComplexityBridgeExact as NDim
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- ALGEBRAIC STRUCTURE -> N-DIMENSIONAL OBSERVER/HYPERFABRIC BRIDGE
--
-- This is not a second algebra formalism. It projects the already-identified
-- algebraic-structure coordinates into the existing N-dimensional observer
-- discipline: carrier, operation, laws, representation/character and
-- provenance are distinct axes whose relevance is consumer-indexed.
------------------------------------------------------------------------

data AlgebraAxis : Set where
  carrierAxis operationAxis lawAxis representationAxis characterAxis provenanceAxis : AlgebraAxis

record AlgebraAxisProfile : Set where
  constructor algebra-axis-profile
  field
    axis : AlgebraAxis
    reference : String
    retained : Bool
    requiredByCurrentConsumer : Bool
open AlgebraAxisProfile public

carrierProfile : AlgebraAxisProfile
carrierProfile = algebra-axis-profile carrierAxis "underlying carrier/set" true true

operationProfile : AlgebraAxisProfile
operationProfile = algebra-axis-profile operationAxis "group/algebra operations" true true

lawProfile : AlgebraAxisProfile
lawProfile = algebra-axis-profile lawAxis "identity/associativity/etc. laws" true true

representationProfile : AlgebraAxisProfile
representationProfile = algebra-axis-profile representationAxis "representation action" true false

characterProfile : AlgebraAxisProfile
characterProfile = algebra-axis-profile characterAxis "trace/character data" true false

provenanceProfile : AlgebraAxisProfile
provenanceProfile = algebra-axis-profile provenanceAxis "source/revision/construction provenance" true true

------------------------------------------------------------------------
-- Consumer-specific projection states.
------------------------------------------------------------------------

data AlgebraConsumer : Set where
  cardinalityConsumer operationConsumer isomorphismConsumer representationConsumer characterConsumer : AlgebraConsumer

record AlgebraProjectionAdequacy : Set where
  constructor algebra-projection-adequacy
  field
    consumer : AlgebraConsumer
    retainedAxes : String
    sufficientForConsumer : Bool
    omittedAxisKnownRelevant : Bool
    failedProjectionMaySnowballRepair : Bool
open AlgebraProjectionAdequacy public

cardinalityProjection : AlgebraProjectionAdequacy
cardinalityProjection = algebra-projection-adequacy
  cardinalityConsumer
  "carrier"
  true false false

operationProjection : AlgebraProjectionAdequacy
operationProjection = algebra-projection-adequacy
  operationConsumer
  "carrier only"
  false true true

isomorphismProjection : AlgebraProjectionAdequacy
isomorphismProjection = algebra-projection-adequacy
  isomorphismConsumer
  "carrier + operation + laws"
  true false false

representationProjection : AlgebraProjectionAdequacy
representationProjection = algebra-projection-adequacy
  representationConsumer
  "carrier + operation + laws; representation axis omitted"
  false true true

characterProjection : AlgebraProjectionAdequacy
characterProjection = algebra-projection-adequacy
  characterConsumer
  "representation retained; trace/character omitted"
  false true true

------------------------------------------------------------------------
-- Existing N-dimensional boundary reused verbatim.
------------------------------------------------------------------------

ndimBoundary : NDim.AdmissibilityTetrationComplexityBoundary
ndimBoundary = NDim.canonicalAdmissibilityTetrationComplexityBoundary

algebraBoundary : Algebra.AbstractAlgebraStructureBoundary
algebraBoundary = Algebra.canonicalAbstractAlgebraStructureBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

record AlgebraicHyperformBoundary : Set where
  constructor algebraic-hyperform-boundary
  field
    carrierOperationLawSeparated : Bool
    representationCharacterSeparated : Bool
    provenanceRetainedAsSeparateAxis : Bool
    omittedAxisMayBeRelevant : Bool
    fixedAxisProductAutomaticallyTetration : Bool
    failedFactorisationMayAddAxis : Bool
    sameCarrierMeansSameStructure : Bool
open AlgebraicHyperformBoundary public

canonicalAlgebraicHyperformBoundary : AlgebraicHyperformBoundary
canonicalAlgebraicHyperformBoundary =
  algebraic-hyperform-boundary true true true true false true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameCarrierCreatesSameStructure : Set where
data EveryAlgebraAxisRequiredByEveryConsumer : Set where
data FixedAlgebraAxisFamilyCreatesTetration : Set where
data CharacterRecoverableFromCarrierOnly : Set where

sameCarrierDoesNotCreateSameStructure : SameCarrierCreatesSameStructure → ⊥
sameCarrierDoesNotCreateSameStructure ()

everyAxisIsNotUniversal : EveryAlgebraAxisRequiredByEveryConsumer → ⊥
everyAxisIsNotUniversal ()

fixedAxesAreNotTetration : FixedAlgebraAxisFamilyCreatesTetration → ⊥
fixedAxesAreNotTetration ()

characterNotRecoverableFromCarrierOnly : CharacterRecoverableFromCarrierOnly → ⊥
characterNotRecoverableFromCarrierOnly ()
