module DASHI.Wikimedia.IbrahimAbstractAlgebraStructureFactorsThroughSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Suff
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Wikimedia.IbrahimPartitionSymmetricGroupRepresentationSnowballExact as Symmetric

------------------------------------------------------------------------
-- ABSTRACT ALGEBRA / ALGEBRAIC STRUCTURE / FACTORSTHROUGH SNOWBALL
--
-- External coordinates inspected 2026-09-11:
--   abstract algebra      Q159943
--   algebraic structure   Q205464
--   symmetric group       Q849512
--
-- Wikidata describes Q159943 as a branch of mathematics studying algebraic
-- structures and Q205464 as a mathematical structure with underlying set and
-- mathematical operations.  Those coordinates are vocabulary/navigation, not
-- proof authority.  DASHI's existing query-relative FactorsThrough machinery
-- supplies the formal distinction between a sufficient projection and a claim
-- of complete structural preservation.
------------------------------------------------------------------------

abstractAlgebraQid : Identity.ExternalIdentityDemand
abstractAlgebraQid = Identity.mkOptionalIdentityDemand
  "abstract-algebra structure snowball"
  "abstract algebra external identity"
  "abstract algebra"
  Identity.wikidataQid
  (Identity.verified "Q159943" "Wikidata oldid 2509231927 inspected 2026-09-11")

algebraicStructureQid : Identity.ExternalIdentityDemand
algebraicStructureQid = Identity.mkOptionalIdentityDemand
  "abstract-algebra structure snowball"
  "algebraic structure external identity"
  "algebraic structure"
  Identity.wikidataQid
  (Identity.verified "Q205464" "Wikidata inspected 2026-09-11")

------------------------------------------------------------------------
-- Minimal finite regression: two structures can have the same underlying
-- carrier/cardinality but different operations.  Carrier-only projection is
-- therefore query-relative, not structure-complete.
------------------------------------------------------------------------

data Carrier2 : Set where
  a b : Carrier2

data OperationKind : Set where
  leftProjection rightProjection : OperationKind

record TwoPointAlgebra : Set where
  constructor two-point-algebra
  field
    operationKind : OperationKind
open TwoPointAlgebra public

leftStructure : TwoPointAlgebra
leftStructure = two-point-algebra leftProjection

rightStructure : TwoPointAlgebra
rightStructure = two-point-algebra rightProjection

data CarrierSurface : Set where
  sameTwoPointCarrier : CarrierSurface

forgetOperation : TwoPointAlgebra → CarrierSurface
forgetOperation _ = sameTwoPointCarrier

data StructureQuery : Set where
  carrierCardinalityQuery operationIdentityQuery : StructureQuery

data StructureAnswer : Set where
  cardinalityTwo leftOperationAnswer rightOperationAnswer : StructureAnswer

structureQuestions : Suff.InquiryQuestionFamily TwoPointAlgebra StructureQuery
structureQuestions = Suff.inquiryQuestionFamily (λ _ → StructureAnswer) ask
  where
    ask : StructureQuery → TwoPointAlgebra → StructureAnswer
    ask carrierCardinalityQuery _ = cardinalityTwo
    ask operationIdentityQuery (two-point-algebra leftProjection) = leftOperationAnswer
    ask operationIdentityQuery (two-point-algebra rightProjection) = rightOperationAnswer

carrierQueryFactorsThroughUnderlyingSet :
  Suff.FactorsThrough structureQuestions forgetOperation carrierCardinalityQuery
carrierQueryFactorsThroughUnderlyingSet = Suff.factorsThrough answer proof
  where
    answer : CarrierSurface → StructureAnswer
    answer sameTwoPointCarrier = cardinalityTwo

    proof : (s : TwoPointAlgebra) →
      Suff.ask structureQuestions carrierCardinalityQuery s ≡
      answer (forgetOperation s)
    proof (two-point-algebra leftProjection) = refl
    proof (two-point-algebra rightProjection) = refl

------------------------------------------------------------------------
-- We retain the non-factorability of the operation query as an explicit
-- snowball status rather than fabricating a quotient answer from the carrier.
------------------------------------------------------------------------

record StructureProjectionAudit : Set where
  constructor structure-projection-audit
  field
    carrierCardinalityFactorsThroughCarrierOnly : Bool
    operationIdentityFactorsThroughCarrierOnly : Bool
    sameUnderlyingSetImpliesSameAlgebra : Bool
    sameCardinalityImpliesIsomorphicAlgebra : Bool
    wikidataUnderlyingSetCreatesFormalForgetfulFunctor : Bool
    failedOperationFactorisationMaySnowballOperationAxis : Bool
    symmetricGroupNeedsOperationComposition : Bool
open StructureProjectionAudit public

canonicalStructureProjectionAudit : StructureProjectionAudit
canonicalStructureProjectionAudit = structure-projection-audit
  true false false false false true true

------------------------------------------------------------------------
-- Typed graph roles.
------------------------------------------------------------------------

data EdgeRole : Set where
  currentFirstBody wikidataStudyRelation wikidataUnderlyingData
  repositoryFactorisationBridge symmetricGroupSpecialization : EdgeRole

record TypedEdge : Set where
  constructor typed-edge
  field
    source : String
    target : String
    role : EdgeRole
    evidence : String
    createsFormalDependency : Bool
open TypedEdge public

abstractAlgebraToStructure : TypedEdge
abstractAlgebraToStructure = typed-edge
  "Abstract algebra/Q159943"
  "Algebraic structure/Q205464"
  wikidataStudyRelation
  "Q159943 is the study of algebraic structure; Q205464 is studied by abstract algebra"
  false

structureToUnderlyingSet : TypedEdge
structureToUnderlyingSet = typed-edge
  "Algebraic structure/Q205464"
  "underlying set"
  wikidataUnderlyingData
  "Q205464 exposes set as underlying structure and mathematical operation as underlying data"
  false

symmetricToAbstractAlgebra : TypedEdge
symmetricToAbstractAlgebra = typed-edge
  "Symmetric group/Q849512"
  "Abstract algebra/Q159943"
  currentFirstBody
  "current EN Symmetric group first body link is Abstract algebra"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data UnderlyingSetCreatesWholeAlgebra : Set where
data SameCardinalityCreatesIsomorphism : Set where
data QidRelationCreatesFunctor : Set where
data StaticSufficiencyCreatesWorldCoverage : Set where

data SymmetricGroupFollowsFromAnyAlgebraicStructure : Set where

underlyingSetDoesNotCreateWholeAlgebra : UnderlyingSetCreatesWholeAlgebra → ⊥
underlyingSetDoesNotCreateWholeAlgebra ()

sameCardinalityDoesNotCreateIsomorphism : SameCardinalityCreatesIsomorphism → ⊥
sameCardinalityDoesNotCreateIsomorphism ()

qidDoesNotCreateFunctor : QidRelationCreatesFunctor → ⊥
qidDoesNotCreateFunctor ()

staticSufficiencyDoesNotCreateWorldCoverage : StaticSufficiencyCreatesWorldCoverage → ⊥
staticSufficiencyDoesNotCreateWorldCoverage ()

arbitraryAlgebraDoesNotCreateSymmetricGroup : SymmetricGroupFollowsFromAnyAlgebraicStructure → ⊥
arbitraryAlgebraDoesNotCreateSymmetricGroup ()

record AbstractAlgebraStructureBoundary : Set where
  constructor abstract-algebra-structure-boundary
  field
    qidsRetained : Bool
    queryRelativeFactorisationReused : Bool
    carrierQueryPositiveWitnessPaid : Bool
    operationQueryCarrierOnlyRejected : Bool
    failedFactorisationSnowballsMissingOperationAxis : Bool
    allPairsEnabled : Bool
    externalGraphCreatesAuthority : Bool
open AbstractAlgebraStructureBoundary public

canonicalAbstractAlgebraStructureBoundary : AbstractAlgebraStructureBoundary
canonicalAbstractAlgebraStructureBoundary =
  abstract-algebra-structure-boundary true true true true true true false

symmetricBoundary : Symmetric.SymmetricRepresentationFrontier
symmetricBoundary = Symmetric.currentSymmetricRepresentationFrontier

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
