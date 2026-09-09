module DASHI.Interop.SensibLawNatCoverageAcquisitionDemandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ZelphBoundedGraphCoverageExact as Coverage
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- NAT Q/P COVERAGE RESIDUAL -> ACQUISITION DEMAND
--
-- Consumer-side descriptor for the exact property-family coordinate blocking a
-- Nat classification. It intentionally does not import the #823-only generic
-- BoundAcquisitionDemand/IntrospectiveProofLoop owners until that branch lands
-- on master; the dependent compatibility weld remains explicit below.
------------------------------------------------------------------------

data NatCoverageCoordinate : Set where
  subjectTypeFamily : NatCoverageCoordinate
  sourcePropertyFamily : NatCoverageCoordinate
  targetPropertyFamily : NatCoverageCoordinate
  qualifierProfileFamily : NatCoverageCoordinate
  referenceFamily : NatCoverageCoordinate
  temporalFamily : NatCoverageCoordinate

producerForCoverageCoordinate : NatCoverageCoordinate → Search.ProducerClass
producerForCoverageCoordinate subjectTypeFamily = Search.identityProducer
producerForCoverageCoordinate sourcePropertyFamily = Search.empiricalEvidenceProducer
producerForCoverageCoordinate targetPropertyFamily = Search.empiricalEvidenceProducer
producerForCoverageCoordinate qualifierProfileFamily = Search.empiricalEvidenceProducer
producerForCoverageCoordinate referenceFamily = Search.propositionSourceProducer
producerForCoverageCoordinate temporalFamily = Search.temporalProducer

record NatCoverageResidual : Set where
  constructor nat-coverage-residual
  field
    subjectQidReference : String
    propertyReference : String
    coverageStatus : Coverage.QueryCoverageStatus
    coordinate : NatCoverageCoordinate
    graphRevisionReference : String
    coveragePolicyReference : String
    consumerReference : String
    residualReference : String
open NatCoverageResidual public

record NatCoverageAcquisitionDemand (residual : NatCoverageResidual) : Set where
  constructor nat-coverage-acquisition-demand
  field
    producer : Search.ProducerClass
    producerMatchesCoordinate : producer ≡ producerForCoverageCoordinate (coordinate residual)
    exactSubjectReference : String
    exactPropertyReference : String
    requiredRepresentationReference : String
    requiresNativeFullStatementFamily : Bool
    requiresNativeFullStatementFamilyIsTrue : requiresNativeFullStatementFamily ≡ true
    truthyProjectionSufficesForCoverage : Bool
    truthyProjectionSufficesForCoverageIsFalse : truthyProjectionSufficesForCoverage ≡ false
    acquisitionReference : String
open NatCoverageAcquisitionDemand public

-- Concrete live example: an uninspected P14143 family cannot be paid by a P31
-- fetch, a peer-item fetch, a merely successful shard transport, or the truthy
-- projection of P14143. Coverage is over the native full statement family.
p14143UninspectedResidual : NatCoverageResidual
p14143UninspectedResidual =
  nat-coverage-residual
    "current Nat subject QID"
    "P14143"
    Coverage.queryCoverageUninspected
    targetPropertyFamily
    "current graph revision"
    "Nat P5991->P14143 coverage policy"
    "Nat migration peer/target-property consumer"
    "P14143 target property family has not been inspected under the current revision/policy"

p14143UninspectedDemand : NatCoverageAcquisitionDemand p14143UninspectedResidual
p14143UninspectedDemand =
  nat-coverage-acquisition-demand
    Search.empiricalEvidenceProducer
    refl
    "the same Nat subject QID"
    "P14143"
    "native full statement-family coverage including every rank and native snak kind, or a certified representation complete for the P14143 query family"
    true
    refl
    false
    refl
    "acquire exactly the P14143 Q/P family required by the live Nat residual"

------------------------------------------------------------------------
-- Payment is downstream of acquisition. A returned row, successful transport,
-- or complete coverage for another property does not close this residual.
------------------------------------------------------------------------

data ShardTransportPaysCoverageResidual : Set where
data OtherPropertyCoveragePaysP14143 : Set where
data ReturnedRowPaysCoverageResidual : Set where
data TruthyProjectionPaysNativeFamilyCoverage : Set where
data AcquisitionDemandCreatesMigrationAuthority : Set where

shardTransportDoesNotPayCoverageResidual : ShardTransportPaysCoverageResidual → ⊥
shardTransportDoesNotPayCoverageResidual ()

otherPropertyDoesNotPayP14143Residual : OtherPropertyCoveragePaysP14143 → ⊥
otherPropertyDoesNotPayP14143Residual ()

returnedRowDoesNotPayCoverageResidualByExistence : ReturnedRowPaysCoverageResidual → ⊥
returnedRowDoesNotPayCoverageResidualByExistence ()

truthyProjectionDoesNotPayNativeFamilyCoverage : TruthyProjectionPaysNativeFamilyCoverage → ⊥
truthyProjectionDoesNotPayNativeFamilyCoverage ()

acquisitionDemandDoesNotCreateMigrationAuthority : AcquisitionDemandCreatesMigrationAuthority → ⊥
acquisitionDemandDoesNotCreateMigrationAuthority ()

------------------------------------------------------------------------
-- Native family vs native snak semantics.
--
-- Cross-pollinated from the attached Aristotle archive:
-- * rank/truthy filtering is downstream visibility and can hide normal or
--   deprecated statements, so it cannot establish native family coverage;
-- * value / somevalue / novalue are all native statements. In particular an
--   explicit novalue is family-present and must never be conflated with the
--   property family being absent from the entity claims map.
------------------------------------------------------------------------

data PropertyFamilyObservation : Set where
  familyPresent : PropertyFamilyObservation
  familyAbsent : PropertyFamilyObservation

data NativeSnakKind : Set where
  concreteValue : NativeSnakKind
  someValue : NativeSnakKind
  noValue : NativeSnakKind

record NativeSnakSummary : Set where
  constructor native-snak-summary
  field
    concreteValueObserved : Bool
    someValueObserved : Bool
    noValueObserved : Bool
open NativeSnakSummary public

data NoValueEqualsFamilyAbsent : Set where
data SomeValueEqualsConcreteValue : Set where

noValueDoesNotMeanFamilyAbsent : NoValueEqualsFamilyAbsent → ⊥
noValueDoesNotMeanFamilyAbsent ()

someValueDoesNotMeanConcreteValue : SomeValueEqualsConcreteValue → ⊥
someValueDoesNotMeanConcreteValue ()

------------------------------------------------------------------------
-- Exact recomputation receipt.
--
-- Runtime counterpart on SensibLaw #493:
--   live residual -> bound shared acquisition -> QID-local projected entity
--   snapshot -> exact native property-family recomputation.
--
-- The entity snapshot is useful only when the same Q, same P and same revision
-- are retained and the representation is certified complete for that exact
-- query family. Under those conditions both family-present and family-absent
-- are valid coverage outcomes. This pays only the coverage coordinate.
------------------------------------------------------------------------

record ExactCoverageRecomputation
    (residual : NatCoverageResidual) : Set where
  constructor exact-coverage-recomputation
  field
    observedSubjectReference : String
    observedSubjectIsExact :
      observedSubjectReference ≡ subjectQidReference residual
    observedPropertyReference : String
    observedPropertyIsExact :
      observedPropertyReference ≡ propertyReference residual
    observedRevisionReference : String
    observedRevisionIsExact :
      observedRevisionReference ≡ graphRevisionReference residual
    coverageUsesNativeFullStatementFamily : Bool
    coverageUsesNativeFullStatementFamilyIsTrue :
      coverageUsesNativeFullStatementFamily ≡ true
    truthyProjectionUsedForCoverage : Bool
    truthyProjectionUsedForCoverageIsFalse :
      truthyProjectionUsedForCoverage ≡ false
    representationCompleteForExactFamily : Bool
    representationCompleteForExactFamilyIsTrue :
      representationCompleteForExactFamily ≡ true
    familyObservation : PropertyFamilyObservation
    snakSummary : NativeSnakSummary
    recomputedCoverageStatus : Coverage.QueryCoverageStatus
    recomputedCoverageIsComplete :
      recomputedCoverageStatus ≡ Coverage.queryCoverageComplete
    sourceSupportPaid : Bool
    sourceSupportPaidIsFalse : sourceSupportPaid ≡ false
    sourceAuthorityEvaluationRequired : Bool
    sourceAuthorityEvaluationRequiredIsTrue :
      sourceAuthorityEvaluationRequired ≡ true
    consumerVerificationPerformed : Bool
    consumerVerificationPerformedIsFalse :
      consumerVerificationPerformed ≡ false
    migrationAuthority : Bool
    migrationAuthorityIsFalse : migrationAuthority ≡ false
    semanticPromotionPerformed : Bool
    semanticPromotionPerformedIsFalse : semanticPromotionPerformed ≡ false
open ExactCoverageRecomputation public

coverageCoordinatePaidByExactRecomputation :
  {residual : NatCoverageResidual} →
  (receipt : ExactCoverageRecomputation residual) →
  recomputedCoverageStatus receipt ≡ Coverage.queryCoverageComplete
coverageCoordinatePaidByExactRecomputation = recomputedCoverageIsComplete

-- Present and absent are both observations under a complete exact-family view;
-- neither proposition says anything about source support or migration safety.
record CoverageCoordinatePayment
    (residual : NatCoverageResidual) : Set where
  constructor coverage-coordinate-payment
  field
    recomputation : ExactCoverageRecomputation residual
    paidResidualReference : String
    coverageCoordinatePaid : Bool
    coverageCoordinatePaidIsTrue : coverageCoordinatePaid ≡ true
    sourceSupportStillSeparate : Bool
    sourceSupportStillSeparateIsTrue : sourceSupportStillSeparate ≡ true
open CoverageCoordinatePayment public

data CoveragePaymentPaysSourceSupport : Set where
data CoveragePaymentClosesConsumer : Set where
data CoveragePaymentCreatesMigrationAuthority : Set where

data ReferencePresencePaysSourceSupport : Set where

coveragePaymentDoesNotPaySourceSupport : CoveragePaymentPaysSourceSupport → ⊥
coveragePaymentDoesNotPaySourceSupport ()

coveragePaymentDoesNotCloseConsumer : CoveragePaymentClosesConsumer → ⊥
coveragePaymentDoesNotCloseConsumer ()

coveragePaymentDoesNotCreateMigrationAuthority :
  CoveragePaymentCreatesMigrationAuthority → ⊥
coveragePaymentDoesNotCreateMigrationAuthority ()

referencePresenceDoesNotPaySourceSupport : ReferencePresencePaysSourceSupport → ⊥
referencePresenceDoesNotPaySourceSupport ()

------------------------------------------------------------------------
-- Runtime/formal boundary summary.
------------------------------------------------------------------------

record NatCoverageAcquisitionBoundary : Set where
  constructor nat-coverage-acquisition-boundary
  field
    demandIndexedByExactSubjectPropertyResidual : Bool
    producerDerivedFromMissingCoordinate : Bool
    transportEqualsCoveragePayment : Bool
    anotherPropertyCanPayTargetPropertyResidual : Bool
    returnedRowEqualsCoveragePayment : Bool
    truthyProjectionEqualsNativeFamilyCoverage : Bool
    noValueEqualsFamilyAbsence : Bool
    referencePresenceEqualsSourceSupport : Bool
    demandCreatesMigrationAuthority : Bool
    recomputationStillRequiredAfterAcquisition : Bool
    exactRecomputationMayPayCoverageCoordinate : Bool
    coveragePaymentPaysSourceSupport : Bool
    coveragePaymentClosesConsumer : Bool
    coveragePaymentCreatesMigrationAuthority : Bool
    pending823WeldExplicit : Bool

canonicalNatCoverageAcquisitionBoundary : NatCoverageAcquisitionBoundary
canonicalNatCoverageAcquisitionBoundary =
  nat-coverage-acquisition-boundary
    true true false false false false false false false true true false false false true
