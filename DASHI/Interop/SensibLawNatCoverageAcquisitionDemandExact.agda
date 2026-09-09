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
-- Acquisition firewalls.
------------------------------------------------------------------------

data ShardTransportPaysCoverageResidual : Set where
data OtherPropertyCoveragePaysP14143 : Set where
data ReturnedRowPaysCoverageResidual : Set where
data TruthyProjectionPaysNativeFamilyCoverage : Set where
data DerivedPropertyRelationPaysNativeFamilyCoverage : Set where
data AcquisitionDemandCreatesMigrationAuthority : Set where

shardTransportDoesNotPayCoverageResidual : ShardTransportPaysCoverageResidual → ⊥
shardTransportDoesNotPayCoverageResidual ()

otherPropertyDoesNotPayP14143Residual : OtherPropertyCoveragePaysP14143 → ⊥
otherPropertyDoesNotPayP14143Residual ()

returnedRowDoesNotPayCoverageResidualByExistence : ReturnedRowPaysCoverageResidual → ⊥
returnedRowDoesNotPayCoverageResidualByExistence ()

truthyProjectionDoesNotPayNativeFamilyCoverage : TruthyProjectionPaysNativeFamilyCoverage → ⊥
truthyProjectionDoesNotPayNativeFamilyCoverage ()

derivedPropertyRelationDoesNotPayNativeFamilyCoverage :
  DerivedPropertyRelationPaysNativeFamilyCoverage → ⊥
derivedPropertyRelationDoesNotPayNativeFamilyCoverage ()

acquisitionDemandDoesNotCreateMigrationAuthority : AcquisitionDemandCreatesMigrationAuthority → ⊥
acquisitionDemandDoesNotCreateMigrationAuthority ()

------------------------------------------------------------------------
-- Native family vs native snak semantics.
--
-- Aristotle cross-pollination:
-- * truthy rank filtering is a visibility projection, not native-family coverage;
-- * value / somevalue / novalue are all native statements;
-- * qualifier conformance, property scope and property-engine derivability are
--   separate consumers even after the native Q/P family has been observed.
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

data CoveragePaymentPaysRankVisibility : Set where
data CoveragePaymentPaysQualifierConstraints : Set where
data CoveragePaymentPaysPropertyScope : Set where
data CoveragePaymentPaysPropertyDerivability : Set where

noValueDoesNotMeanFamilyAbsent : NoValueEqualsFamilyAbsent → ⊥
noValueDoesNotMeanFamilyAbsent ()

someValueDoesNotMeanConcreteValue : SomeValueEqualsConcreteValue → ⊥
someValueDoesNotMeanConcreteValue ()

coveragePaymentDoesNotPayRankVisibility : CoveragePaymentPaysRankVisibility → ⊥
coveragePaymentDoesNotPayRankVisibility ()

coveragePaymentDoesNotPayQualifierConstraints : CoveragePaymentPaysQualifierConstraints → ⊥
coveragePaymentDoesNotPayQualifierConstraints ()

coveragePaymentDoesNotPayPropertyScope : CoveragePaymentPaysPropertyScope → ⊥
coveragePaymentDoesNotPayPropertyScope ()

coveragePaymentDoesNotPayPropertyDerivability : CoveragePaymentPaysPropertyDerivability → ⊥
coveragePaymentDoesNotPayPropertyDerivability ()

------------------------------------------------------------------------
-- Exact recomputation receipt.
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
    derivedPropertyRelationUsedForCoverage : Bool
    derivedPropertyRelationUsedForCoverageIsFalse :
      derivedPropertyRelationUsedForCoverage ≡ false
    representationCompleteForExactFamily : Bool
    representationCompleteForExactFamilyIsTrue :
      representationCompleteForExactFamily ≡ true
    familyObservation : PropertyFamilyObservation
    snakSummary : NativeSnakSummary
    recomputedCoverageStatus : Coverage.QueryCoverageStatus
    recomputedCoverageIsComplete :
      recomputedCoverageStatus ≡ Coverage.queryCoverageComplete
    rankVisibilityEvaluated : Bool
    rankVisibilityEvaluatedIsFalse : rankVisibilityEvaluated ≡ false
    qualifierConstraintsEvaluated : Bool
    qualifierConstraintsEvaluatedIsFalse : qualifierConstraintsEvaluated ≡ false
    propertyScopeEvaluated : Bool
    propertyScopeEvaluatedIsFalse : propertyScopeEvaluated ≡ false
    propertyDerivabilityEvaluated : Bool
    propertyDerivabilityEvaluatedIsFalse : propertyDerivabilityEvaluated ≡ false
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
    derivedPropertyRelationEqualsNativeFamilyCoverage : Bool
    noValueEqualsFamilyAbsence : Bool
    referencePresenceEqualsSourceSupport : Bool
    coveragePaymentPaysRankVisibility : Bool
    coveragePaymentPaysQualifierConstraints : Bool
    coveragePaymentPaysPropertyScope : Bool
    coveragePaymentPaysPropertyDerivability : Bool
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
    true true false false false false false false false false false false false false true true false false false true
