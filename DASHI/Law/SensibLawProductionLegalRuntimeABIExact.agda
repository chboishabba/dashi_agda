module DASHI.Law.SensibLawProductionLegalRuntimeABIExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal

------------------------------------------------------------------------
-- PRODUCTION LEGAL RUNTIME ABI
--
-- DASHI-original formal ABI for the production execution carrier.
--
-- This owner intentionally does not import or encode a Python/PostgreSQL
-- implementation.  It formalises the information that any production runtime
-- (currently intended to be the Rust SLR lane) must preserve when transporting
-- direct PNF output into legal-source IR, typed legal meets, and reviewed legal
-- promotion.
--
-- The historical SensibLaw runtime is therefore a reference producer for these
-- carrier shapes, not an authority that can silently define new legal
-- semantics.
------------------------------------------------------------------------

data RuntimeCarrierKind : Set where
  directNumericPNFCarrier
  legalIRObservationCarrier
  legalTypedMeetCarrier
  reviewedLegalPromotionCarrier
  : RuntimeCarrierKind

record RuntimePNFReceipt : Set where
  constructor runtimePNFReceipt
  field
    documentReference : String
    sourceSpanReference : String
    factorReference : String
    parserObservationReference : String
    structuralFibreReference : String

    occurrence : Status.OccurrenceStatus
    proposition : Status.PropositionStatus
    truth : Status.TruthStatus

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    parserAuthorizesTruth : Bool
    parserAuthorizesTruthIsFalse : parserAuthorizesTruth ≡ false

    parserAuthorizesOccurrence : Bool
    parserAuthorizesOccurrenceIsFalse : parserAuthorizesOccurrence ≡ false

open RuntimePNFReceipt public

record RuntimeLegalIRObservation : Set where
  constructor runtimeLegalIRObservation
  field
    legalSourceReference : String
    legalSourceRoleReference : String
    authorityLevelReference : String
    jurisdictionReference : String
    temporalReference : String
    structuralFibreReference : String
    legalPNF : RuntimePNFReceipt

    projectionCandidateOnly : Bool
    projectionCandidateOnlyIsTrue : projectionCandidateOnly ≡ true

    projectionAuthorizesApplicability : Bool
    projectionAuthorizesApplicabilityIsFalse :
      projectionAuthorizesApplicability ≡ false

    projectionAuthorizesViolation : Bool
    projectionAuthorizesViolationIsFalse :
      projectionAuthorizesViolation ≡ false

open RuntimeLegalIRObservation public

------------------------------------------------------------------------
-- Typed-meet ABI.
--
-- The existing WrongTypeApplicabilityReceipt remains the legal semantic owner.
-- This runtime ABI merely proves that a direct-world PNF carrier and a legal-IR
-- carrier are the same typed interaction being reviewed.  It does not infer a
-- meet from shared words or shared labels.
------------------------------------------------------------------------

record RuntimeLegalTypedMeet : Set₁ where
  constructor runtimeLegalTypedMeet
  field
    worldPNF : RuntimePNFReceipt
    legalIR : RuntimeLegalIRObservation
    applicabilityReceipt : Legal.WrongTypeApplicabilityReceipt

    sameStructuralFibreReceipt : Set
    sameJurisdictionReceipt : Set
    sameTemporalEnvelopeReceipt : Set
    sameActorCoordinateReceipt : Set
    sameConductCoordinateReceipt : Set
    sameObjectCoordinateReceipt : Set
    sameCircumstanceCoordinateReceipt : Set
    sameExceptionCoordinateReceipt : Set
    sameBurdenCoordinateReceipt : Set

    meetReference : String

open RuntimeLegalTypedMeet public

------------------------------------------------------------------------
-- Promotion is deliberately separate from matching.
------------------------------------------------------------------------

data RuntimeLegalPromotionStatus : Set where
  noPromotion
  applicabilityCandidatePromotion
  applicabilityAdmittedPromotion
  inapplicabilityAdmittedPromotion
  promotionBlocked
  : RuntimeLegalPromotionStatus

promotionFor : Status.ApplicabilityStatus → RuntimeLegalPromotionStatus
promotionFor Status.applicabilityUnresolved = noPromotion
promotionFor Status.applicabilityCandidate = applicabilityCandidatePromotion
promotionFor Status.applicabilityAdmitted = applicabilityAdmittedPromotion
promotionFor Status.inapplicabilityAdmitted = inapplicabilityAdmittedPromotion

record ReviewedRuntimeLegalPromotion (meet : RuntimeLegalTypedMeet) : Set₁ where
  constructor reviewedRuntimeLegalPromotion
  field
    status : RuntimeLegalPromotionStatus
    statusMatchesApplicability :
      status ≡ promotionFor (Legal.resultingApplicability (applicabilityReceipt meet))
    authorityReviewReceipt : Set
    applicabilityReviewReceipt : Set
    promotionReference : String

open ReviewedRuntimeLegalPromotion public

------------------------------------------------------------------------
-- Producer boundaries.
------------------------------------------------------------------------

data RuntimeLegalProducer : Set where
  directPNFProducer
  legalSourceFollowProducer
  legalIRProjectionProducer
  typedMeetProducer
  authorityReviewProducer
  applicabilityReviewProducer
  wrongTypeElementProducer
  evidencePaymentProducer
  : RuntimeLegalProducer

record RuntimeLegalProducerBoundary : Set where
  constructor runtimeLegalProducerBoundary
  field
    parserProducesCandidatePNFOnly : Bool
    parserProducesCandidatePNFOnlyIsTrue :
      parserProducesCandidatePNFOnly ≡ true

    legalFollowProducesSourceMaterialOnly : Bool
    legalFollowProducesSourceMaterialOnlyIsTrue :
      legalFollowProducesSourceMaterialOnly ≡ true

    typedMeetAloneClosesApplicability : Bool
    typedMeetAloneClosesApplicabilityIsFalse :
      typedMeetAloneClosesApplicability ≡ false

    legalIRAloneClosesViolation : Bool
    legalIRAloneClosesViolationIsFalse :
      legalIRAloneClosesViolation ≡ false

canonicalRuntimeLegalProducerBoundary : RuntimeLegalProducerBoundary
canonicalRuntimeLegalProducerBoundary =
  runtimeLegalProducerBoundary true refl true refl false refl false refl

------------------------------------------------------------------------
-- Hard no-go laws.
------------------------------------------------------------------------

data SharedSurfaceAutomaticallySameTypedMeet : Set where
data ParserCandidateAutomaticallyTruth : Set where
data ParserCandidateAutomaticallyOccurrence : Set where
data LegalIRProjectionAutomaticallyApplicable : Set where
data TypedMeetAutomaticallyViolation : Set where
data SourceFollowAutomaticallyAuthority : Set where
data HistoricalSensibLawRuntimeDefinesFormalSemantics : Set where

sharedSurfaceDoesNotEstablishTypedMeet :
  SharedSurfaceAutomaticallySameTypedMeet → ⊥
sharedSurfaceDoesNotEstablishTypedMeet ()

parserCandidateDoesNotEstablishTruth :
  ParserCandidateAutomaticallyTruth → ⊥
parserCandidateDoesNotEstablishTruth ()

parserCandidateDoesNotEstablishOccurrence :
  ParserCandidateAutomaticallyOccurrence → ⊥
parserCandidateDoesNotEstablishOccurrence ()

legalIRProjectionDoesNotEstablishApplicability :
  LegalIRProjectionAutomaticallyApplicable → ⊥
legalIRProjectionDoesNotEstablishApplicability ()

typedMeetDoesNotEstablishViolation :
  TypedMeetAutomaticallyViolation → ⊥
typedMeetDoesNotEstablishViolation ()

sourceFollowDoesNotEstablishAuthority :
  SourceFollowAutomaticallyAuthority → ⊥
sourceFollowDoesNotEstablishAuthority ()

historicalRuntimeDoesNotDefineNewFormalSemantics :
  HistoricalSensibLawRuntimeDefinesFormalSemantics → ⊥
historicalRuntimeDoesNotDefineNewFormalSemantics ()

------------------------------------------------------------------------
-- ABI ownership declaration.
------------------------------------------------------------------------

data ImplementationLayer : Set where
  agdaFormalLayer
  rustSLRRuntimeLayer
  historicalSensibLawReferenceLayer
  : ImplementationLayer

data ImplementationRole : Set where
  formalSemanticAuthority
  productionRuntimeConsumer
  referenceOnlyProducer
  : ImplementationRole

roleOf : ImplementationLayer → ImplementationRole
roleOf agdaFormalLayer = formalSemanticAuthority
roleOf rustSLRRuntimeLayer = productionRuntimeConsumer
roleOf historicalSensibLawReferenceLayer = referenceOnlyProducer

record AgdaFirstRuntimeBoundary : Set where
  constructor agdaFirstRuntimeBoundary
  field
    agdaOwnsFormalSemanticContract : Bool
    agdaOwnsFormalSemanticContractIsTrue :
      agdaOwnsFormalSemanticContract ≡ true

    slrConsumesFormalSemanticContract : Bool
    slrConsumesFormalSemanticContractIsTrue :
      slrConsumesFormalSemanticContract ≡ true

    historicalSensibLawMayDefineNewFormalSemantics : Bool
    historicalSensibLawMayDefineNewFormalSemanticsIsFalse :
      historicalSensibLawMayDefineNewFormalSemantics ≡ false

    rustMayPrecedeMissingAgdaSemanticContract : Bool
    rustMayPrecedeMissingAgdaSemanticContractIsFalse :
      rustMayPrecedeMissingAgdaSemanticContract ≡ false

canonicalAgdaFirstRuntimeBoundary : AgdaFirstRuntimeBoundary
canonicalAgdaFirstRuntimeBoundary =
  agdaFirstRuntimeBoundary true refl true refl false refl false refl
