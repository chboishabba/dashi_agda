module DASHI.Interop.SLRFragmentEvidenceContractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRClaimFragmentResidualInheritanceExact as Residual
import DASHI.Policy.ABC730C029LegalMachineryHyperfabricExact as C029

------------------------------------------------------------------------
-- CLAIM-LOCAL FRAGMENT x EVIDENCE CONTRACTION
--
-- Runtime companions:
--   slr_claim_fragment_projection.py
--   slr_claim_fragment_residual_inheritance.py
--   slr_fragment_evidence_contraction.py      : v2
--   run_fragment_evidence_review_loop.sh
--
-- A later evidence receipt may contract an attribution/source dimension or a
-- canonical consumer obligation.  The historical fragment, historical residual
-- row, whole-claim extent, and claim truth remain separate coordinates.
------------------------------------------------------------------------

data FragmentMilestoneState : Set where
  runtimeValidated : FragmentMilestoneState
  formalValidated : FragmentMilestoneState
  active : FragmentMilestoneState
  residualOpen : FragmentMilestoneState

record FragmentValidationReceipt : Set where
  constructor fragmentValidationReceipt
  field
    runtimeSchema : String
    fragmentCount : String
    claimFragmentCount : String
    intermediateFragmentCount : String
    relationCount : String
    exactBoundaryFragmentCount : String
    boundedBoundaryFragmentCount : String
    wholeClaimExtentPaid : Bool
    intermediateSpeakerSegmentsRetained : Bool
    semanticPromotion : Bool
    claimTruthPromoted : Bool
    formalCheckReference : String

open FragmentValidationReceipt public

validatedABCFragmentProjection : FragmentValidationReceipt
validatedABCFragmentProjection = fragmentValidationReceipt
  "slr-claim-fragment-projection-v1"
  "5" "4" "1" "4" "2" "4"
  false true false false
  "SLRClaimFragmentProjectionExact.agda: 146 modules checked, no errors"

record FragmentEvidenceContractionBoundary : Set where
  constructor fragmentEvidenceContractionBoundary
  field
    fragmentProvenanceSeparateFromEvidenceAuthority : Bool
    evidenceMayContractAttributionSourceDimension : Bool
    evidenceMayContractConsumerObligation : Bool
    evidenceMayRewriteFragmentProvenance : Bool
    evidenceMayRewriteHistoricalResidual : Bool
    evidencePaysWholeClaimExtent : Bool
    evidencePromotesClaimTruth : Bool
    contractionAppendOnly : Bool
    candidateOnly : Bool
    runtimeReference : String

open FragmentEvidenceContractionBoundary public

canonicalFragmentEvidenceContractionBoundary : FragmentEvidenceContractionBoundary
canonicalFragmentEvidenceContractionBoundary = fragmentEvidenceContractionBoundary
  true true true false false false false true true
  "slr-fragment-evidence-contraction-v2"

------------------------------------------------------------------------
-- Payment is indexed by the exact consumer obligation.  A valid evidence
-- object can still be non-paying for the obligation it targets.
------------------------------------------------------------------------

data PaymentDisposition : Set where
  paysObligation : PaymentDisposition
  partialEvidenceOnly : PaymentDisposition
  measurementBlockOnly : PaymentDisposition
  rejectedWrongType : PaymentDisposition

record ConsumerObligationPaymentGate : Set where
  constructor consumerObligationPaymentGate
  field
    claimReference : String
    obligationReference : String
    evidenceReference : String
    targetObligationWeldPaid : Bool
    claimRoleWeldPaid : Bool
    evidenceKindCompatible : Bool
    reviewedForPayment : Bool
    disposition : PaymentDisposition
    obligationPaid : Bool

open ConsumerObligationPaymentGate public

ukClassifierComparatorGate : ConsumerObligationPaymentGate
ukClassifierComparatorGate = consumerObligationPaymentGate
  "ABC730-2026-09-09-C029"
  "C029:settlementSubcountryClassifier"
  "ABC730UnintendedConsequencesSnowballEvidenceExact.ukSettlementOriginMechanism"
  true true true true partialEvidenceOnly false

pcbsIncidenceExposureGate : ConsumerObligationPaymentGate
pcbsIncidenceExposureGate = consumerObligationPaymentGate
  "ABC730-2026-09-09-C029"
  "C029:palestinianNetIncidence"
  "ABC730PalestinianIncidenceSnowballExact.pcbsSettlementWorkers"
  true true true true partialEvidenceOnly false

ukMeasurementGapGate : ConsumerObligationPaymentGate
ukMeasurementGapGate = consumerObligationPaymentGate
  "ABC730-2026-09-09-C029"
  "C029:settlementTradeMagnitude"
  "ABC730SettlementTradeMeasurementGapExact.ukSettlementValueNotSeparatelyIdentified"
  true true true true measurementBlockOnly false

record ObligationContractionState : Set where
  constructor obligationContractionState
  field
    claimReference : String
    currentFirstResidualReference : String
    consumerAdequate : Bool
    evaluateAptnessEnabled : Bool
    historicalResidualsRetained : Bool
    paymentReceiptsAppended : Bool
    claimTruthPromoted : Bool

open ObligationContractionState public

currentC029ObligationContraction : ObligationContractionState
currentC029ObligationContraction = obligationContractionState
  "ABC730-2026-09-09-C029"
  "C029:settlementSubcountryClassifier"
  false false true true false

------------------------------------------------------------------------
-- Review recomputation uses the derived active residual view.  It may advance
-- when a later payment closes the first obligation, but eligibility is still
-- not promotion.
------------------------------------------------------------------------

record ReviewRecomputationBoundary : Set where
  constructor reviewRecomputationBoundary
  field
    currentResidualDerivedFromActiveObligations : Bool
    consumerAdequacyDerivedFromActiveObligations : Bool
    reviewMayAdvanceAfterValidPayment : Bool
    eligibilityMeansTruth : Bool
    reviewPerformsPromotion : Bool

open ReviewRecomputationBoundary public

canonicalReviewRecomputationBoundary : ReviewRecomputationBoundary
canonicalReviewRecomputationBoundary = reviewRecomputationBoundary
  true true true false false

------------------------------------------------------------------------
-- Current SLR roadmap after fragment validation.
------------------------------------------------------------------------

record FragmentRoadmapState : Set where
  constructor fragmentRoadmapState
  field
    discourseReconstruction : FragmentMilestoneState
    candidateWorldCarrierParity : FragmentMilestoneState
    canonicalClaimProjection : FragmentMilestoneState
    multiHopDiscoursePath : FragmentMilestoneState
    claimLocalFragmentProjection : FragmentMilestoneState
    fragmentResidualInheritance : FragmentMilestoneState
    fragmentEvidenceContraction : FragmentMilestoneState
    consumerReviewRecomputation : FragmentMilestoneState
    wholeClaimExtentCompletion : FragmentMilestoneState
    substantiveWorldEvidenceAdequacy : FragmentMilestoneState

open FragmentRoadmapState public

currentFragmentRoadmap : FragmentRoadmapState
currentFragmentRoadmap = fragmentRoadmapState
  runtimeValidated runtimeValidated runtimeValidated formalValidated formalValidated
  formalValidated active active residualOpen residualOpen

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FragmentProvenanceIsEvidenceAuthority : Set where
data AttributionEvidencePaysWholeClaimExtent : Set where
data AttributionEvidencePaysClaimTruth : Set where
data PartialEvidenceClosesObligation : Set where
data HistoricalResidualMayBeDeletedAfterPayment : Set where
data LocalFragmentIsWholeClaim : Set where
data IntermediateReporterFragmentMayBeDropped : Set where
data EvidenceContractionMayRewritePriorSource : Set where
data ReviewEligibilityMeansTruth : Set where

fragmentProvenanceIsNotEvidenceAuthority : FragmentProvenanceIsEvidenceAuthority → ⊥
fragmentProvenanceIsNotEvidenceAuthority ()

attributionDoesNotPayWholeExtent : AttributionEvidencePaysWholeClaimExtent → ⊥
attributionDoesNotPayWholeExtent ()

attributionDoesNotPayTruth : AttributionEvidencePaysClaimTruth → ⊥
attributionDoesNotPayTruth ()

partialEvidenceDoesNotCloseObligation : PartialEvidenceClosesObligation → ⊥
partialEvidenceDoesNotCloseObligation ()

historicalResidualMayNotBeDeleted : HistoricalResidualMayBeDeletedAfterPayment → ⊥
historicalResidualMayNotBeDeleted ()

localFragmentIsNotWholeClaim : LocalFragmentIsWholeClaim → ⊥
localFragmentIsNotWholeClaim ()

intermediateReporterMayNotBeDropped : IntermediateReporterFragmentMayBeDropped → ⊥
intermediateReporterMayNotBeDropped ()

contractionDoesNotRewritePriorSource : EvidenceContractionMayRewritePriorSource → ⊥
contractionDoesNotRewritePriorSource ()

reviewEligibilityDoesNotMeanTruth : ReviewEligibilityMeansTruth → ⊥
reviewEligibilityDoesNotMeanTruth ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

residualInheritanceAnchor : Residual.FragmentResidualRuntimeBoundary
residualInheritanceAnchor = Residual.canonicalFragmentResidualRuntimeBoundary

c029CutsetAnchor : C029.C029LegalEvidenceCutset
c029CutsetAnchor = C029.canonicalC029Cutset
