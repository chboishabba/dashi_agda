module DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchV02Everything where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairTwoEyedPosiwidV02Everything as RepairV02
import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchBridgeV02Exact as Bridge
import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairCalibrationV02Exact as Repair
import DASHI.Cognition.PNF.SensibLawCountryCommunityPaymentAcquisitionPlanV02Exact as Acquisition
import DASHI.Cognition.PNF.SensibLawGriffithsCustodialOutcomePaymentV02Exact as GriffithsOutcome
import DASHI.Cognition.PNF.SensibLawGriffithsCustodialAuthorityCutV02Exact as GriffithsAuthority
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- Preferred V02 executable capstone.
--
-- Source-backed realised-repair calibration remains the factual/operational
-- owner.  The bridge only compiles its live residual into bounded research and
-- assessment/recompute work; it does not upgrade mapped evidence to closure.
------------------------------------------------------------------------

communityOutcomeStillNotStateDefined :
  Repair.officialOutcomeReportEqualsAffectedCommunityDefinedJustice Repair.closingGap2026
  ≡ false
communityOutcomeStillNotStateDefined = refl

currentFirstResidualIsCommunityOutcome :
  Bridge.currentFirstResidualV02 ≡ Bridge.affectedCommunityOutcomeResidualV02
currentFirstResidualIsCommunityOutcome = refl

currentFirstProducerIsCommunityPropositionSource :
  Search.producerClass (Bridge.searchIntentFor Bridge.currentFirstResidualV02)
  ≡ Search.propositionSourceProducer
currentFirstProducerIsCommunityPropositionSource = refl

currentFirstSearchExploresCommunityVocabulary :
  Search.mode (Bridge.searchIntentFor Bridge.currentFirstResidualV02)
  ≡ Search.exploreVocabulary
currentFirstSearchExploresCommunityVocabulary = refl

assessedCommunityOutcomeCandidateRecomputesCalibration :
  Bridge.recomputeActionFor
    (Assessment.change Bridge.communityOutcomeCandidateDeltaV02)
  ≡ Bridge.recomputeV02Calibration
assessedCommunityOutcomeCandidateRecomputesCalibration = refl

communityOutcomeCandidateKeepsOutcomeResidualLive :
  Assessment.firstResidualAfterReference Bridge.communityOutcomeCandidateDeltaV02
  ≡ "affectedCommunityOutcomeResidualV02"
communityOutcomeCandidateKeepsOutcomeResidualLive = refl

admittedCommunityOutcomeAdvancesToAuthority :
  Assessment.firstResidualAfterReference Bridge.communityOutcomeAdmittedDeltaV02
  ≡ "communityAuthorityCapacityResidualV02"
admittedCommunityOutcomeAdvancesToAuthority = refl

------------------------------------------------------------------------
-- First genuine consumer-specific outcome payment.
------------------------------------------------------------------------

griffithsNarrowCustodialOutcomePaid :
  GriffithsOutcome.narrowConsumerOutcomePaid
    GriffithsOutcome.canonicalGriffithsCustodialOutcomeBoundary ≡ true
griffithsNarrowCustodialOutcomePaid = refl

griffithsSpecificInstitutionalCorrectionStillOpen :
  GriffithsOutcome.specificInstitutionalCorrectionPaid
    GriffithsOutcome.griffithsCustodialOutcomePayment ≡ false
griffithsSpecificInstitutionalCorrectionStillOpen = refl

griffithsHistoricalRepresentationDoesNotPayPresentMandate :
  GriffithsAuthority.provesPresentCommunityMandate
    GriffithsAuthority.griffithsHistoricalRepresentation ≡ false
griffithsHistoricalRepresentationDoesNotPayPresentMandate = refl

griffithsNextProducerIsMandateAttribution :
  Acquisition.producerForPaymentCoordinate GriffithsAuthority.nextSearchCoordinate
  ≡ Search.attributionProducer
griffithsNextProducerIsMandateAttribution = refl

------------------------------------------------------------------------
-- Existing V02 positive evidence remains visible and bounded.
------------------------------------------------------------------------

nativeTitleCoverageStillNotControl :
  Repair.determinationCoverageEqualsIndigenousControl Repair.nativeTitleCoverage2025 ≡ false
nativeTitleCoverageStillNotControl = refl

pbcCarrierStillDoesNotProveOperationalCapacity :
  Repair.legalCarrierExistenceProvesOperationalCapacity Repair.pbcResourceCapacity ≡ false
pbcCarrierStillDoesNotProveOperationalCapacity = refl

juukanRecurrencePreventionStillUnderNegativePressure :
  Repair.recurrencePreventionStatusV02 ≡ Repair.sourceMappedNegativePressure
juukanRecurrencePreventionStillUnderNegativePressure = refl

billyCaseSpecificProbabilityStillUnrecovered :
  RepairV02.billyProbabilityStillNotRecovered
  ≡ RepairV02.billyProbabilityStillNotRecovered
billyCaseSpecificProbabilityStillUnrecovered = refl

------------------------------------------------------------------------
-- World closure remains external to repository bookkeeping.
------------------------------------------------------------------------

data V02SearchClosureMeansWorldRepair : Set where

v02SearchClosureDoesNotManufactureWorldRepair : V02SearchClosureMeansWorldRepair → ⊥
v02SearchClosureDoesNotManufactureWorldRepair ()
