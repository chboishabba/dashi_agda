module DASHI.Biology.ACPUEAEROClaimAuditProtocolExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ClaimAuditManifestExact as Manifest
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF

------------------------------------------------------------------------
-- ACPUE <-> AERO CLAIM-AUDIT PROTOCOL
--
-- This owner freezes the research design for the claim audit before results are
-- accumulated.  The first tranche is deliberately not selected only from
-- ACPUE adverse codings.  It must calibrate against Matches, Plausible and Does
-- not match, and against multiple logical/source/consequence strata.
------------------------------------------------------------------------

data ACPUESourceCode : Set where
  acpueMatches
  acpuePlausible
  acpueDoesNotMatch
  acpueCodeNotYetRecovered : ACPUESourceCode

data SourceTypeStratum : Set where
  primaryEmpiricalStudy
  systematicOrMetaSynthesis
  scholarlyReview
  practitionerOrAgencySynthesis
  popularLevelBook
  policyOrStandardsDocument
  sourceTypeUnresolved : SourceTypeStratum

data LogicalStrengthStratum : Set where
  boundedDescriptive
  associational
  boundedCausal
  transportClaim
  universalClaim
  comparativeBestClaim
  normativeOrPolicyClaim : LogicalStrengthStratum

data AuditPriority : Set where
  calibrationPriority
  ordinaryPriority
  highConsequencePriority : AuditPriority

record AuditCandidate : Set where
  constructor auditCandidate
  field
    candidateKey : String
    exactAEROText : String
    aeroLocator : String
    acpueCode : ACPUESourceCode
    sourceType : SourceTypeStratum
    logicalStrength : List LogicalStrengthStratum
    consequences : List Manifest.ClaimConsequence
    priority : AuditPriority
    selectionReason : String

open AuditCandidate public

------------------------------------------------------------------------
-- Precommitted coverage dimensions.
------------------------------------------------------------------------

record TrancheCoverageRequirement : Set where
  constructor trancheCoverageRequirement
  field
    includeACPUEMatches : Bool
    includeACPUEPlausible : Bool
    includeACPUEDoesNotMatch : Bool
    includePrimaryEvidence : Bool
    includeSecondarySynthesis : Bool
    includeUniversalOrTransportClaims : Bool
    includeCausalClaims : Bool
    includeComparativeOrBestClaims : Bool
    includeNormativeOrPolicyClaims : Bool
    includeHighConsequenceClaims : Bool
    includeCalibrationControls : Bool
    selectionFrozenBeforeIndependentCoding : Bool

open TrancheCoverageRequirement public

canonicalTrancheCoverageRequirement : TrancheCoverageRequirement
canonicalTrancheCoverageRequirement =
  trancheCoverageRequirement
    true true true true true true true true true true true true

------------------------------------------------------------------------
-- Audit stages.  ACPUE coding and DASHI independent coding remain separate;
-- the independent coder should not need an adverse ACPUE label to select a
-- claim for the tranche.
------------------------------------------------------------------------

record ClaimAuditWorkflow : Set where
  constructor claimAuditWorkflow
  field
    registerExactClaimText : Bool
    recoverEveryCitedSource : Bool
    normalizeToPNFBeforeVerdict : Bool
    auditEachCitationSeparately : Bool
    traceImportantSecondaryClaimsToPrimaryEvidence : Bool
    retainExperimentalDesign : Bool
    codeEveryPNFObligationSeparately : Bool
    reconstructBackwardSafeClaim : Bool
    recordCounterevidenceWithoutForcingNegation : Bool
    independentCodingSeparatedFromACPUECoding : Bool
    disagreementsRemainVisible : Bool

open ClaimAuditWorkflow public

canonicalClaimAuditWorkflow : ClaimAuditWorkflow
canonicalClaimAuditWorkflow =
  claimAuditWorkflow true true true true true true true true true true true

------------------------------------------------------------------------
-- Denominators matter.  A purposive high-consequence tranche is useful for
-- finding failure modes but cannot be re-read as the prevalence of mismatch in
-- all 106 claims.  A full census or an explicitly probability-based sample is
-- needed for population-rate inference.
------------------------------------------------------------------------

data SamplingFrame : Set where
  fullCensus106
  stratifiedCalibrationTranche
  purposiveHighConsequenceTranche
  probabilitySample : SamplingFrame

data SupportsPrevalenceInference : SamplingFrame → Set where
  censusSupportsPrevalence : SupportsPrevalenceInference fullCensus106
  probabilitySampleSupportsPrevalence : SupportsPrevalenceInference probabilitySample

purposiveTrancheDoesNotSupportPrevalence :
  ¬ SupportsPrevalenceInference purposiveHighConsequenceTranche
purposiveTrancheDoesNotSupportPrevalence ()

calibrationTrancheDoesNotSupportPrevalence :
  ¬ SupportsPrevalenceInference stratifiedCalibrationTranche
calibrationTrancheDoesNotSupportPrevalence ()

------------------------------------------------------------------------
-- Planned first-pass strata.  Counts are targets, not empirical results.
------------------------------------------------------------------------

record InitialTranchePlan : Set where
  constructor initialTranchePlan
  field
    targetClaimCount : Nat
    sourceCodeCalibration : String
    logicalStrengthCalibration : String
    sourceTypeCalibration : String
    consequenceCalibration : String
    fullCensusRemainsDestination : Bool

canonicalInitialTranchePlan : InitialTranchePlan
canonicalInitialTranchePlan =
  initialTranchePlan
    18
    "target examples from ACPUE Matches, Plausible and Does not match; recover code from the interactive table before final coding"
    "include bounded/descriptive, causal, transport/universal, comparative-best and normative/policy forms"
    "include primary studies, reviews/meta-syntheses, agency/practitioner syntheses and popular-level sources where they occur"
    "oversample claims capable of downstream policy amplification, while retaining calibration controls"
    true

record ClaimAuditProtocolBoundary : Set where
  constructor claimAuditProtocolBoundary
  field
    selectOnlyAdverseACPUECases : Bool
    purposiveTrancheMismatchRateEqualsFullCensusRate : Bool
    acpueCodingEqualsIndependentCoding : Bool
    oneCitationCheckClosesCompoundClaim : Bool
    secondarySourceMatchClosesPrimaryEvidenceChain : Bool
    fullCensusStillPlanned : Bool

canonicalClaimAuditProtocolBoundary : ClaimAuditProtocolBoundary
canonicalClaimAuditProtocolBoundary =
  claimAuditProtocolBoundary false false false false false true
