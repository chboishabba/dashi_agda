module DASHI.Interop.SLRLegalRuntimeCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ITIRFederatedTypedWorldProjectionExact as World
import DASHI.Interop.SLRSharedEvidenceReducerExact as Shared
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawSourceConditionedApplicabilityViolationExact as SourceConditioned
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Reopen
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Interop.SensibLawMaboProgressiveExplanationProjectionExact as MaboReader

------------------------------------------------------------------------
-- SLR LEGAL RUNTIME CAPSTONE
--
-- Golden composition for the production Rust legal-runtime tranche.
-- No new legal ontology is introduced here.  The owner fixes the exact
-- production cut:
--
--   M2.5 mixed-family evidence replay
--   M3.A reviewed world -> WrongType issue state
--   M3.B source-realised legal evaluator
--   M3.C adaptive persisted Australian capstone
--   M4.A read-only matter / issue projection
------------------------------------------------------------------------

data RuntimeMilestone : Set where
  m25MixedFamilyReplay : RuntimeMilestone
  m3AReviewedWorldToWrongType : RuntimeMilestone
  m3BSourceRealisedEvaluator : RuntimeMilestone
  m3CAdaptiveAustralianCapstone : RuntimeMilestone
  m4AMatterIssueProjection : RuntimeMilestone

canonicalMilestonePath : List RuntimeMilestone
canonicalMilestonePath =
  m25MixedFamilyReplay
  ∷ m3AReviewedWorldToWrongType
  ∷ m3BSourceRealisedEvaluator
  ∷ m3CAdaptiveAustralianCapstone
  ∷ m4AMatterIssueProjection
  ∷ []

------------------------------------------------------------------------
-- M2.5: one persisted/replayed identity carrier over materially different
-- canonical evidence families.
------------------------------------------------------------------------

data ReplayEvidenceFamily : Set where
  structuredWorldEvidence : ReplayEvidenceFamily
  legalAuthorityEvidence : ReplayEvidenceFamily
  matterDocumentEvidence : ReplayEvidenceFamily

record PersistedCanonicalEvidenceIdentity : Set where
  constructor persisted-canonical-evidence-identity
  field
    family : ReplayEvidenceFamily
    manifestationReference : String
    sourceRevisionReference : String
    spanReference : String
    observationReference : String
    reviewReference : String
    paymentReference : String
    projectionSummary : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open PersistedCanonicalEvidenceIdentity public

record MixedFamilyReplayReceipt : Set where
  constructor mixed-family-replay-receipt
  field
    structuredWorld : PersistedCanonicalEvidenceIdentity
    legalAuthority : PersistedCanonicalEvidenceIdentity
    matterDocument : PersistedCanonicalEvidenceIdentity

    structuredFamilyExact :
      family structuredWorld ≡ structuredWorldEvidence

    authorityFamilyExact :
      family legalAuthority ≡ legalAuthorityEvidence

    matterFamilyExact :
      family matterDocument ≡ matterDocumentEvidence

    receiptHead : String
    restartReceiptHead : String
    exactRestartReplay : restartReceiptHead ≡ receiptHead

    replayCreatesSemanticAuthority : Bool
    replayCreatesSemanticAuthorityIsFalse :
      replayCreatesSemanticAuthority ≡ false

    replayCreatesApplicability : Bool
    replayCreatesApplicabilityIsFalse :
      replayCreatesApplicability ≡ false

    replayCreatesClaimTruth : Bool
    replayCreatesClaimTruthIsFalse :
      replayCreatesClaimTruth ≡ false

open MixedFamilyReplayReceipt public

------------------------------------------------------------------------
-- M3.A: Rust four-way element disposition is exactly the existing Agda legal
-- disposition surface, not a replacement ternary/boolean ontology.
------------------------------------------------------------------------

data RustElementDisposition : Set where
  rustSatisfied : RustElementDisposition
  rustUnsatisfied : RustElementDisposition
  rustContested : RustElementDisposition
  rustUnresolved : RustElementDisposition

toGoldenElementDisposition : RustElementDisposition → Legal.ElementDisposition
toGoldenElementDisposition rustSatisfied = Legal.elementSatisfied
toGoldenElementDisposition rustUnsatisfied = Legal.elementUnsatisfied
toGoldenElementDisposition rustContested = Legal.elementContested
toGoldenElementDisposition rustUnresolved = Legal.elementUnresolved

record ReviewedWorldToWrongTypeContract : Set where
  constructor reviewed-world-to-wrong-type-contract
  field
    sharedReducerIsCanonicalIngress : Bool
    sharedReducerIsCanonicalIngressIsTrue :
      sharedReducerIsCanonicalIngress ≡ true

    wrongTypeBundleDefinesElementUniverse : Bool
    wrongTypeBundleDefinesElementUniverseIsTrue :
      wrongTypeBundleDefinesElementUniverse ≡ true

    elementDispositionUsesExistingFourWaySurface : Bool
    elementDispositionUsesExistingFourWaySurfaceIsTrue :
      elementDispositionUsesExistingFourWaySurface ≡ true

    evidenceDispositionIsNotLegalDisposition : Bool
    evidenceDispositionIsNotLegalDispositionIsTrue :
      evidenceDispositionIsNotLegalDisposition ≡ true

    reviewedObservationCreatesWrongType : Bool
    reviewedObservationCreatesWrongTypeIsFalse :
      reviewedObservationCreatesWrongType ≡ false

    elementCandidateCreatesSatisfiedElement : Bool
    elementCandidateCreatesSatisfiedElementIsFalse :
      elementCandidateCreatesSatisfiedElement ≡ false

    elementEvaluationCreatesLiability : Bool
    elementEvaluationCreatesLiabilityIsFalse :
      elementEvaluationCreatesLiability ≡ false

open ReviewedWorldToWrongTypeContract public

canonicalReviewedWorldToWrongTypeContract :
  ReviewedWorldToWrongTypeContract
canonicalReviewedWorldToWrongTypeContract =
  reviewed-world-to-wrong-type-contract
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- M3.B: the production evaluator consumes the already-owned source-conditioned
-- legal algebra.
------------------------------------------------------------------------

sourceConditionedBoundary :
  SourceConditioned.SourceConditionedApplicabilityViolationBoundary
sourceConditionedBoundary =
  SourceConditioned.canonicalSourceConditionedApplicabilityViolationBoundary

record SourceRealisedEvaluatorContract : Set where
  constructor source-realised-evaluator-contract
  field
    premisesRetained : Bool
    premisesRetainedIsTrue : premisesRetained ≡ true

    exceptionsRetained : Bool
    exceptionsRetainedIsTrue : exceptionsRetained ≡ true

    defeatersRetained : Bool
    defeatersRetainedIsTrue : defeatersRetained ≡ true

    burdenSeparateFromViolation : Bool
    burdenSeparateFromViolationIsTrue :
      burdenSeparateFromViolation ≡ true

    remedySeparateFromLiability : Bool
    remedySeparateFromLiabilityIsTrue :
      remedySeparateFromLiability ≡ true

    jurisdictionAndTemporalScopeRetained : Bool
    jurisdictionAndTemporalScopeRetainedIsTrue :
      jurisdictionAndTemporalScopeRetained ≡ true

    laterEvidenceMayReopenConclusion : Bool
    laterEvidenceMayReopenConclusionIsTrue :
      laterEvidenceMayReopenConclusion ≡ true

    sourcePresenceCreatesApplicability : Bool
    sourcePresenceCreatesApplicabilityIsFalse :
      sourcePresenceCreatesApplicability ≡ false

    allElementsEraseExceptionsDefences : Bool
    allElementsEraseExceptionsDefencesIsFalse :
      allElementsEraseExceptionsDefences ≡ false

    violationCreatesLiability : Bool
    violationCreatesLiabilityIsFalse :
      violationCreatesLiability ≡ false

    liabilitySelectsRemedy : Bool
    liabilitySelectsRemedyIsFalse :
      liabilitySelectsRemedy ≡ false

open SourceRealisedEvaluatorContract public

canonicalSourceRealisedEvaluatorContract : SourceRealisedEvaluatorContract
canonicalSourceRealisedEvaluatorContract =
  source-realised-evaluator-contract
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- M3.C: one runner, four existing Australian calibration shapes.
------------------------------------------------------------------------

data AustralianCalibration : Set where
  maboCalibration : AustralianCalibration
  pabaiCalibration : AustralianCalibration
  cullenNSWCLACalibration : AustralianCalibration
  gljCalibration : AustralianCalibration

canonicalAustralianCalibrations : List AustralianCalibration
canonicalAustralianCalibrations =
  maboCalibration
  ∷ pabaiCalibration
  ∷ cullenNSWCLACalibration
  ∷ gljCalibration
  ∷ []

data RuntimeInformationAction : Set where
  lookAction : RuntimeInformationAction
  thinkAction : RuntimeInformationAction
  reviewAction : RuntimeInformationAction

record AdaptiveLegalCampaignContract : Set where
  constructor adaptive-legal-campaign-contract
  field
    currentIssueRecomputedAfterPayment : Bool
    currentIssueRecomputedAfterPaymentIsTrue :
      currentIssueRecomputedAfterPayment ≡ true

    currentResidualsRecomputedAfterPayment : Bool
    currentResidualsRecomputedAfterPaymentIsTrue :
      currentResidualsRecomputedAfterPayment ≡ true

    nextActionMayDependOnNewObservation : Bool
    nextActionMayDependOnNewObservationIsTrue :
      nextActionMayDependOnNewObservation ≡ true

    consumerClosureDoesNotRequireFullWorldIdentity : Bool
    consumerClosureDoesNotRequireFullWorldIdentityIsTrue :
      consumerClosureDoesNotRequireFullWorldIdentity ≡ true

    persistedHopNamesPreviousReceipt : Bool
    persistedHopNamesPreviousReceiptIsTrue :
      persistedHopNamesPreviousReceipt ≡ true

    restartReplaysExactCampaignHead : Bool
    restartReplaysExactCampaignHeadIsTrue :
      restartReplaysExactCampaignHead ≡ true

    selectedActionCreatesAuthority : Bool
    selectedActionCreatesAuthorityIsFalse :
      selectedActionCreatesAuthority ≡ false

    campaignCreatesClaimTruth : Bool
    campaignCreatesClaimTruthIsFalse :
      campaignCreatesClaimTruth ≡ false

open AdaptiveLegalCampaignContract public

canonicalAdaptiveLegalCampaignContract : AdaptiveLegalCampaignContract
canonicalAdaptiveLegalCampaignContract =
  adaptive-legal-campaign-contract
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- M4.A: matter / issue surface is projection-only and preserves source identity.
------------------------------------------------------------------------

data MatterIssueProjectionKind : Set where
  matterProjection : MatterIssueProjectionKind
  issueProjection : MatterIssueProjectionKind
  elementProjection : MatterIssueProjectionKind
  sourceProjection : MatterIssueProjectionKind
  residualProjection : MatterIssueProjectionKind

record SourceAddressableMatterIssueNode : Set where
  constructor source-addressable-matter-issue-node
  field
    semanticIdentity : String
    sourceRevisionReference : String
    spanReference : String
    dependencyReference : String
    downstreamReference : String
    residualReference : String
    projectionKind : MatterIssueProjectionKind
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    projectionOnly : Bool
    projectionOnlyIsTrue : projectionOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

open SourceAddressableMatterIssueNode public

sameNodeAcrossMatterIssueProjection :
  SourceAddressableMatterIssueNode →
  MatterIssueProjectionKind →
  String
sameNodeAcrossMatterIssueProjection node projection =
  semanticIdentity node

matterIssueProjectionPreservesSemanticIdentity :
  (node : SourceAddressableMatterIssueNode) →
  (left right : MatterIssueProjectionKind) →
  sameNodeAcrossMatterIssueProjection node left
  ≡ sameNodeAcrossMatterIssueProjection node right
matterIssueProjectionPreservesSemanticIdentity node left right = refl

------------------------------------------------------------------------
-- Reuse witnesses: these names make the ownership dependency explicit.
------------------------------------------------------------------------

sharedReducerOwnerPresent : Bool
sharedReducerOwnerPresent = true

wrongTypeElementOwnerPresent : Bool
wrongTypeElementOwnerPresent = true

universalLegalAlgebraOwnerPresent : Bool
universalLegalAlgebraOwnerPresent = true

legalReopeningOwnerPresent : Bool
legalReopeningOwnerPresent = true

sequentialConsumerPlannerOwnerPresent : Bool
sequentialConsumerPlannerOwnerPresent = true

progressiveExplanationProjectionOwnerPresent : Bool
progressiveExplanationProjectionOwnerPresent = true

------------------------------------------------------------------------
-- Hard no-collapse laws pinned at the production capstone.
------------------------------------------------------------------------

data MixedFamilyReplayCreatesTruth : Set where
data ReviewedEvidenceCreatesWrongType : Set where
data ElementCandidateCreatesSatisfaction : Set where
data AllElementsCreateLiability : Set where
data LiveExceptionCannotReopenConclusion : Set where
data PersistedCampaignCreatesAuthority : Set where
data MatterIssueProjectionCreatesCanonicalTruth : Set where
data ResidualSuggestionCreatesProof : Set where
data FormalProofPaysExternalWorldPremise : Set where

mixedFamilyReplayDoesNotCreateTruth : MixedFamilyReplayCreatesTruth → ⊥
mixedFamilyReplayDoesNotCreateTruth ()

reviewedEvidenceDoesNotCreateWrongType : ReviewedEvidenceCreatesWrongType → ⊥
reviewedEvidenceDoesNotCreateWrongType ()

elementCandidateDoesNotCreateSatisfaction :
  ElementCandidateCreatesSatisfaction → ⊥
elementCandidateDoesNotCreateSatisfaction ()

allElementsDoNotCreateLiability : AllElementsCreateLiability → ⊥
allElementsDoNotCreateLiability ()

liveExceptionMayReopenConclusion :
  LiveExceptionCannotReopenConclusion → ⊥
liveExceptionMayReopenConclusion ()

persistedCampaignDoesNotCreateAuthority :
  PersistedCampaignCreatesAuthority → ⊥
persistedCampaignDoesNotCreateAuthority ()

matterIssueProjectionDoesNotCreateCanonicalTruth :
  MatterIssueProjectionCreatesCanonicalTruth → ⊥
matterIssueProjectionDoesNotCreateCanonicalTruth ()

residualSuggestionDoesNotCreateProof :
  ResidualSuggestionCreatesProof → ⊥
residualSuggestionDoesNotCreateProof ()

formalProofDoesNotPayExternalWorldPremise :
  FormalProofPaysExternalWorldPremise → ⊥
formalProofDoesNotPayExternalWorldPremise ()

------------------------------------------------------------------------
-- One formal capability receipt matching the Rust capstone output.
------------------------------------------------------------------------

record LegalRuntimeCapabilityReceipt : Set where
  constructor legal-runtime-capability-receipt
  field
    m25MixedFamilyReplayImplemented : Bool
    m25MixedFamilyReplayImplementedIsTrue :
      m25MixedFamilyReplayImplemented ≡ true

    m3AReviewedWorldToWrongTypeImplemented : Bool
    m3AReviewedWorldToWrongTypeImplementedIsTrue :
      m3AReviewedWorldToWrongTypeImplemented ≡ true

    m3BSourceRealisedEvaluatorImplemented : Bool
    m3BSourceRealisedEvaluatorImplementedIsTrue :
      m3BSourceRealisedEvaluatorImplemented ≡ true

    m3COneRunnerFourCalibrationsImplemented : Bool
    m3COneRunnerFourCalibrationsImplementedIsTrue :
      m3COneRunnerFourCalibrationsImplemented ≡ true

    m3CRestartReplayImplemented : Bool
    m3CRestartReplayImplementedIsTrue :
      m3CRestartReplayImplemented ≡ true

    m4AMatterIssueProjectionImplemented : Bool
    m4AMatterIssueProjectionImplementedIsTrue :
      m4AMatterIssueProjectionImplemented ≡ true

    sourceWrittenOnlyUntilRuntimeReceipt : Bool
    sourceWrittenOnlyUntilRuntimeReceiptIsTrue :
      sourceWrittenOnlyUntilRuntimeReceipt ≡ true

    capabilityReceiptCreatesSemanticAuthority : Bool
    capabilityReceiptCreatesSemanticAuthorityIsFalse :
      capabilityReceiptCreatesSemanticAuthority ≡ false

open LegalRuntimeCapabilityReceipt public

canonicalLegalRuntimeCapabilityReceipt : LegalRuntimeCapabilityReceipt
canonicalLegalRuntimeCapabilityReceipt =
  legal-runtime-capability-receipt
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
