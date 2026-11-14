module DASHI.Biology.SourceCueTruthNoncollapseExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SOURCE-CUE / TRUTH NON-COLLAPSE
--
-- External empirical owner:
-- Hidde Roovers, Marieke A. Adriaanse, Hedwig M. M. Vos, et al. (2026),
-- "An experimental study of source and engagement cues for susceptibility to
-- dietary supplement misinformation", Scientific Reports.
-- DOI: 10.1038/s41598-026-74733-8.
--
-- The study reports a source-cue effect on perceived reliability of misleading
-- claims, largely explained by perceived source credibility.  DASHI owns only
-- the formal separation among source identity, source-credibility judgement,
-- perceived message reliability, claim accuracy, and proposition truth.
------------------------------------------------------------------------

roovers2026Source : Source.AttributedSource
roovers2026Source =
  Source.mkDOISource
    "Hidde Roovers; Marieke A. Adriaanse; Hedwig M. M. Vos; et al."
    "An experimental study of source and engagement cues for susceptibility to dietary supplement misinformation"
    "Scientific Reports"
    "2026"
    "10.1038/s41598-026-74733-8"
    "https://doi.org/10.1038/s41598-026-74733-8"
    Source.academicArticleSource
    "Experimental study in 1,298 Dutch-speaking adults using ten mock dietary-supplement social-media posts, with source type and engagement manipulated between participants. Misleading claims attributed to a fictional health professional were judged more reliable than those attributed to a fictional influencer, largely via perceived source credibility. High-versus-low engagement did not change reliability judgements of misleading posts and social-consensus mediation was not supported."
    Source.publicAttribution

data SourceCueOutcomeFamily : Set where
  rooversMisleadingReliabilityOutcome : SourceCueOutcomeFamily

data AdmittedSourceCueEvidence :
  SourceCueOutcomeFamily → Source.AttributedSource → Set where
  rooversPaysMisleadingReliabilityOutcome :
    AdmittedSourceCueEvidence rooversMisleadingReliabilityOutcome roovers2026Source

record SourceCueReliabilityReceipt : Set where
  constructor source-cue-reliability-receipt
  field
    source : Source.AttributedSource
    sourceAdmission :
      AdmittedSourceCueEvidence rooversMisleadingReliabilityOutcome source
    sampleReference : String
    misleadingClaimsAccuracyHeldFixedByStimulusClassification : Bool
    misleadingClaimsAccuracyHeldFixedByStimulusClassificationIsTrue :
      misleadingClaimsAccuracyHeldFixedByStimulusClassification ≡ true
    healthProfessionalCueRaisedPerceivedReliability : Bool
    healthProfessionalCueRaisedPerceivedReliabilityIsTrue :
      healthProfessionalCueRaisedPerceivedReliability ≡ true
    effectLargelyExplainedByPerceivedSourceCredibility : Bool
    effectLargelyExplainedByPerceivedSourceCredibilityIsTrue :
      effectLargelyExplainedByPerceivedSourceCredibility ≡ true
    highEngagementRaisedMisleadingPostReliability : Bool
    highEngagementRaisedMisleadingPostReliabilityIsFalse :
      highEngagementRaisedMisleadingPostReliability ≡ false
    socialConsensusMediationPaid : Bool
    socialConsensusMediationPaidIsFalse : socialConsensusMediationPaid ≡ false
    reading : String

open SourceCueReliabilityReceipt public

canonicalSourceCueReliabilityReceipt : SourceCueReliabilityReceipt
canonicalSourceCueReliabilityReceipt =
  source-cue-reliability-receipt
    roovers2026Source
    rooversPaysMisleadingReliabilityOutcome
    "N=1,298 Dutch-speaking adults; ten mock posts; five misleading and five non-misleading claims"
    true refl
    true refl
    true refl
    false refl
    false refl
    "Roovers et al. report that the source cue altered perceived reliability of misleading claims through perceived source credibility. This is evidence about judgement under a source cue; it does not change the stimulus claim's accuracy classification and it does not supply proposition-truth authority."

------------------------------------------------------------------------
-- DASHI SYNTHESIS / PROMOTION BOUNDARY
------------------------------------------------------------------------

data SourceCredibilityDeterminesTruthPermission : Set where
data PerceivedReliabilityDeterminesTruthPermission : Set where
data SourceCueReattributesClaimPermission : Set where

data SourceCueReplacesEvidenceAdmissionPermission : Set where

sourceCredibilityDoesNotDetermineTruth :
  SourceCredibilityDeterminesTruthPermission → ⊥
sourceCredibilityDoesNotDetermineTruth ()

perceivedReliabilityDoesNotDetermineTruth :
  PerceivedReliabilityDeterminesTruthPermission → ⊥
perceivedReliabilityDoesNotDetermineTruth ()

sourceCueDoesNotReattributeClaim :
  SourceCueReattributesClaimPermission → ⊥
sourceCueDoesNotReattributeClaim ()

sourceCueDoesNotReplaceEvidenceAdmission :
  SourceCueReplacesEvidenceAdmissionPermission → ⊥
sourceCueDoesNotReplaceEvidenceAdmission ()

record SourceCueTruthBoundary : Set where
  constructor source-cue-truth-boundary
  field
    sourceCueCanAffectPerceivedReliability : Bool
    sourceCueCanAffectPerceivedReliabilityIsTrue :
      sourceCueCanAffectPerceivedReliability ≡ true
    sourceCueChangesClaimAccuracy : Bool
    sourceCueChangesClaimAccuracyIsFalse : sourceCueChangesClaimAccuracy ≡ false
    perceivedReliabilityCreatesTruthAuthority : Bool
    perceivedReliabilityCreatesTruthAuthorityIsFalse :
      perceivedReliabilityCreatesTruthAuthority ≡ false
    sourceCredibilityCreatesTruthAuthority : Bool
    sourceCredibilityCreatesTruthAuthorityIsFalse :
      sourceCredibilityCreatesTruthAuthority ≡ false
    sourceCueChangesClaimOwner : Bool
    sourceCueChangesClaimOwnerIsFalse : sourceCueChangesClaimOwner ≡ false
    externalEmpiricalClaimAndDASHISynthesisHaveSeparateOwners : Bool
    externalEmpiricalClaimAndDASHISynthesisHaveSeparateOwnersIsTrue :
      externalEmpiricalClaimAndDASHISynthesisHaveSeparateOwners ≡ true

open SourceCueTruthBoundary public

canonicalSourceCueTruthBoundary : SourceCueTruthBoundary
canonicalSourceCueTruthBoundary =
  source-cue-truth-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
