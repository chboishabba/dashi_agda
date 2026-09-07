module DASHI.Reasoning.EvidenceDesignAdmissibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.DialecticalOppositionNonExplosionExact as Dialectic

------------------------------------------------------------------------
-- EXPERIMENTAL / STUDY DESIGN AS A TYPED EVIDENCE AFFORDANCE
--
-- Designs answer different questions.  This module therefore does not impose
-- one universal evidence ladder.  Internal validity, transportability,
-- interpretive depth and epistemic participation remain separate coordinates.
------------------------------------------------------------------------

data DesignKind : Set where
  randomisedControlledTrial : DesignKind
  quasiExperiment : DesignKind
  observationalQuantitative : DesignKind
  qualitativeInterview : DesignKind
  qualitativeFocusGroup : DesignKind
  mixedMethods : DesignKind
  designBasedResearch : DesignKind
  systematicReview : DesignKind
  metaAnalysis : DesignKind
  narrativeReview : DesignKind
  practitionerSynthesis : DesignKind
  conceptualFramework : DesignKind

data ValidityLevel : Set where
  validityUnassessed : ValidityLevel
  validityLimited : ValidityLevel
  validityModerate : ValidityLevel
  validityStrong : ValidityLevel

data EpistemicRole : Set where
  measuredSubject : EpistemicRole
  respondent : EpistemicRole
  informant : EpistemicRole
  domainExpert : EpistemicRole
  coDesigner : EpistemicRole
  researchPartner : EpistemicRole
  governingParticipant : EpistemicRole

data EvidenceQuestion : Set where
  existenceQuestion : EvidenceQuestion
  associationQuestion : EvidenceQuestion
  causalQuestion : EvidenceQuestion
  mechanismQuestion : EvidenceQuestion
  livedExperienceQuestion : EvidenceQuestion
  acceptabilityQuestion : EvidenceQuestion
  implementationQuestion : EvidenceQuestion
  transportQuestion : EvidenceQuestion
  normativeQuestion : EvidenceQuestion

record StudyDesignReceipt : Set where
  constructor studyDesignReceipt
  field
    designKey : String
    designKind : DesignKind
    samplingFrame : String
    allocationMechanism : String
    comparator : String
    measurementValidity : String
    attritionHandling : String
    confoundingControl : String
    implementationFidelity : String
    multiplicityHandling : String
    effectSizeSurface : String
    uncertaintySurface : String
    externalValidityDomain : String
    participantRole : EpistemicRole
    internalValidity : ValidityLevel
    externalValidity : ValidityLevel
    designReference : String

open StudyDesignReceipt public

record EvidenceReceipt : Set where
  constructor evidenceReceipt
  field
    evidenceKey : String
    design : StudyDesignReceipt
    sourceCitation : String
    sourcePassage : String
    extractionMethod : String
    transformationHistory : String
    interpretationAuthority : String
    limitations : String

open EvidenceReceipt public

------------------------------------------------------------------------
-- Admissibility is relational: evidence is admissible FOR an obligation.
------------------------------------------------------------------------

data AdmissibilityFinding : Set where
  fullyAdmissible : AdmissibilityFinding
  partiallyAdmissible : AdmissibilityFinding
  scopeOverreach : AdmissibilityFinding
  strengthOverreach : AdmissibilityFinding
  designMismatch : AdmissibilityFinding
  provenanceFailure : AdmissibilityFinding
  contradictedFinding : AdmissibilityFinding
  unresolvedFinding : AdmissibilityFinding

record EvidenceForObligation : Set where
  constructor evidenceForObligation
  field
    evidence : EvidenceReceipt
    obligation : PNF.AssertionObligation
    finding : AdmissibilityFinding
    reason : String

open EvidenceForObligation public

-- A positive promotion permission is not inferred from an arbitrary audit
-- result.  The constructors make the relevant gate explicit.
data AdmissibleForPromotion : AdmissibilityFinding → Set where
  admitFully : AdmissibleForPromotion fullyAdmissible
  admitPartiallyWithNarrowing : AdmissibleForPromotion partiallyAdmissible

scopeOverreachNotPromotionAdmissible :
  ¬ AdmissibleForPromotion scopeOverreach
scopeOverreachNotPromotionAdmissible ()

strengthOverreachNotPromotionAdmissible :
  ¬ AdmissibleForPromotion strengthOverreach
strengthOverreachNotPromotionAdmissible ()

designMismatchNotPromotionAdmissible :
  ¬ AdmissibleForPromotion designMismatch
designMismatchNotPromotionAdmissible ()

provenanceFailureNotPromotionAdmissible :
  ¬ AdmissibleForPromotion provenanceFailure
provenanceFailureNotPromotionAdmissible ()

------------------------------------------------------------------------
-- Dialectical evidence is typed by what kind of opposition it constitutes.
-- A null result, scope qualification or methodological challenge is not
-- silently converted into logical negation.
------------------------------------------------------------------------

data EvidenceOpposition : Set where
  directSameScopeContradiction : EvidenceOpposition
  scopeQualifiedDisagreement : EvidenceOpposition
  methodologicalChallenge : EvidenceOpposition
  alternativeExplanation : EvidenceOpposition
  effectSizeDisagreement : EvidenceOpposition
  nullEvidence : EvidenceOpposition
  constructedCounterevidence : EvidenceOpposition

evidenceOppositionMode : EvidenceOpposition → Dialectic.OppositionMode
evidenceOppositionMode directSameScopeContradiction = Dialectic.logicalNegation
evidenceOppositionMode scopeQualifiedDisagreement = Dialectic.constructedCounterposition
evidenceOppositionMode methodologicalChallenge = Dialectic.constructedCounterposition
evidenceOppositionMode alternativeExplanation = Dialectic.constructedCounterposition
evidenceOppositionMode effectSizeDisagreement = Dialectic.constructedCounterposition
evidenceOppositionMode nullEvidence = Dialectic.constructedCounterposition
evidenceOppositionMode constructedCounterevidence = Dialectic.constructedCounterposition

nullEvidenceMode≢logicalNegation :
  ¬ (evidenceOppositionMode nullEvidence ≡ Dialectic.logicalNegation)
nullEvidenceMode≢logicalNegation = Dialectic.counterposition≢negation

methodologicalChallengeMode≢logicalNegation :
  ¬ (evidenceOppositionMode methodologicalChallenge ≡ Dialectic.logicalNegation)
methodologicalChallengeMode≢logicalNegation = Dialectic.counterposition≢negation

------------------------------------------------------------------------
-- Design affordance is explicit rather than a universal ranking.
------------------------------------------------------------------------

data DesignAffords : DesignKind → EvidenceQuestion → Set where
  rctCanAddressCausal : DesignAffords randomisedControlledTrial causalQuestion
  quasiCanAddressCausal : DesignAffords quasiExperiment causalQuestion
  interviewCanAddressExperience : DesignAffords qualitativeInterview livedExperienceQuestion
  focusGroupCanAddressExperience : DesignAffords qualitativeFocusGroup livedExperienceQuestion
  mixedCanAddressImplementation : DesignAffords mixedMethods implementationQuestion
  designResearchCanAddressImplementation : DesignAffords designBasedResearch implementationQuestion
  reviewCanAddressSynthesis : DesignAffords systematicReview existenceQuestion
  metaCanAddressSynthesis : DesignAffords metaAnalysis existenceQuestion
  conceptualCanAddressMechanism : DesignAffords conceptualFramework mechanismQuestion

-- No constructor turns qualitative interview design into a population-average
-- causal-effect certificate; conversely no constructor says an RCT alone
-- supplies situated lived-experience interpretation.

record EvidenceDesignBoundary : Set where
  constructor evidenceDesignBoundary
  field
    oneUniversalMethodHierarchy : Bool
    statisticalSignificanceImpliesGeneralPolicyRecommendation : Bool
    causalInternalValidityImpliesUniversalTransport : Bool
    qualitativeSituatedEvidenceImpliesPopulationPrevalence : Bool
    nullResultIsLogicalNegation : Bool
    oppositionMustRetainItsMode : Bool
    promotionAdmissibilityIsRelational : Bool

canonicalEvidenceDesignBoundary : EvidenceDesignBoundary
canonicalEvidenceDesignBoundary =
  evidenceDesignBoundary false false false false false true true
