module DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownDocumentLineageExact as Lineage
import DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact as Design

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: SECTION / HYPOTHESIS BIDI MANIFEST
--
-- Current canonical manuscript surface: the latest of the three supplied
-- Drive documents by revision timestamp, namely the 2026 comparative mixed-
-- methods proposal.  The older Draft 3 and tracked-changes versions remain
-- genealogy/provenance surfaces rather than being silently discarded.
------------------------------------------------------------------------

data SectionKey : Set where
  introduction : SectionKey
  researchAim : SectionKey
  researchQuestions : SectionKey
  hypotheses : SectionKey
  conceptualDefinitions : SectionKey
  studyDesign : SectionKey
  participantGroups : SectionKey
  recruitmentSampling : SectionKey
  dataCollection : SectionKey
  quantitativeAnalysis : SectionKey
  qualitativeAnalysis : SectionKey
  mixedMethodsIntegration : SectionKey
  ethicalConsiderations : SectionKey
  rightsPolicyFramework : SectionKey
  limitations : SectionKey
  expectedContribution : SectionKey

data SectionAuditStatus : Set where
  sourceRecovered : SectionAuditStatus
  formalOwnerInstalled : SectionAuditStatus
  needsExternalEvidence : SectionAuditStatus
  needsInstrumentValidation : SectionAuditStatus
  needsRightsAuthorityCheck : SectionAuditStatus
  needsJurisdictionSpecificLaw : SectionAuditStatus

record SectionManifestEntry : Set where
  constructor section-manifest-entry
  field
    section : SectionKey
    source : Lineage.BrownDocumentSnapshot
    sourceLocator : String
    paperFunction : String
    formalOwner : String
    currentAuditStatus : SectionAuditStatus
    backwardRevisionRule : String

open SectionManifestEntry public

introductionEntry : SectionManifestEntry
introductionEntry = section-manifest-entry
  introduction Lineage.latestProposalSnapshot "1. INTRODUCTION"
  "distinguishes supportive religious belonging from coercive religious socialisation and frames the inquiry around power asymmetry, fear, dissent, punishment, dependency and institutional betrayal"
  "JohnAnthonyBrownChildReligiousPowerBidiExact + JohnAnthonyBrownStudyDesignBidiExact"
  needsExternalEvidence
  "retain the bounded comparison religion-as-such != coercive practice; source every proposed mechanism independently"

researchQuestionsEntry : SectionManifestEntry
researchQuestionsEntry = section-manifest-entry
  researchQuestions Lineage.latestProposalSnapshot "3. RESEARCH QUESTIONS"
  "five questions covering adult outcomes, adjustment for other adversity/confounding, exposure characteristics, resilience/recovery and survivor interpretation"
  "JohnAnthonyBrownPaperSectionHypothesisManifestExact"
  formalOwnerInstalled
  "keep question form until the matching evidence obligation is discharged"

hypothesesEntry : SectionManifestEntry
hypothesesEntry = section-manifest-entry
  hypotheses Lineage.latestProposalSnapshot "4. HYPOTHESES"
  "five testable hypotheses H1-H5"
  "JohnAnthonyBrownPaperSectionHypothesisManifestExact"
  formalOwnerInstalled
  "report association, incremental association and moderation at the level actually supported by the design; do not silently strengthen to causation"

studyDesignEntry : SectionManifestEntry
studyDesignEntry = section-manifest-entry
  studyDesign Lineage.latestProposalSnapshot "6. STUDY DESIGN"
  "prospective longitudinal multi-cohort mixed-methods adult study with retrospective childhood-exposure measurement"
  "JohnAnthonyBrownStudyDesignBidiExact"
  formalOwnerInstalled
  "retain the proposal's own statement that the design cannot by itself establish causation"

participantGroupsEntry : SectionManifestEntry
participantGroupsEntry = section-manifest-entry
  participantGroups Lineage.latestProposalSnapshot "7. PARTICIPANT GROUPS"
  "descriptive groups A-D plus continuous/dimensional exposure analysis"
  "JohnAnthonyBrownStudyDesignBidiExact"
  formalOwnerInstalled
  "comparison groups are analytical comparators, not moral or clinical equivalence classes"

data HypothesisKey : Set where H1 H2 H3 H4 H5 : HypothesisKey

data InferentialForce : Set where
  longitudinalAssociation : InferentialForce
  adjustedAssociation : InferentialForce
  incrementalPrediction : InferentialForce
  moderationInteraction : InferentialForce
  qualitativeInterpretation : InferentialForce

data ReceiptKind : Set where
  exposureMeasurementReceipt : ReceiptKind
  outcomeMeasurementReceipt : ReceiptKind
  samplingReceipt : ReceiptKind
  comparatorReceipt : ReceiptKind
  confoundingReceipt : ReceiptKind
  temporalReceipt : ReceiptKind
  moderationReceipt : ReceiptKind
  attritionReceipt : ReceiptKind
  multiplicityReceipt : ReceiptKind
  qualitativeProvenanceReceipt : ReceiptKind

record HypothesisManifestEntry : Set where
  constructor hypothesis-manifest-entry
  field
    key : HypothesisKey
    source : Lineage.BrownDocumentSnapshot
    paperHypothesis : String
    normalizedClaim : String
    force : InferentialForce
    primaryDesign : Design.StudyDesignReceipt
    requiredReceipts : String
    externalEvidenceStatus : String
    backwardSafeWording : String

open HypothesisManifestEntry public

h1Manifest : HypothesisManifestEntry
h1Manifest = hypothesis-manifest-entry
  H1 Lineage.latestProposalSnapshot
  "Greater exposure to coercive religious practices in childhood will be associated with higher levels of psychological distress and post-traumatic stress symptoms in adulthood."
  "coercive-religious-exposure intensity is longitudinally associated with adult distress/PTSS under the declared measurement and population scope"
  longitudinalAssociation
  Design.canonicalLongitudinalReceipt
  "validated exposure measure + validated distress/PTSS outcomes + sampling/attrition/confounding/multiplicity/effect-size/uncertainty receipts"
  "hypothesis source recovered; independent empirical support remains to be audited study-by-study"
  "greater measured coercive exposure was associated with the bounded adult distress/PTSS outcomes under the fitted model; causal language withheld unless independently identified"

h2Manifest : HypothesisManifestEntry
h2Manifest = hypothesis-manifest-entry
  H2 Lineage.latestProposalSnapshot
  "Greater exposure will be associated with lower perceived autonomy, reduced self-trust, greater spiritual distress, and increased interpersonal difficulty."
  "coercive-exposure intensity is associated with a multidimensional outcome vector: autonomy, self-trust, spiritual distress and interpersonal difficulty"
  longitudinalAssociation
  Design.canonicalLongitudinalReceipt
  "construct-valid outcome measures for each coordinate + multiplicity and dependence handling + uncertainty receipt"
  "hypothesis source recovered; measures and independent outcome literature require audit"
  "report each outcome coordinate separately and preserve null/divergent findings rather than collapsing the vector into one harm score"

h3Manifest : HypothesisManifestEntry
h3Manifest = hypothesis-manifest-entry
  H3 Lineage.latestProposalSnapshot
  "Institutional betrayal and punishment for disclosure or dissent will predict poorer outcomes beyond the effects of religious exposure alone."
  "institutional-betrayal/refusal-penalty variables add explanatory/predictive information beyond the declared religious-exposure measure"
  incrementalPrediction
  Design.canonicalLongitudinalReceipt
  "institutional-betrayal construct receipt + nested-model/incremental-effect receipt + confounding and collinearity audit + uncertainty"
  "hypothesis source recovered; target-domain empirical instantiation still needs direct evidence"
  "incremental association/prediction is not automatically a unique mechanism or causal mediation theorem"

h4Manifest : HypothesisManifestEntry
h4Manifest = hypothesis-manifest-entry
  H4 Lineage.latestProposalSnapshot
  "Social support, access to trauma-informed care, and the presence of non-coercive communities will moderate the association between exposure and adverse outcomes."
  "support/care/non-coercive-community coordinates interact with exposure in relation to bounded outcomes"
  moderationInteraction
  Design.canonicalLongitudinalReceipt
  "pre-specified interaction/moderation model + scale validity + treatment/support timing + multiplicity + effect-size/uncertainty receipt"
  "hypothesis source recovered; no protective-effect magnitude installed by the manuscript itself"
  "moderation is reported as interaction under observed conditions; it does not prove a universal protective intervention"

h5Manifest : HypothesisManifestEntry
h5Manifest = hypothesis-manifest-entry
  H5 Lineage.latestProposalSnapshot
  "The relationship between coercive religious exposure and adult functioning will remain statistically detectable after adjustment for other adverse childhood experiences, although its magnitude may be reduced."
  "an exposure-outcome association remains statistically detectable after the declared measured-covariate adjustment set, with magnitude permitted to attenuate"
  adjustedAssociation
  Design.canonicalLongitudinalReceipt
  "pre-specified covariate set + measurement quality + missingness/attrition + sensitivity analysis + effect-size/CI + residual-confounding acknowledgement"
  "hypothesis source recovered; detectability is a study result to be tested, not assumed"
  "adjusted association != unconfounded causal effect; non-detection != logical negation of every narrower mechanism claim"

------------------------------------------------------------------------
-- Earlier-draft -> latest-proposal crosswalk.
------------------------------------------------------------------------

data CrosswalkKind : Set where
  retainedAndNarrowed : CrosswalkKind
  redesigned : CrosswalkKind
  convertedToComparator : CrosswalkKind
  convertedToLimitation : CrosswalkKind
  notPromotedForward : CrosswalkKind

record DraftCrosswalk : Set where
  constructor draft-crosswalk
  field
    earlierSource : Lineage.BrownDocumentSnapshot
    latestSource : Lineage.BrownDocumentSnapshot
    kind : CrosswalkKind
    earlierSurface : String
    latestSurface : String
    bidiReading : String

oldTraumaComparisonCrosswalk : DraftCrosswalk
oldTraumaComparisonCrosswalk = draft-crosswalk
  Lineage.draft3Snapshot Lineage.latestProposalSnapshot convertedToComparator
  "earlier draft directly compared named mass-violence/terrorism/enslavement/disaster and religious-indoctrination cohorts"
  "latest proposal uses other substantial childhood adversity as a comparator while explicitly stating the groups must not be described as equivalent harms"
  "structural comparison retained; moral/clinical equivalence removed"

oldPositiveNegativeOutcomeCrosswalk : DraftCrosswalk
oldPositiveNegativeOutcomeCrosswalk = draft-crosswalk
  Lineage.trackedChangesSnapshot Lineage.latestProposalSnapshot retainedAndNarrowed
  "earlier hypotheses allowed positive and negative outcomes depending on beliefs/practices, family dynamics and social context"
  "latest introduction explicitly retains religious belonging as potentially protective for some people and H4 models support/non-coercive communities as moderators"
  "the later proposal narrows the empirical target from religion-as-label to measured coercive practice while preserving risk and resilience"

oldANOVACrosswalk : DraftCrosswalk
oldANOVACrosswalk = draft-crosswalk
  Lineage.draft3Snapshot Lineage.latestProposalSnapshot redesigned
  "earlier study plan proposed repeated-measures ANOVA and HLM"
  "latest quantitative plan makes linear/generalised linear mixed-effects models primary and reserves propensity/IPW methods as sensitivity analyses"
  "analysis redesign improves fit to irregular follow-up and missing observations but does not itself validate any hypothesis"

------------------------------------------------------------------------
-- Claim/source attribution boundary.
------------------------------------------------------------------------

data PaperCitationPromotesVerifiedSource : Set where

data HypothesisPromotesFinding : Set where

data StatisticalDetectabilityPromotesClinicalImportance : Set where

data SourceDocumentPromotesExternalAuthority : Set where

paperCitationDoesNotPromoteVerifiedSource : PaperCitationPromotesVerifiedSource → ⊥
paperCitationDoesNotPromoteVerifiedSource ()

hypothesisDoesNotPromoteFinding : HypothesisPromotesFinding → ⊥
hypothesisDoesNotPromoteFinding ()

statisticalDetectabilityDoesNotPromoteClinicalImportance :
  StatisticalDetectabilityPromotesClinicalImportance → ⊥
statisticalDetectabilityDoesNotPromoteClinicalImportance ()

sourceDocumentDoesNotPromoteExternalAuthority : SourceDocumentPromotesExternalAuthority → ⊥
sourceDocumentDoesNotPromoteExternalAuthority ()

record SectionHypothesisManifestBoundary : Set where
  constructor section-hypothesis-manifest-boundary
  field
    latestProposalIsCanonicalCurrentSurface : Bool
    olderDraftsDeletedFromProvenance : Bool
    allFiveHypothesesTyped : Bool
    hypothesesTreatedAsFindings : Bool
    citationsTreatedAsVerifiedBecauseListed : Bool
    designLimitsCausalPromotion : Bool
    riskAndResilienceBothPreserved : Bool
    backwardSafeWordingInstalled : Bool

canonicalSectionHypothesisManifestBoundary : SectionHypothesisManifestBoundary
canonicalSectionHypothesisManifestBoundary =
  section-hypothesis-manifest-boundary true false true false false true true true
