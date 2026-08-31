module DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownDocumentLineageExact as Lineage

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: STUDY-DESIGN BIDI OWNER
--
-- Source-calibrated to the latest supplied proposal.  Structurally cross-
-- pollinated with PR #650 / DASHI.Reasoning.EvidenceDesignAdmissibilityExact,
-- whose core rule is that evidence admissibility is relational to the exact
-- obligation and that no universal study-design hierarchy is assumed.
--
-- This branch does not import the unmerged #650 owner; it records the same
-- audit coordinates locally so the paper-specific lane remains compilable on
-- master while retaining explicit upstream provenance.
------------------------------------------------------------------------

data BrownDesignKind : Set where
  prospectiveLongitudinalMultiCohort : BrownDesignKind
  retrospectiveExposureAssessment : BrownDesignKind
  nestedQualitativeInterview : BrownDesignKind
  mixedMethodsIntegration : BrownDesignKind
  sensitivityAnalysis : BrownDesignKind

record CrossPollinatedDesignProvenance : Set where
  constructor cross-pollinated-design-provenance
  field
    upstreamPR : String
    upstreamOwner : String
    transferMode : String
    noImportClaim : Bool

canonicalDesignProvenance : CrossPollinatedDesignProvenance
canonicalDesignProvenance =
  cross-pollinated-design-provenance
    "PR #650"
    "DASHI.Reasoning.EvidenceDesignAdmissibilityExact"
    "structural cross-pollination of design-receipt and obligation-relative admissibility coordinates"
    true

record StudyDesignReceipt : Set where
  constructor study-design-receipt
  field
    source : Lineage.BrownDocumentSnapshot
    designKind : BrownDesignKind
    population : String
    samplingFrame : String
    comparator : String
    exposureTiming : String
    repeatedMeasurement : String
    measurementValidity : String
    attritionHandling : String
    confoundingControl : String
    multiplicityHandling : String
    effectSizeSurface : String
    uncertaintySurface : String
    externalValidityDomain : String
    participantRole : String
    designLimitation : String

open StudyDesignReceipt public

canonicalLongitudinalReceipt : StudyDesignReceipt
canonicalLongitudinalReceipt = study-design-receipt
  Lineage.latestProposalSnapshot
  prospectiveLongitudinalMultiCohort
  "adults aged 18 years or older recalling childhood experiences; diverse age, gender, culture, socioeconomic status, disability, sexuality, geography and current religious identity sought"
  "recruitment across survivor, mental-health, community, secular/religious, university, public-advertising and social-media channels; stratification proposed to reduce advocacy-network over-representation"
  "dimensionally measured exposure plus descriptive groups A-D; groups are not asserted to have morally or clinically equivalent harms"
  "childhood exposure precedes enrolment and is therefore partly retrospective even though adult outcomes are followed prospectively"
  "baseline, 12 months, 3 years, 5 years, and subject to funding/retention 10 years"
  "validated outcome instruments preferred; any new coercive-religious-experience measure requires pilot testing and psychometric validation"
  "oversampling anticipated; mixed-effects models selected partly for incomplete observations and unequal follow-up intervals"
  "other adverse childhood experiences, family environment, socioeconomic conditions, demographics, current support/religion/treatment and baseline mental health considered; unmeasured confounding remains"
  "correction for multiple testing where appropriate"
  "effect sizes required"
  "confidence intervals, model diagnostics and explicit uncertainty required"
  "claims bounded to recruited populations, measures, cultures and observed follow-up; transport requires separate justification"
  "participants are measured subjects and qualitative informants; survivor consultation is proposed for design/governance but does not automatically make every participant a governing co-researcher"
  "observational exposure history prevents the design by itself from establishing causation"

canonicalQualitativeReceipt : StudyDesignReceipt
canonicalQualitativeReceipt = study-design-receipt
  Lineage.latestProposalSnapshot
  nestedQualitativeInterview
  "nested adult qualitative cohort"
  "purposive/nested selection within the wider recruited study, to be specified"
  "cross-case comparison may examine different exposure histories without converting narrative difference into prevalence estimates"
  "retrospective interpretation of childhood experience with repeated interviews at selected follow-up points"
  "semi-structured interviews at baseline and selected later points"
  "reflexive thematic or framework analysis; multidisciplinary coding team; audit trail and researcher positionality"
  "qualitative retention and missing follow-up must be documented"
  "alternative interpretations and contextual explanations retained rather than statistically 'controlled away'"
  "not a primary multiplicity framework; coding/search-space decisions still require audit trail"
  "qualitative claims report themes, mechanisms, contradictions, meanings and negative cases rather than population effect sizes"
  "interpretive uncertainty, disagreement and silence between data sources retained"
  "participants and contexts represented in the qualitative sample"
  "participant narrative is evidence about experience/meaning; it is not automatically a clinical diagnosis or population-frequency estimate"
  "qualitative evidence is not merely illustrative of quantitative results and does not by itself establish population prevalence or causal effect"

record MixedMethodsIntegrationReceipt : Set where
  constructor mixed-methods-integration-receipt
  field
    source : Lineage.BrownDocumentSnapshot
    quantitativeLane : StudyDesignReceipt
    qualitativeLane : StudyDesignReceipt
    integrationSurface : String
    convergenceMayBeReported : Bool
    divergenceMayBeReported : Bool
    silenceMayBeReported : Bool
    forcedSingleNarrative : Bool

canonicalMixedMethodsIntegration : MixedMethodsIntegrationReceipt
canonicalMixedMethodsIntegration = mixed-methods-integration-receipt
  Lineage.latestProposalSnapshot
  canonicalLongitudinalReceipt
  canonicalQualitativeReceipt
  "joint displays, cross-case comparison and explanatory analysis"
  true true true false

------------------------------------------------------------------------
-- Proposal-specific design corrections visible across the document lineage.
------------------------------------------------------------------------

data LegacyDesignMove : Set where
  repeatedMeasuresANOVAToMixedEffects : LegacyDesignMove
  fixedTraumaGroupEquivalenceToDimensionalExposure : LegacyDesignMove
  broadFocusGroupUseToSensitivityRestrictedUse : LegacyDesignMove
  instrumentListToSystematicReviewAndValidationGate : LegacyDesignMove

record DesignRevisionReceipt : Set where
  constructor design-revision-receipt
  field
    move : LegacyDesignMove
    earlierSurface : String
    latestSurface : String
    bidiReading : String

mixedEffectsRevision : DesignRevisionReceipt
mixedEffectsRevision = design-revision-receipt
  repeatedMeasuresANOVAToMixedEffects
  "earlier Draft 3 proposed repeated-measures ANOVA alongside HLM"
  "latest proposal makes linear/generalised linear mixed-effects models primary and explicitly motivates unequal intervals, incomplete observations, individual trajectories and time-varying covariates"
  "later method is a refinement of the analysis plan, not evidence that earlier empirical hypotheses are true"

dimensionalExposureRevision : DesignRevisionReceipt
dimensionalExposureRevision = design-revision-receipt
  fixedTraumaGroupEquivalenceToDimensionalExposure
  "earlier draft foregrounded named trauma/religion/control cohorts"
  "latest proposal analyses exposure dimensionally and states descriptive groups must not be described as experiencing equivalent harms"
  "comparison is an identification strategy, not moral or clinical equivalence"

instrumentValidationRevision : DesignRevisionReceipt
instrumentValidationRevision = design-revision-receipt
  instrumentListToSystematicReviewAndValidationGate
  "earlier draft listed candidate instruments as a study toolkit"
  "latest proposal requires instrument selection after systematic review plus checks of licensing, target-population validation, cultural appropriateness, respondent burden and repeated-measure compatibility"
  "naming an instrument is not a validity receipt for this target population"

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data LongitudinalDesignPromotesCausation : Set where

data CovariateAdjustmentPromotesNoConfounding : Set where

data ComparatorPromotesEquivalentHarm : Set where

data QualitativeThemePromotesPrevalence : Set where

data ProposedMeasurePromotesValidatedMeasure : Set where

data MixedMethodsPromotesForcedConvergence : Set where

longitudinalDoesNotPromoteCausation : LongitudinalDesignPromotesCausation → ⊥
longitudinalDoesNotPromoteCausation ()

adjustmentDoesNotPromoteNoConfounding : CovariateAdjustmentPromotesNoConfounding → ⊥
adjustmentDoesNotPromoteNoConfounding ()

comparatorDoesNotPromoteEquivalentHarm : ComparatorPromotesEquivalentHarm → ⊥
comparatorDoesNotPromoteEquivalentHarm ()

qualitativeThemeDoesNotPromotePrevalence : QualitativeThemePromotesPrevalence → ⊥
qualitativeThemeDoesNotPromotePrevalence ()

proposedMeasureDoesNotPromoteValidatedMeasure : ProposedMeasurePromotesValidatedMeasure → ⊥
proposedMeasureDoesNotPromoteValidatedMeasure ()

mixedMethodsDoesNotPromoteForcedConvergence : MixedMethodsPromotesForcedConvergence → ⊥
mixedMethodsDoesNotPromoteForcedConvergence ()

record JohnAnthonyBrownStudyDesignBoundary : Set where
  constructor john-anthony-brown-study-design-boundary
  field
    latestProposalUsesLongitudinalMixedMethods : Bool
    childhoodExposureIsProspectivelyRandomised : Bool
    primaryAnalysisUsesMixedEffects : Bool
    exposureGroupsAssertEquivalentHarms : Bool
    newExposureMeasureRequiresValidation : Bool
    propensityMethodsEraseUnmeasuredConfounding : Bool
    qualitativeFindingsReducedToIllustration : Bool
    convergenceDivergenceAndSilenceRetained : Bool
    pr650StructuralCrossPollinationRecorded : Bool

canonicalJohnAnthonyBrownStudyDesignBoundary : JohnAnthonyBrownStudyDesignBoundary
canonicalJohnAnthonyBrownStudyDesignBoundary =
  john-anthony-brown-study-design-boundary
    true false true false true false false true true
