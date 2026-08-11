module DASHI.Governance.ChildReligiousCoercionResearchBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion
import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as Diachronic
import DASHI.Governance.GuardedPropositionResponseTree as Guarded
import DASHI.Biology.TraumaMemoryAttractorPortfolio as TraumaMemory
import DASHI.Biology.ChildAuthorityTraumaSourceAtlas as Sources

data ExposureDimension : Set where
  fearExposure compulsionExposure punishmentExposure isolationExposure : ExposureDimension
  institutionalBetrayalExposure directAbuseExposure epistemicClosureExposure disclosureSuppressionExposure : ExposureDimension

data OutcomeDimension : Set where
  psychologicalDistressOutcome postTraumaticStressOutcome autonomyOutcome selfTrustOutcome : OutcomeDimension
  interpersonalTrustOutcome relationalFunctionOutcome qualityOfLifeOutcome socialSupportOutcome : OutcomeDimension
  resilienceOutcome spiritualWellbeingOutcome : OutcomeDimension

data ComparisonClass : Set where
  coerciveReligiousExposureClass religiousInstitutionalAbuseClass : ComparisonClass
  otherChildhoodAdversityClass lowerExposureComparisonClass : ComparisonClass

data EvidenceLevel : Set where
  definitionEvidence logicalConsequenceEvidence mechanisticPlausibilityEvidence : EvidenceLevel
  crossSectionalAssociationEvidence longitudinalAssociationEvidence quasiCausalEvidence establishedCausalEvidence : EvidenceLevel

record ExposureCoordinate : Set where
  constructor exposureCoordinate
  field
    dimension : ExposureDimension
    frequency severity duration developmentalStage exitRestriction refusalPenalty : Nat
    provenance : String

record OutcomeCoordinate : Set where
  constructor outcomeCoordinate
  field
    outcomeDimension : OutcomeDimension
    observationTime measuredValue : Nat
    measurementInstrument measurementProvenance : String

record ExposureHyperedge : Set where
  constructor exposureHyperedge
  field
    childRole authorityRole institutionRole : Coercion.RelationalRole
    propositionNode : Guarded.PropositionNode
    exposureCoordinates : List ExposureCoordinate
    observedBehaviour : Coercion.ObservedBehaviour
    disclosureAvailable : Bool
    edgeProvenance : String

record ParticipantExposureHistory : Set where
  constructor participantExposureHistory
  field
    edges : List ExposureHyperedge
    comparisonClass : ComparisonClass
    otherAdversityCovariates familyContextCovariates : List String
    socioeconomicCovariates currentSupportCovariates : List String

record ResearchClaim : Set where
  constructor researchClaim
  field
    claimLabel : String
    exposureDimensions : List ExposureDimension
    outcomeDimensions : List OutcomeDimension
    evidenceLevel : EvidenceLevel
    associational causal candidateOnly : Bool
    claimBoundary : String

coercionDistressAssociationClaim : ResearchClaim
coercionDistressAssociationClaim =
  researchClaim
    "Greater coercive childhood exposure may be associated with greater later distress."
    (fearExposure ∷ compulsionExposure ∷ punishmentExposure ∷ institutionalBetrayalExposure ∷ [])
    (psychologicalDistressOutcome ∷ postTraumaticStressOutcome ∷ [])
    longitudinalAssociationEvidence true false true
    "Requires longitudinal adjustment for other adversity, family context, socioeconomic conditions, selection, attrition, and measurement error."

autonomyAssociationClaim : ResearchClaim
autonomyAssociationClaim =
  researchClaim
    "Coercive childhood exposure may be associated with reduced later autonomy or self-trust."
    (compulsionExposure ∷ epistemicClosureExposure ∷ disclosureSuppressionExposure ∷ [])
    (autonomyOutcome ∷ selfTrustOutcome ∷ [])
    mechanisticPlausibilityEvidence true false true
    "Mechanistic plausibility is not an established causal estimate."

institutionalBetrayalClaim : ResearchClaim
institutionalBetrayalClaim =
  researchClaim
    "Institutional betrayal may add explanatory value beyond direct exposure alone."
    (institutionalBetrayalExposure ∷ disclosureSuppressionExposure ∷ [])
    (psychologicalDistressOutcome ∷ interpersonalTrustOutcome ∷ relationalFunctionOutcome ∷ [])
    crossSectionalAssociationEvidence true false true
    "The predicate must be established from institution-specific prevention, response, retaliation, investigation, and remedy evidence."

data ChildRightsSurface : Set where
  safetyRight developmentRight conscienceRight participationRight familyRight : ChildRightsSurface
  educationRight privacyRight remedyRight : ChildRightsSurface

canonicalChildRightsSurfaces : List ChildRightsSurface
canonicalChildRightsSurfaces = safetyRight ∷ developmentRight ∷ conscienceRight ∷ participationRight ∷ familyRight ∷ educationRight ∷ privacyRight ∷ remedyRight ∷ []

data FollowUpPoint : Set where baselinePoint oneYearPoint threeYearPoint fiveYearPoint tenYearCandidatePoint : FollowUpPoint

data AnalysisMethod : Set where
  descriptiveAnalysis longitudinalMixedEffectsAnalysis multidimensionalExposureAnalysis : AnalysisMethod
  mediationSensitivityAnalysis moderationAnalysis missingDataSensitivityAnalysis : AnalysisMethod
  qualitativeThematicAnalysis mixedMethodsIntegration : AnalysisMethod

record StudyDesignBoundary : Set where
  constructor studyDesignBoundary
  field
    adultInitialRecruitment partlyRetrospective longitudinalFollowUp mixedMethods : Bool
    dimensionalExposurePrimary comparisonClassesMorallyEquivalent : Bool
    repeatedMeasuresANOVAPrimary mixedEffectsPrimary causalIdentificationComplete : Bool
    traumaInformedSafeguarding survivorConsultation : Bool
    followUpPoints : List FollowUpPoint
    analysisMethods : List AnalysisMethod
    designReading : String

open StudyDesignBoundary public

canonicalStudyDesignBoundary : StudyDesignBoundary
canonicalStudyDesignBoundary =
  studyDesignBoundary true true true true true false false true false true true
    (baselinePoint ∷ oneYearPoint ∷ threeYearPoint ∷ fiveYearPoint ∷ tenYearCandidatePoint ∷ [])
    (descriptiveAnalysis ∷ longitudinalMixedEffectsAnalysis ∷ multidimensionalExposureAnalysis ∷ mediationSensitivityAnalysis ∷ moderationAnalysis ∷ missingDataSensitivityAnalysis ∷ qualitativeThematicAnalysis ∷ mixedMethodsIntegration ∷ [])
    "Prospective follow-up is applied to retrospectively reported childhood exposure. Mixed-effects modelling is primary; causal conclusions remain blocked without stronger identification."

canonicalComparisonClassesNotEquivalent : comparisonClassesMorallyEquivalent canonicalStudyDesignBoundary ≡ false
canonicalComparisonClassesNotEquivalent = refl

canonicalCausalIdentificationIncomplete : causalIdentificationComplete canonicalStudyDesignBoundary ≡ false
canonicalCausalIdentificationIncomplete = refl

record ChildReligiousCoercionResearchBridge : Set where
  constructor childReligiousCoercionResearchBridge
  field
    coercionBoundary : Coercion.DependentAuthorityCoercionBoundary
    diachronicBoundary : Diachronic.DiachronicAuthorityPromotionBoundary
    traumaMemoryBoundary : TraumaMemory.TraumaMemoryAttractorPromotionBoundary
    sourceCount : Nat
    rightsSurfaces : List ChildRightsSurface
    studyBoundary : StudyDesignBoundary
    canonicalClaims : List ResearchClaim
    religionInherentlyHarmfulPromotion : Bool
    religionInherentlyHarmfulPromotionIsFalse : religionInherentlyHarmfulPromotion ≡ false
    comparisonGroupEquivalencePromotion : Bool
    comparisonGroupEquivalencePromotionIsFalse : comparisonGroupEquivalencePromotion ≡ false
    associationEqualsCausationPromotion : Bool
    associationEqualsCausationPromotionIsFalse : associationEqualsCausationPromotion ≡ false
    participantNarrativeEqualsClinicalDiagnosisPromotion : Bool
    participantNarrativeEqualsClinicalDiagnosisPromotionIsFalse : participantNarrativeEqualsClinicalDiagnosisPromotion ≡ false
    strongBeliefEqualsCoercionPromotion : Bool
    strongBeliefEqualsCoercionPromotionIsFalse : strongBeliefEqualsCoercionPromotion ≡ false
    researchReading : String

open ChildReligiousCoercionResearchBridge public

canonicalChildReligiousCoercionResearchBridge : ChildReligiousCoercionResearchBridge
canonicalChildReligiousCoercionResearchBridge =
  childReligiousCoercionResearchBridge
    Coercion.canonicalDependentAuthorityCoercionBoundary
    Diachronic.canonicalDiachronicAuthorityPromotionBoundary
    TraumaMemory.canonicalTraumaMemoryAttractorPromotionBoundary
    Sources.canonicalChildAuthorityTraumaSourceCount
    canonicalChildRightsSurfaces canonicalStudyDesignBoundary
    (coercionDistressAssociationClaim ∷ autonomyAssociationClaim ∷ institutionalBetrayalClaim ∷ [])
    false refl false refl false refl false refl false refl
    "The research bridge tests dimensional coercion, fear, epistemic closure, disclosure suppression, direct abuse, and institutional betrayal against longitudinal psychosocial outcomes. Religion is not equated with harm, comparison classes are not equated, and observational association is not promoted to causation."

canonicalAssociationEqualsCausationPromotionFalse :
  associationEqualsCausationPromotion canonicalChildReligiousCoercionResearchBridge ≡ false
canonicalAssociationEqualsCausationPromotionFalse =
  associationEqualsCausationPromotionIsFalse canonicalChildReligiousCoercionResearchBridge
