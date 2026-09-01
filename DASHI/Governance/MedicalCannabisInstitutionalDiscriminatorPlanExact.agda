module DASHI.Governance.MedicalCannabisInstitutionalDiscriminatorPlanExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ComparativeInstitutionalDiscriminatorExact as Discriminator
import DASHI.Reasoning.SemanticEpistemicInterpretationExact as SemEpi
import DASHI.Governance.MedicalCannabisContaminantSemanticEpistemicExact as Cannabis
import DASHI.Governance.MedicalCannabisComparativeInstitutionalMeaningExact as ComparativeCannabis

------------------------------------------------------------------------
-- STUDY-CLASS BACKPROP FOR THE STRUCTURAL CAPITALISM INTERPRETATION
--
-- These are prospective study classes, not completed studies and not evidence.
-- They spell out which institutional contrast each design would try to make
-- observable. Admission into the generic discriminator calculus still requires
-- a calibrated `BundleSeparates` proof for the realised study.
------------------------------------------------------------------------

data CannabisInstitutionalStudy : Set where
  matchedJurisdictionCannabisStudy
  regulatoryDiscontinuityCannabisStudy
  longitudinalEnforcementChangeCannabisStudy
  ownershipProvisioningContrastCannabisStudy
  medicalCannabisPolicyTransitionStudy
  : CannabisInstitutionalStudy

studyKind : CannabisInstitutionalStudy → Discriminator.InstitutionalStudyKind
studyKind matchedJurisdictionCannabisStudy = Discriminator.matchedJurisdictionStudy
studyKind regulatoryDiscontinuityCannabisStudy = Discriminator.regulatoryDiscontinuityStudy
studyKind longitudinalEnforcementChangeCannabisStudy = Discriminator.longitudinalEnforcementChangeStudy
studyKind ownershipProvisioningContrastCannabisStudy = Discriminator.ownershipProvisioningContrastStudy
studyKind medicalCannabisPolicyTransitionStudy = Discriminator.policyTransitionStudy

record CannabisStudyDemand : Set where
  constructor cannabisStudyDemand
  field
    study : CannabisInstitutionalStudy
    targetMeaning : Cannabis.CannabisMeaning
    targetIsStructuralCapitalism :
      targetMeaning ≡ Cannabis.possibleStructuralCapitalistContribution
    primaryDemand : SemEpi.SystemEvidenceDemand
    secondaryDemand : SemEpi.SystemEvidenceDemand
    matchingDemandReference : String
    outcomeDemandReference : String
    nuisanceDemandReference : String
    calibrationDemandReference : String

open CannabisStudyDemand public

matchedJurisdictionDemand : CannabisStudyDemand
matchedJurisdictionDemand = cannabisStudyDemand
  matchedJurisdictionCannabisStudy
  Cannabis.possibleStructuralCapitalistContribution
  refl
  SemEpi.comparativeInstitutionalDemand
  SemEpi.ownershipMarketStructureDemand
  "match product standards, population, time, assay regime and relevant enforcement capacity"
  "compare contamination/release-control outcomes across institutional ownership/provisioning forms"
  "audit cultivation technology, product mix, reporting intensity, climate and market-selection nuisance"
  "requires prospective protocol + realised data; study label alone is not a separator"

regulatoryDiscontinuityDemand : CannabisStudyDemand
regulatoryDiscontinuityDemand = cannabisStudyDemand
  regulatoryDiscontinuityCannabisStudy
  Cannabis.possibleStructuralCapitalistContribution
  refl
  SemEpi.enforcementPracticeDemand
  SemEpi.causalMediationDemand
  "identify a regulatory threshold/discontinuity with defensible local comparability"
  "test whether contamination/release failures shift across the discontinuity"
  "audit manipulation, sorting, anticipatory behaviour and concurrent policy changes"
  "requires discontinuity diagnostics before causal use"

longitudinalEnforcementDemand : CannabisStudyDemand
longitudinalEnforcementDemand = cannabisStudyDemand
  longitudinalEnforcementChangeCannabisStudy
  Cannabis.possibleStructuralCapitalistContribution
  refl
  SemEpi.enforcementPracticeDemand
  SemEpi.recurrenceDemand
  "hold product/assay definitions stable across enforcement change where possible"
  "compare recurrence and release-failure rate before/after enforcement-capacity change"
  "audit secular trend, assay changes, production turnover and reporting changes"
  "requires time-series calibration and intervention-timing receipt"

ownershipProvisioningDemand : CannabisStudyDemand
ownershipProvisioningDemand = cannabisStudyDemand
  ownershipProvisioningContrastCannabisStudy
  Cannabis.possibleStructuralCapitalistContribution
  refl
  SemEpi.ownershipMarketStructureDemand
  SemEpi.externalityAllocationDemand
  "match therapeutic product class, quality standard and patient population across provisioning forms"
  "compare contamination, recall, remediation and patient-borne cost/risk outcomes"
  "audit scale, procurement, technology, market maturity and regulatory-selection nuisance"
  "requires actual ownership/provisioning realization and comparable outcome data"

policyTransitionDemand : CannabisStudyDemand
policyTransitionDemand = cannabisStudyDemand
  medicalCannabisPolicyTransitionStudy
  Cannabis.possibleStructuralCapitalistContribution
  refl
  SemEpi.counterfactualInstitutionalDemand
  SemEpi.incentiveStructureDemand
  "characterise institutional coordinates before and after a policy/provisioning transition"
  "estimate whether contamination/release outcomes change when incentives/ownership/risk allocation change"
  "audit contemporaneous policy, market, testing and production changes"
  "requires transition provenance and mediation evidence"

canonicalStudyMenu : List CannabisStudyDemand
canonicalStudyMenu =
    matchedJurisdictionDemand
  ∷ regulatoryDiscontinuityDemand
  ∷ longitudinalEnforcementDemand
  ∷ ownershipProvisioningDemand
  ∷ policyTransitionDemand
  ∷ []

------------------------------------------------------------------------
-- Link to the explicit comparative gap. The menu addresses the gap but does not
-- discharge it; all missing measurements/matching/mediation remain open until a
-- realised study is admitted.
------------------------------------------------------------------------

comparativeGap : ComparativeCannabis.ComparativeCannabisEvidenceGap
comparativeGap = ComparativeCannabis.canonicalComparativeEvidenceGap

record MedicalCannabisInstitutionalDiscriminatorPlanBoundary : Set where
  constructor medicalCannabisInstitutionalDiscriminatorPlanBoundary
  field
    namingNaturalExperimentCreatesEmpiricalEvidence : Bool
    namingNaturalExperimentCreatesEmpiricalEvidenceIsFalse :
      namingNaturalExperimentCreatesEmpiricalEvidence ≡ false
    studyMenuCanBeGeneratedFromPoliticalEconomyEvidenceGap : Bool
    studyMenuCanBeGeneratedFromPoliticalEconomyEvidenceGapIsTrue :
      studyMenuCanBeGeneratedFromPoliticalEconomyEvidenceGap ≡ true
    admittedDiscriminatorStillRequiresCalibratedSeparation : Bool
    admittedDiscriminatorStillRequiresCalibratedSeparationIsTrue :
      admittedDiscriminatorStillRequiresCalibratedSeparation ≡ true
    oneInstitutionalContrastSettlesCompleteCapitalismTheory : Bool
    oneInstitutionalContrastSettlesCompleteCapitalismTheoryIsFalse :
      oneInstitutionalContrastSettlesCompleteCapitalismTheory ≡ false

canonicalMedicalCannabisInstitutionalDiscriminatorPlanBoundary :
  MedicalCannabisInstitutionalDiscriminatorPlanBoundary
canonicalMedicalCannabisInstitutionalDiscriminatorPlanBoundary =
  medicalCannabisInstitutionalDiscriminatorPlanBoundary
    false refl
    true refl
    true refl
    false refl
