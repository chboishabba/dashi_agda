module DASHI.Cognition.PNF.SensibLawClimateForumCompulsionEnforcementLatticeExact where

------------------------------------------------------------------------
-- CLIMATE FORUM / COMPULSION / ENFORCEMENT LATTICE
--
-- A legal finding, remedy, bindingness, domestic enforceability, constitutional
-- invalidity power and actual compliance are separate coordinates. This owner
-- compares Pabai, Daniel Billy and Neubauer without pretending their legal
-- systems or causes of action are interchangeable.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data ForumKind : Set where
  domesticOrdinaryCourt : ForumKind
  domesticConstitutionalCourt : ForumKind
  internationalTreatyBody : ForumKind
  internationalCourtAdvisory : ForumKind


data NormSource : Set where
  commonLawNegligence : NormSource
  domesticConstitutionalRights : NormSource
  treatyHumanRights : NormSource
  generalInternationalLaw : NormSource


data DecisionForm : Set where
  meritsJudgment : DecisionForm
  constitutionalIncompatibilityOrder : DecisionForm
  treatyBodyViews : DecisionForm
  advisoryOpinion : DecisionForm


data EnforcementChannel : Set where
  domesticJudicialExecution : EnforcementChannel
  legislativeCorrectionDuty : EnforcementChannel
  treatyImplementationAndReporting : EnforcementChannel
  diplomaticAndInterpretivePressure : EnforcementChannel
  noPositiveDutyRecognised : EnforcementChannel


data ProceedingState : Set where
  firstInstanceDecidedAppealPending : ProceedingState
  finalDomesticConstitutionalDecision : ProceedingState
  treatyBodyViewsAdopted : ProceedingState
  advisoryOpinionIssued : ProceedingState


record ForumEnforcementReceipt : Set where
  constructor forum-enforcement-receipt
  field
    forumReference : String
    forumKind : ForumKind
    normSource : NormSource
    decisionForm : DecisionForm
    proceedingState : ProceedingState
    violationOrInvalidityFound : Bool
    positiveRemedySpecified : Bool
    directlySelfExecutingInAustralianDomesticCourt : Bool
    canInvalidateLegislationOnThisNormSource : Bool
    canRequireLegislativeCorrection : Bool
    enforcementChannel : EnforcementChannel
    actualComplianceEstablishedByReceipt : Bool
    actualComplianceEstablishedByReceiptIsFalse :
      actualComplianceEstablishedByReceipt ≡ false
    sourceReference : String

open ForumEnforcementReceipt public

pabaiFirstInstanceAndAppeal : ForumEnforcementReceipt
pabaiFirstInstanceAndAppeal = forum-enforcement-receipt
  "Pabai Pabai & Anor v Commonwealth of Australia; VID622/2021 first instance; VID1479/2025 appeal"
  domesticOrdinaryCourt
  commonLawNegligence
  meritsJudgment
  firstInstanceDecidedAppealPending
  false
  false
  true
  false
  false
  noPositiveDutyRecognised
  false refl
  "Federal Court of Australia public online file; [2025] FCA 796; 2026 appeal submissions and oral outlines"

pabaiAppealRemainsLive :
  proceedingState pabaiFirstInstanceAndAppeal ≡ firstInstanceDecidedAppealPending
pabaiAppealRemainsLive = refl

billyTorresStraitViews : ForumEnforcementReceipt
billyTorresStraitViews = forum-enforcement-receipt
  "Daniel Billy and others v Australia, communication 3624/2019"
  internationalTreatyBody
  treatyHumanRights
  treatyBodyViews
  treatyBodyViewsAdopted
  true
  true
  false
  false
  false
  treatyImplementationAndReporting
  false refl
  "UN Human Rights Committee CCPR/C/135/D/3624/2019, Views adopted 21 July 2022: violations of ICCPR arts 17 and 27; effective remedy/full reparation, adequate compensation, consultation, protective measures, monitoring, prevention and 180-day implementation reporting"

billyFoundViolation : violationOrInvalidityFound billyTorresStraitViews ≡ true
billyFoundViolation = refl

billySpecifiedPositiveRemedy : positiveRemedySpecified billyTorresStraitViews ≡ true
billySpecifiedPositiveRemedy = refl

billyNotDirectAustralianDomesticExecution :
  directlySelfExecutingInAustralianDomesticCourt billyTorresStraitViews ≡ false
billyNotDirectAustralianDomesticExecution = refl

neubauerConstitutionalDecision : ForumEnforcementReceipt
neubauerConstitutionalDecision = forum-enforcement-receipt
  "Neubauer et al v Germany, Federal Constitutional Court, 1 BvR 2656/18 et al"
  domesticConstitutionalCourt
  domesticConstitutionalRights
  constitutionalIncompatibilityOrder
  finalDomesticConstitutionalDecision
  true
  true
  false
  true
  true
  legislativeCorrectionDuty
  false refl
  "Bundesverfassungsgericht order 24 March 2021, published 29 April 2021: KSG provisions incompatible with fundamental rights insofar as post-2030 reductions were insufficiently specified; legislature required to regulate further reduction targets by 31 December 2022 while challenged provisions temporarily remained applicable"

neubauerCanRequireLegislativeCorrection :
  canRequireLegislativeCorrection neubauerConstitutionalDecision ≡ true
neubauerCanRequireLegislativeCorrection = refl

record ExistingDutyCompulsionBoundary : Set where
  constructor existing-duty-compulsion-boundary
  field
    mandamusCanCompelExistingLegalDuty : Bool
    mandamusCanCompelExistingLegalDutyIsTrue :
      mandamusCanCompelExistingLegalDuty ≡ true
    mandamusCreatesNewSubstantiveDuty : Bool
    mandamusCreatesNewSubstantiveDutyIsFalse : mandamusCreatesNewSubstantiveDuty ≡ false
    mandamusDictatesOutcomeOfOpenDiscretion : Bool
    mandamusDictatesOutcomeOfOpenDiscretionIsFalse :
      mandamusDictatesOutcomeOfOpenDiscretion ≡ false
    mandamusRunsAgainstParliamentToLegislate : Bool
    mandamusRunsAgainstParliamentToLegislateIsFalse :
      mandamusRunsAgainstParliamentToLegislate ≡ false

open ExistingDutyCompulsionBoundary public

canonicalExistingDutyCompulsionBoundary : ExistingDutyCompulsionBoundary
canonicalExistingDutyCompulsionBoundary = existing-duty-compulsion-boundary
  true refl
  false refl
  false refl
  false refl

data CulturalLossLegalRegime : Set where
  generalNegligenceRegime : CulturalLossLegalRegime
  nativeTitleCompensationRegime : CulturalLossLegalRegime


data CulturalLossCompensabilitySurface : Set where
  notRecognisedOnCurrentNegligenceRoute : CulturalLossCompensabilitySurface
  culturallyCompensableUnderNativeTitleStatute : CulturalLossCompensabilitySurface


culturalLossVisibility : CulturalLossLegalRegime → CulturalLossCompensabilitySurface
culturalLossVisibility generalNegligenceRegime = notRecognisedOnCurrentNegligenceRoute
culturalLossVisibility nativeTitleCompensationRegime = culturallyCompensableUnderNativeTitleStatute

regimeChangesLegalVisibility :
  culturalLossVisibility generalNegligenceRegime ≡
  culturalLossVisibility nativeTitleCompensationRegime → ⊥
regimeChangesLegalVisibility ()

record CulturalLossRegimeBoundary : Set where
  constructor cultural-loss-regime-boundary
  field
    pabaiAilanKastomAndTimberCreekLossAreFactuallyIdentical : Bool
    pabaiAilanKastomAndTimberCreekLossAreFactuallyIdenticalIsFalse :
      pabaiAilanKastomAndTimberCreekLossAreFactuallyIdentical ≡ false
    relatedCulturalSpiritualHarmsCanReceiveDifferentLegalTreatment : Bool
    relatedCulturalSpiritualHarmsCanReceiveDifferentLegalTreatmentIsTrue :
      relatedCulturalSpiritualHarmsCanReceiveDifferentLegalTreatment ≡ true
    legalRegimeDeterminesWhetherTheUnderlyingHarmExists : Bool
    legalRegimeDeterminesWhetherTheUnderlyingHarmExistsIsFalse :
      legalRegimeDeterminesWhetherTheUnderlyingHarmExists ≡ false
    timberCreekStatutoryCompensationAutomaticallyExtendsToNegligence : Bool
    timberCreekStatutoryCompensationAutomaticallyExtendsToNegligenceIsFalse :
      timberCreekStatutoryCompensationAutomaticallyExtendsToNegligence ≡ false

open CulturalLossRegimeBoundary public

canonicalCulturalLossRegimeBoundary : CulturalLossRegimeBoundary
canonicalCulturalLossRegimeBoundary = cultural-loss-regime-boundary
  false refl
  true refl
  false refl
  false refl

record ForumCapabilityBoundary : Set where
  constructor forum-capability-boundary
  field
    violationFindingEqualsDomesticExecution : Bool
    violationFindingEqualsDomesticExecutionIsFalse :
      violationFindingEqualsDomesticExecution ≡ false
    bindingJudgmentAutomaticallyCreatesPositiveDuty : Bool
    bindingJudgmentAutomaticallyCreatesPositiveDutyIsFalse :
      bindingJudgmentAutomaticallyCreatesPositiveDuty ≡ false
    treatyBodyViewsEqualDomesticWrit : Bool
    treatyBodyViewsEqualDomesticWritIsFalse : treatyBodyViewsEqualDomesticWrit ≡ false
    constitutionalInvalidityEqualsActualCompliance : Bool
    constitutionalInvalidityEqualsActualComplianceIsFalse :
      constitutionalInvalidityEqualsActualCompliance ≡ false
    forumCapabilityIsSingleScalar : Bool
    forumCapabilityIsSingleScalarIsFalse : forumCapabilityIsSingleScalar ≡ false
    causeOfActionVisibilityCreatesUnderlyingHarm : Bool
    causeOfActionVisibilityCreatesUnderlyingHarmIsFalse :
      causeOfActionVisibilityCreatesUnderlyingHarm ≡ false

open ForumCapabilityBoundary public

canonicalForumCapabilityBoundary : ForumCapabilityBoundary
canonicalForumCapabilityBoundary = forum-capability-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl

data FindingViolationMeansDomesticCompulsion : Set where
data TreatyBodyViewIsAustralianDomesticMandamus : Set where
data PabaiFirstInstanceIsFinalAppealDisposition : Set where
data DifferentCompensationRegimeMeansDifferentUnderlyingReality : Set where
data NeubauerMeansEveryConstitutionalCourtCanOrderClimateTargets : Set where

findingDoesNotEqualDomesticCompulsion : FindingViolationMeansDomesticCompulsion → ⊥
findingDoesNotEqualDomesticCompulsion ()

treatyViewDoesNotBecomeAustralianMandamus : TreatyBodyViewIsAustralianDomesticMandamus → ⊥
treatyViewDoesNotBecomeAustralianMandamus ()

pabaiFirstInstanceIsNotEncodedAsFinalAppeal : PabaiFirstInstanceIsFinalAppealDisposition → ⊥
pabaiFirstInstanceIsNotEncodedAsFinalAppeal ()

regimeDifferenceDoesNotCreateDifferentUnderlyingReality :
  DifferentCompensationRegimeMeansDifferentUnderlyingReality → ⊥
regimeDifferenceDoesNotCreateDifferentUnderlyingReality ()

neubauerDoesNotUniversaliseAcrossConstitutions :
  NeubauerMeansEveryConstitutionalCourtCanOrderClimateTargets → ⊥
neubauerDoesNotUniversaliseAcrossConstitutions ()
