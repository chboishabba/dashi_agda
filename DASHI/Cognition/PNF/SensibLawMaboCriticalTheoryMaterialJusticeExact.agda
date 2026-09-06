module DASHI.Cognition.PNF.SensibLawMaboCriticalTheoryMaterialJusticeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboColonialSovereigntyCriticalResidualExact as Critical
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Governance.SituatedConstituency as Situated

------------------------------------------------------------------------
-- Critical-theory/material-justice layer.
--
-- This owner intentionally separates:
--   * court holdings and court-internal premises;
--   * official empirical/public-administration receipts;
--   * critical-theory interpretive lenses;
--   * normative/decolonial hypotheses.
--
-- Agda may type the relationships and non-collapse rules.  It does not turn a
-- critical lens into an adjudicated world-truth proposition merely by formalising
-- it.
------------------------------------------------------------------------

data ClaimAuthorityClass : Set where
  courtHoldingClass
  courtInternalPremiseClass
  officialEmpiricalReceiptClass
  criticalTheoryLensClass
  decolonialNormativeHypothesisClass
  affectedCommunityClaimClass
  : ClaimAuthorityClass

data CriticalCourtFeature : Set where
  crownSovereigntyTreatedAsNonJusticiable
  consequencesOfCrownSovereigntyRemainJusticiable
  recognitionPowerHeldByColonialState
  remedyDefinedInsideColonialLegalOrder
  affectedCommunityNormativeSourceExternalToCourt
  landReturnNotEntailedByRecognition
  : CriticalCourtFeature

data LensStatus : Set where
  lensCandidate
  sourceBackedCriticalLens
  contestedInterpretiveFramework
  adjudicatedWorldTruth
  : LensStatus

record CriticalCourtLens : Set where
  constructor criticalCourtLens
  field
    lensReference : String
    authorityClass : ClaimAuthorityClass
    status : LensStatus
    features : List CriticalCourtFeature
    courtInternalLegalityEqualsColonialLegitimacy : Bool
    courtInternalLegalityEqualsColonialLegitimacyIsFalse : courtInternalLegalityEqualsColonialLegitimacy ≡ false
    courtRecognitionEqualsMaterialJustice : Bool
    courtRecognitionEqualsMaterialJusticeIsFalse : courtRecognitionEqualsMaterialJustice ≡ false
    selfLegitimatingJurisdictionConcernRecorded : Bool
    selfLegitimatingJurisdictionConcernRecordedIsTrue : selfLegitimatingJurisdictionConcernRecorded ≡ true
    finalWorldTruthClaimed : Bool
    finalWorldTruthClaimedIsFalse : finalWorldTruthClaimed ≡ false
open CriticalCourtLens public

westernCourtStructuralSupremacyLens : CriticalCourtLens
westernCourtStructuralSupremacyLens = criticalCourtLens
  "critical-theory lens: colonial court supremacy / white-supremacist institutional structure hypothesis"
  criticalTheoryLensClass
  contestedInterpretiveFramework
  (crownSovereigntyTreatedAsNonJusticiable
    ∷ consequencesOfCrownSovereigntyRemainJusticiable
    ∷ recognitionPowerHeldByColonialState
    ∷ remedyDefinedInsideColonialLegalOrder
    ∷ affectedCommunityNormativeSourceExternalToCourt
    ∷ landReturnNotEntailedByRecognition
    ∷ [])
  false refl
  false refl
  true refl
  false refl

------------------------------------------------------------------------
-- Mabo jurisdictional insulation receipt.
------------------------------------------------------------------------

record MaboSovereigntyJusticiabilityReceipt : Set where
  constructor maboSovereigntyJusticiabilityReceipt
  field
    sourceReference : String
    acquisitionOfCrownSovereigntyJusticiable : Bool
    acquisitionOfCrownSovereigntyJusticiableIsFalse : acquisitionOfCrownSovereigntyJusticiable ≡ false
    municipalConsequencesJusticiable : Bool
    municipalConsequencesJusticiableIsTrue : municipalConsequencesJusticiable ≡ true
    courtPremiseProvesIndigenousCession : Bool
    courtPremiseProvesIndigenousCessionIsFalse : courtPremiseProvesIndigenousCession ≡ false
    courtPremiseProvesColonialLegitimacy : Bool
    courtPremiseProvesColonialLegitimacyIsFalse : courtPremiseProvesColonialLegitimacy ≡ false
open MaboSovereigntyJusticiabilityReceipt public

maboSovereigntyJusticiability : MaboSovereigntyJusticiabilityReceipt
maboSovereigntyJusticiability = maboSovereigntyJusticiabilityReceipt
  "Mabo (No 2) Brennan J sovereignty section; acquisition treated as non-justiciable, municipal consequences as justiciable"
  false refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- Material-efficacy receipts.
------------------------------------------------------------------------

data MaterialJusticeDomain : Set where
  landProtectionDomain
  landRestitutionDomain
  sovereigntyRecognitionDomain
  politicalRecognitionDomain
  apologyAcknowledgementDomain
  socioeconomicOutcomeDomain
  institutionalRepairDomain
  : MaterialJusticeDomain

record BarrambinMaterialEfficacyReceipt : Set where
  constructor barrambinMaterialEfficacyReceipt
  field
    sourceReference : String
    significanceAcknowledged : Bool
    significanceAcknowledgedIsTrue : significanceAcknowledged ≡ true
    emergencyProtectionGranted : Bool
    emergencyProtectionGrantedIsFalse : emergencyProtectionGranted ≡ false
    drillingAlreadyCompleteAtDecision : Bool
    drillingAlreadyCompleteAtDecisionIsTrue : drillingAlreadyCompleteAtDecision ≡ true
    recognitionGuaranteedProtection : Bool
    recognitionGuaranteedProtectionIsFalse : recognitionGuaranteedProtection ≡ false
    domain : MaterialJusticeDomain
open BarrambinMaterialEfficacyReceipt public

barrambin2026Receipt : BarrambinMaterialEfficacyReceipt
barrambin2026Receipt = barrambinMaterialEfficacyReceipt
  "DCCEEW 2026 Barrambin (Victoria Park) section 9 reasons and Minister statement"
  true refl
  false refl
  true refl
  false refl
  landProtectionDomain

record ClosingGapOutcomeReceipt : Set where
  constructor closingGapOutcomeReceipt
  field
    sourceReference : String
    targetCount : Nat
    targetsMet : Nat
    targetsOnTrack : Nat
    targetsWorsening : Nat
    structuralCauseIdentifiedByStatisticsAlone : Bool
    structuralCauseIdentifiedByStatisticsAloneIsFalse : structuralCauseIdentifiedByStatisticsAlone ≡ false
    landBackCounterfactualProved : Bool
    landBackCounterfactualProvedIsFalse : landBackCounterfactualProved ≡ false
open ClosingGapOutcomeReceipt public

closingGapJuly2026 : ClosingGapOutcomeReceipt
closingGapJuly2026 = closingGapOutcomeReceipt
  "Productivity Commission Closing the Gap Annual Data Compilation Report July 2026"
  19
  1
  3
  4
  false refl
  false refl

record VoiceReferendumReceipt : Set where
  constructor voiceReferendumReceipt
  field
    sourceReference : String
    nationalYesBasisPoints : Nat
    nationalNoBasisPoints : Nat
    referendumCarried : Bool
    referendumCarriedIsFalse : referendumCarried ≡ false
    referendumOutcomeDeterminesIndigenousSovereignty : Bool
    referendumOutcomeDeterminesIndigenousSovereigntyIsFalse : referendumOutcomeDeterminesIndigenousSovereignty ≡ false
open VoiceReferendumReceipt public

voiceReferendum2023 : VoiceReferendumReceipt
voiceReferendum2023 = voiceReferendumReceipt
  "Australian Electoral Commission returned writ, 2023 referendum"
  3994
  6006
  false refl
  false refl

record NationalApologyReceipt : Set where
  constructor nationalApologyReceipt
  field
    sourceReference : String
    apologyIssued : Bool
    apologyIssuedIsTrue : apologyIssued ≡ true
    landRestitutionEffect : Bool
    landRestitutionEffectIsFalse : landRestitutionEffect ≡ false
    sovereigntyRecognitionEffect : Bool
    sovereigntyRecognitionEffectIsFalse : sovereigntyRecognitionEffect ≡ false
open NationalApologyReceipt public

ruddApology2008 : NationalApologyReceipt
ruddApology2008 = nationalApologyReceipt
  "Parliament of Australia National Apology, 13 February 2008"
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- Recognition / repair / land-return are independent fibres.
------------------------------------------------------------------------

data RepairAxis : Set where
  nativeTitleRecognitionAxis
  indigenousSovereigntyRecognitionAxis
  landProtectionAxis
  landReturnAxis
  treatyAgreementAxis
  politicalRepresentationAxis
  apologyAxis
  materialReparationAxis
  institutionalRepairAxis
  socioeconomicOutcomeAxis
  : RepairAxis

data AxisClosure : Set where
  repairAxisOpen
  repairAxisPartiallyIdentified
  repairAxisSourceMapped
  repairAxisMateriallySatisfied
  : AxisClosure

record CriticalRepairState : Set where
  constructor criticalRepairState
  field
    nativeTitleRecognition : AxisClosure
    sovereigntyRecognition : AxisClosure
    landProtection : AxisClosure
    landReturn : AxisClosure
    treatyAgreement : AxisClosure
    politicalRepresentation : AxisClosure
    apology : AxisClosure
    materialReparation : AxisClosure
    institutionalRepair : AxisClosure
    socioeconomicOutcome : AxisClosure
    stateReference : String
open CriticalRepairState public

currentCriticalRepairState : CriticalRepairState
currentCriticalRepairState = criticalRepairState
  repairAxisSourceMapped
  repairAxisOpen
  repairAxisPartiallyIdentified
  repairAxisOpen
  repairAxisOpen
  repairAxisPartiallyIdentified
  repairAxisSourceMapped
  repairAxisOpen
  repairAxisOpen
  repairAxisPartiallyIdentified
  "Mabo/native-title and apology source maps exist; Barrambin and Closing the Gap expose material residuals; sovereignty, land return, treaty, reparation and institutional repair remain independently open"

------------------------------------------------------------------------
-- Decolonial hypothesis layer.
------------------------------------------------------------------------

data DecolonialHypothesisKind : Set where
  landBackWouldMateriallyReduceGap
  sovereigntyRecognitionWouldAlterInstitutionalRelation
  landReturnRequiredForAdequateRepair
  courtReformCannotByItselfDecoloniseLandRelation
  : DecolonialHypothesisKind

record DecolonialHypothesis : Set where
  constructor decolonialHypothesis
  field
    kind : DecolonialHypothesisKind
    authorityClass : ClaimAuthorityClass
    sourceReference : String
    treatedAsEmpiricallyProved : Bool
    treatedAsEmpiricallyProvedIsFalse : treatedAsEmpiricallyProved ≡ false
    eligibleForCriticalAnalysis : Bool
    eligibleForCriticalAnalysisIsTrue : eligibleForCriticalAnalysis ≡ true
open DecolonialHypothesis public

landBackGapHypothesis : DecolonialHypothesis
landBackGapHypothesis = decolonialHypothesis
  landBackWouldMateriallyReduceGap
  decolonialNormativeHypothesisClass
  "decolonial LAND BACK hypothesis; empirical causal closure requires additional evidence beyond Closing the Gap outcome statistics"
  false refl
  true refl

courtReformInsufficiencyHypothesis : DecolonialHypothesis
courtReformInsufficiencyHypothesis = decolonialHypothesis
  courtReformCannotByItselfDecoloniseLandRelation
  criticalTheoryLensClass
  "critical institutional hypothesis: intersectional/informed reform inside a colonial court may improve adjudication without itself returning land or resolving sovereignty"
  false refl
  true refl

------------------------------------------------------------------------
-- Intersectional axes remain explicit.
------------------------------------------------------------------------

landAxisRemainsNonEraseable :
  Situated.landAxisEraseable Situated.canonicalAxisAwareRepresentationBoundary ≡ false
landAxisRemainsNonEraseable = refl

affectedCommunityMayArticulateAxes :
  Situated.affectedConstituencyMayArticulateAxes Situated.canonicalAxisAwareRepresentationBoundary ≡ true
affectedCommunityMayArticulateAxes = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CourtInternalLegalityProvesColonialLegitimacy : Set where
data NativeTitleRecognitionProvesDecolonialRepair : Set where
data BarrambinSignificanceRecognitionGuaranteesLandProtection : Set where
data ApologyPaysLandReturn : Set where
data VoiceReferendumResultDeterminesSovereigntyTruth : Set where
data ClosingGapStatisticsProveSingleCause : Set where
data ClosingGapStatisticsProveLandBackCounterfactual : Set where
data IntersectionalCourtReformEliminatesColonialPowerRelation : Set where
data CriticalLensAutomaticallyBecomesWorldTruth : Set where

courtLegalityDoesNotProveColonialLegitimacy : CourtInternalLegalityProvesColonialLegitimacy → ⊥
courtLegalityDoesNotProveColonialLegitimacy ()

nativeTitleRecognitionDoesNotProveRepair : NativeTitleRecognitionProvesDecolonialRepair → ⊥
nativeTitleRecognitionDoesNotProveRepair ()

barrambinRecognitionDoesNotGuaranteeProtection : BarrambinSignificanceRecognitionGuaranteesLandProtection → ⊥
barrambinRecognitionDoesNotGuaranteeProtection ()

apologyDoesNotPayLandReturn : ApologyPaysLandReturn → ⊥
apologyDoesNotPayLandReturn ()

referendumDoesNotDetermineSovereigntyTruth : VoiceReferendumResultDeterminesSovereigntyTruth → ⊥
referendumDoesNotDetermineSovereigntyTruth ()

statisticsDoNotProveSingleCause : ClosingGapStatisticsProveSingleCause → ⊥
statisticsDoNotProveSingleCause ()

statisticsDoNotProveLandBackCounterfactual : ClosingGapStatisticsProveLandBackCounterfactual → ⊥
statisticsDoNotProveLandBackCounterfactual ()

intersectionalCourtReformDoesNotEraseColonialRelation : IntersectionalCourtReformEliminatesColonialPowerRelation → ⊥
intersectionalCourtReformDoesNotEraseColonialPowerRelation ()

criticalLensDoesNotAutoBecomeWorldTruth : CriticalLensAutomaticallyBecomesWorldTruth → ⊥
criticalLensDoesNotAutoBecomeWorldTruth ()

------------------------------------------------------------------------
-- Cross-checks against the existing doctrinal/critical owners.
------------------------------------------------------------------------

nativeTitleRecognitionStillNotSovereigntyRecognition :
  Critical.NativeTitleRecognitionProvesSovereigntyRecognition → ⊥
nativeTitleRecognitionStillNotSovereigntyRecognition =
  Critical.nativeTitleDoesNotProveSovereigntyRecognition

recognitionConditionStillDistinctFromContinuity :
  Minimal.axis Minimal.dawsonRecognitionConditionReceipt ≡ Minimal.recognitionConditionAxis
recognitionConditionStillDistinctFromContinuity = refl
