module DASHI.Governance.HistoricalDrugClassifierCounterfactualDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Governance.HistoricalDrugGovernanceClassifierExact as Historical
import DASHI.Governance.DrugClassificationAsymmetryDiscriminatorExact as Classify

------------------------------------------------------------------------
-- HISTORICAL CLASSIFIER COUNTERFACTUAL DISCRIMINATOR
--
-- Hold a carrier profile fixed and vary classifier-rule coordinates.  The aim
-- is to identify which rule difference would separate care/punishment outcomes,
-- not to infer a real historical causal effect from a synthetic comparison.
------------------------------------------------------------------------

data RuleCoordinate : Set where
  punitiveWeightCoordinate
  treatmentAuthorityCoordinate
  veteranExceptionCoordinate
  medicalDiagnosisGateCoordinate
  sponsorshipContainmentCoordinate
  sovereigntyRecognitionCoordinate
  : RuleCoordinate

data RuleState : Set where
  ruleInstalled
  ruleAbsent
  rulePartial
  ruleUnknown
  : RuleState

record HistoricalRuleWorld : Set where
  constructor historicalRuleWorld
  field
    epoch : Historical.DrugPolicyEpoch
    profile : Historical.HistoricalCarrierProfile
    punitiveWeight : RuleState
    treatmentAuthority : RuleState
    veteranException : RuleState
    medicalDiagnosisGate : RuleState
    sponsorshipContainment : RuleState
    sovereigntyRecognition : RuleState
    resultingCone : Classify.GovernanceCone

open HistoricalRuleWorld public

nixonVeteranProfileWorld : HistoricalRuleWorld
nixonVeteranProfileWorld = historicalRuleWorld
  Historical.nixonBifurcatedWarOnDrugsEpoch
  Historical.veteranDiagnosedPsilocybinProfile
  ruleInstalled
  rulePartial
  ruleAbsent
  ruleAbsent
  ruleAbsent
  ruleAbsent
  Classify.punitiveSecurityCone

trumpVeteranProfileWorld : HistoricalRuleWorld
trumpVeteranProfileWorld = historicalRuleWorld
  Historical.trumpPsychedelicSplitEpoch
  Historical.veteranDiagnosedPsilocybinProfile
  ruleInstalled
  ruleInstalled
  ruleInstalled
  ruleInstalled
  ruleInstalled
  ruleUnknown
  Classify.careResearchCone

------------------------------------------------------------------------
-- Current coarse observer sees only the fixed carrier profile.
------------------------------------------------------------------------

coarseProfileObserver : HistoricalRuleWorld → Historical.HistoricalCarrierProfile
coarseProfileObserver = profile

historicalWorldsCollapseOnProfile :
  coarseProfileObserver nixonVeteranProfileWorld
  ≡ coarseProfileObserver trumpVeteranProfileWorld
historicalWorldsCollapseOnProfile = refl

routeDiffersAcrossClassifierWorlds :
  resultingCone nixonVeteranProfileWorld
  ≡ resultingCone trumpVeteranProfileWorld → ⊥
routeDiffersAcrossClassifierWorlds ()

readRule : RuleCoordinate → HistoricalRuleWorld → RuleState
readRule punitiveWeightCoordinate = punitiveWeight
readRule treatmentAuthorityCoordinate = treatmentAuthority
readRule veteranExceptionCoordinate = veteranException
readRule medicalDiagnosisGateCoordinate = medicalDiagnosisGate
readRule sponsorshipContainmentCoordinate = sponsorshipContainment
readRule sovereigntyRecognitionCoordinate = sovereigntyRecognition

ruleBundle : RuleCoordinate → Discriminator.ExperimentBundle HistoricalRuleWorld
ruleBundle coordinate = Discriminator.experimentBundle
  RuleState
  (readRule coordinate)
  (suc zero)
  "historical classifier-rule coordinate"
  "synthetic counterfactual discriminator; real historical mediation requires external evidence"

veteranExceptionSeparatesHistoricalClassifierWorlds :
  Discriminator.BundleSeparates
    (ruleBundle veteranExceptionCoordinate)
    nixonVeteranProfileWorld
    trumpVeteranProfileWorld
veteranExceptionSeparatesHistoricalClassifierWorlds = record
  { separates = λ () }

treatmentAuthoritySeparatesHistoricalClassifierWorlds :
  Discriminator.BundleSeparates
    (ruleBundle treatmentAuthorityCoordinate)
    nixonVeteranProfileWorld
    trumpVeteranProfileWorld
treatmentAuthoritySeparatesHistoricalClassifierWorlds = record
  { separates = λ () }

medicalDiagnosisGateSeparatesHistoricalClassifierWorlds :
  Discriminator.BundleSeparates
    (ruleBundle medicalDiagnosisGateCoordinate)
    nixonVeteranProfileWorld
    trumpVeteranProfileWorld
medicalDiagnosisGateSeparatesHistoricalClassifierWorlds = record
  { separates = λ () }

------------------------------------------------------------------------
-- BIDI interpretation: desired route change -> rule coordinates to investigate.
------------------------------------------------------------------------

data RouteFlipQuestion : Set where
  punishmentToCareFlip
  punishmentToCeremonialAuthorityFlip
  punishmentToRegulatedMedicalFlip
  : RouteFlipQuestion

data CandidateRuleDemand : RouteFlipQuestion → RuleCoordinate → Set where
  careNeedsTreatmentAuthority :
    CandidateRuleDemand punishmentToCareFlip treatmentAuthorityCoordinate
  careNeedsVeteranException :
    CandidateRuleDemand punishmentToCareFlip veteranExceptionCoordinate
  careNeedsDiagnosisGate :
    CandidateRuleDemand punishmentToCareFlip medicalDiagnosisGateCoordinate
  careMayNeedInstitutionalSponsorship :
    CandidateRuleDemand punishmentToCareFlip sponsorshipContainmentCoordinate
  ceremonialNeedsSovereigntyRecognition :
    CandidateRuleDemand punishmentToCeremonialAuthorityFlip sovereigntyRecognitionCoordinate
  regulatedMedicalNeedsTreatmentAuthority :
    CandidateRuleDemand punishmentToRegulatedMedicalFlip treatmentAuthorityCoordinate
  regulatedMedicalNeedsDiagnosisGate :
    CandidateRuleDemand punishmentToRegulatedMedicalFlip medicalDiagnosisGateCoordinate

------------------------------------------------------------------------
-- Separation is not historical mediation or normatively justified classification.
------------------------------------------------------------------------

data RuleSeparationPromotesHistoricalCause : Set where

data RuleSeparationPromotesJustClassification : Set where

data CareFlipPromotesUniversalEligibility : Set where

ruleSeparationDoesNotPromoteHistoricalCause :
  RuleSeparationPromotesHistoricalCause → ⊥
ruleSeparationDoesNotPromoteHistoricalCause ()

ruleSeparationDoesNotPromoteJustice :
  RuleSeparationPromotesJustClassification → ⊥
ruleSeparationDoesNotPromoteJustice ()

careFlipDoesNotPromoteUniversalEligibility :
  CareFlipPromotesUniversalEligibility → ⊥
careFlipDoesNotPromoteUniversalEligibility ()

record HistoricalDrugClassifierCounterfactualBoundary : Set where
  constructor historicalDrugClassifierCounterfactualBoundary
  field
    fixedCarrierCanReceiveDifferentRouteUnderDifferentClassifier : Bool
    fixedCarrierCanReceiveDifferentRouteUnderDifferentClassifierIsTrue :
      fixedCarrierCanReceiveDifferentRouteUnderDifferentClassifier ≡ true
    ruleCoordinateCanSeparateClassifierWorlds : Bool
    ruleCoordinateCanSeparateClassifierWorldsIsTrue :
      ruleCoordinateCanSeparateClassifierWorlds ≡ true
    desiredRouteFlipCanBackpropToRuleDemand : Bool
    desiredRouteFlipCanBackpropToRuleDemandIsTrue :
      desiredRouteFlipCanBackpropToRuleDemand ≡ true
    separatingRuleProvesHistoricalCausalMechanism : Bool
    separatingRuleProvesHistoricalCausalMechanismIsFalse :
      separatingRuleProvesHistoricalCausalMechanism ≡ false
    careRouteProvesNormativelyJustClassifier : Bool
    careRouteProvesNormativelyJustClassifierIsFalse :
      careRouteProvesNormativelyJustClassifier ≡ false

canonicalHistoricalDrugClassifierCounterfactualBoundary :
  HistoricalDrugClassifierCounterfactualBoundary
canonicalHistoricalDrugClassifierCounterfactualBoundary =
  historicalDrugClassifierCounterfactualBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
