module DASHI.Economics.AISafetyRegulatoryMoatGameExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Agda.Builtin.String using (String)

import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Attribution

------------------------------------------------------------------------
-- SAFETY EVIDENCE / REGULATORY-MOAT / INCENTIVE-COMPATIBILITY BOUNDARY
--
-- This owner deliberately separates:
--   real hazard evidence,
--   the policy chosen in response,
--   distribution of compliance costs,
--   beneficiary structure,
--   and allegations of intent/collusion.
--
-- A regulatory moat can arise from asymmetric fixed compliance costs without
-- proving that hazard evidence was fabricated or that actors conspired.
------------------------------------------------------------------------

record HazardEvidenceProvenance : Set where
  constructor hazardEvidenceProvenance
  field
    evidenceProducer : String
    evidenceFunder : String
    proposedPolicyBeneficiary : String
    evidenceClaim : String
    independentReplicationAvailable : Bool
    sourceBound : Bool

open HazardEvidenceProvenance public

record ComplianceBurdenProfile : Set where
  constructor complianceBurdenProfile
  field
    incumbentRelativeBurden : Trit
    startupRelativeBurden : Trit
    academicRelativeBurden : Trit
    openWeightRelativeBurden : Trit
    individualRelativeBurden : Trit

open ComplianceBurdenProfile public

record RegulatoryMoatReceipt : Set where
  constructor regulatoryMoatReceipt
  field
    fixedComplianceCostMaterial : Bool
    incumbentCanAbsorbCost : Bool
    smallerActorsCannotComparablyAbsorbCost : Bool
    entryBarrierRises : Bool
    incumbentRelativePositionImproves : Bool
    intentToExcludeEstablished : Bool
    collusionEstablished : Bool

open RegulatoryMoatReceipt public

canonicalStructuralMoatWithoutIntent : RegulatoryMoatReceipt
canonicalStructuralMoatWithoutIntent =
  regulatoryMoatReceipt
    true true true true true false false

data TrueHazardImpliesOptimalRegulationPermission : Set where
data IncumbentBenefitsImpliesFabricationPermission : Set where
data RegulatoryMoatImpliesConspiracyPermission : Set where
data SafetyRegulationImpliesCompetitiveNeutralityPermission : Set where
data SafetyClaimImpliesPurePublicInterestPermission : Set where

trueHazardDoesNotAutoSelectOptimalRegulation :
  TrueHazardImpliesOptimalRegulationPermission → ⊥
trueHazardDoesNotAutoSelectOptimalRegulation ()

benefitDoesNotAutoProveFabrication :
  IncumbentBenefitsImpliesFabricationPermission → ⊥
benefitDoesNotAutoProveFabrication ()

moatDoesNotAutoProveConspiracy :
  RegulatoryMoatImpliesConspiracyPermission → ⊥
moatDoesNotAutoProveConspiracy ()

safetyRegulationDoesNotAutoProveNeutrality :
  SafetyRegulationImpliesCompetitiveNeutralityPermission → ⊥
safetyRegulationDoesNotAutoProveNeutrality ()

safetyClaimDoesNotAutoProvePurePublicInterest :
  SafetyClaimImpliesPurePublicInterestPermission → ⊥
safetyClaimDoesNotAutoProvePurePublicInterest ()

record IncidentRegulatoryFeedback : Set where
  constructor incidentRegulatoryFeedback
  field
    frontierCapabilityRace : Bool
    boundaryCircumventionIncident : Bool
    publicRiskSalienceRises : Bool
    regulatoryDemandRises : Bool
    fixedComplianceCostRises : Bool
    incumbentCanInternaliseCompliance : Bool
    deliberateManufactureEstablished : Bool

open IncidentRegulatoryFeedback public

canonicalAccidentCanStillCreateMoatFeedback : IncidentRegulatoryFeedback
canonicalAccidentCanStillCreateMoatFeedback =
  incidentRegulatoryFeedback
    true true true true true true false

record ConcentratedInterestGame : Set where
  constructor concentratedInterestGame
  field
    concentratedBenefit : Bool
    diffuseOpenEcosystemCost : Bool
    incumbentPolicyParticipationCapacity : Bool
    affectedOpenUsersCollectivelyLarge : Bool
    collectiveLossAutomaticallyPreventsCapture : Bool
    collectiveLossAutomaticallyPreventsCaptureIsFalse :
      collectiveLossAutomaticallyPreventsCapture ≡ false

canonicalConcentratedInterestGame : ConcentratedInterestGame
canonicalConcentratedInterestGame =
  concentratedInterestGame true true true true false refl

attributionBoundary : String
attributionBoundary =
  "Observed regulatory-moat formation, common funding/provenance, or incumbent benefit must not be promoted into fabrication, collusion or motive without a distinct source-to-systemic promotion producer."
