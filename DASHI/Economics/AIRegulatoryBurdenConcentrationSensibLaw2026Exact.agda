module DASHI.Economics.AIRegulatoryBurdenConcentrationSensibLaw2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as SensibLaw
import DASHI.Economics.AISafetyRegulatoryMoatGameExact as Regulatory
import DASHI.Economics.AIPolicyBackstopCommercialMoat2026Exact as Policy
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital

------------------------------------------------------------------------
-- INCIDENT -> POLICY -> BURDEN -> MARKET-STRUCTURE WELD
--
-- SensibLaw supplies source, event and evidence identity.  The existing AI
-- safety owner supplies the structural moat logic.  This bridge adds a typed
-- compliance-cost observation surface while keeping three claims distinct:
--   (1) a safety justification may be supported;
--   (2) a structural incumbent advantage may be supported;
--   (3) intentional capture requires its own evidence producer.
------------------------------------------------------------------------

record PolicyEvidenceCarrier : Set where
  constructor policyEvidenceCarrier
  field
    policyEvent : SensibLaw.Event
    legalSystem : SensibLaw.LegalSystem
    policySource : SensibLaw.LegalSource
    evidence : SensibLaw.EvidenceItem
    eventEvidence : SensibLaw.EventEvidenceLink
    eventEvidenceEventIdentityPreserved :
      SensibLaw.EventEvidenceLink.linkedEvent eventEvidence
      ≡ SensibLaw.Event.eventId policyEvent
    eventEvidenceItemIdentityPreserved :
      SensibLaw.EventEvidenceLink.linkedEvidence eventEvidence
      ≡ SensibLaw.EvidenceItem.evidenceId evidence
    sourceSystemIdentityPreserved :
      SensibLaw.LegalSource.sourceSystem policySource
      ≡ SensibLaw.LegalSystem.systemId legalSystem

open PolicyEvidenceCarrier public

record ComplianceCostVector : Set where
  constructor complianceCostVector
  field
    incumbentCost : Nat
    startupCost : Nat
    academicCost : Nat
    openWeightCost : Nat
    individualCost : Nat
    commonAccountingBasis : Bool
    commonTimeHorizon : Bool
    sourceBound : Bool

open ComplianceCostVector public

record RelativeBurdenObservation : Set where
  constructor relativeBurdenObservation
  field
    costs : ComplianceCostVector
    fixedCostMaterial : Bool
    incumbentCanSpreadFixedCost : Bool
    entrantBurdenDisproportionate : Bool
    openWeightBurdenDisproportionate : Bool
    entryBarrierRises : Bool
    measurementPromotable : Bool

open RelativeBurdenObservation public

-- Numeric fields are evidence carriers only.  No arithmetic comparison is
-- invented here without a declared accounting basis, denominator and horizon.
candidateBurdenMeasurementBoundary : RelativeBurdenObservation
candidateBurdenMeasurementBoundary =
  relativeBurdenObservation
    (complianceCostVector 0 0 0 0 0 false false false)
    false false false false false false

record SafetyMoatCaptureSeparation : Set where
  constructor safetyMoatCaptureSeparation
  field
    safetyJustificationSupported : Bool
    structuralIncumbentAdvantageSupported : Bool
    intentionalCaptureEstablished : Bool
    fabricationEstablished : Bool
    collusionEstablished : Bool

open SafetyMoatCaptureSeparation public

canonicalSafetyAndStructuralMoat : SafetyMoatCaptureSeparation
canonicalSafetyAndStructuralMoat =
  safetyMoatCaptureSeparation true true false false false

data StructuralAdvantageImpliesIntentionalCapturePermission : Set where
data SafetyJustificationImpliesCompetitiveNeutralityPermission : Set where
data IncidentImpliesOptimalPolicyPermission : Set where
data CommonFunderImpliesFabricationPermission : Set where

structuralAdvantageDoesNotAutoProveIntentionalCapture :
  StructuralAdvantageImpliesIntentionalCapturePermission → ⊥
structuralAdvantageDoesNotAutoProveIntentionalCapture ()

safetyJustificationDoesNotAutoProveCompetitiveNeutrality :
  SafetyJustificationImpliesCompetitiveNeutralityPermission → ⊥
safetyJustificationDoesNotAutoProveCompetitiveNeutrality ()

incidentDoesNotAutoSelectOptimalPolicy :
  IncidentImpliesOptimalPolicyPermission → ⊥
incidentDoesNotAutoSelectOptimalPolicy ()

commonFunderDoesNotAutoProveFabrication :
  CommonFunderImpliesFabricationPermission → ⊥
commonFunderDoesNotAutoProveFabrication ()

------------------------------------------------------------------------
-- Existing proof surfaces are retained as authorities rather than duplicated.
------------------------------------------------------------------------

existingStructuralMoat : Regulatory.RegulatoryMoatReceipt
existingStructuralMoat = Regulatory.canonicalStructuralMoatWithoutIntent

existingAccidentFeedback : Regulatory.IncidentRegulatoryFeedback
existingAccidentFeedback = Regulatory.canonicalAccidentCanStillCreateMoatFeedback

existingConcentratedInterestGame : Regulatory.ConcentratedInterestGame
existingConcentratedInterestGame = Regulatory.canonicalConcentratedInterestGame

existingCommercialStrategicBoundary : Policy.CommercialStrategicSeparation
existingCommercialStrategicBoundary = Policy.candidateOctober2026CommercialStrategicState

existingCapitalBackstopHypothesis : Capital.StrategicBackstopTransitionHypothesis
existingCapitalBackstopHypothesis = Capital.candidateCommercialToStrategicMoatHypothesis

------------------------------------------------------------------------
-- MEASUREMENT / PROMOTION BOUNDARY
------------------------------------------------------------------------

record RegulatoryBurdenProducerResidual : Set where
  constructor regulatoryBurdenProducerResidual
  field
    policyTextAcquired : Bool
    affectedActorClassesDeclared : Bool
    sameBasisComplianceCostsAcquired : Bool
    implementationHorizonAligned : Bool
    marketEntryResponseObserved : Bool
    openWeightEffectObserved : Bool
    concentrationEffectObserved : Bool
    motiveEvidenceAcquired : Bool

open RegulatoryBurdenProducerResidual public

currentRegulatoryBurdenResidual : RegulatoryBurdenProducerResidual
currentRegulatoryBurdenResidual =
  regulatoryBurdenProducerResidual
    false true false false false false false false

data StructuralMoatImpliesMeasuredCostRatioPermission : Set where

structuralMoatDoesNotManufactureMeasuredCostRatio :
  StructuralMoatImpliesMeasuredCostRatioPermission → ⊥
structuralMoatDoesNotManufactureMeasuredCostRatio ()

promotionBoundary : String
promotionBoundary =
  "Safety evidence, policy adoption, asymmetric compliance burden, structural incumbent advantage and intentional regulatory capture are separate evidence claims. SensibLaw source/event/evidence identity is preserved; none of the earlier claims manufactures the later one."
