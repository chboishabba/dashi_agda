module DASHI.Law.SensibLawWoogarooDevelopmentPressureVisibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- DEVELOPMENT PRESSURE != PUBLIC VISIBILITY
--
-- Fresh Ipswich witness: 12285/2026/MCU is recorded by Council as code
-- assessment, public notification not required, while the same historic
-- property record also contains earthworks/vegetation-clearing and BESS
-- approvals. This is a bounded same-LGA procedural witness, not a Woogaroo
-- project fact and not a numeric offset risk-of-loss estimate.
------------------------------------------------------------------------

record VisibilityPressureWitness : Set where
  constructor visibility-pressure-witness
  field
    sourceOwner : String
    application : String
    locality : String
    assessmentLevel : String
    publicNotificationRequired : Bool
    vegetationClearingApprovalOnPropertyRecord : Bool
    otherMajorDevelopmentApprovalOnPropertyRecord : Bool
    provenanceStage : Provenance.LegalClaimProvenanceStage
    sameParcelAsWoogaroo : Bool
    provesOffsetParcelRiskOfLoss : Bool

open VisibilityPressureWitness public

swanbankVisibilityPressureWitness : VisibilityPressureWitness
swanbankVisibilityPressureWitness = visibility-pressure-witness
  "Ipswich City Council Development.i"
  "12285/2026/MCU — Material Change of Use — Warehouse (Data Centre)"
  "Swanbank"
  "Code"
  false
  true
  true
  Provenance.externalSourceClaim
  false
  false

record VisibilityBoundary : Set where
  constructor visibility-boundary
  field
    noNotificationDoesNotImplyNoDevelopmentPressure : Bool
    noRecentNotifiedApplicationDoesNotProveLowRiskOfLoss : Bool
    codeAssessmentDoesNotProveImpropriety : Bool
    sameLGAPlanningWitnessDoesNotSetAnotherParcelsRisk : Bool
    applicationHistoryDoesNotProveFutureApproval : Bool

visibilityBoundary : VisibilityBoundary
visibilityBoundary = visibility-boundary true true true true true

record CounterfactualInference : Set where
  constructor counterfactual-inference
  field
    proposition : String
    stage : Provenance.LegalClaimProvenanceStage
    legalConsumer : String
    conclusionPaid : Bool

visibilityCorrectedRiskInference : CounterfactualInference
visibilityCorrectedRiskInference = counterfactual-inference
  "When auditing EPBC offset risk of loss, absence of public notification or obvious public controversy is not sufficient evidence of low development pressure; lawful code-assessable and pre-existing approval pathways must also be checked."
  Provenance.crossSourceInference
  "EPBC offset risk-of-loss / additionality counterfactual"
  false

record AcquisitionDemand : Set where
  constructor acquisition-demand
  field
    target : String
    requiredEvidence : String
    why : String

candidateOffsetPressureDemand : AcquisitionDemand
candidateOffsetPressureDemand = acquisition-demand
  "Each exact 2019/8575 proposed offset parcel"
  "lot/plan + zoning + current and superseded planning schemes + existing approvals + clearing permissions + infrastructure constraints + conservation instruments + notified and non-notified development pathways"
  "To estimate the without-offset risk of loss from actual lawful development/clearing exposure rather than from public visibility alone."
