module DASHI.Law.SensibLawWoogarooSwanbankDataCentreDevelopmentPressureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Provenance

------------------------------------------------------------------------
-- SWANBANK DATA-CENTRE DEVELOPMENT-PRESSURE WITNESS
--
-- This is a bounded same-LGA / same-landscape development-pressure witness.
-- It does NOT assert that the Swanbank data-centre parcel is the Woogaroo
-- action parcel, nor that its planning pathway governs EPBC 2019/8575.
------------------------------------------------------------------------

record DevelopmentPressureWitness : Set where
  constructor development-pressure-witness
  field
    project : String
    application : String
    locality : String
    proposalScale : String
    assessmentLevel : String
    publicNotificationRequired : Bool
    mappedKoalaHabitatIssueReported : Bool
    stateReferralReported : Bool
    supersededSchemeRequestExists : Bool
    sameParcelAsWoogaroo : Bool
    provesWoogarooPlanningOutcome : Bool
    provesOffsetRiskOfLoss : Bool

open DevelopmentPressureWitness public

swanbankDataCentre : DevelopmentPressureWitness
swanbankDataCentre = development-pressure-witness
  "Northern Concept Swanb data-centre proposal"
  "Ipswich City Council 12285/2026/MCU; antecedent 9000/2026/SPSR"
  "Lot 5 Six Leaf Street, Swanbank"
  "10-storey / approximately 72 m / approximately 82,576 m2"
  "Code assessment"
  false
  true
  true
  true
  false
  false
  false

------------------------------------------------------------------------
-- Attribution and WrongType boundaries.
------------------------------------------------------------------------

record SwanbankBoundary : Set where
  constructor swanbank-boundary
  field
    sameLGAEvidenceDoesNotCreateSameParcelFact : Bool
    codeAssessmentDoesNotProveImpropriety : Bool
    noPublicNotificationDoesNotMeanNoAssessment : Bool
    mappedKoalaHabitatDoesNotDetermineRefusal : Bool
    supersededSchemeUseDoesNotDetermineWoogarooExemption : Bool
    developmentPressureWitnessDoesNotSetNumericRiskOfLoss : Bool
    newsReportDoesNotBecomeAgencyFinding : Bool

swanbankBoundary : SwanbankBoundary
swanbankBoundary = swanbank-boundary true true true true true true true

------------------------------------------------------------------------
-- Cross-source inference allowed at repository stage only.
------------------------------------------------------------------------

record BoundedInference : Set where
  constructor bounded-inference
  field
    proposition : String
    provenanceStage : Provenance.LegalClaimProvenanceStage
    consumer : String
    conclusionPaid : Bool

sameLGAUrbanPressureInference : BoundedInference
sameLGAUrbanPressureInference = bounded-inference
  "A fresh large development application on mapped koala habitat in Swanbank is evidence that parts of the broader Ipswich growth landscape face active development pressure and that habitat can remain exposed despite regulatory koala mapping."
  Provenance.crossSourceInference
  "EPBC offset risk-of-loss / additionality comparison; planning-exemption audit"
  false

publicParticipationInference : BoundedInference
publicParticipationInference = bounded-inference
  "The Swanbank code-assessment pathway is a fresh example in Ipswich where a substantial proposal can proceed without statutory public notification; this is relevant to counsel's audit of participation rights and superseded/planning instruments, but not proof that the Woogaroo pathway is identical."
  Provenance.crossSourceInference
  "planning procedure / public-participation comparison"
  false

------------------------------------------------------------------------
-- Useful residuals.
------------------------------------------------------------------------

record Residual : Set where
  constructor residual
  field
    question : String
    status : String

whiteRockRelationship : Residual
whiteRockRelationship = residual
  "Quantify the actual spatial/ecological relationship between the Swanbank data-centre parcel, White Rock-Spring Mountain Conservation Estate, the Flinders-Karawatha corridor and the Woogaroo/Springfield project chain before using proximity rhetorically or legally."
  "OPEN — same broader south-Ipswich landscape is supported; exact distance/intersection/function remains to be measured."

offsetPressureResidual : Residual
offsetPressureResidual = residual
  "Use planning history, zoning, lawful clearing pathways and current development applications to compare defensible without-offset risk of loss at Woogaroo against each proposed offset parcel."
  "OPEN — Swanbank is contextual pressure evidence only, not an offset-parcel risk value."
