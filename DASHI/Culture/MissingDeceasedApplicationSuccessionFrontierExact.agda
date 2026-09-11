module DASHI.Culture.MissingDeceasedApplicationSuccessionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.DistributedApplicationSurfaceBidiExact as D

scorpiusDistributionSurface : D.CarrierDistributionReceipt
scorpiusDistributionSurface = D.carrier-distribution-receipt
  "DARHT / Scorpius application engineering"
  "diagnostics, cell/module assembly, accelerator configuration and radiography application stack"
  (D.multiLabProgramme ∷ D.multiAuthorPublication ∷ D.documentedProcedure ∷ D.configurationManagement ∷ [])
  D.distributedSourceBacked
  "LANL Summer 2024 Scorpius Takes Shape; LANL Anthony Chavez Summer 2025 profile; LA-UR-24-27763; DOI 10.1063/1.5029837"
  "Public evidence establishes a distributed programme and substantial proceduralisation. It does not establish that every calibration/configuration/inverse-model carrier was distributed or that Anthony Chavez had no tacit residual."

ficsDistributionSurface : D.CarrierDistributionReceipt
ficsDistributionSurface = D.carrier-distribution-receipt
  "NASA FSP/SNP fission instrumentation and controls"
  "technology maturation, qualification and system integration"
  (D.multiAuthorPublication ∷ D.multiLeadOrganisation ∷ D.sharedDatabase ∷ [])
  D.distributedSourceBacked
  "NASA NTRS 20250008475"
  "The FICS Executive Committee names distinct project-integration, I&C, TechMat, electronics, materials/processes, nuclear and payload leads, and describes a shared live database. This does not prove that component-specific failure envelopes or qualification histories were fully distributed."

rezaDistributionSurface : D.CarrierDistributionReceipt
rezaDistributionSurface = D.carrier-distribution-receipt
  "Jacinto-Hardwick burn-resistant alloy family"
  "alloy composition, processing description and later manufacturing/qualification knowledge"
  (D.multiAuthorPublication ∷ D.configurationManagement ∷ [])
  D.mixedOrPartial
  "US20030053926A1; US20040208777A1 and USPTO assignment lineage"
  "The public record establishes co-invention and institutional IP transfer, but does not close distribution of exact heat-treatment, microstructure, manufacturing tolerances, qualification evidence or tacit process knowledge."

------------------------------------------------------------------------
-- Loureiro continuation surfaces.
------------------------------------------------------------------------

loureiroPedagogicalContinuationSurface : D.CarrierDistributionReceipt
loureiroPedagogicalContinuationSurface = D.carrier-distribution-receipt
  "Nuno F. G. Loureiro magnetic-reconnection teaching lineage"
  "public lecture/pedagogical continuation after loss"
  (D.documentedProcedure ∷ D.multiAuthorPublication ∷ [])
  D.distributedSourceBacked
  "Princeton Plasma Physics Laboratory 2026 Intro Course; Loureiro 2018 Reconnection lecture replay with Q&A led by Prof. Muni Zhou and Dr. Suying Jin"
  "This closes public pedagogical/intellectual continuation. It does not close Loureiro Group PI succession, student/grant reassignment, Viriato/KREHM repository custody, target-specific simulation state, notebooks, or same-carrier application handover."

record LoureiroCenterLeadershipSuccessionReceipt : Set where
  constructor loureiro-center-leadership-succession-receipt
  field predecessor : String; predecessorRole : String; successor : String; successorRole : String; firstLocatedPostLossCarrier : String; primaryInstitutionalSource : String; centerLeadershipSuccessionPaid : Bool; loureiroGroupScientificSuccessionPaid : Bool; studentReassignmentPaid : Bool; grantReassignmentPaid : Bool; repositoryCustodyPaid : Bool
open LoureiroCenterLeadershipSuccessionReceipt public

loureiroCenterLeadershipSuccession : LoureiroCenterLeadershipSuccessionReceipt
loureiroCenterLeadershipSuccession = loureiro-center-leadership-succession-receipt
  "Nuno F. G. Loureiro" "Director, MIT Plasma Science and Fusion Center"
  "Steve Wukitch" "Interim Director, MIT Plasma Science and Fusion Center"
  "MIT/MITEI March-April 2026 public reporting naming Steve Wukitch as PSFC Interim Director"
  "MIT News 2026-04-21; MIT Energy Initiative 2026-03-20; PSFC mirror"
  true false false false false

------------------------------------------------------------------------
-- Named student/coauthored-output continuation.
--
-- MIT's memorial identifies Dion Li as one of Loureiro's PhD students. The PSFC
-- library subsequently lists a 2026 publication entry for "Role of ion acoustic
-- instability in magnetic reconnection" by Dion Li, Zhuo Liu and Nuno Loureiro.
-- This pays a concrete post-loss continuation of a student/coauthored scientific
-- output. It does NOT identify Li's replacement advisor, grant transfer,
-- repository custody, or who owns the underlying simulation/configuration state.
------------------------------------------------------------------------

record LoureiroStudentPublicationContinuation : Set where
  constructor loureiro-student-publication-continuation
  field student : String; advisorRelationSource : String; postLossOutput : String; postLossOutputSource : String; studentAdvisorRelationPaid : Bool; postLossCoauthoredOutputLocated : Bool; replacementAdvisorPaid : Bool; grantTransferPaid : Bool; repositoryTransferPaid : Bool; sameSimulationStateTransferPaid : Bool
open LoureiroStudentPublicationContinuation public

loureiroDionLiContinuation : LoureiroStudentPublicationContinuation
loureiroDionLiContinuation = loureiro-student-publication-continuation
  "Dion Li"
  "MIT News memorial quotes Dion Li as one of Nuno Loureiro's PhD students"
  "Role of ion acoustic instability in magnetic reconnection — Dion Li; Zhuo Liu; Nuno F. Loureiro"
  "MIT PSFC Library PSFC/JA-25-49, public 2026 listing"
  true true false false false false

record LoureiroSuccessionBoundary : Set where
  constructor loureiro-succession-boundary
  field centerDirectorSuccessionImpliesLoureiroGroupPISuccession : Bool; centerDirectorSuccessionImpliesStudentReassignment : Bool; centerDirectorSuccessionImpliesGrantReassignment : Bool; pedagogicalContinuationImpliesRepositoryTransfer : Bool; postLossStudentPublicationImpliesAdvisorReassignment : Bool; postLossStudentPublicationImpliesGrantOrRepositoryTransfer : Bool; centerLeadershipAndPedagogyMayGuideSameCarrierSearch : Bool
open LoureiroSuccessionBoundary public
canonicalLoureiroSuccessionBoundary = loureiro-succession-boundary false false false false false false true

record SuccessionSearchStatus : Set where
  constructor succession-search-status
  field chavezNamedSameCarrierSuccessorLocated : Bool; chavezNamedSameCarrierSuccessorLocatedIsFalse : chavezNamedSameCarrierSuccessorLocated ≡ false; leblancNamedSameCarrierSuccessorLocated : Bool; leblancNamedSameCarrierSuccessorLocatedIsFalse : leblancNamedSameCarrierSuccessorLocated ≡ false; rezaNamedSameCarrierSuccessorLocated : Bool; rezaNamedSameCarrierSuccessorLocatedIsFalse : rezaNamedSameCarrierSuccessorLocated ≡ false; loureiroPedagogicalContinuationLocated : Bool; loureiroPedagogicalContinuationLocatedIsTrue : loureiroPedagogicalContinuationLocated ≡ true; loureiroCenterLeadershipSuccessorLocated : Bool; loureiroCenterLeadershipSuccessorLocatedIsTrue : loureiroCenterLeadershipSuccessorLocated ≡ true; loureiroStudentPublicationContinuationLocated : Bool; loureiroStudentPublicationContinuationLocatedIsTrue : loureiroStudentPublicationContinuationLocated ≡ true; loureiroSameCarrierSuccessorLocated : Bool; loureiroSameCarrierSuccessorLocatedIsFalse : loureiroSameCarrierSuccessorLocated ≡ false; absencePromotedToNoSuccessor : Bool; absencePromotedToNoSuccessorIsFalse : absencePromotedToNoSuccessor ≡ false

canonicalSuccessionSearchStatus : SuccessionSearchStatus
canonicalSuccessionSearchStatus = succession-search-status false refl false refl false refl true refl true refl true refl false refl false refl

data SuccessionReverseTarget : Set where
  chavezSameCarrierTaskAllocation chavezNamedSuccessorOrHandover chavezPostDepartureRework leblancTechMatTaskAllocation leblancNamedSuccessorOrHandover leblancQualificationContinuity rezaProcessWindowTaskAllocation rezaNamedSuccessorOrHandover rezaManufacturingRequalification loureiroFormalAdvisorReassignment loureiroGrantReassignment loureiroRepositoryAndNotebookCustody loureiroTargetSpecificSimulationContinuation loureiroNamedSameCarrierSuccessorOrHandover : SuccessionReverseTarget

firstLoureiroSameCarrierTarget : SuccessionReverseTarget
firstLoureiroSameCarrierTarget = loureiroFormalAdvisorReassignment
