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
  "DOI 10.1017/S002237782510113X; MIT PSFC Library PSFC/JA-25-49; Journal of Plasma Physics 92 E20"
  true true false false false false

------------------------------------------------------------------------
-- Publication manifestation chronology.
------------------------------------------------------------------------

record LoureiroPublicationManifestationChronology : Set where
  constructor loureiro-publication-manifestation-chronology
  field
    doi : String
    receivedDate : String
    revisedDate : String
    acceptedDate : String
    loureiroDeathDate : String
    publicManifestation : String
    receivedBeforeDeath : Bool
    revisedBeforeDeath : Bool
    acceptedBeforeDeath : Bool
    manifestationAfterDeath : Bool
    manifestationProvesPostLossScientificWork : Bool
    manifestationProvesAdvisorReassignment : Bool
    manifestationProvesGrantTransfer : Bool
    manifestationProvesRepositoryTransfer : Bool

open LoureiroPublicationManifestationChronology public

loureiroLiLiuPublicationChronology : LoureiroPublicationManifestationChronology
loureiroLiLiuPublicationChronology = loureiro-publication-manifestation-chronology
  "10.1017/S002237782510113X"
  "2025-05-14"
  "2025-10-29"
  "2025-11-25"
  "2025-12-16"
  "Journal of Plasma Physics 2026 vol. 92 E20; MIT PSFC report PSFC/JA-25-49 publicly listed 2026-02-27"
  true true true true false false false false

------------------------------------------------------------------------
-- Data-access and repository-custody discriminator.
------------------------------------------------------------------------

record LoureiroDataAccessReceipt : Set where
  constructor loureiro-data-access-receipt
  field
    publicationDOI : String
    correspondingAuthor : String
    primaryDataAvailabilityStatement : String
    psfcRepositoryStatement : String
    dataAccessResponsibilityLocated : Bool
    exactDataverseObjectLocated : Bool
    repositoryDOILocated : Bool
    rawSimulationStateCustodyPaid : Bool
    advisorReassignmentPaid : Bool
    grantTransferPaid : Bool

open LoureiroDataAccessReceipt public

loureiroLiDataAccess : LoureiroDataAccessReceipt
loureiroLiDataAccess = loureiro-data-access-receipt
  "10.1017/S002237782510113X"
  "Dion Li"
  "Journal of Plasma Physics: data supporting the findings are available from the corresponding author upon reasonable request"
  "MIT PSFC Library PSFC/JA-25-49: associated dataset files are located in Dataverse, if applicable"
  true false false false false false

------------------------------------------------------------------------
-- Genuine post-loss independent student scientific work.
--
-- APS Open Science records Dion Li as sole author of a new paper received on
-- 2026-02-19, after Loureiro's 2025-12-16 death. This is stronger than a
-- post-loss manifestation of a pre-loss accepted Loureiro coauthored object:
-- it pays that a named Loureiro PhD student continued producing independent
-- plasma-science work after the loss. It does not identify a replacement
-- advisor, grant, repository, or same-simulation-state handover.
------------------------------------------------------------------------

record LoureiroStudentIndependentContinuation : Set where
  constructor loureiro-student-independent-continuation
  field
    student : String
    priorAdvisorRelation : String
    title : String
    doi : String
    preprintId : String
    receivedDate : String
    acceptedDate : String
    publishedDate : String
    sourceClass : String
    qid : String
    deweyTraversal : String
    receivedAfterLoureiroDeath : Bool
    soleAuthorScientificOutputPaid : Bool
    replacementAdvisorPaid : Bool
    grantTransferPaid : Bool
    repositoryTransferPaid : Bool
    sameSimulationStateTransferPaid : Bool

open LoureiroStudentIndependentContinuation public

loureiroDionLiIndependentContinuation : LoureiroStudentIndependentContinuation
loureiroDionLiIndependentContinuation = loureiro-student-independent-continuation
  "Dion Li"
  "MIT News identifies Dion Li as one of Nuno F. G. Loureiro's PhD students"
  "Kinetic route to helicity-constrained decay"
  "10.1103/j5p4-jj3d"
  "arXiv:2602.17514"
  "2026-02-19"
  "2026-06-15"
  "2026-07-06"
  "primary peer-reviewed APS publication + primary arXiv preprint"
  "unresolvedQid"
  "530 Physics"
  true true false false false false

record LoureiroSuccessionBoundary : Set where
  constructor loureiro-succession-boundary
  field centerDirectorSuccessionImpliesLoureiroGroupPISuccession : Bool; centerDirectorSuccessionImpliesStudentReassignment : Bool; centerDirectorSuccessionImpliesGrantReassignment : Bool; pedagogicalContinuationImpliesRepositoryTransfer : Bool; postLossStudentPublicationImpliesAdvisorReassignment : Bool; postLossStudentPublicationImpliesGrantOrRepositoryTransfer : Bool; postLossPublicationManifestationImpliesPostLossScientificWork : Bool; dataAccessContactImpliesRepositoryCustodyTransfer : Bool; conditionalDataverseLanguageImpliesDatasetExists : Bool; independentStudentOutputImpliesAdvisorSuccession : Bool; independentStudentOutputImpliesSameCarrierHandover : Bool; centerLeadershipAndPedagogyMayGuideSameCarrierSearch : Bool
open LoureiroSuccessionBoundary public
canonicalLoureiroSuccessionBoundary = loureiro-succession-boundary false false false false false false false false false false false true

record SuccessionSearchStatus : Set where
  constructor succession-search-status
  field chavezNamedSameCarrierSuccessorLocated : Bool; chavezNamedSameCarrierSuccessorLocatedIsFalse : chavezNamedSameCarrierSuccessorLocated ≡ false; leblancNamedSameCarrierSuccessorLocated : Bool; leblancNamedSameCarrierSuccessorLocatedIsFalse : leblancNamedSameCarrierSuccessorLocated ≡ false; rezaNamedSameCarrierSuccessorLocated : Bool; rezaNamedSameCarrierSuccessorLocatedIsFalse : rezaNamedSameCarrierSuccessorLocated ≡ false; loureiroPedagogicalContinuationLocated : Bool; loureiroPedagogicalContinuationLocatedIsTrue : loureiroPedagogicalContinuationLocated ≡ true; loureiroCenterLeadershipSuccessorLocated : Bool; loureiroCenterLeadershipSuccessorLocatedIsTrue : loureiroCenterLeadershipSuccessorLocated ≡ true; loureiroStudentPublicationContinuationLocated : Bool; loureiroStudentPublicationContinuationLocatedIsTrue : loureiroStudentPublicationContinuationLocated ≡ true; loureiroIndependentStudentContinuationLocated : Bool; loureiroIndependentStudentContinuationLocatedIsTrue : loureiroIndependentStudentContinuationLocated ≡ true; loureiroSameCarrierSuccessorLocated : Bool; loureiroSameCarrierSuccessorLocatedIsFalse : loureiroSameCarrierSuccessorLocated ≡ false; absencePromotedToNoSuccessor : Bool; absencePromotedToNoSuccessorIsFalse : absencePromotedToNoSuccessor ≡ false

canonicalSuccessionSearchStatus : SuccessionSearchStatus
canonicalSuccessionSearchStatus = succession-search-status false refl false refl false refl true refl true refl true refl true refl false refl false refl

data SuccessionReverseTarget : Set where
  chavezSameCarrierTaskAllocation chavezNamedSuccessorOrHandover chavezPostDepartureRework leblancTechMatTaskAllocation leblancNamedSuccessorOrHandover leblancQualificationContinuity rezaProcessWindowTaskAllocation rezaNamedSuccessorOrHandover rezaManufacturingRequalification loureiroFormalAdvisorReassignment loureiroGrantReassignment loureiroRepositoryAndNotebookCustody loureiroTargetSpecificSimulationContinuation loureiroNamedSameCarrierSuccessorOrHandover loureiroExactDataverseDatasetIdentity : SuccessionReverseTarget

firstLoureiroSameCarrierTarget : SuccessionReverseTarget
firstLoureiroSameCarrierTarget = loureiroFormalAdvisorReassignment
