module DASHI.Culture.MissingDeceasedApplicationSuccessionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DistributedApplicationSurfaceBidiExact as D

------------------------------------------------------------------------
-- APPLICATION SUCCESSION FRONTIER
--
-- Public programme continuity and visible team structure do not answer whether
-- the same capability-bearing carrier had a successor or was difficult to
-- replace.  This file records only what the bounded public search supports.
------------------------------------------------------------------------

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

record SuccessionSearchStatus : Set where
  constructor succession-search-status
  field
    chavezNamedSameCarrierSuccessorLocated : Bool
    chavezNamedSameCarrierSuccessorLocatedIsFalse : chavezNamedSameCarrierSuccessorLocated ≡ false
    leblancNamedSameCarrierSuccessorLocated : Bool
    leblancNamedSameCarrierSuccessorLocatedIsFalse : leblancNamedSameCarrierSuccessorLocated ≡ false
    rezaNamedSameCarrierSuccessorLocated : Bool
    rezaNamedSameCarrierSuccessorLocatedIsFalse : rezaNamedSameCarrierSuccessorLocated ≡ false
    absencePromotedToNoSuccessor : Bool
    absencePromotedToNoSuccessorIsFalse : absencePromotedToNoSuccessor ≡ false

canonicalSuccessionSearchStatus : SuccessionSearchStatus
canonicalSuccessionSearchStatus = succession-search-status false refl false refl false refl false refl

data SuccessionReverseTarget : Set where
  chavezSameCarrierTaskAllocation
  chavezNamedSuccessorOrHandover
  chavezPostDepartureRework
  leblancTechMatTaskAllocation
  leblancNamedSuccessorOrHandover
  leblancQualificationContinuity
  rezaProcessWindowTaskAllocation
  rezaNamedSuccessorOrHandover
  rezaManufacturingRequalification
  : SuccessionReverseTarget
