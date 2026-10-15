module DASHI.Chemistry.LineageEvidenceAcquisitionStatusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.LineageAcquiredQuantitativePaymentsExact as Acquired
import DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact as Frontier

------------------------------------------------------------------------
-- ACQUISITION STATUS AFTER PRIMARY/DIRECT WEB PASS
------------------------------------------------------------------------

data PaymentStatus : Set where
  paidForDeclaredCoordinate : PaymentStatus
  partiallyPaid : PaymentStatus
  unpaid : PaymentStatus
  publicArtifactLinkedUninspected : PaymentStatus

record AcquisitionStatusReceipt : Set where
  constructor acquisitionStatusReceipt
  field
    targetKey : String
    status : PaymentStatus
    acquiredPaymentReference : String
    closedCoordinate : String
    remainingObligation : String
    attributionState : String
    statusCreatesTruth : Bool
    statusCreatesTruthIsFalse : statusCreatesTruth ≡ false

open AcquisitionStatusReceipt public

pahAtomMappingStatus : AcquisitionStatusReceipt
pahAtomMappingStatus =
  acquisitionStatusReceipt
    "A2 PAH isotope/atom-map replay"
    partiallyPaid
    "LineageAcquiredQuantitativePaymentsExact.pah4aOxygenLineagePayment"
    "source of the 4a-hydroxypterin oxygen is paid by a primary 18O experiment"
    "complete atom mapping across phenylalanine, molecular oxygen, tyrosine, pterin and water remains unpaid"
    "Dix/Bollag/Domanico/Benkovic 1985 retain source ownership; DASHI owns only the lineage projection"
    false refl

pahKineticsStatus : AcquisitionStatusReceipt
pahKineticsStatus =
  acquisitionStatusReceipt
    "A3 BH4 enzyme kinetic calibration set"
    partiallyPaid
    "pahHumanPhenylalanineKmPayment + pahHuman7BH4KmPayment"
    "two source-bounded apparent Km coordinates for recombinant human PAH are paid"
    "network-wide GCH1/PTPS/SPR/DHPR/TH/TPH/NOS/AGMO kinetics and matched contexts remain unpaid"
    "Kowlessur/Citron/Kaufman 1996 retain experimental ownership"
    false refl

pbCaTargetStatus : AcquisitionStatusReceipt
pbCaTargetStatus =
  acquisitionStatusReceipt
    "A5 Pb/Ca same-target structural-functional replay"
    partiallyPaid
    "pbCa fluorescence/PDE EC50 payments + pbCaNnosTargetRecognitionPayment"
    "calmodulin target-relative activation concentrations and nNOS-peptide recognition are paid in source-specific assays"
    "single same-object structure->occupancy->conformation->full-function tuple and organism dose-response remain unpaid"
    "Kern et al. 2000 and Shirran/Barran 2009 retain experiment ownership"
    false refl

carbonSiliconStatus : AcquisitionStatusReceipt
carbonSiliconStatus =
  acquisitionStatusReceipt
    "A6 matched carbon-vs-silicon reachable chemistry"
    partiallyPaid
    "siliconBiocatalysisPayment + siliconBiochemistryAssessment2020 source"
    "silicon chemical constraints are directly compared in the literature and biological C-Si catalysis is experimentally demonstrated"
    "matched carbon-versus-silicon reaction families under one frozen solvent/T/P/redox/catalyst protocol remain unpaid"
    "Petkowski/Bains/Seager and Kan/Lewis/Chen/Arnold retain their respective source results"
    false refl

bh4FluxStatus : AcquisitionStatusReceipt
bh4FluxStatus =
  acquisitionStatusReceipt
    "A1 BH4 same-system flux discriminator dataset"
    unpaid
    "none acquired in this pass"
    "no same-system branch-allocation coordinate promoted"
    "controlled BH4/BH2 + NAD(P)H + J_PAH/J_TH/J_TPH/J_NOS/J_AGMO perturbation dataset remains the decisive payment"
    "nearby pathway/mechanism sources remain attributed but cannot substitute for the missing same-object flux experiment"
    false refl

chlorCalibrationStatus : AcquisitionStatusReceipt
chlorCalibrationStatus =
  acquisitionStatusReceipt
    "A4 chlor-alkali electrochemical calibration"
    partiallyPaid
    "existing canonical half reactions + technical process sources"
    "stoichiometric/electron half-reaction identity and process context are paid"
    "same-cell electrode material, temperature, electrolyte, potential/current density and microkinetic dataset remains unpaid"
    "technical/textbook/process sources do not inherit authority for unavailable plant-specific calibration"
    false refl

stanfordContactStatus : AcquisitionStatusReceipt
stanfordContactStatus =
  acquisitionStatusReceipt
    "P1 Stanford contact provenance"
    publicArtifactLinkedUninspected
    "stanfordPublicArtifactDiscoveryPayment"
    "originator-maintained public timeline exposes a direct Adobe link labelled View Email Screenshot"
    "linked contents, metadata, authenticity, completeness, institutional actor identity and any later use/derivation remain uninspected/unpaid"
    "Kitzerow is the originator of the public claim; no independent verification is inferred"
    false refl

brazilContactStatus : AcquisitionStatusReceipt
brazilContactStatus =
  acquisitionStatusReceipt
    "P2 Brazil/MDPI correspondence provenance"
    unpaid
    "originator report located; underlying correspondence not acquired"
    "public account of alleged post-publication journal/author response remains discoverable"
    "underlying correspondence, exact message contents, metadata and manuscript-derivation chronology remain unpaid"
    "originator report remains distinct from authenticated correspondence"
    false refl

iaccContactStatus : AcquisitionStatusReceipt
iaccContactStatus =
  acquisitionStatusReceipt
    "P3 IACC/MedMaps contact provenance"
    unpaid
    "originator attribution page located; underlying contact artifact not acquired"
    "public allegation/exposure-path narrative remains discoverable"
    "underlying message/export, metadata, institutional chronology and use/derivation remain unpaid"
    "originator report remains distinct from authenticated contact evidence"
    false refl

canonicalAcquisitionStatuses : List AcquisitionStatusReceipt
canonicalAcquisitionStatuses =
  bh4FluxStatus
  ∷ pahAtomMappingStatus
  ∷ pahKineticsStatus
  ∷ chlorCalibrationStatus
  ∷ pbCaTargetStatus
  ∷ carbonSiliconStatus
  ∷ stanfordContactStatus
  ∷ brazilContactStatus
  ∷ iaccContactStatus
  ∷ []

record EvidenceAcquisitionStatusBoundary : Set where
  constructor evidenceAcquisitionStatusBoundary
  field
    partialPaymentClosesWholeTarget : Bool
    partialPaymentClosesWholeTargetIsFalse : partialPaymentClosesWholeTarget ≡ false
    publicLinkEqualsAuthenticatedArtifact : Bool
    publicLinkEqualsAuthenticatedArtifactIsFalse : publicLinkEqualsAuthenticatedArtifact ≡ false
    nearbyEvidenceSubstitutesForSameObjectFlux : Bool
    nearbyEvidenceSubstitutesForSameObjectFluxIsFalse : nearbyEvidenceSubstitutesForSameObjectFlux ≡ false
    unresolvedTargetRemainsTyped : Bool
    unresolvedTargetRemainsTypedIsTrue : unresolvedTargetRemainsTyped ≡ true

open EvidenceAcquisitionStatusBoundary public

canonicalEvidenceAcquisitionStatusBoundary : EvidenceAcquisitionStatusBoundary
canonicalEvidenceAcquisitionStatusBoundary =
  evidenceAcquisitionStatusBoundary false refl false refl false refl true refl
