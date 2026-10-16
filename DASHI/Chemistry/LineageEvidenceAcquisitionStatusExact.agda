module DASHI.Chemistry.LineageEvidenceAcquisitionStatusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.LineageAcquiredQuantitativePaymentsExact as Acquired
import DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact as Frontier
import DASHI.Chemistry.PAHMechanismStatePromotionExact as PAH
import DASHI.Chemistry.PAHElectronicStateHamiltonianMonsterProbeExact as ElectronicProbe
import DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorExact as Hepatic
import DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorExact as Neural
import DASHI.Biology.KitzerowBH4RedoxSpatialDiscriminatorExact as RedoxSpatial

------------------------------------------------------------------------
-- ACQUISITION STATUS AFTER PRIMARY/DIRECT WEB + MECHANISTIC/CAUSAL PASSES
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
    "pahHumanPhenylalanineKmPayment + pahHuman7BH4KmPayment + PAHMechanismStatePromotionExact source-backed single-turnover mechanism"
    "two source-bounded apparent Km coordinates and a source-backed ordered single-turnover mechanism are paid"
    "network-wide GCH1/PTPS/SPR/DHPR/TH/TPH/NOS/AGMO kinetics and matched contexts remain unpaid"
    "Kowlessur/Citron/Kaufman 1996 and Fitzpatrick et al. 2013 retain experimental ownership"
    false refl

pahMechanisticReplayStatus : AcquisitionStatusReceipt
pahMechanisticReplayStatus =
  acquisitionStatusReceipt
    "A7 PAH structure/QM-MM independent mechanistic replay"
    partiallyPaid
    "PAHMechanismStatePromotionExact.canonicalPAHMechanisticPromotion"
    "reaction identity, partial isotope lineage, 1J8U/6HYC released structural coordinate artifacts, source-backed kinetic mechanism and source-backed QM/MM reaction-path/energetics model are paid"
    "independent DASHI numerical replay of the structure-to-QM/MM path, complete atom map, electronic Hamiltonian matrix, real-space wavefunction/eigenvector coefficients and independent numerical artifact remain unpaid"
    "Andersen/Flatmark/Hough; Flydal et al.; Ishida et al.; Fitzpatrick et al. retain external source ownership; wwPDB artifacts retain artifact identity; DASHI owns only the promotion composition"
    false refl

pahElectronicHamiltonianMonsterStatus : AcquisitionStatusReceipt
pahElectronicHamiltonianMonsterStatus =
  acquisitionStatusReceipt
    "PAH attempted Hamiltonian/state/Monster promotion"
    partiallyPaid
    "PAHElectronicStateHamiltonianMonsterProbeExact"
    "literal finite catalytic-state carrier plus source-backed human Fe(II):BH4 structural state and bacterial high-spin Fe(IV) catalytic intermediate are paid"
    "human same-object Fe(IV) spectroscopy, numerical electronic Hamiltonian matrix, diagonalization/eigenvector coefficients and any nontrivial PAH-to-Monster representation remain unpaid; full-length 6HYC D2 symmetry supplies no same-object C3 coordinate"
    "Panay et al. 2011 retain bacterial ferryl evidence; human PAH structural sources retain human Fe(II):BH4 geometry; DASHI owns only the finite-state/probe construction and negative promotion receipts"
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
    partiallyPaid
    "KitzerowBH4HepaticCompetitionDiscriminatorExact + KitzerowBH4NeuralContextDiscriminatorExact + KitzerowBH4RedoxSpatialDiscriminatorExact"
    "rat hepatic PAH/iNOS competition, mouse neural state-history constraints, NOS-bound BH4 redox regeneration, GTPCH/nNOS spatial separation, direct cellular BH4 uptake, functional catecholaminergic-to-nNOS coculture crosstalk and intracellular-versus-extracellular striatal route effects are constrained; naive fixed/well-mixed/current-pool-sufficiency readings are therefore narrowed"
    "target-relevant human/neural multi-branch BH4/BH2 + NAD(P)H + J_PAH/J_TH/J_TPH/J_NOS/J_AGMO measurements with NOS-bound redox/coupling, enzyme abundance/localization, intracellular/extracellular route, quantitative donor-to-recipient transfer flux, compartment, region/cell type, timing and subgroup controls remain the decisive payment"
    "Pastor 1996; Anastasiadis/Kuhn/Levine 1994; Hyland et al. 1996; Hwang et al. 1998; Liang/Kaufman 1998; Witteveen/Giovanelli/Kaufman 1999; Sumi-Ichinose et al. 2001; Choi et al. 2003; Jiang et al. 2024 retain experimental ownership. DASHI owns only the cross-study discriminator composition; these studies do not establish autism causation or whole-model validity"
    false refl

bh4NeuralContextStatus : AcquisitionStatusReceipt
bh4NeuralContextStatus =
  acquisitionStatusReceipt
    "A1-neural BH4 current-pool versus state-history discriminator"
    paidForDeclaredCoordinate
    "KitzerowBH4NeuralContextDiscriminatorExact.canonicalNeuralContextDiscriminator"
    "current total brain BH4 alone is insufficient to identify downstream monoamine/dopamine recovery after chronic/developmental deficiency; enzyme abundance, anatomical region and developmental timing remain necessary coordinates"
    "translate this state-history/region dependence into target-relevant human or organoid same-object branch-flux measurements and determine which refined architecture explains it"
    "three primary mouse studies retain their individual claims; the declared coordinate is paid without transferring species/context or proving the broader causal model"
    false refl

bh4RedoxSpatialStatus : AcquisitionStatusReceipt
bh4RedoxSpatialStatus =
  acquisitionStatusReceipt
    "A1-redox-spatial BH4 pool-topology discriminator"
    paidForDeclaredCoordinate
    "KitzerowBH4RedoxSpatialDiscriminatorExact.canonicalRedoxSpatialDiscriminator"
    "NOS-bound BH4 requires explicit oxidation/regeneration state; monoaminergic synthesis and nNOS consumption need not be colocalized; exogenous BH4 uptake into neural/catecholaminergic preparations is directly measured; human nNOS-recipient cells support BH4 uptake/NO response plus functional catecholaminergic coculture crosstalk; and intracellular versus extracellular BH4 routes produce distinct striatal dopamine-release mechanisms. A single well-mixed scalar pool is therefore insufficient for the declared coordinate"
    "directly quantify donor-to-recipient BH4 molecular transfer rate/direction in target-relevant intact neural systems and integrate it with route-resolved BH4/BH2/NAD(P)H redox state plus simultaneous multi-branch flux"
    "Anastasiadis/Kuhn/Levine 1994, Hwang 1998, Liang/Kaufman 1998, Witteveen/Giovanelli/Kaufman 1999 and Choi et al. 2003 retain their individual observations; uptake/coculture function does not become a measured in-vivo donor-to-recipient flux and no whole allocator theorem is inferred"
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
  ∷ bh4NeuralContextStatus
  ∷ bh4RedoxSpatialStatus
  ∷ pahAtomMappingStatus
  ∷ pahKineticsStatus
  ∷ pbCaTargetStatus
  ∷ carbonSiliconStatus
  ∷ chlorCalibrationStatus
  ∷ pahMechanisticReplayStatus
  ∷ pahElectronicHamiltonianMonsterStatus
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
    mechanisticPromotionClosesFluxTarget : Bool
    mechanisticPromotionClosesFluxTargetIsFalse : mechanisticPromotionClosesFluxTarget ≡ false
    failedMonsterProbeCreatesAcquisitionPriority : Bool
    failedMonsterProbeCreatesAcquisitionPriorityIsFalse : failedMonsterProbeCreatesAcquisitionPriority ≡ false
    hepaticTwoBranchPaymentClosesWholeMultiBranchTarget : Bool
    hepaticTwoBranchPaymentClosesWholeMultiBranchTargetIsFalse : hepaticTwoBranchPaymentClosesWholeMultiBranchTarget ≡ false
    currentPoolRestorationGuaranteesFunctionalRescue : Bool
    currentPoolRestorationGuaranteesFunctionalRescueIsFalse : currentPoolRestorationGuaranteesFunctionalRescue ≡ false
    scalarWellMixedPoolSufficient : Bool
    scalarWellMixedPoolSufficientIsFalse : scalarWellMixedPoolSufficient ≡ false
    directIntercellularTransferAlreadyPaid : Bool
    directIntercellularTransferAlreadyPaidIsFalse : directIntercellularTransferAlreadyPaid ≡ false
    directDiscriminatorCanUpgradePreviouslyUnpaidTargetToPartial : Bool
    directDiscriminatorCanUpgradePreviouslyUnpaidTargetToPartialIsTrue : directDiscriminatorCanUpgradePreviouslyUnpaidTargetToPartial ≡ true
    unresolvedTargetRemainsTyped : Bool
    unresolvedTargetRemainsTypedIsTrue : unresolvedTargetRemainsTyped ≡ true

open EvidenceAcquisitionStatusBoundary public

canonicalEvidenceAcquisitionStatusBoundary : EvidenceAcquisitionStatusBoundary
canonicalEvidenceAcquisitionStatusBoundary =
  evidenceAcquisitionStatusBoundary
    false refl false refl false refl false refl false refl
    false refl false refl false refl false refl true refl true refl
