module DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- UNIFIED SCIENTIFIC + ATTRIBUTION ACQUISITION FRONTIER
------------------------------------------------------------------------

data ScientificAcquisitionKind : Set where
  exactPrimaryLocator : ScientificAcquisitionKind
  numericCalibration : ScientificAcquisitionKind
  isotopeTracerDataset : ScientificAcquisitionKind
  kineticDataset : ScientificAcquisitionKind
  fluxDataset : ScientificAcquisitionKind
  structuralFunctionalDataset : ScientificAcquisitionKind
  matchedAlternativeChemistryDataset : ScientificAcquisitionKind

data EvidenceIndependence : Set where
  sameSourceRefinement : EvidenceIndependence
  independentPrimaryMeasurement : EvidenceIndependence
  independentReplication : EvidenceIndependence
  independenceUndetermined : EvidenceIndependence

record ScientificAcquisitionItem : Set where
  constructor scientificAcquisitionItem
  field
    scientificKey : String
    scientificKind : ScientificAcquisitionKind
    targetReplayReference : String
    targetCoordinateReference : String
    desiredSourceRole : String
    exactManifestationNeed : String
    expectedDischarge : String
    independence : EvidenceIndependence
    scientificCostRank : Nat
    reuseValueRank : Nat
    causalValueRank : Nat
    scientificAttributionValueRank : Nat
    scientificTruthRank : Nat
    scientificTruthRankIsSentinelOnly : Bool
    scientificTruthRankIsSentinelOnlyIsTrue : scientificTruthRankIsSentinelOnly ≡ true

open ScientificAcquisitionItem public

bh4FluxDataset : ScientificAcquisitionItem
bh4FluxDataset =
  scientificAcquisitionItem
    "A1 BH4 same-system flux discriminator dataset" fluxDataset
    "Kitzerow BH4 flux causal models"
    "BH4/BH2 + NAD(P)H + J_PAH/J_TH/J_TPH/J_NOS/J_AGMO under controlled perturbation"
    "primary experimental dataset with exact methods/sample context"
    "dataset/table/supplement locator plus assay calibration"
    "separates symbolic pool balance from measured branch allocation and discriminates H1/H2/H3/H4"
    independentPrimaryMeasurement 5 10 10 8 0 true refl

pahAtomMap : ScientificAcquisitionItem
pahAtomMap =
  scientificAcquisitionItem
    "A2 PAH isotope/atom-map replay" isotopeTracerDataset
    "gold-R2 PAH BH4 hydroxylation"
    "oxygen/phenylalanine/pterin atom mapping through hydroxylation"
    "primary isotope-tracing or mechanistic experiment"
    "exact figure/table/scheme/method locator"
    "pays typed nuclear-lineage mapping rather than mechanism-family analogy"
    independentPrimaryMeasurement 4 8 7 7 0 true refl

bh4KineticSet : ScientificAcquisitionItem
bh4KineticSet =
  scientificAcquisitionItem
    "A3 BH4 enzyme kinetic calibration set" kineticDataset
    "BH4 synthesis/recycle/consumer network"
    "Km/Vmax/kcat with isoform, species, substrate/cofactor and assay context"
    "primary kinetic experiments; curated databases may discover but not replace provenance"
    "exact numeric table/figure/dataset row with units and uncertainty"
    "pays context-bounded rate parameters without transferring them across isoforms/conditions"
    independentPrimaryMeasurement 5 9 8 8 0 true refl

chlorLocator : ScientificAcquisitionItem
chlorLocator =
  scientificAcquisitionItem
    "A4 chlor-alkali electrochemical calibration" numericCalibration
    "gold-R1 chlor-alkali"
    "potential/current density/electrode material/temperature and exact half-reaction locator"
    "primary electrochemistry or audited technical dataset"
    "exact page/equation/table/dataset locator on same manifestation"
    "pays context-specific calibration without manufacturing microkinetics"
    independentPrimaryMeasurement 3 7 4 8 0 true refl

pbCaTargetDataset : ScientificAcquisitionItem
pbCaTargetDataset =
  scientificAcquisitionItem
    "A5 Pb/Ca same-target structural-functional replay" structuralFunctionalDataset
    "Pb/Ca end-to-end replay"
    "same target: occupancy -> coordination geometry -> conformation/function"
    "primary same-object structural/biophysical/functional study"
    "exact target/structure/assay locator"
    "reduces cross-study composition and pays stronger same-object replay"
    independentPrimaryMeasurement 6 9 9 9 0 true refl

carbonSiliconMatchedDataset : ScientificAcquisitionItem
carbonSiliconMatchedDataset =
  scientificAcquisitionItem
    "A6 matched carbon-vs-silicon reachable chemistry" matchedAlternativeChemistryDataset
    "carbon/silicon reachable-chemistry benchmark"
    "matched solvent/T/P/redox/water activity/catalyst reachability and stability/reactivity coordinates"
    "primary comparative experimental or validated computational dataset"
    "same protocol/model and explicit environment across both backbones"
    "turns overview carbon context into a direct comparative discriminator"
    independentPrimaryMeasurement 9 10 8 8 0 true refl

canonicalScientificAcquisitionItems : List ScientificAcquisitionItem
canonicalScientificAcquisitionItems =
  bh4FluxDataset ∷ pahAtomMap ∷ bh4KineticSet ∷ chlorLocator ∷ pbCaTargetDataset ∷ carbonSiliconMatchedDataset ∷ []

------------------------------------------------------------------------
-- Contact/exposure provenance queue. These items have zero causal-scientific
-- value by construction; they pay chronology/exposure/derivation provenance.
------------------------------------------------------------------------

data ProvenanceAcquisitionKind : Set where
  contactMessageArtifact : ProvenanceAcquisitionKind
  correspondenceThreadArtifact : ProvenanceAcquisitionKind
  manuscriptHistoryArtifact : ProvenanceAcquisitionKind
  institutionalRoleTimeline : ProvenanceAcquisitionKind

data ProvenanceStatus : Set where
  originatorReportedOnly : ProvenanceStatus
  artifactAcquiredUnverified : ProvenanceStatus
  artifactAuthenticated : ProvenanceStatus
  directUseDocumented : ProvenanceStatus

record ProvenanceAcquisitionItem : Set where
  constructor provenanceAcquisitionItem
  field
    provenanceKey : String
    provenanceKind : ProvenanceAcquisitionKind
    targetAttributionReference : String
    claimedEventReference : String
    exactArtifactNeed : String
    authenticationNeed : String
    expectedUpgrade : String
    currentStatus : ProvenanceStatus
    provenanceCostRank : Nat
    provenanceAttributionValueRank : Nat
    provenanceCausalScientificValueRank : Nat
    provenanceTruthRank : Nat
    provenanceTruthRankIsSentinelOnly : Bool
    provenanceTruthRankIsSentinelOnlyIsTrue : provenanceTruthRankIsSentinelOnly ≡ true

open ProvenanceAcquisitionItem public

stanfordContactArtifact : ProvenanceAcquisitionItem
stanfordContactArtifact =
  provenanceAcquisitionItem
    "P1 Stanford contact provenance" contactMessageArtifact
    "Kitzerow priority/attribution: Stanford"
    "claimed 27 Nov 2023 Stanford Neurodiversity Project contact requesting model information"
    "underlying email/message export with sender, recipient, timestamp and substantive content"
    "metadata/context sufficient to authenticate communication and chronology"
    "may upgrade originator-reported contact to authenticated exposure evidence only"
    originatorReportedOnly 3 10 0 0 true refl

brazilCorrespondenceArtifact : ProvenanceAcquisitionItem
brazilCorrespondenceArtifact =
  provenanceAcquisitionItem
    "P2 Brazil/MDPI correspondence provenance" correspondenceThreadArtifact
    "Kitzerow priority/attribution: BH4 systematic review"
    "claimed MDPI/Latini correspondence after attribution concern"
    "underlying correspondence plus manuscript/publication timeline records"
    "message/export authenticity and chronology against manuscript versions"
    "may resolve who communicated what and when; does not by itself establish derivation/copying"
    originatorReportedOnly 4 10 0 0 true refl

iaccMedMapsContactArtifact : ProvenanceAcquisitionItem
iaccMedMapsContactArtifact =
  provenanceAcquisitionItem
    "P3 IACC/MedMaps contact provenance" contactMessageArtifact
    "Kitzerow priority/attribution: IACC developmental-systems framework"
    "claimed 2024 MedMaps/Honey Rinicella awareness/contact before later IACC role"
    "underlying message/export with date, participants and substantive content"
    "communication metadata plus institutional-role chronology"
    "may upgrade awareness/exposure evidence; scientific convergence and derivation remain separate"
    originatorReportedOnly 4 10 0 0 true refl

canonicalContactProvenanceItems : List ProvenanceAcquisitionItem
canonicalContactProvenanceItems =
  stanfordContactArtifact ∷ brazilCorrespondenceArtifact ∷ iaccMedMapsContactArtifact ∷ []

record LineageAttributionAcquisitionFrontier : Set where
  constructor lineageAttributionAcquisitionFrontier
  field
    scientificItems : List ScientificAcquisitionItem
    contactProvenanceItems : List ProvenanceAcquisitionItem
    sourcePrimacyAxisExplicit : Bool
    sourcePrimacyAxisExplicitIsTrue : sourcePrimacyAxisExplicit ≡ true
    manifestationAxisExplicit : Bool
    manifestationAxisExplicitIsTrue : manifestationAxisExplicit ≡ true
    sameObjectAxisExplicit : Bool
    sameObjectAxisExplicitIsTrue : sameObjectAxisExplicit ≡ true
    causalValueSeparateFromAttributionValue : Bool
    causalValueSeparateFromAttributionValueIsTrue : causalValueSeparateFromAttributionValue ≡ true
    scientificSupportSeparateFromContactProvenance : Bool
    scientificSupportSeparateFromContactProvenanceIsTrue : scientificSupportSeparateFromContactProvenance ≡ true
    contactEvidenceAutomaticallyProvesDerivation : Bool
    contactEvidenceAutomaticallyProvesDerivationIsFalse : contactEvidenceAutomaticallyProvesDerivation ≡ false
    contactEvidenceAutomaticallyProvesPlagiarism : Bool
    contactEvidenceAutomaticallyProvesPlagiarismIsFalse : contactEvidenceAutomaticallyProvesPlagiarism ≡ false
    scientificSupportAutomaticallyProvesPriority : Bool
    scientificSupportAutomaticallyProvesPriorityIsFalse : scientificSupportAutomaticallyProvesPriority ≡ false
    priorityAutomaticallyProvesCorrectness : Bool
    priorityAutomaticallyProvesCorrectnessIsFalse : priorityAutomaticallyProvesCorrectness ≡ false
    frontierRankIsTruthRank : Bool
    frontierRankIsTruthRankIsFalse : frontierRankIsTruthRank ≡ false
    unpaidCoordinateRetainsAttribution : Bool
    unpaidCoordinateRetainsAttributionIsTrue : unpaidCoordinateRetainsAttribution ≡ true
    acquisitionCreatesAuthority : Bool
    acquisitionCreatesAuthorityIsFalse : acquisitionCreatesAuthority ≡ false

open LineageAttributionAcquisitionFrontier public

canonicalLineageAttributionAcquisitionFrontier : LineageAttributionAcquisitionFrontier
canonicalLineageAttributionAcquisitionFrontier =
  lineageAttributionAcquisitionFrontier
    canonicalScientificAcquisitionItems
    canonicalContactProvenanceItems
    true refl true refl true refl true refl true refl
    false refl false refl false refl false refl
    false refl true refl false refl
