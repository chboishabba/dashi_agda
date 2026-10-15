module DASHI.Chemistry.LineageAttributionAcquisitionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact as Attribution
import DASHI.Chemistry.LineageSourceManifestationGuardExact as Manifestation

------------------------------------------------------------------------
-- PARETO ACQUISITION FRONTIER FOR ATTRIBUTION / CALIBRATION PAYMENT
--
-- Rank is investigative utility only. It never ranks truth or scientific
-- correctness. Unpaid coordinates keep their source identity and role.
------------------------------------------------------------------------

data AcquisitionKind : Set where
  exactPrimaryLocator : AcquisitionKind
  numericCalibration : AcquisitionKind
  atomMappingDataset : AcquisitionKind
  isotopeTracerDataset : AcquisitionKind
  kineticDataset : AcquisitionKind
  fluxDataset : AcquisitionKind
  structuralManifestation : AcquisitionKind
  matchedAlternativeChemistryDataset : AcquisitionKind
  provenanceContactArtifact : AcquisitionKind

data EvidenceIndependence : Set where
  sameSourceRefinement : EvidenceIndependence
  independentPrimaryMeasurement : EvidenceIndependence
  independentReplication : EvidenceIndependence
  independenceUndetermined : EvidenceIndependence

record AcquisitionItem : Set where
  constructor acquisitionItem
  field
    itemKey : String
    kind : AcquisitionKind
    targetReplayReference : String
    targetCoordinateReference : String
    desiredSourceRole : String
    exactManifestationNeed : String
    expectedDischarge : String
    independence : EvidenceIndependence
    acquisitionCostRank : Nat
    reuseValueRank : Nat
    causalValueRank : Nat
    attributionValueRank : Nat
    truthRank : Nat
    truthRankIsSentinelOnly : Bool
    truthRankIsSentinelOnlyIsTrue : truthRankIsSentinelOnly ≡ true

open AcquisitionItem public

bh4FluxDataset : AcquisitionItem
bh4FluxDataset =
  acquisitionItem
    "A1 BH4 same-system flux discriminator dataset"
    fluxDataset
    "Kitzerow BH4 flux causal models"
    "BH4/BH2 + NAD(P)H + J_PAH/J_TH/J_TPH/J_NOS/J_AGMO under controlled perturbation"
    "primary experimental dataset with exact methods and sample context"
    "dataset/table/supplement locator plus assay calibration"
    "separates symbolic pool balance from measured branch allocation and helps discriminate H1/H2/H3/H4"
    independentPrimaryMeasurement
    5 10 10 8 0 true refl

pahAtomMap : AcquisitionItem
pahAtomMap =
  acquisitionItem
    "A2 PAH isotope/atom-map replay"
    isotopeTracerDataset
    "gold-R2 PAH BH4 hydroxylation"
    "oxygen/phenylalanine/pterin atom mapping through hydroxylation"
    "primary isotope-tracing or mechanistic experiment"
    "exact figure/table/scheme/method locator"
    "pays typed nuclear-lineage mapping and distinguishes mechanism-family support from same-object atom map"
    independentPrimaryMeasurement
    4 8 7 7 0 true refl

chlorLocator : AcquisitionItem
chlorLocator =
  acquisitionItem
    "A3 chlor-alkali exact half-reaction locator"
    exactPrimaryLocator
    "gold-R1 chlor-alkali"
    "anode/cathode reaction identity and electron multiplicity"
    "institutional or primary electrochemistry source"
    "exact page/equation/figure locator on the same manifestation"
    "upgrades section-level attribution to exact locator without manufacturing kinetics"
    sameSourceRefinement
    2 7 3 8 0 true refl

pbCaTargetDataset : AcquisitionItem
pbCaTargetDataset =
  acquisitionItem
    "A4 Pb/Ca same-target structural-functional replay"
    structuralManifestation
    "Pb/Ca end-to-end replay"
    "same target: ion occupancy -> coordination geometry -> conformational/function readout"
    "primary same-object structural/functional study"
    "exact target/structure/assay locator"
    "reduces cross-study composition and pays a stronger end-to-end same-object replay"
    independentPrimaryMeasurement
    6 9 9 9 0 true refl

carbonSiliconMatchedDataset : AcquisitionItem
carbonSiliconMatchedDataset =
  acquisitionItem
    "A5 matched carbon-vs-silicon reachable chemistry"
    matchedAlternativeChemistryDataset
    "carbon/silicon reachable-chemistry benchmark"
    "matched solvent/T/P/redox/catalyst reaction reachability and stability/reactivity coordinates"
    "primary comparative experimental or validated computational dataset"
    "same protocol/model and explicit environment across both backbones"
    "turns overview-level carbon context into a direct comparative discriminator"
    independentPrimaryMeasurement
    9 10 8 8 0 true refl

canonicalAcquisitionItems : List AcquisitionItem
canonicalAcquisitionItems =
  bh4FluxDataset ∷ pahAtomMap ∷ chlorLocator ∷ pbCaTargetDataset ∷ carbonSiliconMatchedDataset ∷ []

record LineageAttributionAcquisitionFrontier : Set where
  constructor lineageAttributionAcquisitionFrontier
  field
    items : List AcquisitionItem
    sourcePrimacyAxisExplicit : Bool
    sourcePrimacyAxisExplicitIsTrue : sourcePrimacyAxisExplicit ≡ true
    manifestationAxisExplicit : Bool
    manifestationAxisExplicitIsTrue : manifestationAxisExplicit ≡ true
    sameObjectAxisExplicit : Bool
    sameObjectAxisExplicitIsTrue : sameObjectAxisExplicit ≡ true
    causalValueSeparateFromAttributionValue : Bool
    causalValueSeparateFromAttributionValueIsTrue :
      causalValueSeparateFromAttributionValue ≡ true
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
    canonicalAcquisitionItems
    true refl true refl true refl true refl false refl true refl false refl
