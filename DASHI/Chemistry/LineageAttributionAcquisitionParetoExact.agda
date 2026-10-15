module DASHI.Chemistry.LineageAttributionAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery

record LineageAcquisitionTarget : Set where
  constructor lineageAcquisitionTarget
  field
    targetKey : String
    scientificPayment : String
    attributionPayment : String
    primaryAuthorityRequirement : String
    exactLocatorRequirement : String
    contextMatchRequirement : String
    reuseValue : String
    acquisitionCost : String
    discoveryRoute : Discovery.DiscoveryRoute
    selectedMeansTrue : Bool
    selectedMeansTrueIsFalse : selectedMeansTrue ≡ false

open LineageAcquisitionTarget public

bh4SameObjectFluxDataset : LineageAcquisitionTarget
bh4SameObjectFluxDataset =
  lineageAcquisitionTarget
    "A1 same-object BH4/redox/branch-flux perturbation dataset"
    "directly separates allocator/downstream/parallel/context-specific BH4 models"
    "primary experiment must retain authors, protocol, dataset/version and measurement provenance"
    "primary interventional molecular/cellular study"
    "assay/table/dataset columns for BH4/BH2, NAD(P)H and branch-specific products/fluxes"
    "same cell type/compartment/time course across perturbation and readouts"
    "very high: pays Kitzerow discriminator plus generic flux lineage machinery"
    "high"
    Discovery.experimentalDesign
    false refl

bh4KineticParameterSet : LineageAcquisitionTarget
bh4KineticParameterSet =
  lineageAcquisitionTarget
    "A2 BH4 enzyme kinetic calibration set"
    "Km/Vmax/Kcat or source-bounded rate parameters for synthesis, recycle and consumer enzymes"
    "parameter values remain attached to original species/isoform/assay source"
    "primary kinetic experiments preferred; curated database may discover but not replace primary provenance"
    "exact table/figure/dataset row and units for every numeric value"
    "organism, isoform, pH, temperature, substrate/cofactor state and compartment"
    "high: reusable quantitative reaction kernel calibration"
    "medium-high"
    Discovery.residualObservation
    false refl

isotopeAtomMapBenchmarks : LineageAcquisitionTarget
isotopeAtomMapBenchmarks =
  lineageAcquisitionTarget
    "A3 isotope/atom-mapped reaction benchmark data"
    "pays literal source->product nuclear lineage for gold replays"
    "retain experiment authorship, tracer identity, instrument/protocol and raw/processed mapping distinction"
    "primary isotope tracing or expert-curated atom mapping with traceable primary source"
    "exact reaction, tracer position, product position and confidence/ambiguity locator"
    "matched species, compartment and reaction context"
    "very high: reusable across chemistry/biology lineage consumers"
    "medium"
    Discovery.experimentalDesign
    false refl

chlorAlkaliElectrodeCalibration : LineageAcquisitionTarget
chlorAlkaliElectrodeCalibration =
  lineageAcquisitionTarget
    "A4 chlor-alkali electrode calibration"
    "pays potential/current-density/electrode/material/temperature coordinates for gold-R1"
    "retain technical/experimental source role; BAT process description is not kinetic calibration"
    "primary electrochemical study or audited technical dataset"
    "exact polarization/kinetic table or dataset with electrode/material metadata"
    "chlor-alkali-relevant electrolyte, temperature, electrode and operating regime"
    "medium: validates external-electron-reservoir branch of generic transport"
    "medium"
    Discovery.residualObservation
    false refl

pbCaTargetCalibration : LineageAcquisitionTarget
pbCaTargetCalibration =
  lineageAcquisitionTarget
    "A5 Pb/Ca same-target structural/affinity/function calibration"
    "links occupancy/geometry to downstream function on the same protein target"
    "each structural, affinity and functional coordinate retains its original primary source unless same-object"
    "primary structural/biophysical/functional experiment"
    "exact target, site, concentration, affinity/occupancy, geometry and functional assay locator"
    "same target/site and controlled competing ions, pH, hydration and expression"
    "high: generic ionic/molecular substitution benchmark"
    "medium"
    Discovery.experimentalDesign
    false refl

carbonSiliconMatchedDataset : LineageAcquisitionTarget
carbonSiliconMatchedDataset =
  lineageAcquisitionTarget
    "A6 matched carbon/silicon reachable-chemistry comparison"
    "turns carbon-vs-alternative benchmark from design surface into comparative evidence"
    "retain separate sources for measured chemistry; DASHI owns any common matched-consumer comparison"
    "primary experimental/computational chemistry with reproducible methods"
    "exact reaction families, conditions, yields/energetics/kinetics and negative-result coverage"
    "matched solvent, temperature, pressure, redox, water activity, catalysts and availability assumptions"
    "high for prebiotic/carbon programme but does not settle abiogenesis"
    "high"
    Discovery.experimentalDesign
    false refl

canonicalLineageAcquisitionTargets : List LineageAcquisitionTarget
canonicalLineageAcquisitionTargets =
  bh4SameObjectFluxDataset
  ∷ isotopeAtomMapBenchmarks
  ∷ bh4KineticParameterSet
  ∷ pbCaTargetCalibration
  ∷ chlorAlkaliElectrodeCalibration
  ∷ carbonSiliconMatchedDataset
  ∷ []

record LineageAttributionAcquisitionFrontier : Set where
  constructor lineageAttributionAcquisitionFrontier
  field
    targets : List LineageAcquisitionTarget
    scientificImpactSeparated : Bool
    scientificImpactSeparatedIsTrue : scientificImpactSeparated ≡ true
    attributionClosureSeparated : Bool
    attributionClosureSeparatedIsTrue : attributionClosureSeparated ≡ true
    contextMatchSeparated : Bool
    contextMatchSeparatedIsTrue : contextMatchSeparated ≡ true
    reuseValueSeparated : Bool
    reuseValueSeparatedIsTrue : reuseValueSeparated ≡ true
    acquisitionCostSeparated : Bool
    acquisitionCostSeparatedIsTrue : acquisitionCostSeparated ≡ true
    frontierRankIsTruthRank : Bool
    frontierRankIsTruthRankIsFalse : frontierRankIsTruthRank ≡ false
    selectionCreatesEvidence : Bool
    selectionCreatesEvidenceIsFalse : selectionCreatesEvidence ≡ false
    reading : String

open LineageAttributionAcquisitionFrontier public

canonicalLineageAttributionAcquisitionFrontier : LineageAttributionAcquisitionFrontier
canonicalLineageAttributionAcquisitionFrontier =
  lineageAttributionAcquisitionFrontier
    canonicalLineageAcquisitionTargets
    true refl true refl true refl true refl true refl
    false refl false refl
    "Acquisition is a Pareto work frontier over scientific payment, attribution/provenance closure, context match, cross-domain reuse and cost. Selection neither proves a claim nor upgrades the selected source. Primary-source recovery and exact numeric locators remain independent obligations."
