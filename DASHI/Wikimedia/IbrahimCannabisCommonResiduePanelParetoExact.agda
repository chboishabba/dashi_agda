module DASHI.Wikimedia.IbrahimCannabisCommonResiduePanelParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisContaminantToxicantAssayParetoExact as Parent
import DASHI.Wikimedia.IbrahimCannabisFadedFarmingPesticideOccurrenceParetoExact as Occurrence
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- COMMON CANNABIS RESIDUE PANEL / COVERAGE OWNER
--
-- A finite residue panel is an observer, not the contaminant universe.
-- This owner records common empirically observed cannabis residues, registry
-- identity, method-family coverage and explicit blind spots.  It does not turn
-- detection into toxicity and does not infer a molecule from a remembered
-- trade name or typo.
------------------------------------------------------------------------

data ResidueRole : Set where
  fungicide : ResidueRole
  herbicide : ResidueRole
  insecticide : ResidueRole
  acaricide : ResidueRole
  plantGrowthRegulator : ResidueRole
  pesticideSynergist : ResidueRole
  biologicalInsecticideMixture : ResidueRole
  unresolvedTradeName : ResidueRole

record ResidueRegistry : Set where
  constructor residue-registry
  field
    canonicalName : String
    role : ResidueRole
    pubChemCID : String
    molecularFormula : String
    pubChemLink : String
    registryPaid : Bool
open ResidueRegistry public

myclobutanil : ResidueRegistry
myclobutanil = residue-registry
  "myclobutanil" fungicide "6336" "C15H17ClN4"
  "https://pubchem.ncbi.nlm.nih.gov/compound/6336" true

chlorfenapyr : ResidueRegistry
chlorfenapyr = residue-registry
  "chlorfenapyr" insecticide "91778" "C15H11BrClF3N2O"
  "https://pubchem.ncbi.nlm.nih.gov/compound/91778" true

bifenazate : ResidueRegistry
bifenazate = residue-registry
  "bifenazate" acaricide "" ""
  "unpaid: PubChem registry row to be joined before CID promotion" false

paclobutrazol : ResidueRegistry
paclobutrazol = residue-registry
  "paclobutrazol" plantGrowthRegulator "73671" "C13H20ClN3O"
  "https://pubchem.ncbi.nlm.nih.gov/compound/73671" true

abamectin : ResidueRegistry
abamectin = residue-registry
  "abamectin" insecticide "9920327" ""
  "https://pubchem.ncbi.nlm.nih.gov/compound/9920327" true

piperonylButoxide : ResidueRegistry
piperonylButoxide = residue-registry
  "piperonyl butoxide" pesticideSynergist "5794" "C19H30O5"
  "https://pubchem.ncbi.nlm.nih.gov/compound/5794" true

glyphosate : ResidueRegistry
glyphosate = residue-registry
  "glyphosate" herbicide "3496" "C3H8NO5P"
  "https://pubchem.ncbi.nlm.nih.gov/compound/3496" true

spinosad : ResidueRegistry
spinosad = residue-registry
  "spinosad (mixture of spinosyn A and spinosyn D)" biologicalInsecticideMixture
  "17754356" "C83H132N2O20"
  "https://pubchem.ncbi.nlm.nih.gov/compound/17754356" true

------------------------------------------------------------------------
-- User-supplied token "concerta" is deliberately not silently normalized.
-- Public authoritative results identify CONCERTA as methylphenidate medicine,
-- not an agricultural pesticide.  A plausible nearby pesticide trade-name is
-- CONSERVE, whose active ingredient is spinosad, but same-referent identity is
-- unpaid until the intended term/source is recovered.
------------------------------------------------------------------------

record AliasResolution : Set where
  constructor alias-resolution
  field
    observedToken : String
    literalPublicIdentity : String
    candidateAgriculturalIdentity : String
    candidateActiveIngredient : String
    sameReferentPaid : Bool
open AliasResolution public

concertaTokenResolution : AliasResolution
concertaTokenResolution = alias-resolution
  "concerta"
  "CONCERTA is a methylphenidate modified-release medicine in current Australian medicine records"
  "possible intended agricultural trade name: CONSERVE / Conserve SC; not asserted"
  "candidate only: spinosad"
  false

------------------------------------------------------------------------
-- Current high-value occurrence anchor: Fiering et al. 2026 expands the
-- Gagnon 2023 Canadian survey to 50 legal + 50 illegal inflorescences.
------------------------------------------------------------------------

record ResidueOccurrence : Set where
  constructor residue-occurrence
  field
    analyte : ResidueRegistry
    study : String
    population : String
    detectionRate : String
    concentrationRange : String
    measurementMethod : String
    occurrencePaid : Bool
    commonInLicensedCannabisPaid : Bool
    inhaledToxicDosePaid : Bool
open ResidueOccurrence public

fiering2026Reference : String
fiering2026Reference =
  "Quinton Fiering et al., Comparative analysis of metals, pesticides, mycotoxins, microbial contaminants and THC potency in illegal and regulated cannabis inflorescences in Canada, Journal of Cannabis Research 8:48 (2026), DOI 10.1186/s42238-026-00414-y"

myclobutanil2026Illegal : ResidueOccurrence
myclobutanil2026Illegal = residue-occurrence
  myclobutanil fiering2026Reference
  "50 illegal Canadian cannabis inflorescence samples"
  "72%"
  "0.01-130 ug/g"
  "validated LC-MS/MS and GC-MS/MS pesticide methods"
  true false false

myclobutanil2026Legal : ResidueOccurrence
myclobutanil2026Legal = residue-occurrence
  myclobutanil fiering2026Reference
  "50 legal Canadian cannabis products"
  "trace detection in one of two legal pesticide-positive products"
  "0.01 ug/g lowest calibrated level"
  "validated LC-MS/MS and GC-MS/MS pesticide methods"
  true false false

chlorfenapyr2026Illegal : ResidueOccurrence
chlorfenapyr2026Illegal = residue-occurrence
  chlorfenapyr fiering2026Reference
  "50 illegal Canadian cannabis inflorescence samples"
  "24%"
  "<0.02-1.4 ug/g"
  "validated LC-MS/MS and GC-MS/MS pesticide methods"
  true false false

bifenazate2026Illegal : ResidueOccurrence
bifenazate2026Illegal = residue-occurrence
  bifenazate fiering2026Reference
  "50 illegal Canadian cannabis inflorescence samples"
  "12%"
  "0.027-2.0 ug/g"
  "validated LC-MS/MS and GC-MS/MS pesticide methods"
  true false false

paclobutrazol2026Illegal : ResidueOccurrence
paclobutrazol2026Illegal = residue-occurrence
  paclobutrazol fiering2026Reference
  "50 illegal Canadian cannabis inflorescence samples"
  "60%"
  "0.048-2.4 ug/g"
  "validated LC-MS/MS and GC-MS/MS pesticide methods"
  true false false

piperonylButoxide2026Illegal : ResidueOccurrence
piperonylButoxide2026Illegal = residue-occurrence
  piperonylButoxide fiering2026Reference
  "50 illegal Canadian cannabis inflorescence samples"
  "6%"
  "1.5-1700 ug/g"
  "validated LC-MS/MS and GC-MS/MS pesticide methods"
  true false false

spinosad2026Illegal : ResidueOccurrence
spinosad2026Illegal = residue-occurrence
  spinosad fiering2026Reference
  "50 illegal Canadian cannabis inflorescence samples"
  "2%"
  "10 ug/g"
  "validated LC-MS/MS and GC-MS/MS pesticide methods; source table reports spinosad"
  true false false

------------------------------------------------------------------------
-- Glyphosate requires an explicit coverage lane rather than being smuggled into
-- a generic multiresidue panel.  Its high polarity/ionic chemistry commonly
-- motivates dedicated methods.  Australia's National Measurement Institute,
-- for example, derivatizes glyphosate/AMPA and uses isotope-dilution UPLC-MS/MS.
------------------------------------------------------------------------

record CoverageReceipt : Set where
  constructor coverage-receipt
  field
    analyte : ResidueRegistry
    targetMatrix : String
    methodReference : String
    reportingLimitReference : String
    methodValidatedForCannabis : Bool
    includedInFiering2026PanelPaid : Bool
    measuredCannabisOccurrencePaid : Bool
open CoverageReceipt public

glyphosateCoverageResidual : CoverageReceipt
glyphosateCoverageResidual = coverage-receipt
  glyphosate
  "cannabis flower"
  "dedicated glyphosate/AMPA method likely required; Australian NMI NR53 uses FMOC derivatization plus isotope-dilution UPLC-MS/MS for water/soil/foliage"
  "NMI foliage reporting limit 0.5 mg/kg for glyphosate and AMPA; this is not a cannabis-specific validated LOQ"
  false false false

------------------------------------------------------------------------
-- Finite-panel / blacklist coverage boundary.
------------------------------------------------------------------------

data PanelNonDetectionCreatesAbsence : Set where
data ResidueOccurrenceCreatesInhaledToxicDose : Set where
data TradeNameSimilarityCreatesMoleculeIdentity : Set where
data GenericMultiresiduePanelCreatesGlyphosateCoverage : Set where

panelNonDetectionDoesNotCreateAbsence : PanelNonDetectionCreatesAbsence → ⊥
panelNonDetectionDoesNotCreateAbsence ()

occurrenceDoesNotCreateInhaledToxicDose : ResidueOccurrenceCreatesInhaledToxicDose → ⊥
occurrenceDoesNotCreateInhaledToxicDose ()

tradeNameSimilarityDoesNotCreateMoleculeIdentity : TradeNameSimilarityCreatesMoleculeIdentity → ⊥
tradeNameSimilarityDoesNotCreateMoleculeIdentity ()

genericPanelDoesNotCreateGlyphosateCoverage : GenericMultiresiduePanelCreatesGlyphosateCoverage → ⊥
genericPanelDoesNotCreateGlyphosateCoverage ()

record CommonResiduePanelBoundary : Set where
  constructor common-residue-panel-boundary
  field
    panelCoverageComplete : Bool
    glyphosateCoveragePaid : Bool
    brandOrTypoCreatesMolecule : Bool
    occurrenceCreatesInhaledToxicDose : Bool
    licensedAndIllegalMarketsSeparated : Bool
    analyteSpecificLOQRequired : Bool
open CommonResiduePanelBoundary public

canonicalCommonResiduePanelBoundary : CommonResiduePanelBoundary
canonicalCommonResiduePanelBoundary =
  common-residue-panel-boundary false false false false true true

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data ResidueParetoTarget : Set where
  completeRegistryCoordinates : ResidueParetoTarget
  recoverPanelAnalyteLists : ResidueParetoTarget
  dedicatedGlyphosateCannabisMethod : ResidueParetoTarget
  licensedMarketReplication : ResidueParetoTarget
  combustionTransfer : ResidueParetoTarget
  vaporisationTransfer : ResidueParetoTarget
  routeDoseToxicology : ResidueParetoTarget

record ResidueParetoStep : Set where
  constructor residue-pareto-step
  field
    priority : Nat
    target : ResidueParetoTarget
    action : String
    pays : String
open ResidueParetoStep public

pareto0 : ResidueParetoStep
pareto0 = residue-pareto-step
  0 completeRegistryCoordinates
  "finish PubChem identity for every high-prevalence residue, including bifenazate and remaining 2026 table analytes"
  "molecule identity closure"

pareto1 : ResidueParetoStep
pareto1 = residue-pareto-step
  1 recoverPanelAnalyteLists
  "compare exact 2023/2026 Health Canada analyte lists against California, Canadian mandatory, Australian TGO 93/Ph. Eur. and ASTM cannabis panels"
  "observable-coverage map and unobserved-analyte residual"

pareto2 : ResidueParetoStep
pareto2 = residue-pareto-step
  2 dedicatedGlyphosateCannabisMethod
  "locate a validated cannabis-matrix glyphosate plus AMPA method or direct occurrence study; do not infer coverage from generic QuEChERS panels"
  "glyphosate-specific observation admission"

pareto3 : ResidueParetoStep
pareto3 = residue-pareto-step
  3 licensedMarketReplication
  "replicate common residues in licensed-market surveys before calling them common in regulated cannabis"
  "market-specific prevalence"

pareto4 : ResidueParetoStep
pareto4 = residue-pareto-step
  4 combustionTransfer
  "bind measured flower concentration to analyte-specific smoke transfer/degradation products"
  "smoking exposure bridge"

pareto5 : ResidueParetoStep
pareto5 = residue-pareto-step
  5 vaporisationTransfer
  "measure vaporisation transfer independently from combustion"
  "vapor exposure bridge"

pareto9 : ResidueParetoStep
pareto9 = residue-pareto-step
  9 routeDoseToxicology
  "compare absorbed route-specific dose with toxicological thresholds only after transfer and dose are paid"
  "bounded toxicology conclusion"

------------------------------------------------------------------------
-- Temporal owner: panel expansion refines observability but does not rewrite
-- earlier negative tests as evidence that newly added analytes were absent.
------------------------------------------------------------------------

data PanelTime : Set where
  legacyFinitePanels : PanelTime
  gagnon2023Expanded327 : PanelTime
  fiering2026BroadSurveillance : PanelTime
  currentDashi : PanelTime

data PanelInterpretation : Set where
  finitePanelLeavesBlindSpots : PanelInterpretation
  commonIllegalResiduesObserved : PanelInterpretation
  glyphosateCannabisOccurrenceKnown : PanelInterpretation
  inhaledToxicDoseKnown : PanelInterpretation

data PanelSummary : Set where coverageIsAnalyteIndexed : PanelSummary

PanelCompatible : PanelTime → PanelInterpretation → Set
PanelCompatible legacyFinitePanels finitePanelLeavesBlindSpots = ⊤
PanelCompatible legacyFinitePanels commonIllegalResiduesObserved = ⊥
PanelCompatible legacyFinitePanels glyphosateCannabisOccurrenceKnown = ⊥
PanelCompatible legacyFinitePanels inhaledToxicDoseKnown = ⊥
PanelCompatible gagnon2023Expanded327 finitePanelLeavesBlindSpots = ⊤
PanelCompatible gagnon2023Expanded327 commonIllegalResiduesObserved = ⊤
PanelCompatible gagnon2023Expanded327 glyphosateCannabisOccurrenceKnown = ⊥
PanelCompatible gagnon2023Expanded327 inhaledToxicDoseKnown = ⊥
PanelCompatible fiering2026BroadSurveillance finitePanelLeavesBlindSpots = ⊤
PanelCompatible fiering2026BroadSurveillance commonIllegalResiduesObserved = ⊤
PanelCompatible fiering2026BroadSurveillance glyphosateCannabisOccurrenceKnown = ⊥
PanelCompatible fiering2026BroadSurveillance inhaledToxicDoseKnown = ⊥
PanelCompatible currentDashi finitePanelLeavesBlindSpots = ⊤
PanelCompatible currentDashi commonIllegalResiduesObserved = ⊤
PanelCompatible currentDashi glyphosateCannabisOccurrenceKnown = ⊥
PanelCompatible currentDashi inhaledToxicDoseKnown = ⊥

panelTemporalSystem : Temporal.TemporalEvidenceSystem
panelTemporalSystem = record
  { Time = PanelTime
  ; Interpretation = PanelInterpretation
  ; Compatible = PanelCompatible
  ; Summary = PanelSummary
  ; summarize = λ _ → coverageIsAnalyteIndexed
  ; timeReference = λ
      { legacyFinitePanels → "finite cannabis contaminant panels before expanded Health Canada surveillance"
      ; gagnon2023Expanded327 → "Gagnon et al. 2023 DOI 10.1186/s42238-023-00200-0"
      ; fiering2026BroadSurveillance → "Fiering et al. 2026 DOI 10.1186/s42238-026-00414-y"
      ; currentDashi → "current common-residue coverage frontier"
      }
  }

currentCoverageFibre : Temporal.EvidenceFibre panelTemporalSystem currentDashi
currentCoverageFibre = Temporal.liveInterpretationAt finitePanelLeavesBlindSpots tt
