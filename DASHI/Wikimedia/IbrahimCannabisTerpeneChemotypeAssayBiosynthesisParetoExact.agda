module DASHI.Wikimedia.IbrahimCannabisTerpeneChemotypeAssayBiosynthesisParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTerpeneEntourageMoleculeCrossPollinationExact as Entourage
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- CANNABIS TERPENE CHEMOTYPE / ASSAY / BIOSYNTHESIS PARETO BRIDGE
--
-- Molecule identity is followed downward into an exact analytical sample and
-- upward into plant biosynthesis.  Chemotype labels are not treated as fixed
-- terpene profiles, and terpene-synthase capability is not treated as measured
-- product composition.
------------------------------------------------------------------------

data CompositionSourceRole : Set where
  longitudinalChemotypeAssay
  cannabisTerpeneSynthasePrimary
  terpeneVariationPrimary : CompositionSourceRole

record CompositionSource : Set where
  constructor composition-source
  field
    authors : String
    title : String
    publication : String
    year : Nat
    doi : String
    directLink : String
    role : CompositionSourceRole
    boundedReading : String
    excludedPromotion : String
open CompositionSource public

aizpuruaOlaizola2016 : CompositionSource
aizpuruaOlaizola2016 = composition-source
  "Oier Aizpurua-Olaizola; Umut Soydaner; Ekin Ozturk; Daniele Schibano; Yilmaz Simsir; Patricia Navarro; Nestor Etxebarria; Aresatz Usobiaga"
  "Evolution of the Cannabinoid and Terpene Content during the Growth of Cannabis sativa Plants from Different Chemotypes"
  "Journal of Natural Products 79(2):324-331"
  2016 "10.1021/acs.jnatprod.5b00949"
  "https://doi.org/10.1021/acs.jnatprod.5b00949"
  longitudinalChemotypeAssay
  "Primary controlled-growth analytical study: seven mother plants spanning chemotypes I-III, fifty clones per mother, weekly destructive sampling, leaves and flowers separated; eight major cannabinoids by HPLC-DAD and 28 terpenes quantified by GC-FID with GC-MS verification. Terpene trajectories differed among chemotypes and through growth."
  "Does not establish a universal strain label -> terpene profile, a consumer product batch composition, an entourage mechanism, or clinical effect."

boothPageBohlmann2017 : CompositionSource
boothPageBohlmann2017 = composition-source
  "Judith K. Booth; Jonathan E. Page; Jorg Bohlmann"
  "Terpene synthases from Cannabis sativa"
  "PLOS ONE 12(3):e0173911"
  2017 "10.1371/journal.pone.0173911"
  "https://doi.org/10.1371/journal.pone.0173911"
  cannabisTerpeneSynthasePrimary
  "Primary Cannabis terpene-synthase/transcriptome source connecting glandular-trichome terpene biosynthesis to identified CsTPS gene/enzyme family members."
  "A synthase gene or enzyme does not by itself determine abundance in an arbitrary plant, flower, extract or commercial product."

boothYuenEtAl2020 : CompositionSource
boothYuenEtAl2020 = composition-source
  "Judith K. Booth; Macaire M. S. Yuen; Sharon Jancsik; Lufiani L. Madilao; Jonathan E. Page; Jorg Bohlmann"
  "Terpene Synthases and Terpene Variation in Cannabis sativa"
  "Plant Physiology 184(1):130-147"
  2020 "10.1104/pp.20.00593"
  "https://doi.org/10.1104/pp.20.00593"
  terpeneVariationPrimary
  "Primary Cannabis terpene-synthase/variation source retained as a later plant-genetics and chemistry coordinate."
  "Variation source does not turn cultivar names into exact batch chemistry and does not establish pharmacological synergy."

------------------------------------------------------------------------
-- Same-object plant/sample assay carrier.
------------------------------------------------------------------------

record ChemotypeAssayReceipt : Set where
  constructor chemotype-assay-receipt
  field
    plantIdentityReference : String
    motherPlantReference : String
    cloneReference : String
    chemotypeDefinitionReference : String
    tissueReference : String
    growthTimeReference : String
    harvestDryingReference : String
    extractionReference : String
    cannabinoidMethodReference : String
    terpeneQuantificationMethodReference : String
    terpeneIdentityVerificationReference : String
    calibrationReference : String
    molecule : Entourage.TerpeneMolecule
    concentrationReference : String
    concentrationUnitReference : String
    assayUncertaintyReference : String
    sameObjectPlantPaid : Bool
    sameObjectSamplePaid : Bool
    quantitativeMoleculePaid : Bool
open ChemotypeAssayReceipt public

------------------------------------------------------------------------
-- Biosynthetic identity is distinct from abundance.
------------------------------------------------------------------------

record TerpeneSynthaseReceipt : Set where
  constructor terpene-synthase-receipt
  field
    plantReference : String
    tissueOrTrichomeReference : String
    geneOrTranscriptReference : String
    enzymeReference : String
    substrateReference : String
    productMolecule : Entourage.TerpeneMolecule
    productIdentityReference : String
    functionalAssayReference : String
    sequenceAccessionReference : String
    sourceReference : String
    geneIdentityPaid : Bool
    enzymeFunctionPaid : Bool
    productIdentityPaid : Bool
    productAbundancePaid : Bool
open TerpeneSynthaseReceipt public

------------------------------------------------------------------------
-- Ibrahim/xlink continuation.  Source-paid semantic/dependency edges are
-- separate from historical Wikipedia first-link edges.
------------------------------------------------------------------------

data CannabisCompositionXLinkRole : Set where
  plantToAssay
  assayToMolecule
  plantToTrichomeBiosynthesis
  biosynthesisToMolecule
  moleculeToEntourageTest : CannabisCompositionXLinkRole

record CannabisCompositionXLink : Set where
  constructor cannabis-composition-xlink
  field
    fromReference : String
    toReference : String
    role : CannabisCompositionXLinkRole
    sourceDOI : String
    sourceLink : String
    sameObjectRequired : Bool
    historicalIbrahimFirstLinkPaid : Bool
    dependencyOrSemanticXLinkPaid : Bool
open CannabisCompositionXLink public

cannabisToAssayXLink : CannabisCompositionXLink
cannabisToAssayXLink = cannabis-composition-xlink
  "Cannabis sativa Q26726"
  "longitudinal chemotype cannabinoid/terpene assay"
  plantToAssay
  "10.1021/acs.jnatprod.5b00949"
  "https://doi.org/10.1021/acs.jnatprod.5b00949"
  true false true

assayToTerpeneMoleculeXLink : CannabisCompositionXLink
assayToTerpeneMoleculeXLink = cannabis-composition-xlink
  "same-object GC-FID/GC-MS sample result"
  "stereochemistry-aware terpene molecule coordinate"
  assayToMolecule
  "10.1021/acs.jnatprod.5b00949"
  "https://doi.org/10.1021/acs.jnatprod.5b00949"
  true false true

cannabisToSynthaseXLink : CannabisCompositionXLink
cannabisToSynthaseXLink = cannabis-composition-xlink
  "Cannabis sativa glandular-trichome biosynthesis"
  "CsTPS terpene synthase family"
  plantToTrichomeBiosynthesis
  "10.1371/journal.pone.0173911"
  "https://doi.org/10.1371/journal.pone.0173911"
  true false true

synthaseToMoleculeXLink : CannabisCompositionXLink
synthaseToMoleculeXLink = cannabis-composition-xlink
  "functionally identified Cannabis terpene synthase"
  "specific terpene molecular product"
  biosynthesisToMolecule
  "10.1371/journal.pone.0173911"
  "https://doi.org/10.1371/journal.pone.0173911"
  true false true

moleculeToEntourageTestXLink : CannabisCompositionXLink
moleculeToEntourageTestXLink = cannabis-composition-xlink
  "quantitatively identified terpene in exact Cannabis sample"
  "pairwise concentration- and endpoint-indexed interaction test"
  moleculeToEntourageTest
  "10.3389/fphar.2020.00359"
  "https://doi.org/10.3389/fphar.2020.00359"
  true false true

------------------------------------------------------------------------
-- Pareto frontier.
------------------------------------------------------------------------

data CompositionTarget : Set where
  exactBatchAssay
  stereochemicalClosure
  synthaseProductClosure
  longitudinalTrajectory
  pairwiseInteraction
  historicalWikipediaReplay : CompositionTarget

record CompositionParetoStep : Set where
  constructor composition-pareto-step
  field
    priority : Nat
    target : CompositionTarget
    action : String
    pays : String
    dominatedUntil : String
open CompositionParetoStep public

firstCompositionTarget : CompositionParetoStep
firstCompositionTarget = composition-pareto-step
  0 exactBatchAssay
  "acquire one exact sample/batch assay with quantitative terpene identities, units, calibration and sample custody"
  "same-object composition; highest information gain for every downstream pharmacology question"
  "none"

secondCompositionTarget : CompositionParetoStep
secondCompositionTarget = composition-pareto-step
  1 stereochemicalClosure
  "resolve enantiomer/stereoisomer identity where the analytical method supports it; otherwise retain group-level identity explicitly"
  "prevents limonene/pinene/linalool/caryophyllene stereochemistry from being silently collapsed"
  "requires an assay capable of the claimed stereochemical discrimination"

thirdCompositionTarget : CompositionParetoStep
thirdCompositionTarget = composition-pareto-step
  2 synthaseProductClosure
  "join identified CsTPS gene/enzyme products to molecule coordinates only where functional source receipts pay the product"
  "biosynthesis dependency without inventing abundance"
  "gene/transcript presence alone is insufficient"

fourthCompositionTarget : CompositionParetoStep
fourthCompositionTarget = composition-pareto-step
  3 longitudinalTrajectory
  "retain terpene concentration as a fibre over growth, tissue, harvest and processing time rather than a strain scalar"
  "time-indexed chemical phenotype"
  "same-object repeated/scheduled assay coordinates required"

fifthCompositionTarget : CompositionParetoStep
fifthCompositionTarget = composition-pareto-step
  4 pairwiseInteraction
  "use exact measured composition to select physiologically relevant molecule pairs/concentrations for interaction tests"
  "mechanism-specific entourage discriminator"
  "dominated until composition is paid"

historicalCompositionTarget : CompositionParetoStep
historicalCompositionTarget = composition-pareto-step
  6 historicalWikipediaReplay
  "replay any proposed Cannabis/terpene first-link relation through the existing Ibrahim 2014 dump/parser archaeology before promoting it as historical FLN state"
  "historical traversal coordinate only"
  "source xlinks and current QIDs do not identify historical Wikipedia first-link output"

------------------------------------------------------------------------
-- Time-indexed composition interpretation.
------------------------------------------------------------------------

data CompositionTime : Set where
  source2016
  synthase2017
  variation2020
  currentDashi : CompositionTime

data CompositionInterpretation : Set where
  terpeneProfilesVaryWithChemotypeAndGrowth
  synthaseIdentityCanConstrainProductCandidate
  cultivarNameDeterminesExactProfile
  exactBatchStillNeedsAssay : CompositionInterpretation

data CompositionSummary : Set where
  compositionIsSituatedAndTimeIndexed : CompositionSummary

CompositionCompatible : CompositionTime → CompositionInterpretation → Set
CompositionCompatible source2016 terpeneProfilesVaryWithChemotypeAndGrowth = ⊤
CompositionCompatible source2016 synthaseIdentityCanConstrainProductCandidate = ⊥
CompositionCompatible source2016 cultivarNameDeterminesExactProfile = ⊥
CompositionCompatible source2016 exactBatchStillNeedsAssay = ⊤
CompositionCompatible synthase2017 terpeneProfilesVaryWithChemotypeAndGrowth = ⊤
CompositionCompatible synthase2017 synthaseIdentityCanConstrainProductCandidate = ⊤
CompositionCompatible synthase2017 cultivarNameDeterminesExactProfile = ⊥
CompositionCompatible synthase2017 exactBatchStillNeedsAssay = ⊤
CompositionCompatible variation2020 terpeneProfilesVaryWithChemotypeAndGrowth = ⊤
CompositionCompatible variation2020 synthaseIdentityCanConstrainProductCandidate = ⊤
CompositionCompatible variation2020 cultivarNameDeterminesExactProfile = ⊥
CompositionCompatible variation2020 exactBatchStillNeedsAssay = ⊤
CompositionCompatible currentDashi terpeneProfilesVaryWithChemotypeAndGrowth = ⊤
CompositionCompatible currentDashi synthaseIdentityCanConstrainProductCandidate = ⊤
CompositionCompatible currentDashi cultivarNameDeterminesExactProfile = ⊥
CompositionCompatible currentDashi exactBatchStillNeedsAssay = ⊤

compositionTemporalSystem : Temporal.TemporalEvidenceSystem
compositionTemporalSystem = record
  { Time = CompositionTime
  ; Interpretation = CompositionInterpretation
  ; Compatible = CompositionCompatible
  ; Summary = CompositionSummary
  ; summarize = λ _ → compositionIsSituatedAndTimeIndexed
  ; timeReference = λ
      { source2016 → "Aizpurua-Olaizola et al. 2016, DOI 10.1021/acs.jnatprod.5b00949"
      ; synthase2017 → "Booth, Page, Bohlmann 2017, DOI 10.1371/journal.pone.0173911"
      ; variation2020 → "Booth et al. 2020, DOI 10.1104/pp.20.00593"
      ; currentDashi → "current DASHI cannabis-terpene molecule/composition frontier"
      }
  }

currentBatchAssayStillRequired : Temporal.EvidenceFibre compositionTemporalSystem currentDashi
currentBatchAssayStillRequired = Temporal.liveInterpretationAt exactBatchStillNeedsAssay tt

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ChemotypeCreatesExactBatchProfile : Set where
data SynthaseCreatesProductAbundance : Set where
data GenePresenceCreatesEnzymeActivity : Set where
data AssayCoOccurrenceCreatesEntourage : Set where
data CultivarNameCreatesStereochemistry : Set where
data SourceXLinkCreatesHistoricalFirstLink : Set where

chemotypeDoesNotCreateExactBatchProfile : ChemotypeCreatesExactBatchProfile → ⊥
chemotypeDoesNotCreateExactBatchProfile ()

synthaseDoesNotCreateProductAbundance : SynthaseCreatesProductAbundance → ⊥
synthaseDoesNotCreateProductAbundance ()

genePresenceDoesNotCreateEnzymeActivity : GenePresenceCreatesEnzymeActivity → ⊥
genePresenceDoesNotCreateEnzymeActivity ()

assayCoOccurrenceDoesNotCreateEntourage : AssayCoOccurrenceCreatesEntourage → ⊥
assayCoOccurrenceDoesNotCreateEntourage ()

cultivarNameDoesNotCreateStereochemistry : CultivarNameCreatesStereochemistry → ⊥
cultivarNameDoesNotCreateStereochemistry ()

sourceXLinkDoesNotCreateHistoricalFirstLink : SourceXLinkCreatesHistoricalFirstLink → ⊥
sourceXLinkDoesNotCreateHistoricalFirstLink ()

record CannabisTerpeneCompositionBoundary : Set where
  constructor cannabis-terpene-composition-boundary
  field
    parentMoleculeEntourageOwnerReused : Bool
    primaryAssaySourceRetained : Bool
    primarySynthaseSourceRetained : Bool
    compositionIsSampleIndexed : Bool
    compositionIsTimeIndexed : Bool
    stereochemistryRemainsExplicit : Bool
    synthaseAndAbundanceRemainDistinct : Bool
    currentXlinksRemainNonHistorical : Bool
    assayCreatesEntourageMechanism : Bool
open CannabisTerpeneCompositionBoundary public

canonicalCannabisTerpeneCompositionBoundary : CannabisTerpeneCompositionBoundary
canonicalCannabisTerpeneCompositionBoundary =
  cannabis-terpene-composition-boundary
    true true true true true true true true false
