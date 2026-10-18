module DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisCommonResiduePanelParetoExact as Residues
import DASHI.Wikimedia.IbrahimCannabisBtBiopesticideExposureParetoExact as Bt
import DASHI.Wikimedia.IbrahimCannabisContaminantToxicantAssayParetoExact as Toxicants
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- CANNABIS CONTAMINANT MEASUREMENT ARCHITECTURE / PANEL PARETO OWNER
--
-- A compliance panel is a family of observers, not the contaminant universe.
-- This owner factors the contaminant problem by analyte class and observer
-- modality before any downstream toxicity conclusion.
------------------------------------------------------------------------

data ContaminantCarrierClass : Set where
  ordinarySmallMoleculeResidue : ContaminantCarrierClass
  polarIonicResidue : ContaminantCarrierClass
  elementalContaminant : ContaminantCarrierClass
  viableMicroorganism : ContaminantCarrierClass
  microbialProteinOrBiopesticide : ContaminantCarrierClass
  mycotoxin : ContaminantCarrierClass
  residualSolventOrProcessingChemical : ContaminantCarrierClass
  foreignMatterOrPhysicalContaminant : ContaminantCarrierClass

data ObserverModality : Set where
  gcMsMs : ObserverModality
  lcMsMs : ObserverModality
  dedicatedPolarLcMsMs : ObserverModality
  icpMs : ObserverModality
  cultureCount : ObserverModality
  targetedPCRorQPCR : ObserverModality
  immunoassayOrProteomics : ObserverModality
  mycotoxinLcMsOrPharmacopoeial : ObserverModality
  headspaceGc : ObserverModality
  microscopyOrPhysicalInspection : ObserverModality

record ObserverCoverageReceipt : Set where
  constructor observer-coverage-receipt
  field
    carrierClass : ContaminantCarrierClass
    modality : ObserverModality
    sourceReference : String
    targetMatrixReference : String
    validatedForCannabis : Bool
    exactAnalyteListPaid : Bool
    analyteSpecificLOQorLimitPaid : Bool
    nonDetectionCreatesAbsence : Bool
open ObserverCoverageReceipt public

canadaPesticideObserver : ObserverCoverageReceipt
canadaPesticideObserver = observer-coverage-receipt
  ordinarySmallMoleculeResidue lcMsMs
  "Health Canada Mandatory cannabis testing for pesticide active ingredients: required list plus laboratory LoQ for every required active ingredient"
  "fresh/dried cannabis and cannabis used for derived cannabis products"
  true true true false

californiaChemicalResidueObserver : ObserverCoverageReceipt
californiaChemicalResidueObserver = observer-coverage-receipt
  ordinarySmallMoleculeResidue lcMsMs
  "California DCC requires residual pesticide testing for every batch; current action levels are regulation-defined and updated by rulemaking"
  "California cannabis goods"
  true true true false

australiaTgo93PesticideObserver : ObserverCoverageReceipt
australiaTgo93PesticideObserver = observer-coverage-receipt
  ordinarySmallMoleculeResidue lcMsMs
  "TGO 93 Schedule 1 requires pesticide compliance against Ph. Eur. 2.8.13 or an equivalent suitably validated method"
  "cannabis plant used to manufacture medicinal cannabis products"
  true false true false

glyphosateObserverResidual : ObserverCoverageReceipt
glyphosateObserverResidual = observer-coverage-receipt
  polarIonicResidue dedicatedPolarLcMsMs
  "glyphosate/AMPA commonly require dedicated derivatization or polar-analyte workflows; cannabis-specific inclusion remains an explicit coverage question"
  "cannabis flower"
  false false false false

metalObserver : ObserverCoverageReceipt
metalObserver = observer-coverage-receipt
  elementalContaminant icpMs
  "Health Canada survey used inhalation-appropriate elemental impurity criteria; TGO 93 specifies arsenic, cadmium, lead and mercury limits"
  "dried cannabis / medicinal cannabis plant material"
  true true true false

microbialObserver : ObserverCoverageReceipt
microbialObserver = observer-coverage-receipt
  viableMicroorganism cultureCount
  "Health Canada baseline survey measured TAMC, TYMC, bile-tolerant Gram-negative bacteria, E. coli, Salmonella and Aspergillus; California requires microbial impurity testing"
  "dried cannabis"
  true true true false

btCultureObserverResidual : ObserverCoverageReceipt
btCultureObserverResidual = observer-coverage-receipt
  viableMicroorganism cultureCount
  "generic microbial counts may observe viable Bacillus burden but do not identify a B. thuringiensis strain without a strain-specific join"
  "post-application cannabis flower"
  false false false false

btMolecularObserverResidual : ObserverCoverageReceipt
btMolecularObserverResidual = observer-coverage-receipt
  microbialProteinOrBiopesticide targetedPCRorQPCR
  "Bt strain or cry/vip-gene identity requires organism/molecular methods rather than ordinary pesticide residue LC/GC panels"
  "post-application cannabis flower"
  false false false false

btProteinObserverResidual : ObserverCoverageReceipt
btProteinObserverResidual = observer-coverage-receipt
  microbialProteinOrBiopesticide immunoassayOrProteomics
  "Cry/Vip protein residue requires protein-sensitive observation such as validated immunoassay or targeted proteomics"
  "post-application cannabis flower"
  false false false false

mycotoxinObserver : ObserverCoverageReceipt
mycotoxinObserver = observer-coverage-receipt
  mycotoxin mycotoxinLcMsOrPharmacopoeial
  "TGO 93 explicitly specifies aflatoxins and ochratoxin A; Health Canada survey additionally measured deoxynivalenol"
  "dried cannabis / medicinal cannabis plant material"
  true true true false

californiaSolventObserver : ObserverCoverageReceipt
californiaSolventObserver = observer-coverage-receipt
  residualSolventOrProcessingChemical headspaceGc
  "California DCC requires residual solvent and processing-chemical testing for cannabis goods"
  "processed cannabis goods"
  true true true false

australiaForeignMatterObserver : ObserverCoverageReceipt
australiaForeignMatterObserver = observer-coverage-receipt
  foreignMatterOrPhysicalContaminant microscopyOrPhysicalInspection
  "TGO 93 Schedule 1 specifies foreign matter and total ash for cannabis plant material"
  "cannabis plant used to manufacture medicinal cannabis products"
  true true true false

------------------------------------------------------------------------
-- Regulatory architecture packets.
------------------------------------------------------------------------

record RegulatoryPanelArchitecture : Set where
  constructor regulatory-panel-architecture
  field
    jurisdiction : String
    productScope : String
    requiredClassesReference : String
    routeSensitiveLimitsReference : String
    exactAnalyteUniverseReference : String
    panelIsCompleteContaminantUniverse : Bool
open RegulatoryPanelArchitecture public

canadaArchitecture : RegulatoryPanelArchitecture
canadaArchitecture = regulatory-panel-architecture
  "Canada"
  "licensed cannabis products, with route-appropriate contaminant limits"
  "mandatory pesticide active ingredient list plus microbial and chemical contaminant controls; Health Canada baseline survey additionally measured heavy metals, mycotoxins and microbial organisms"
  "Cannabis Regulations require tolerances appropriate to intended and reasonably foreseeable use; Health Canada explicitly distinguishes inhaled heavy-metal limits from oral herbal-drug limits"
  "pesticide list/LoQs are explicit and periodically revised; wider contaminant universe is not claimed exhausted"
  false

californiaArchitecture : RegulatoryPanelArchitecture
californiaArchitecture = regulatory-panel-architecture
  "California"
  "each batch of cannabis goods before sale"
  "cannabinoids/terpenes, residual solvents/processing chemicals, residual pesticides, heavy metals, microbial impurities, mycotoxins, moisture/water activity and foreign material"
  "action levels are matrix/product-class and regulation specific"
  "finite regulation-defined analyte/action-level panel"
  false

australiaArchitecture : RegulatoryPanelArchitecture
australiaArchitecture = regulatory-panel-architecture
  "Australia"
  "medicinal cannabis plant material and products under TGO 93/TGO 100/GMP"
  "Schedule 1: aflatoxins, ochratoxin A, foreign matter, heavy metals, pesticides and total ash; microbiological requirements are separately specified"
  "TGA permits equivalent validated methods and states additional tests may be warranted; every batch must comply even when justified reduced/rotational testing is used"
  "Pharmacopoeial parameter set is not asserted to enumerate every possible contaminant"
  false

------------------------------------------------------------------------
-- Coverage defects / non-factorability firewalls.
------------------------------------------------------------------------

data ChemicalPanelSeesBtProtein : Set where
data MicrobialCountIdentifiesBtStrain : Set where
data PesticideListExhaustsContaminantUniverse : Set where
data NegativePanelCreatesUniversalCleanliness : Set where
data OralLimitCreatesInhalationSafety : Set where

chemicalPanelDoesNotSeeBtProtein : ChemicalPanelSeesBtProtein → ⊥
chemicalPanelDoesNotSeeBtProtein ()

microbialCountDoesNotIdentifyBtStrain : MicrobialCountIdentifiesBtStrain → ⊥
microbialCountDoesNotIdentifyBtStrain ()

pesticideListDoesNotExhaustContaminantUniverse : PesticideListExhaustsContaminantUniverse → ⊥
pesticideListDoesNotExhaustContaminantUniverse ()

negativePanelDoesNotCreateUniversalCleanliness : NegativePanelCreatesUniversalCleanliness → ⊥
negativePanelDoesNotCreateUniversalCleanliness ()

oralLimitDoesNotCreateInhalationSafety : OralLimitCreatesInhalationSafety → ⊥
oralLimitDoesNotCreateInhalationSafety ()

------------------------------------------------------------------------
-- Cross-class Pareto: choose next observer by uncovered consumer-sensitive
-- class, not by simply adding more names to the existing LC/GC pesticide list.
------------------------------------------------------------------------

data MeasurementParetoTarget : Set where
  closeBtObserverGap : MeasurementParetoTarget
  closeGlyphosateObserverGap : MeasurementParetoTarget
  compareJurisdictionPanelUniverses : MeasurementParetoTarget
  acquireCannabisSpecificBtResidue : MeasurementParetoTarget
  acquireCannabisSpecificGlyphosateOccurrence : MeasurementParetoTarget
  routeSpecificThermalTransfer : MeasurementParetoTarget
  broaderSmallMoleculeListExpansion : MeasurementParetoTarget

record MeasurementParetoStep : Set where
  constructor measurement-pareto-step
  field
    priority : Nat
    target : MeasurementParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open MeasurementParetoStep public

pareto0 : MeasurementParetoStep
pareto0 = measurement-pareto-step
  0 closeBtObserverGap
  "identify an exact cannabis-relevant Bt formulation, then specify strain/spore and Cry/Vip protein observers separately"
  "biopesticide observability rather than small-molecule-panel false negatives"
  "none"

pareto1 : MeasurementParetoStep
pareto1 = measurement-pareto-step
  1 closeGlyphosateObserverGap
  "determine whether each jurisdiction/lab panel includes glyphosate and AMPA with a cannabis-validated method and LOQ"
  "polar-herbicide observability"
  "none"

pareto2 : MeasurementParetoStep
pareto2 = measurement-pareto-step
  2 compareJurisdictionPanelUniverses
  "normalize Canada, California and Australia into carrier-class × observer-modality × analyte/limit coverage"
  "actual blacklist/whitelist measurement coverage rather than slogan-level comparison"
  "Bt/glyphosate observer distinctions should be retained"

pareto3 : MeasurementParetoStep
pareto3 = measurement-pareto-step
  3 acquireCannabisSpecificBtResidue
  "find post-application cannabis flower data for viable Bt, strain identity and/or Cry/Vip protein residue"
  "empirical cannabis-specific biological-residue packet"
  "observer definition required first"

pareto4 : MeasurementParetoStep
pareto4 = measurement-pareto-step
  4 acquireCannabisSpecificGlyphosateOccurrence
  "find cannabis/hemp flower glyphosate plus AMPA data with validated matrix and LOQ"
  "empirical polar-herbicide occurrence packet"
  "coverage definition required first"

pareto5 : MeasurementParetoStep
pareto5 = measurement-pareto-step
  5 routeSpecificThermalTransfer
  "only after source residue is measured, quantify combustion and vaporisation transfer/degradation independently by contaminant class"
  "consumer exposure admission"
  "source concentration and identity required"

pareto99 : MeasurementParetoStep
pareto99 = measurement-pareto-step
  99 broaderSmallMoleculeListExpansion
  "do not simply add more conventional pesticide names while entire carrier classes remain weakly observed"
  "low marginal information until modality gaps close"
  "dominated by cross-class observer gaps"

------------------------------------------------------------------------
-- Temporal fibre.
------------------------------------------------------------------------

data MeasurementTime : Set where
  chemicalPanelEra : MeasurementTime
  crossClassReview : MeasurementTime
  currentArchitecture : MeasurementTime

data MeasurementInterpretation : Set where
  finitePanelOnly : MeasurementInterpretation
  crossClassObserverRequired : MeasurementInterpretation
  everyRelevantClassObserved : MeasurementInterpretation

data MeasurementSummary : Set where panelCoverageIsObserverIndexed : MeasurementSummary

MeasurementCompatible : MeasurementTime → MeasurementInterpretation → Set
MeasurementCompatible chemicalPanelEra finitePanelOnly = ⊤
MeasurementCompatible chemicalPanelEra crossClassObserverRequired = ⊥
MeasurementCompatible chemicalPanelEra everyRelevantClassObserved = ⊥
MeasurementCompatible crossClassReview finitePanelOnly = ⊤
MeasurementCompatible crossClassReview crossClassObserverRequired = ⊤
MeasurementCompatible crossClassReview everyRelevantClassObserved = ⊥
MeasurementCompatible currentArchitecture finitePanelOnly = ⊤
MeasurementCompatible currentArchitecture crossClassObserverRequired = ⊤
MeasurementCompatible currentArchitecture everyRelevantClassObserved = ⊥

measurementTemporalSystem : Temporal.TemporalEvidenceSystem
measurementTemporalSystem = record
  { Time = MeasurementTime
  ; Interpretation = MeasurementInterpretation
  ; Compatible = MeasurementCompatible
  ; Summary = MeasurementSummary
  ; summarize = λ _ → panelCoverageIsObserverIndexed
  ; timeReference = λ
      { chemicalPanelEra → "conventional small-molecule residue-panel abstraction"
      ; crossClassReview → "Bt/glyphosate/metals/microbes/mycotoxins expose modality-specific observer requirements"
      ; currentArchitecture → "current DASHI cross-class measurement Pareto frontier"
      }
  }

currentMeasurementResidual : Temporal.EvidenceFibre measurementTemporalSystem currentArchitecture
currentMeasurementResidual = Temporal.liveInterpretationAt crossClassObserverRequired tt

record CannabisMeasurementArchitectureBoundary : Set where
  constructor cannabis-measurement-architecture-boundary
  field
    contaminantUniverseExceedsPesticideList : Bool
    modalityDependsOnCarrierClass : Bool
    btNeedsBiologicalOrProteinObserver : Bool
    glyphosateMayNeedDedicatedPolarMethod : Bool
    routeAppropriateLimitsRequired : Bool
    negativePanelMeansUniversallyClean : Bool
open CannabisMeasurementArchitectureBoundary public

canonicalCannabisMeasurementArchitectureBoundary : CannabisMeasurementArchitectureBoundary
canonicalCannabisMeasurementArchitectureBoundary =
  cannabis-measurement-architecture-boundary true true true true true false
