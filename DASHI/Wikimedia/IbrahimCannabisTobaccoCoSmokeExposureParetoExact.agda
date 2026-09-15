module DASHI.Wikimedia.IbrahimCannabisTobaccoCoSmokeExposureParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisThermalTransferEvidenceGradeExact as CannabisThermal
import DASHI.Wikimedia.IbrahimCannabisMeasurementArchitectureParetoExact as Measurement
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- CANNABIS + TOBACCO CO-SMOKE EXPOSURE OWNER
--
-- A spliff/mulled cigarette is not cannabis smoke plus a harmless diluent.
-- It is a mixed source whose tobacco fraction contributes its own pesticide
-- residue vector, tobacco-specific harmful constituents and combustion
-- products.  Regulatory testing of tobacco differs materially from current
-- cannabis contaminant-panel architectures.
------------------------------------------------------------------------

data SmokeSource : Set where cannabis tobacco mixedCannabisTobacco : SmokeSource

data RegulatoryTestingMode : Set where
  statutoryResidueTolerance
  constituentReporting
  productApplicationAnalytics
  batchMultiresiduePanel
  ignitionPerformanceOnly
  ingredientReporting : RegulatoryTestingMode

record TobaccoRegulatoryReceipt : Set where
  constructor tobacco-regulatory-receipt
  field
    jurisdiction : String
    sourceReference : String
    pesticideRuleReference : String
    routineRetailBatchPesticidePanelReference : String
    constituentTestingReference : String
    pesticideTolerancePaid : Bool
    routineBatchMultiresiduePanelPaid : Bool
    smokeConstituentTestingAuthorityPaid : Bool
open TobaccoRegulatoryReceipt public

usTobaccoReceipt : TobaccoRegulatoryReceipt
usTobaccoReceipt = tobacco-regulatory-receipt
  "United States"
  "FD&C Act tobacco authorities administered by FDA"
  "Section 907 prohibits manufacturers from using tobacco with pesticide chemical residues above any applicable federal tolerance for domestically grown tobacco"
  "no cannabis-style routine batch-by-batch multiresidue retail compliance panel located in current FDA tobacco rules searched for this tranche"
  "Sections 915 and FDA HPHC framework authorize/require testing and reporting of selected tobacco-product and smoke constituents; FDA Tobacco Products Laboratory supports LC-MS/MS, GC-MS and smoking-machine analysis"
  true false true

australiaTobaccoReceipt : TobaccoRegulatoryReceipt
australiaTobaccoReceipt = tobacco-regulatory-receipt
  "Australia"
  "Public Health (Tobacco and Other Products) Act 2023 and Regulations 2024"
  "no tobacco-specific pesticide-residue batch panel located in current federal tobacco-product testing provisions searched for this tranche"
  "current Regulations section 126 prescribes cigarette testing under AS 4830-2007 for reduced ignition propensity; annual reporting covers product ingredients/volumes"
  "Act section 131 requires annual reporting of manufacturing ingredients, not a cannabis-style pesticide residue certificate for every retail batch"
  false false false

------------------------------------------------------------------------
-- Empirical tobacco pesticide transfer.
------------------------------------------------------------------------

record TobaccoPesticideSmokeStudy : Set where
  constructor tobacco-pesticide-smoke-study
  field
    citation : String
    analyteScope : String
    tobaccoObservation : String
    smokeObservation : String
    transferRange : String
    exactCannabisTobaccoMixtureStudied : Bool
open TobaccoPesticideSmokeStudy public

tobaccoTransfer2021 : TobaccoPesticideSmokeStudy
tobaccoTransfer2021 = tobacco-pesticide-smoke-study
  "Determination of Commonly Used Multiclass Pesticide Residues in Tobacco and Cigarette Smoke by UPLC-MS/MS, 2021"
  "16 commonly used tobacco pesticides"
  "51 commercial cigarettes with one or more pesticide residues plus spiked tobacco experiments"
  "mainstream smoke particulate collected on Cambridge filter pads under ISO smoking"
  "observed tobacco-to-smoke transfer 0.0-26.1% for residues in commercial cigarettes; artificial-spike experiments 0.0-56.5%"
  false

tobaccoRisk2020 : TobaccoPesticideSmokeStudy
tobaccoRisk2020 = tobacco-pesticide-smoke-study
  "Pesticides residues in tobacco smoke: risk assessment study, 2020"
  "ten pesticide active ingredients observed in harvested tobacco"
  "pesticide residues detected in all analysed tobacco samples in the study"
  "study recovered pesticide residues from cigarette smoke and concluded active/passive smokers can be exposed"
  "analyte-specific; no universal transfer coefficient promoted here"
  false

------------------------------------------------------------------------
-- Co-use / spliff prevalence establishes the consumer object, not chemistry.
------------------------------------------------------------------------

record CoUseEvidence : Set where
  constructor co-use-evidence
  field
    citation : String
    boundedReading : String
    mixedProductExistencePaid : Bool
    mixedPesticideChemistryPaid : Bool
open CoUseEvidence public

spliffSystematicReview : CoUseEvidence
spliffSystematicReview = co-use-evidence
  "Marijuana and tobacco co-administration in blunts, spliffs, and mulled cigarettes: A systematic literature review, Addictive Behaviors 2017, DOI 10.1016/j.addbeh.2016.09.001"
  "Documents cannabis+tobacco co-administration as a common research object and reviews 45 studies; most studies concern behaviour rather than pesticide-residue chemistry"
  true false

spliffUsage2020 : CoUseEvidence
spliffUsage2020 = co-use-evidence
  "The Intersection between Spliff Usage, Tobacco Smoking, and Having the First Joint after Waking, Scientific Reports 2020, DOI 10.1038/s41598-020-64110-4"
  "Documents spliff/mulled cannabis+tobacco use behaviour; does not provide residue-transfer chemistry"
  true false

------------------------------------------------------------------------
-- Mixed-source exposure packet.
------------------------------------------------------------------------

record MixedSmokeExposurePacket : Set where
  constructor mixed-smoke-exposure-packet
  field
    cannabisMassReference : String
    tobaccoMassReference : String
    cannabisResidueVectorReference : String
    tobaccoResidueVectorReference : String
    cannabisSmokeTransferReference : String
    tobaccoSmokeTransferReference : String
    interactionReference : String
    inhalationTopographyReference : String
    cannabisResiduePaid : Bool
    tobaccoResiduePaid : Bool
    mixedCombustionInteractionPaid : Bool
    absorbedDosePaid : Bool
open MixedSmokeExposurePacket public

currentSpliffResidual : MixedSmokeExposurePacket
currentSpliffResidual = mixed-smoke-exposure-packet
  "unpaid: actual cannabis mass per mixed joint"
  "unpaid: actual tobacco mass per mixed joint"
  "partially paid only for selected cannabis contaminants from existing owners"
  "unpaid for the actual tobacco product used; tobacco literature proves residue occurrence/transfer generally, not this product"
  "direct cannabis smoke-transfer data exist for selected residues such as paclobutrazol"
  "tobacco cigarette studies show analyte- and method-dependent transfer into mainstream smoke"
  "unpaid: co-combustion may alter burn temperature, puffing, particle phase, and transfer; additive superposition is not assumed"
  "unpaid: puff volume, frequency, depth, breath hold, device/paper/filter characteristics"
  false false false false

------------------------------------------------------------------------
-- Formal source equation.
------------------------------------------------------------------------

mixedSourceEquation : String
mixedSourceEquation =
  "E_mixed is a function of cannabis mass/residue vector, tobacco mass/residue vector, source-specific thermal transfer, mixed-combustion interaction, device/paper/filter and inhalation topography; it is not determined by cannabis concentration alone"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TobaccoToleranceCreatesBatchTesting : Set where
data IngredientReportingCreatesResidueMeasurement : Set where
data TobaccoSmokeTransferCreatesCannabisTransfer : Set where
data SeparateTransferCreatesAdditiveMixedTransfer : Set where
data CannabisCleanCreatesSpliffClean : Set where

tobaccoToleranceDoesNotCreateBatchTesting : TobaccoToleranceCreatesBatchTesting → ⊥
tobaccoToleranceDoesNotCreateBatchTesting ()

ingredientReportingDoesNotCreateResidueMeasurement : IngredientReportingCreatesResidueMeasurement → ⊥
ingredientReportingDoesNotCreateResidueMeasurement ()

tobaccoSmokeTransferDoesNotCreateCannabisTransfer : TobaccoSmokeTransferCreatesCannabisTransfer → ⊥
tobaccoSmokeTransferDoesNotCreateCannabisTransfer ()

separateTransferDoesNotCreateAdditiveMixedTransfer : SeparateTransferCreatesAdditiveMixedTransfer → ⊥
separateTransferDoesNotCreateAdditiveMixedTransfer ()

cannabisCleanDoesNotCreateSpliffClean : CannabisCleanCreatesSpliffClean → ⊥
cannabisCleanDoesNotCreateSpliffClean ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data CoSmokeParetoTarget : Set where
  quantifyTobaccoRetailResidues
  identifySharedAnalytes
  controlledMixedCombustion
  comparePureCannabisPureTobaccoMixed
  includeHPHCBackground
  routeDoseModel
  broaderBehaviouralLiterature : CoSmokeParetoTarget

record CoSmokeParetoStep : Set where
  constructor co-smoke-pareto-step
  field
    priority : Nat
    target : CoSmokeParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open CoSmokeParetoStep public

pareto0 : CoSmokeParetoStep
pareto0 = co-smoke-pareto-step
  0 quantifyTobaccoRetailResidues
  "acquire modern US/Australian retail tobacco residue datasets with analyte lists, concentrations, LOQs and brand/product provenance"
  "tobacco-side source vector for realistic spliff exposure"
  "none"

pareto1 : CoSmokeParetoStep
pareto1 = co-smoke-pareto-step
  1 identifySharedAnalytes
  "intersect tobacco and cannabis residue universes to identify shared pesticides/PGRs and tobacco-only/cannabis-only coordinates"
  "joint analyte basis"
  "requires product-residue data"

pareto2 : CoSmokeParetoStep
pareto2 = co-smoke-pareto-step
  2 controlledMixedCombustion
  "run/search a controlled experiment with known cannabis:tobacco mass ratios and matched pure-source controls"
  "whether mixed transfer factors through source-wise additive transfer"
  "must not assume linearity"

pareto3 : CoSmokeParetoStep
pareto3 = co-smoke-pareto-step
  3 comparePureCannabisPureTobaccoMixed
  "compare parent residues and thermal products in pure cannabis, pure tobacco and mixed smoke under matched puffing"
  "interaction residual and route chemistry"
  "controlled mixed combustion required"

pareto4 : CoSmokeParetoStep
pareto4 = co-smoke-pareto-step
  4 includeHPHCBackground
  "add nicotine, tobacco-specific nitrosamines, PAHs and VOC background to pesticide-specific exposure without conflating these with pesticide residues"
  "total mixed-source toxicant context"
  "pesticide source vectors remain separate"

pareto5 : CoSmokeParetoStep
pareto5 = co-smoke-pareto-step
  5 routeDoseModel
  "combine product masses, residue concentrations, transfer products and user topography into inhaled and absorbed dose distributions"
  "consumer exposure packet"
  "all upstream coordinates required"

pareto99 : CoSmokeParetoStep
pareto99 = co-smoke-pareto-step
  99 broaderBehaviouralLiterature
  "do not accumulate more generic co-use prevalence studies until chemistry/source vectors are paid"
  "low marginal information for contaminant consumer"
  "dominated by exposure chemistry"

------------------------------------------------------------------------
-- Temporal evidence fibre.
------------------------------------------------------------------------

data CoSmokeTime : Set where tobaccoRegulatoryBaseline cannabisResidueProgramme mixedSourceFrontier : CoSmokeTime

data CoSmokeInterpretation : Set where
  tobaccoHasIndependentResidueSource
  mixedUseExists
  mixedChemistryPaid : CoSmokeInterpretation

data CoSmokeSummary : Set where mixedSourceNeedsDualProvenance : CoSmokeSummary

CoSmokeCompatible : CoSmokeTime → CoSmokeInterpretation → Set
CoSmokeCompatible tobaccoRegulatoryBaseline tobaccoHasIndependentResidueSource = ⊤
CoSmokeCompatible tobaccoRegulatoryBaseline mixedUseExists = ⊥
CoSmokeCompatible tobaccoRegulatoryBaseline mixedChemistryPaid = ⊥
CoSmokeCompatible cannabisResidueProgramme tobaccoHasIndependentResidueSource = ⊤
CoSmokeCompatible cannabisResidueProgramme mixedUseExists = ⊤
CoSmokeCompatible cannabisResidueProgramme mixedChemistryPaid = ⊥
CoSmokeCompatible mixedSourceFrontier tobaccoHasIndependentResidueSource = ⊤
CoSmokeCompatible mixedSourceFrontier mixedUseExists = ⊤
CoSmokeCompatible mixedSourceFrontier mixedChemistryPaid = ⊥

coSmokeTemporalSystem : Temporal.TemporalEvidenceSystem
coSmokeTemporalSystem = record
  { Time = CoSmokeTime
  ; Interpretation = CoSmokeInterpretation
  ; Compatible = CoSmokeCompatible
  ; Summary = CoSmokeSummary
  ; summarize = λ _ → mixedSourceNeedsDualProvenance
  ; timeReference = λ
      { tobaccoRegulatoryBaseline → "US/Australian tobacco regulatory and pesticide-smoke evidence baseline"
      ; cannabisResidueProgramme → "DASHI cannabis contaminant and thermal-transfer owners"
      ; mixedSourceFrontier → "current cannabis+tobacco mixed-smoke exposure frontier"
      }
  }

currentCoSmokeResidual : Temporal.EvidenceFibre coSmokeTemporalSystem mixedSourceFrontier
currentCoSmokeResidual = Temporal.liveInterpretationAt tobaccoHasIndependentResidueSource tt

record CoSmokeBoundary : Set where
  constructor co-smoke-boundary
  field
    tobaccoIsIndependentResidueSource : Bool
    usRoutineBatchPanelPaid : Bool
    australiaRoutineBatchPanelPaid : Bool
    separateSourceTransferImpliesMixedLinearity : Bool
    cleanCannabisImpliesCleanSpliff : Bool
    mixedCombustionExperimentRequired : Bool
open CoSmokeBoundary public

canonicalCoSmokeBoundary : CoSmokeBoundary
canonicalCoSmokeBoundary = co-smoke-boundary true false false false false true
