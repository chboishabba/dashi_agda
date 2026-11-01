module DASHI.Wikimedia.IbrahimTobaccoPesticideSourceDatasetExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTobaccoSharedResidueObservationPanelExact as Panel
import DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmExecutionExact as ThreeArm

------------------------------------------------------------------------
-- PURPOSE
--
-- Bind a real tobacco source-residue/smoke-transfer dataset that can inform
-- T-arm acquisition priors without pretending its anonymised samples are the
-- same object as the future T-SRC-001 experimental tobacco specimen.
------------------------------------------------------------------------

record TobaccoDatasetReceipt : Set where
  constructor tobacco-dataset-receipt
  field
    sourceLabel : String
    doi : String
    publicationYear : Nat
    tobaccoSampleCount : Nat
    duplicateSourceMeasurements : Bool
    smokeTransferSampleCount : Nat
    analyteCount : Nat
    sourceCountriesMultiple : Bool
    retailProductIdentityAvailable : Bool
    sameObjectAsFutureTArm : Bool
    matrixMethod : String
    smokeCollection : String
open TobaccoDatasetReceipt public

xiongTobaccoDataset : TobaccoDatasetReceipt
xiongTobaccoDataset = tobacco-dataset-receipt
  "Xiong et al. Determination of Commonly Used Multiclass Pesticide Residues in Tobacco and Cigarette Smoke"
  "10.1093/chromsci/bmab113"
  2021
  62 true
  51
  16 true false false
  "modified QuEChERS + UPLC-MS/MS; tobacco samples determined in duplicate"
  "mainstream smoke particulate on Cambridge filter pad; ISO and HCI transfer comparison"

record TobaccoOccurrenceSummary : Set where
  constructor tobacco-occurrence-summary
  field
    analyte : String
    sourceFinding : String
    smokeFinding : String
    exactPerSampleProductIdentityPaid : Bool
open TobaccoOccurrenceSummary public

imidaclopridSummary : TobaccoOccurrenceSummary
imidaclopridSummary = tobacco-occurrence-summary
  "imidacloprid"
  "5 of 62 tobacco samples exceeded 1.18 microgram/g"
  "not found in ISO/HCI smoke TPM except detected under HCI for some samples; exact sample-level mapping is not promoted here"
  false

metalaxylSummary : TobaccoOccurrenceSummary
metalaxylSummary = tobacco-occurrence-summary
  "metalaxyl"
  "among 8 samples containing pendimethalin and/or metalaxyl; reported maximum metalaxyl 0.88 microgram/g"
  "detected in HCI smoke TPM for some samples"
  false

myclobutanilSummary : TobaccoOccurrenceSummary
myclobutanilSummary = tobacco-occurrence-summary
  "myclobutanil"
  "not above LOQ in any of the 62 tobacco samples"
  "not found in smoke TPM in the reported residue-positive transfer experiment"
  false

carbendazimSummary : TobaccoOccurrenceSummary
carbendazimSummary = tobacco-occurrence-summary
  "carbendazim"
  "trace detections in some source samples, usually below 1.18 microgram/g"
  "23 samples above smoke LOQ under ISO; high smoke detection rate also reported under HCI"
  false

triadimenolSummary : TobaccoOccurrenceSummary
triadimenolSummary = tobacco-occurrence-summary
  "triadimenol"
  "trace detections in some source samples, usually below 1.18 microgram/g"
  "reported as one of the analytes with relatively high smoke detection rate under ISO/HCI"
  false

record TransferRangeReceipt : Set where
  constructor transfer-range-receipt
  field
    naturalISO : String
    naturalHCI : String
    artificialSpike : String
    spikeEqualsNatural : Bool
    gasPhaseGeneralisedFromStudy : Bool
open TransferRangeReceipt public

xiongTransferRanges : TransferRangeReceipt
xiongTransferRanges = transfer-range-receipt
  "0.0-26.1% parent-residue transfer to smoke TPM under ISO"
  "0.0-33.3% parent-residue transfer to smoke TPM under HCI"
  "0.0-56.5% for artificially spiked tobacco under the reported experiment"
  false false

record TArmAcquisitionStatus : Set where
  constructor t-arm-acquisition-status
  field
    realTobaccoResidueDatasetPaid : Bool
    realSmokeTransferDatasetPaid : Bool
    exactRetailSpecimenIdentityPaid : Bool
    exactAustralianRetailSpecimenPaid : Bool
    exactUSRetailSpecimenPaid : Bool
    futureSpecimenMustBeReassayed : Bool
    priorUse : String
open TArmAcquisitionStatus public

canonicalTArmAcquisitionStatus : TArmAcquisitionStatus
canonicalTArmAcquisitionStatus = t-arm-acquisition-status
  true true false false false true
  "use the 62-sample distribution and 51-sample transfer experiment only to choose analytes, expected concentration scale and collection sensitivity; T-SRC-001 must receive its own source assay"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data PopulationDatasetCreatesSpecimenIdentity : Set where
data HistoricalSampleCreatesCurrentRetailLevel : Set where
data SourceNonDetectionCreatesFutureTArmAbsence : Set where
data NaturalResidueTransferCreatesMixedTransfer : Set where

populationDoesNotCreateSpecimen : PopulationDatasetCreatesSpecimenIdentity → ⊥
populationDoesNotCreateSpecimen ()

historicalDoesNotCreateCurrentLevel : HistoricalSampleCreatesCurrentRetailLevel → ⊥
historicalDoesNotCreateCurrentLevel ()

sourceNonDetectionNotFutureAbsence : SourceNonDetectionCreatesFutureTArmAbsence → ⊥
sourceNonDetectionNotFutureAbsence ()

naturalTobaccoTransferNotMixedTransfer : NaturalResidueTransferCreatesMixedTransfer → ⊥
naturalTobaccoTransferNotMixedTransfer ()
