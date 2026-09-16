module DASHI.Wikimedia.IbrahimCannabisTobaccoSharedResidueObservationPanelExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmExecutionExact as ThreeArm

------------------------------------------------------------------------
-- PURPOSE
--
-- Build the three-arm observation vector from analytes with actual method
-- support in BOTH source matrices where possible, then add source-specific or
-- high-priority cannabis analytes as explicit extensions.  A long cannabis
-- panel is not automatically a valid tobacco/smoke panel, and vice versa.
------------------------------------------------------------------------

data EvidenceRole : Set where
  tobaccoMethod cannabisMethod cannabisOccurrence tobaccoSmokeTransfer sharedMethodBridge : EvidenceRole

record ResidueMethodReceipt : Set where
  constructor residue-method-receipt
  field
    sourceLabel : String
    doi : String
    matrix : String
    analyteCount : Nat
    method : String
    validationSummary : String
    smokeTransferMeasured : Bool
open ResidueMethodReceipt public

tobacco16Method : ResidueMethodReceipt
tobacco16Method = residue-method-receipt
  "Xiong et al. Determination of Commonly Used Multiclass Pesticide Residues in Tobacco and Cigarette Smoke"
  "10.1093/chromsci/bmab113"
  "tobacco plus cigarette mainstream-smoke particulate"
  16
  "modified QuEChERS + UPLC-MS/MS; Cambridge filter pad smoke collection"
  "reported recoveries, precision and LODs; compared ISO and Health Canada Intense smoking conditions"
  true

cannabis96Method : ResidueMethodReceipt
cannabis96Method = residue-method-receipt
  "MacKenzie, Anyanwu, McRae, Melanson 2025 Quantitative determination and validation of 96 pesticides in cannabis by LC-MS/MS and GC-MS/MS"
  "10.1007/s00216-025-05918-9"
  "dried cannabis flower and hemp"
  96
  "LC-MS/MS + GC-MS/MS"
  "validated linearity, precision, accuracy, recovery, ion suppression and LOQ across cannabis/hemp matrices; 10 cannabis cultivars used for accuracy evaluation"
  false

record SharedAnalyte : Set where
  constructor shared-analyte
  field
    name : String
    tobaccoMethodPaid : Bool
    cannabisMethodPaid : Bool
    cannabisOccurrence2026Paid : Bool
    tobaccoSmokeTransfer2021Paid : Bool
    role : String
open SharedAnalyte public

-- Method overlap is paid from explicit analyte lists.  Occurrence and smoke
-- transfer are kept separate: inclusion in a validated panel is not occurrence.

imidaclopridBridge : SharedAnalyte
imidaclopridBridge = shared-analyte
  "imidacloprid" true true true true
  "shared source/smoke bridge; 2026 cannabis occurrence also observed"

metalaxylBridge : SharedAnalyte
metalaxylBridge = shared-analyte
  "metalaxyl" true true true true
  "shared source/smoke bridge; 2026 cannabis occurrence also observed"

myclobutanilBridge : SharedAnalyte
myclobutanilBridge = shared-analyte
  "myclobutanil" true true true true
  "high-priority shared bridge because cannabis occurrence is strong and tobacco method includes it"

acetamipridBridge : SharedAnalyte
acetamipridBridge = shared-analyte
  "acetamiprid" true true false true
  "shared validated-method bridge; current owner does not promote occurrence"

carbarylBridge : SharedAnalyte
carbarylBridge = shared-analyte
  "carbaryl" true true false true
  "shared validated-method bridge; current owner does not promote occurrence"

thiophanateMethylBridge : SharedAnalyte
thiophanateMethylBridge = shared-analyte
  "thiophanate-methyl" true true false true
  "shared validated-method bridge; current owner does not promote occurrence"

------------------------------------------------------------------------
-- Source-specific extension panel.
------------------------------------------------------------------------

record ExtensionAnalyte : Set where
  constructor extension-analyte
  field
    name : String
    priorityReason : String
    cannabisOccurrencePaid : Bool
    tobaccoMethodPaid : Bool
    mustValidateInTargetMatrixBeforeUse : Bool
open ExtensionAnalyte public

paclobutrazolExtension : ExtensionAnalyte
paclobutrazolExtension = extension-analyte
  "paclobutrazol"
  "high cannabis occurrence plus direct legacy cannabis-smoke transfer data"
  true false true

chlorfenapyrExtension : ExtensionAnalyte
chlorfenapyrExtension = extension-analyte
  "chlorfenapyr"
  "substantial cannabis occurrence and current thermal/aerosol evidence gap"
  true false true

piperonylButoxideExtension : ExtensionAnalyte
piperonylButoxideExtension = extension-analyte
  "piperonyl butoxide"
  "lower prevalence but very high observed concentration in one 2026 illegal-cannabis sample"
  true false true

permethrinExtension : ExtensionAnalyte
permethrinExtension = extension-analyte
  "permethrin"
  "cannabis occurrence plus direct legacy cannabis-smoke transfer data"
  true false true

------------------------------------------------------------------------
-- Tobacco-study-specific transfer lesson.
------------------------------------------------------------------------

record TobaccoTransferLesson : Set where
  constructor tobacco-transfer-lesson
  field
    naturalResidueTransferRange : String
    spikedResidueTransferRange : String
    protocolDependenceObserved : Bool
    naturalEqualsSpiked : Bool
    gasPhaseAbsenceGeneralised : Bool
open TobaccoTransferLesson public

xiongTransferLesson : TobaccoTransferLesson
xiongTransferLesson = tobacco-transfer-lesson
  "0.0-26.1% under ISO for cigarettes with naturally occurring residues; up to 33.3% under HCI in the compared samples"
  "0.0-56.5% for artificially spiked tobacco in the reported experiment"
  true false false

------------------------------------------------------------------------
-- Panel compiler contract.
------------------------------------------------------------------------

record ThreeArmPanelCompiler : Set where
  constructor three-arm-panel-compiler
  field
    sharedCore : String
    cannabisExtensions : String
    sourceMarkers : String
    phaseSeparation : String
    thermalProducts : String
    admissionRule : String
open ThreeArmPanelCompiler public

canonicalThreeArmPanel : ThreeArmPanelCompiler
canonicalThreeArmPanel = three-arm-panel-compiler
  "shared core: imidacloprid, metalaxyl, myclobutanil, acetamiprid, carbaryl, thiophanate-methyl where matrix/method validation is retained"
  "cannabis-priority extensions: paclobutrazol, chlorfenapyr, piperonyl butoxide, permethrin; validate tobacco/smoke performance before interpreting mixed-arm non-detection"
  "nicotine plus cannabinoid marker(s) retained separately from pesticide panel"
  "particulate and gas phases retained separately where collection supports them"
  "parent-residue panel cannot substitute for non-targeted/targeted thermal-product observation"
  "an analyte contributes to an arm comparison only when the relevant source/smoke matrix validation, calibration, LOD/LOQ and recovery receipt are paid"

------------------------------------------------------------------------
-- HARD FIREWALLS
------------------------------------------------------------------------

data MethodMembershipCreatesOccurrence : Set where
data CannabisValidationCreatesTobaccoValidation : Set where
data TobaccoValidationCreatesCannabisValidation : Set where
data ArtificialSpikeCreatesNaturalTransferRate : Set where
data ParticulateNonDetectionCreatesGasAbsence : Set where

data SharedParentPanelCreatesThermalCompleteness : Set where

methodMembershipNotOccurrence : MethodMembershipCreatesOccurrence → ⊥
methodMembershipNotOccurrence ()

cannabisMethodNotTobaccoMethod : CannabisValidationCreatesTobaccoValidation → ⊥
cannabisMethodNotTobaccoMethod ()

tobaccoMethodNotCannabisMethod : TobaccoValidationCreatesCannabisValidation → ⊥
tobaccoMethodNotCannabisMethod ()

spikeDoesNotCreateNaturalTransfer : ArtificialSpikeCreatesNaturalTransferRate → ⊥
spikeDoesNotCreateNaturalTransfer ()

particulateNonDetectionNotGasAbsence : ParticulateNonDetectionCreatesGasAbsence → ⊥
particulateNonDetectionNotGasAbsence ()

parentPanelNotThermalComplete : SharedParentPanelCreatesThermalCompleteness → ⊥
parentPanelNotThermalComplete ()

record SharedPanelBoundary : Set where
  constructor shared-panel-boundary
  field
    sharedMethodBridgePaid : Bool
    sourceSpecificExtensionsTyped : Bool
    matrixTransferValidationStillRequired : Bool
    smokePhaseSeparationRequired : Bool
    artificialSpikeSeparatedFromNaturalResidue : Bool
    fullMixedCombustionPanelValidated : Bool
open SharedPanelBoundary public

canonicalSharedPanelBoundary : SharedPanelBoundary
canonicalSharedPanelBoundary =
  shared-panel-boundary true true true true true false
