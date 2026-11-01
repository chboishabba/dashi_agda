module DASHI.Physics.Closure.NSCutoffRieszCommutatorKernelProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ns_cutoff_riesz_commutator_kernel_proxy_harness.py
--
-- The harness is a finite diagnostic for the NS A6 pressure/localization
-- cutoff/Riesz commutator kernel bookkeeping target:
--
--   smooth compact cutoff + separated annulus + shell recentering
--     -> small synthetic commutator kernel proxy
--   rough cutoff/no cancellation/core-touching annulus
--     -> visibly bad proxy rows
--
-- This module records the expected executable result only.  It does not prove
-- a cutoff/Riesz commutator estimate, prove a pressure commutator estimate,
-- prove localization, prove A6, solve NS Clay, or promote terminal
-- unification.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary
  as Contract

------------------------------------------------------------------------
-- Local list and counting utilities.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Harness identity and run configuration.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ns_cutoff_riesz_commutator_kernel_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_cutoff_riesz_commutator_kernel_proxy_smoke.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ns_cutoff_riesz_commutator_kernel_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_synthetic_cutoff_riesz_commutator_kernel_proxy_not_pde_proof"

runCommandText : String
runCommandText =
  "python scripts/ns_cutoff_riesz_commutator_kernel_proxy_harness.py --json-output outputs/ns_cutoff_riesz_commutator_kernel_proxy_smoke.json --json"

manifestCommandText : String
manifestCommandText =
  "python scripts/ns_cutoff_riesz_commutator_kernel_proxy_harness.py --json-output outputs/local_clay_harness_manifest_children/ns_cutoff_riesz_commutator_kernel_proxy_smoke.json --json"

defaultParameterText : String
defaultParameterText =
  "synthetic cutoff/Riesz commutator kernel proxy parameters recorded by harness JSON"

kernelProxyFormulaText : String
kernelProxyFormulaText =
  "commutator_kernel_proxy compares cutoff oscillation, annular separation, cancellation, and shell recentering"

summaryNumericFieldsText : String
summaryNumericFieldsText =
  "tolerance, max_good_commutator_proxy, min_bad_commutator_proxy, profile_count"

summaryStringFieldsText : String
summaryStringFieldsText =
  "harness, output_path, status, good_split_labels, bad_split_labels, receipt_hash_like, profile_hash_like"

------------------------------------------------------------------------
-- Imported pressure-commutator contract support.

pressureCommutatorContractReference : String
pressureCommutatorContractReference =
  "DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary"

pressureCommutatorContractImported : Bool
pressureCommutatorContractImported =
  true

record ImportedCutoffRieszProxySupport : Set where
  field
    pressureCommutatorContract :
      Contract.NSPressureCommutatorEstimateContractBoundary
    pressureCommutatorContractIsCanonical :
      pressureCommutatorContract
        ≡ Contract.canonicalNSPressureCommutatorEstimateContractBoundary
    pressureCommutatorContractImportedIsTrue :
      pressureCommutatorContractImported ≡ true
    importedContractKeepsPressureCommutatorEstimateFalse :
      Contract.pressureCommutatorEstimateProved ≡ false
    importedContractKeepsLocalizationTheoremFalse :
      Contract.localizationTheoremProved ≡ false
    importedContractKeepsA6False :
      Contract.triadicCompensatedLeakageIdentityProved ≡ false
    importedContractKeepsNSClayFalse :
      Contract.nsClayPromoted ≡ false
    importedContractKeepsTerminalFalse :
      Contract.terminalPromotion ≡ false

canonicalImportedCutoffRieszProxySupport :
  ImportedCutoffRieszProxySupport
canonicalImportedCutoffRieszProxySupport =
  record
    { pressureCommutatorContract =
        Contract.canonicalNSPressureCommutatorEstimateContractBoundary
    ; pressureCommutatorContractIsCanonical =
        refl
    ; pressureCommutatorContractImportedIsTrue =
        refl
    ; importedContractKeepsPressureCommutatorEstimateFalse =
        refl
    ; importedContractKeepsLocalizationTheoremFalse =
        refl
    ; importedContractKeepsA6False =
        refl
    ; importedContractKeepsNSClayFalse =
        refl
    ; importedContractKeepsTerminalFalse =
        refl
    }

------------------------------------------------------------------------
-- Top-level harness fields.

data CutoffRieszHarnessField : Set where
  harnessField :
    CutoffRieszHarnessField
  outputPathField :
    CutoffRieszHarnessField
  manifestChildPathField :
    CutoffRieszHarnessField
  statusField :
    CutoffRieszHarnessField
  diagnosticOnlyField :
    CutoffRieszHarnessField
  splitLabelsField :
    CutoffRieszHarnessField
  toleranceField :
    CutoffRieszHarnessField
  numericSummaryField :
    CutoffRieszHarnessField
  stringSummaryField :
    CutoffRieszHarnessField
  theoremFlagsField :
    CutoffRieszHarnessField
  promotionFlagsField :
    CutoffRieszHarnessField
  interpretationField :
    CutoffRieszHarnessField

canonicalCutoffRieszHarnessFields :
  List CutoffRieszHarnessField
canonicalCutoffRieszHarnessFields =
  harnessField
  ∷ outputPathField
  ∷ manifestChildPathField
  ∷ statusField
  ∷ diagnosticOnlyField
  ∷ splitLabelsField
  ∷ toleranceField
  ∷ numericSummaryField
  ∷ stringSummaryField
  ∷ theoremFlagsField
  ∷ promotionFlagsField
  ∷ interpretationField
  ∷ []

cutoffRieszHarnessFieldCount : Nat
cutoffRieszHarnessFieldCount =
  listLength canonicalCutoffRieszHarnessFields

cutoffRieszHarnessFieldCountIs12 :
  cutoffRieszHarnessFieldCount ≡ 12
cutoffRieszHarnessFieldCountIs12 =
  refl

ok_observed : Bool
ok_observed =
  true

diagnostic_only : Bool
diagnostic_only =
  true

promotion : Bool
promotion =
  false

ok_observed_is_true :
  ok_observed ≡ true
ok_observed_is_true =
  refl

diagnostic_only_is_true :
  diagnostic_only ≡ true
diagnostic_only_is_true =
  refl

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

------------------------------------------------------------------------
-- Good/bad split labels.

goodSmoothCompactCutoffLabel : String
goodSmoothCompactCutoffLabel =
  "smooth compact cutoff"

goodSeparatedAnnulusLabel : String
goodSeparatedAnnulusLabel =
  "separated annulus"

goodShellRecenteredLabel : String
goodShellRecenteredLabel =
  "shell-recentered"

badRoughCutoffLabel : String
badRoughCutoffLabel =
  "rough cutoff"

badNoCancellationLabel : String
badNoCancellationLabel =
  "no cancellation"

badAnnulusTouchingCoreLabel : String
badAnnulusTouchingCoreLabel =
  "annulus touching core"

data CutoffRieszProxyProfile : Set where
  smoothCompactCutoffGood :
    CutoffRieszProxyProfile
  separatedAnnulusGood :
    CutoffRieszProxyProfile
  shellRecenteredGood :
    CutoffRieszProxyProfile
  roughCutoffBad :
    CutoffRieszProxyProfile
  noCancellationBad :
    CutoffRieszProxyProfile
  annulusTouchingCoreBad :
    CutoffRieszProxyProfile

record CutoffRieszProfileReceipt : Set where
  field
    profile :
      CutoffRieszProxyProfile
    label :
      String
    expectedGood :
      Bool
    expectedBad :
      Bool
    interpretation :
      String

goodProfileInterpretation : String
goodProfileInterpretation =
  "Good cutoff/Riesz proxy row: smooth localization, separated annulus, or shell recentering supports cancellation in the finite diagnostic."

badProfileInterpretation : String
badProfileInterpretation =
  "Bad cutoff/Riesz proxy row: rough cutoff, missing cancellation, or core-touching annulus obstructs the finite diagnostic."

smoothCompactCutoffGoodReceipt :
  CutoffRieszProfileReceipt
smoothCompactCutoffGoodReceipt =
  record
    { profile =
        smoothCompactCutoffGood
    ; label =
        goodSmoothCompactCutoffLabel
    ; expectedGood =
        true
    ; expectedBad =
        false
    ; interpretation =
        goodProfileInterpretation
    }

separatedAnnulusGoodReceipt :
  CutoffRieszProfileReceipt
separatedAnnulusGoodReceipt =
  record
    { profile =
        separatedAnnulusGood
    ; label =
        goodSeparatedAnnulusLabel
    ; expectedGood =
        true
    ; expectedBad =
        false
    ; interpretation =
        goodProfileInterpretation
    }

shellRecenteredGoodReceipt :
  CutoffRieszProfileReceipt
shellRecenteredGoodReceipt =
  record
    { profile =
        shellRecenteredGood
    ; label =
        goodShellRecenteredLabel
    ; expectedGood =
        true
    ; expectedBad =
        false
    ; interpretation =
        goodProfileInterpretation
    }

roughCutoffBadReceipt :
  CutoffRieszProfileReceipt
roughCutoffBadReceipt =
  record
    { profile =
        roughCutoffBad
    ; label =
        badRoughCutoffLabel
    ; expectedGood =
        false
    ; expectedBad =
        true
    ; interpretation =
        badProfileInterpretation
    }

noCancellationBadReceipt :
  CutoffRieszProfileReceipt
noCancellationBadReceipt =
  record
    { profile =
        noCancellationBad
    ; label =
        badNoCancellationLabel
    ; expectedGood =
        false
    ; expectedBad =
        true
    ; interpretation =
        badProfileInterpretation
    }

annulusTouchingCoreBadReceipt :
  CutoffRieszProfileReceipt
annulusTouchingCoreBadReceipt =
  record
    { profile =
        annulusTouchingCoreBad
    ; label =
        badAnnulusTouchingCoreLabel
    ; expectedGood =
        false
    ; expectedBad =
        true
    ; interpretation =
        badProfileInterpretation
    }

canonicalCutoffRieszProfileReceipts :
  List CutoffRieszProfileReceipt
canonicalCutoffRieszProfileReceipts =
  smoothCompactCutoffGoodReceipt
  ∷ separatedAnnulusGoodReceipt
  ∷ shellRecenteredGoodReceipt
  ∷ roughCutoffBadReceipt
  ∷ noCancellationBadReceipt
  ∷ annulusTouchingCoreBadReceipt
  ∷ []

cutoffRieszProfileReceiptCount : Nat
cutoffRieszProfileReceiptCount =
  listLength canonicalCutoffRieszProfileReceipts

cutoffRieszProfileReceiptCountIs6 :
  cutoffRieszProfileReceiptCount ≡ 6
cutoffRieszProfileReceiptCountIs6 =
  refl

------------------------------------------------------------------------
-- Harness checks.

data CutoffRieszHarnessCheck : Set where
  sourceHarnessPathRecorded :
    CutoffRieszHarnessCheck
  jsonOutputPathRecorded :
    CutoffRieszHarnessCheck
  manifestChildPathRecorded :
    CutoffRieszHarnessCheck
  diagnosticOnlyRecorded :
    CutoffRieszHarnessCheck
  okObservedRecorded :
    CutoffRieszHarnessCheck
  goodSplitLabelsRecorded :
    CutoffRieszHarnessCheck
  badSplitLabelsRecorded :
    CutoffRieszHarnessCheck
  numericSummariesRecorded :
    CutoffRieszHarnessCheck
  stringSummariesRecorded :
    CutoffRieszHarnessCheck
  theoremFlagsFalseRecorded :
    CutoffRieszHarnessCheck

canonicalCutoffRieszHarnessChecks :
  List CutoffRieszHarnessCheck
canonicalCutoffRieszHarnessChecks =
  sourceHarnessPathRecorded
  ∷ jsonOutputPathRecorded
  ∷ manifestChildPathRecorded
  ∷ diagnosticOnlyRecorded
  ∷ okObservedRecorded
  ∷ goodSplitLabelsRecorded
  ∷ badSplitLabelsRecorded
  ∷ numericSummariesRecorded
  ∷ stringSummariesRecorded
  ∷ theoremFlagsFalseRecorded
  ∷ []

cutoffRieszHarnessCheckCount : Nat
cutoffRieszHarnessCheckCount =
  listLength canonicalCutoffRieszHarnessChecks

cutoffRieszHarnessCheckCountIs10 :
  cutoffRieszHarnessCheckCount ≡ 10
cutoffRieszHarnessCheckCountIs10 =
  refl

------------------------------------------------------------------------
-- Explicit non-promotion theorem flags.

cutoffRieszCommutatorEstimateProved : Bool
cutoffRieszCommutatorEstimateProved =
  false

pressureCommutatorEstimateProved : Bool
pressureCommutatorEstimateProved =
  false

localizationTheoremProved : Bool
localizationTheoremProved =
  false

A6Proved : Bool
A6Proved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

cutoffRieszCommutatorEstimateProvedIsFalse :
  cutoffRieszCommutatorEstimateProved ≡ false
cutoffRieszCommutatorEstimateProvedIsFalse =
  refl

pressureCommutatorEstimateProvedIsFalse :
  pressureCommutatorEstimateProved ≡ false
pressureCommutatorEstimateProvedIsFalse =
  refl

localizationTheoremProvedIsFalse :
  localizationTheoremProved ≡ false
localizationTheoremProvedIsFalse =
  refl

A6ProvedIsFalse :
  A6Proved ≡ false
A6ProvedIsFalse =
  refl

nsClayPromotedIsFalse :
  nsClayPromoted ≡ false
nsClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

contractPressureCommutatorEstimateStillFalse :
  Contract.pressureCommutatorEstimateProved ≡ false
contractPressureCommutatorEstimateStillFalse =
  refl

contractLocalizationTheoremStillFalse :
  Contract.localizationTheoremProved ≡ false
contractLocalizationTheoremStillFalse =
  refl

contractA6StillFalse :
  Contract.triadicCompensatedLeakageIdentityProved ≡ false
contractA6StillFalse =
  refl

contractNSClayStillFalse :
  Contract.nsClayPromoted ≡ false
contractNSClayStillFalse =
  refl

contractTerminalStillFalse :
  Contract.terminalPromotion ≡ false
contractTerminalStillFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F summary.

controlO : String
controlO =
  "O: Worker Lane 2 Raman Agda receipt for the finite NS cutoff/Riesz commutator kernel proxy harness."

controlR : String
controlR =
  "R: Record good labels smooth compact cutoff, separated annulus, shell-recentered and bad labels rough cutoff, no cancellation, annulus touching core."

controlC : String
controlC =
  "C: DASHI.Physics.Closure.NSCutoffRieszCommutatorKernelProxyHarnessResult imports DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary and records scripts/ns_cutoff_riesz_commutator_kernel_proxy_harness.py with smoke and manifest child output paths."

controlS : String
controlS =
  "S: diagnostic_only=true, ok_observed=true, promotion=false, cutoffRieszCommutatorEstimateProved=false, pressureCommutatorEstimateProved=false, localizationTheoremProved=false, A6Proved=false, nsClayPromoted=false, terminalPromotion=false."

controlL : String
controlL =
  "L: imported pressure-commutator contract false flags -> harness source/output paths -> good/bad split labels -> numeric/string summaries -> fail-closed theorem flags."

controlP : String
controlP =
  "P: Promote nothing; use only as expected executable bookkeeping for a synthetic cutoff/Riesz commutator kernel proxy."

controlG : String
controlG =
  "G: diagnostic_only=true; finite proxy separation does not certify a cutoff/Riesz estimate, pressure commutator theorem, localization theorem, A6, NS Clay, or terminal promotion."

controlF : String
controlF =
  "F: Missing analytic cutoff/Riesz commutator estimate, pressure commutator estimate, localization theorem, A6 proof, NS Clay proof, and terminal promotion."

canonicalORCSLPGFSummary : List String
canonicalORCSLPGFSummary =
  controlO
  ∷ controlR
  ∷ controlC
  ∷ controlS
  ∷ controlL
  ∷ controlP
  ∷ controlG
  ∷ controlF
  ∷ []

orcsLpgfSummaryCount : Nat
orcsLpgfSummaryCount =
  listLength canonicalORCSLPGFSummary

orcsLpgfSummaryCountIs8 :
  orcsLpgfSummaryCount ≡ 8
orcsLpgfSummaryCountIs8 =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record NSCutoffRieszCommutatorKernelProxyHarnessResult : Set where
  field
    importedSupport :
      ImportedCutoffRieszProxySupport
    harnessFields :
      List CutoffRieszHarnessField
    harnessFieldCountProof :
      cutoffRieszHarnessFieldCount ≡ 12
    profileReceipts :
      List CutoffRieszProfileReceipt
    profileReceiptCountProof :
      cutoffRieszProfileReceiptCount ≡ 6
    checks :
      List CutoffRieszHarnessCheck
    checkCountProof :
      cutoffRieszHarnessCheckCount ≡ 10
    sourceHarness :
      String
    jsonReceipt :
      String
    manifestChildReceipt :
      String
    scope :
      String
    runCommand :
      String
    manifestCommand :
      String
    parameters :
      String
    kernelProxyFormula :
      String
    numericSummaryFields :
      String
    stringSummaryFields :
      String
    goodSmoothCompactCutoff :
      String
    goodSeparatedAnnulus :
      String
    goodShellRecentered :
      String
    badRoughCutoff :
      String
    badNoCancellation :
      String
    badAnnulusTouchingCore :
      String
    okObservedIsTrue :
      ok_observed ≡ true
    diagnosticOnlyIsTrue :
      diagnostic_only ≡ true
    promotionIsFalse :
      promotion ≡ false
    cutoffRieszCommutatorEstimateProvedFalse :
      cutoffRieszCommutatorEstimateProved ≡ false
    pressureCommutatorEstimateProvedFalse :
      pressureCommutatorEstimateProved ≡ false
    localizationTheoremProvedFalse :
      localizationTheoremProved ≡ false
    A6ProvedFalse :
      A6Proved ≡ false
    nsClayPromotedFalse :
      nsClayPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    O :
      String
    R :
      String
    C :
      String
    S :
      String
    L :
      String
    P :
      String
    G :
      String
    F :
      String

open NSCutoffRieszCommutatorKernelProxyHarnessResult public

canonicalNSCutoffRieszCommutatorKernelProxyHarnessResult :
  NSCutoffRieszCommutatorKernelProxyHarnessResult
canonicalNSCutoffRieszCommutatorKernelProxyHarnessResult =
  record
    { importedSupport =
        canonicalImportedCutoffRieszProxySupport
    ; harnessFields =
        canonicalCutoffRieszHarnessFields
    ; harnessFieldCountProof =
        refl
    ; profileReceipts =
        canonicalCutoffRieszProfileReceipts
    ; profileReceiptCountProof =
        refl
    ; checks =
        canonicalCutoffRieszHarnessChecks
    ; checkCountProof =
        refl
    ; sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        jsonReceiptPath
    ; manifestChildReceipt =
        manifestChildReceiptPath
    ; scope =
        receiptScope
    ; runCommand =
        runCommandText
    ; manifestCommand =
        manifestCommandText
    ; parameters =
        defaultParameterText
    ; kernelProxyFormula =
        kernelProxyFormulaText
    ; numericSummaryFields =
        summaryNumericFieldsText
    ; stringSummaryFields =
        summaryStringFieldsText
    ; goodSmoothCompactCutoff =
        goodSmoothCompactCutoffLabel
    ; goodSeparatedAnnulus =
        goodSeparatedAnnulusLabel
    ; goodShellRecentered =
        goodShellRecenteredLabel
    ; badRoughCutoff =
        badRoughCutoffLabel
    ; badNoCancellation =
        badNoCancellationLabel
    ; badAnnulusTouchingCore =
        badAnnulusTouchingCoreLabel
    ; okObservedIsTrue =
        refl
    ; diagnosticOnlyIsTrue =
        refl
    ; promotionIsFalse =
        refl
    ; cutoffRieszCommutatorEstimateProvedFalse =
        refl
    ; pressureCommutatorEstimateProvedFalse =
        refl
    ; localizationTheoremProvedFalse =
        refl
    ; A6ProvedFalse =
        refl
    ; nsClayPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; O =
        controlO
    ; R =
        controlR
    ; C =
        controlC
    ; S =
        controlS
    ; L =
        controlL
    ; P =
        controlP
    ; G =
        controlG
    ; F =
        controlF
    }
