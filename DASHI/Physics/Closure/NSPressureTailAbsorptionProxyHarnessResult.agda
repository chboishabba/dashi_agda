module DASHI.Physics.Closure.NSPressureTailAbsorptionProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ns_pressure_tail_absorption_proxy_harness.py
--
-- The harness is an expected finite diagnostic for the NS localization
-- pressure-tail absorption bookkeeping target:
--
--   pressure tail budget + absorption margin
--     -> good/bad synthetic split
--     -> tolerance/hash-like summary receipt
--
-- This module records the expected executable receipt shape only.  It does
-- not prove pressure-tail absorption, prove a pressure commutator estimate,
-- prove localization, prove A6, solve NS Clay, or promote terminal
-- unification.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary
  as Localization

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
-- Harness identity and expected output.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ns_pressure_tail_absorption_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_pressure_tail_absorption_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_synthetic_pressure_tail_absorption_proxy_not_pde_proof"

expectedRunCommandText : String
expectedRunCommandText =
  "python scripts/ns_pressure_tail_absorption_proxy_harness.py --json-output outputs/ns_pressure_tail_absorption_proxy_smoke.json --json"

expectedStatusText : String
expectedStatusText =
  "diagnostic_only"

defaultParameterText : String
defaultParameterText =
  "synthetic pressure-tail absorption proxy parameters recorded by harness JSON"

absorptionProxyFormulaText : String
absorptionProxyFormulaText =
  "absorbed_tail_proxy = pressure_tail_load <= tolerance * absorption_margin for good profiles"

summaryNumericFieldsText : String
summaryNumericFieldsText =
  "tolerance, max_good_tail_load, max_good_absorption_ratio, min_bad_absorption_ratio, profile_count"

summaryStringFieldsText : String
summaryStringFieldsText =
  "harness, output_path, status, good_split_label, bad_split_label, receipt_hash_like, profile_hash_like"

receiptHashLikeText : String
receiptHashLikeText =
  "hash-like summary field expected from deterministic harness receipt"

profileHashLikeText : String
profileHashLikeText =
  "hash-like per-profile field expected from deterministic harness receipt"

------------------------------------------------------------------------
-- Imported localization/pressure boundary support.

localizationPressureBoundaryReference : String
localizationPressureBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary"

localizationPressureBoundaryImported : Bool
localizationPressureBoundaryImported =
  true

record ImportedPressureTailAbsorptionProxySupport : Set where
  field
    localizationPressureBoundary :
      Localization.NSLocalizationPressureCommutatorBoundary
    localizationPressureBoundaryIsCanonical :
      localizationPressureBoundary
        ≡ Localization.canonicalNSLocalizationPressureCommutatorBoundary
    localizationPressureBoundaryImportedIsTrue :
      localizationPressureBoundaryImported ≡ true
    importedBoundaryLocalizationTheoremNowTrue :
      Localization.localizedCutoffTheoremProved ≡ true
    importedBoundaryPressureCommutatorNowTrue :
      Localization.pressureCommutatorTheoremProved ≡ true
    importedBoundaryKeepsA6False :
      Localization.triadicCompensatedLeakageIdentityProved ≡ false
    importedBoundaryKeepsResidualDepletionFalse :
      Localization.residualDepletionProved ≡ false
    importedBoundaryKeepsClayFalse :
      Localization.clayNavierStokesPromoted ≡ false
    importedBoundaryKeepsTerminalFalse :
      Localization.terminalUnificationPromoted ≡ false

canonicalImportedPressureTailAbsorptionProxySupport :
  ImportedPressureTailAbsorptionProxySupport
canonicalImportedPressureTailAbsorptionProxySupport =
  record
    { localizationPressureBoundary =
        Localization.canonicalNSLocalizationPressureCommutatorBoundary
    ; localizationPressureBoundaryIsCanonical =
        refl
    ; localizationPressureBoundaryImportedIsTrue =
        refl
    ; importedBoundaryLocalizationTheoremNowTrue =
        refl
    ; importedBoundaryPressureCommutatorNowTrue =
        refl
    ; importedBoundaryKeepsA6False =
        refl
    ; importedBoundaryKeepsResidualDepletionFalse =
        refl
    ; importedBoundaryKeepsClayFalse =
        refl
    ; importedBoundaryKeepsTerminalFalse =
        refl
    }

------------------------------------------------------------------------
-- Top-level harness fields.

data PressureTailAbsorptionHarnessField : Set where
  harnessField :
    PressureTailAbsorptionHarnessField
  outputPathField :
    PressureTailAbsorptionHarnessField
  statusField :
    PressureTailAbsorptionHarnessField
  diagnosticOnlyField :
    PressureTailAbsorptionHarnessField
  splitLabelsField :
    PressureTailAbsorptionHarnessField
  toleranceField :
    PressureTailAbsorptionHarnessField
  numericSummaryField :
    PressureTailAbsorptionHarnessField
  stringSummaryField :
    PressureTailAbsorptionHarnessField
  hashLikeSummaryField :
    PressureTailAbsorptionHarnessField
  theoremFlagsField :
    PressureTailAbsorptionHarnessField
  promotionFlagsField :
    PressureTailAbsorptionHarnessField
  interpretationField :
    PressureTailAbsorptionHarnessField

canonicalPressureTailAbsorptionHarnessFields :
  List PressureTailAbsorptionHarnessField
canonicalPressureTailAbsorptionHarnessFields =
  harnessField
  ∷ outputPathField
  ∷ statusField
  ∷ diagnosticOnlyField
  ∷ splitLabelsField
  ∷ toleranceField
  ∷ numericSummaryField
  ∷ stringSummaryField
  ∷ hashLikeSummaryField
  ∷ theoremFlagsField
  ∷ promotionFlagsField
  ∷ interpretationField
  ∷ []

pressureTailAbsorptionHarnessFieldCount : Nat
pressureTailAbsorptionHarnessFieldCount =
  listLength canonicalPressureTailAbsorptionHarnessFields

pressureTailAbsorptionHarnessFieldCountIs12 :
  pressureTailAbsorptionHarnessFieldCount ≡ 12
pressureTailAbsorptionHarnessFieldCountIs12 =
  refl

ok_observed : Bool
ok_observed =
  true

diagnostic_only : Bool
diagnostic_only =
  true

status_diagnostic_only : Bool
status_diagnostic_only =
  true

promotion : Bool
promotion =
  false

clay_promoted : Bool
clay_promoted =
  false

ok_observed_is_true :
  ok_observed ≡ true
ok_observed_is_true =
  refl

diagnostic_only_is_true :
  diagnostic_only ≡ true
diagnostic_only_is_true =
  refl

status_diagnostic_only_is_true :
  status_diagnostic_only ≡ true
status_diagnostic_only_is_true =
  refl

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

clay_promoted_is_false :
  clay_promoted ≡ false
clay_promoted_is_false =
  refl

------------------------------------------------------------------------
-- Good/bad split labels and profile observations.

goodSplitLabel : String
goodSplitLabel =
  "good_pressure_tail_absorbed"

badSplitLabel : String
badSplitLabel =
  "bad_pressure_tail_unabsorbed"

data PressureTailAbsorptionProxyProfile : Set where
  goodSmallTailAbsorbed :
    PressureTailAbsorptionProxyProfile
  goodRefinedTailAbsorbed :
    PressureTailAbsorptionProxyProfile
  badPersistentTailUnabsorbed :
    PressureTailAbsorptionProxyProfile
  badMarginDeficitUnabsorbed :
    PressureTailAbsorptionProxyProfile

profileName : PressureTailAbsorptionProxyProfile → String
profileName goodSmallTailAbsorbed =
  "good_small_tail_absorbed"
profileName goodRefinedTailAbsorbed =
  "good_refined_tail_absorbed"
profileName badPersistentTailUnabsorbed =
  "bad_persistent_tail_unabsorbed"
profileName badMarginDeficitUnabsorbed =
  "bad_margin_deficit_unabsorbed"

profileSplitLabel : PressureTailAbsorptionProxyProfile → String
profileSplitLabel goodSmallTailAbsorbed =
  goodSplitLabel
profileSplitLabel goodRefinedTailAbsorbed =
  goodSplitLabel
profileSplitLabel badPersistentTailUnabsorbed =
  badSplitLabel
profileSplitLabel badMarginDeficitUnabsorbed =
  badSplitLabel

profileDescription : PressureTailAbsorptionProxyProfile → String
profileDescription goodSmallTailAbsorbed =
  "Synthetic localized profile whose pressure tail is below the absorption budget."
profileDescription goodRefinedTailAbsorbed =
  "Synthetic refined profile whose pressure tail decays into the absorption budget."
profileDescription badPersistentTailUnabsorbed =
  "Deliberately bad profile: pressure tail remains above the absorption budget."
profileDescription badMarginDeficitUnabsorbed =
  "Deliberately bad profile: absorption margin is too small for the pressure tail."

expectedProfilePasses : PressureTailAbsorptionProxyProfile → Bool
expectedProfilePasses goodSmallTailAbsorbed =
  true
expectedProfilePasses goodRefinedTailAbsorbed =
  true
expectedProfilePasses badPersistentTailUnabsorbed =
  false
expectedProfilePasses badMarginDeficitUnabsorbed =
  false

profileClassification : PressureTailAbsorptionProxyProfile → String
profileClassification goodSmallTailAbsorbed =
  "good_pressure_tail_absorption_proxy"
profileClassification goodRefinedTailAbsorbed =
  "good_pressure_tail_absorption_proxy"
profileClassification badPersistentTailUnabsorbed =
  "bad_pressure_tail_absorption_obstruction"
profileClassification badMarginDeficitUnabsorbed =
  "bad_pressure_tail_absorption_obstruction"

canonicalPressureTailAbsorptionProfiles :
  List PressureTailAbsorptionProxyProfile
canonicalPressureTailAbsorptionProfiles =
  goodSmallTailAbsorbed
  ∷ goodRefinedTailAbsorbed
  ∷ badPersistentTailUnabsorbed
  ∷ badMarginDeficitUnabsorbed
  ∷ []

canonicalGoodPressureTailProfiles :
  List PressureTailAbsorptionProxyProfile
canonicalGoodPressureTailProfiles =
  goodSmallTailAbsorbed
  ∷ goodRefinedTailAbsorbed
  ∷ []

canonicalBadPressureTailProfiles :
  List PressureTailAbsorptionProxyProfile
canonicalBadPressureTailProfiles =
  badPersistentTailUnabsorbed
  ∷ badMarginDeficitUnabsorbed
  ∷ []

pressureTailAbsorptionProfileCount : Nat
pressureTailAbsorptionProfileCount =
  listLength canonicalPressureTailAbsorptionProfiles

goodPressureTailProfileCount : Nat
goodPressureTailProfileCount =
  listLength canonicalGoodPressureTailProfiles

badPressureTailProfileCount : Nat
badPressureTailProfileCount =
  listLength canonicalBadPressureTailProfiles

pressureTailAbsorptionProfileCountIs4 :
  pressureTailAbsorptionProfileCount ≡ 4
pressureTailAbsorptionProfileCountIs4 =
  refl

goodPressureTailProfileCountIs2 :
  goodPressureTailProfileCount ≡ 2
goodPressureTailProfileCountIs2 =
  refl

badPressureTailProfileCountIs2 :
  badPressureTailProfileCount ≡ 2
badPressureTailProfileCountIs2 =
  refl

record PressureTailAbsorptionProfileReceipt : Set where
  field
    profile :
      PressureTailAbsorptionProxyProfile
    name :
      String
    splitLabel :
      String
    description :
      String
    passedTolerance :
      Bool
    expectedPassedTolerance :
      Bool
    passedToleranceIsExpected :
      passedTolerance ≡ expectedPassedTolerance
    classification :
      String
    tolerance :
      String
    pressureTailLoad :
      String
    absorptionMargin :
      String
    absorptionRatio :
      String
    numericSummary :
      String
    hashLikeSummary :
      String
    promotionForProfile :
      Bool
    promotionForProfileIsFalse :
      promotionForProfile ≡ false

open PressureTailAbsorptionProfileReceipt public

goodSmallTailAbsorbedReceipt :
  PressureTailAbsorptionProfileReceipt
goodSmallTailAbsorbedReceipt =
  record
    { profile =
        goodSmallTailAbsorbed
    ; name =
        profileName goodSmallTailAbsorbed
    ; splitLabel =
        profileSplitLabel goodSmallTailAbsorbed
    ; description =
        profileDescription goodSmallTailAbsorbed
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification goodSmallTailAbsorbed
    ; tolerance =
        "expected_tolerance"
    ; pressureTailLoad =
        "numeric: below absorption margin"
    ; absorptionMargin =
        "numeric: positive margin"
    ; absorptionRatio =
        "numeric: <= 1"
    ; numericSummary =
        "good_small_tail_absorbed: tail_load <= tolerance * margin"
    ; hashLikeSummary =
        "hash-like: good_small_tail_absorbed"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

goodRefinedTailAbsorbedReceipt :
  PressureTailAbsorptionProfileReceipt
goodRefinedTailAbsorbedReceipt =
  record
    { profile =
        goodRefinedTailAbsorbed
    ; name =
        profileName goodRefinedTailAbsorbed
    ; splitLabel =
        profileSplitLabel goodRefinedTailAbsorbed
    ; description =
        profileDescription goodRefinedTailAbsorbed
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification goodRefinedTailAbsorbed
    ; tolerance =
        "expected_tolerance"
    ; pressureTailLoad =
        "numeric: decays below absorption margin"
    ; absorptionMargin =
        "numeric: positive refined margin"
    ; absorptionRatio =
        "numeric: <= 1"
    ; numericSummary =
        "good_refined_tail_absorbed: refined tail ratio within tolerance"
    ; hashLikeSummary =
        "hash-like: good_refined_tail_absorbed"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

badPersistentTailUnabsorbedReceipt :
  PressureTailAbsorptionProfileReceipt
badPersistentTailUnabsorbedReceipt =
  record
    { profile =
        badPersistentTailUnabsorbed
    ; name =
        profileName badPersistentTailUnabsorbed
    ; splitLabel =
        profileSplitLabel badPersistentTailUnabsorbed
    ; description =
        profileDescription badPersistentTailUnabsorbed
    ; passedTolerance =
        false
    ; expectedPassedTolerance =
        false
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification badPersistentTailUnabsorbed
    ; tolerance =
        "expected_tolerance"
    ; pressureTailLoad =
        "numeric: persistent tail above budget"
    ; absorptionMargin =
        "numeric: positive but insufficient"
    ; absorptionRatio =
        "numeric: > 1"
    ; numericSummary =
        "bad_persistent_tail_unabsorbed: tail load visibly exceeds absorption budget"
    ; hashLikeSummary =
        "hash-like: bad_persistent_tail_unabsorbed"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

badMarginDeficitUnabsorbedReceipt :
  PressureTailAbsorptionProfileReceipt
badMarginDeficitUnabsorbedReceipt =
  record
    { profile =
        badMarginDeficitUnabsorbed
    ; name =
        profileName badMarginDeficitUnabsorbed
    ; splitLabel =
        profileSplitLabel badMarginDeficitUnabsorbed
    ; description =
        profileDescription badMarginDeficitUnabsorbed
    ; passedTolerance =
        false
    ; expectedPassedTolerance =
        false
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification badMarginDeficitUnabsorbed
    ; tolerance =
        "expected_tolerance"
    ; pressureTailLoad =
        "numeric: tail load not absorbed"
    ; absorptionMargin =
        "numeric: margin deficit"
    ; absorptionRatio =
        "numeric: > 1"
    ; numericSummary =
        "bad_margin_deficit_unabsorbed: absorption margin too small for pressure tail"
    ; hashLikeSummary =
        "hash-like: bad_margin_deficit_unabsorbed"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

canonicalPressureTailAbsorptionProfileReceipts :
  List PressureTailAbsorptionProfileReceipt
canonicalPressureTailAbsorptionProfileReceipts =
  goodSmallTailAbsorbedReceipt
  ∷ goodRefinedTailAbsorbedReceipt
  ∷ badPersistentTailUnabsorbedReceipt
  ∷ badMarginDeficitUnabsorbedReceipt
  ∷ []

pressureTailAbsorptionProfileReceiptCount : Nat
pressureTailAbsorptionProfileReceiptCount =
  listLength canonicalPressureTailAbsorptionProfileReceipts

pressureTailAbsorptionProfileReceiptCountIs4 :
  pressureTailAbsorptionProfileReceiptCount ≡ 4
pressureTailAbsorptionProfileReceiptCountIs4 =
  refl

goodSmallTailPassed :
  passedTolerance goodSmallTailAbsorbedReceipt ≡ true
goodSmallTailPassed =
  refl

goodRefinedTailPassed :
  passedTolerance goodRefinedTailAbsorbedReceipt ≡ true
goodRefinedTailPassed =
  refl

badPersistentTailFailed :
  passedTolerance badPersistentTailUnabsorbedReceipt ≡ false
badPersistentTailFailed =
  refl

badMarginDeficitFailed :
  passedTolerance badMarginDeficitUnabsorbedReceipt ≡ false
badMarginDeficitFailed =
  refl

------------------------------------------------------------------------
-- Harness checks and summary fields.

data PressureTailAbsorptionHarnessCheck : Set where
  goodProfilesIncludedCheck :
    PressureTailAbsorptionHarnessCheck
  badProfilesIncludedCheck :
    PressureTailAbsorptionHarnessCheck
  allGoodProfilesPassCheck :
    PressureTailAbsorptionHarnessCheck
  badProfilesFailVisiblyCheck :
    PressureTailAbsorptionHarnessCheck
  toleranceSlotRecordedCheck :
    PressureTailAbsorptionHarnessCheck
  numericSummariesRecordedCheck :
    PressureTailAbsorptionHarnessCheck
  stringSummariesRecordedCheck :
    PressureTailAbsorptionHarnessCheck
  hashLikeSummariesRecordedCheck :
    PressureTailAbsorptionHarnessCheck
  diagnosticOnlyStatusCheck :
    PressureTailAbsorptionHarnessCheck
  promotionFalseCheck :
    PressureTailAbsorptionHarnessCheck

canonicalPressureTailAbsorptionHarnessChecks :
  List PressureTailAbsorptionHarnessCheck
canonicalPressureTailAbsorptionHarnessChecks =
  goodProfilesIncludedCheck
  ∷ badProfilesIncludedCheck
  ∷ allGoodProfilesPassCheck
  ∷ badProfilesFailVisiblyCheck
  ∷ toleranceSlotRecordedCheck
  ∷ numericSummariesRecordedCheck
  ∷ stringSummariesRecordedCheck
  ∷ hashLikeSummariesRecordedCheck
  ∷ diagnosticOnlyStatusCheck
  ∷ promotionFalseCheck
  ∷ []

pressureTailAbsorptionHarnessCheckCount : Nat
pressureTailAbsorptionHarnessCheckCount =
  listLength canonicalPressureTailAbsorptionHarnessChecks

pressureTailAbsorptionHarnessCheckCountIs10 :
  pressureTailAbsorptionHarnessCheckCount ≡ 10
pressureTailAbsorptionHarnessCheckCountIs10 =
  refl

good_profiles_included : Bool
good_profiles_included =
  true

bad_profiles_included : Bool
bad_profiles_included =
  true

all_good_profiles_pass : Bool
all_good_profiles_pass =
  true

bad_profiles_fail_visibly : Bool
bad_profiles_fail_visibly =
  true

tolerance_slot_recorded : Bool
tolerance_slot_recorded =
  true

numeric_summaries_recorded : Bool
numeric_summaries_recorded =
  true

string_summaries_recorded : Bool
string_summaries_recorded =
  true

hash_like_summaries_recorded : Bool
hash_like_summaries_recorded =
  true

good_profiles_included_is_true :
  good_profiles_included ≡ true
good_profiles_included_is_true =
  refl

bad_profiles_included_is_true :
  bad_profiles_included ≡ true
bad_profiles_included_is_true =
  refl

all_good_profiles_pass_is_true :
  all_good_profiles_pass ≡ true
all_good_profiles_pass_is_true =
  refl

bad_profiles_fail_visibly_is_true :
  bad_profiles_fail_visibly ≡ true
bad_profiles_fail_visibly_is_true =
  refl

tolerance_slot_recorded_is_true :
  tolerance_slot_recorded ≡ true
tolerance_slot_recorded_is_true =
  refl

numeric_summaries_recorded_is_true :
  numeric_summaries_recorded ≡ true
numeric_summaries_recorded_is_true =
  refl

string_summaries_recorded_is_true :
  string_summaries_recorded ≡ true
string_summaries_recorded_is_true =
  refl

hash_like_summaries_recorded_is_true :
  hash_like_summaries_recorded ≡ true
hash_like_summaries_recorded_is_true =
  refl

toleranceObservedText : String
toleranceObservedText =
  "expected numeric tolerance field recorded by outputs/ns_pressure_tail_absorption_proxy_smoke.json"

maxGoodTailLoadObservedText : String
maxGoodTailLoadObservedText =
  "expected numeric max_good_tail_load field"

maxGoodAbsorptionRatioObservedText : String
maxGoodAbsorptionRatioObservedText =
  "expected numeric max_good_absorption_ratio <= 1"

minBadAbsorptionRatioObservedText : String
minBadAbsorptionRatioObservedText =
  "expected numeric min_bad_absorption_ratio > 1"

splitSummaryText : String
splitSummaryText =
  "good_pressure_tail_absorbed=2; bad_pressure_tail_unabsorbed=2"

hashLikeSummaryText : String
hashLikeSummaryText =
  "receipt_hash_like and profile_hash_like string summary fields are expected in the diagnostic JSON"

------------------------------------------------------------------------
-- Explicit non-promotion theorem flags.

pressureTailAbsorptionTheoremProved : Bool
pressureTailAbsorptionTheoremProved =
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

pressureTailAbsorptionTheoremProvedIsFalse :
  pressureTailAbsorptionTheoremProved ≡ false
pressureTailAbsorptionTheoremProvedIsFalse =
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

boundaryLocalizationTheoremNowTrue :
  Localization.localizedCutoffTheoremProved ≡ true
boundaryLocalizationTheoremNowTrue =
  refl

boundaryPressureCommutatorNowTrue :
  Localization.pressureCommutatorTheoremProved ≡ true
boundaryPressureCommutatorNowTrue =
  refl

boundaryA6StillFalse :
  Localization.triadicCompensatedLeakageIdentityProved ≡ false
boundaryA6StillFalse =
  refl

boundaryNSClayStillFalse :
  Localization.clayNavierStokesPromoted ≡ false
boundaryNSClayStillFalse =
  refl

boundaryTerminalStillFalse :
  Localization.terminalUnificationPromoted ≡ false
boundaryTerminalStillFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F summary.

controlO : String
controlO =
  "O: Lane 3 Newton Agda receipt for the finite NS pressure-tail absorption proxy harness."

controlR : String
controlR =
  "R: Record expected good pressure-tail absorption cases passing and bad unabsorbed-tail cases failing."

controlC : String
controlC =
  "C: DASHI.Physics.Closure.NSPressureTailAbsorptionProxyHarnessResult imports DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary and records scripts/ns_pressure_tail_absorption_proxy_harness.py with outputs/ns_pressure_tail_absorption_proxy_smoke.json."

controlS : String
controlS =
  "S: Diagnostic-only finite receipt; pressureTailAbsorptionTheoremProved=false, pressureCommutatorEstimateProved=false, localizationTheoremProved=false, A6Proved=false, nsClayPromoted=false, terminalPromotion=false."

controlL : String
controlL =
  "L: boundary false flags -> expected harness path/output path -> good/bad split labels -> tolerance/hash-like summaries -> fail-closed flags."

controlP : String
controlP =
  "P: Promote nothing; use only as expected executable bookkeeping for a synthetic pressure-tail absorption proxy."

controlG : String
controlG =
  "G: diagnostic_only=true; all theorem and promotion flags remain false."

controlF : String
controlF =
  "F: Missing analytic pressure-tail absorption theorem, pressure commutator estimate, localization theorem, A6 proof, NS Clay proof, and terminal promotion."

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

record NSPressureTailAbsorptionProxyHarnessResult : Set where
  field
    importedSupport :
      ImportedPressureTailAbsorptionProxySupport
    harnessFields :
      List PressureTailAbsorptionHarnessField
    harnessFieldCountProof :
      pressureTailAbsorptionHarnessFieldCount ≡ 12
    profileReceipts :
      List PressureTailAbsorptionProfileReceipt
    profileReceiptCountProof :
      pressureTailAbsorptionProfileReceiptCount ≡ 4
    checks :
      List PressureTailAbsorptionHarnessCheck
    checkCountProof :
      pressureTailAbsorptionHarnessCheckCount ≡ 10
    sourceHarness :
      String
    jsonReceipt :
      String
    scope :
      String
    expectedRunCommand :
      String
    status :
      String
    statusDiagnosticOnlyIsTrue :
      status_diagnostic_only ≡ true
    parameters :
      String
    absorptionProxyFormula :
      String
    goodLabel :
      String
    badLabel :
      String
    splitSummary :
      String
    tolerance :
      String
    maxGoodTailLoad :
      String
    maxGoodAbsorptionRatio :
      String
    minBadAbsorptionRatio :
      String
    numericSummaryFields :
      String
    stringSummaryFields :
      String
    hashLikeReceiptSummary :
      String
    hashLikeProfileSummary :
      String
    hashLikeSummary :
      String
    okObservedIsTrue :
      ok_observed ≡ true
    diagnosticOnlyIsTrue :
      diagnostic_only ≡ true
    promotionIsFalse :
      promotion ≡ false
    clayPromotedIsFalse :
      clay_promoted ≡ false
    goodProfilesIncludedIsTrue :
      good_profiles_included ≡ true
    badProfilesIncludedIsTrue :
      bad_profiles_included ≡ true
    allGoodProfilesPassIsTrue :
      all_good_profiles_pass ≡ true
    badProfilesFailVisiblyIsTrue :
      bad_profiles_fail_visibly ≡ true
    toleranceSlotRecordedIsTrue :
      tolerance_slot_recorded ≡ true
    numericSummariesRecordedIsTrue :
      numeric_summaries_recorded ≡ true
    stringSummariesRecordedIsTrue :
      string_summaries_recorded ≡ true
    hashLikeSummariesRecordedIsTrue :
      hash_like_summaries_recorded ≡ true
    pressureTailAbsorptionTheoremProvedFalse :
      pressureTailAbsorptionTheoremProved ≡ false
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

open NSPressureTailAbsorptionProxyHarnessResult public

canonicalNSPressureTailAbsorptionProxyHarnessResult :
  NSPressureTailAbsorptionProxyHarnessResult
canonicalNSPressureTailAbsorptionProxyHarnessResult =
  record
    { importedSupport =
        canonicalImportedPressureTailAbsorptionProxySupport
    ; harnessFields =
        canonicalPressureTailAbsorptionHarnessFields
    ; harnessFieldCountProof =
        refl
    ; profileReceipts =
        canonicalPressureTailAbsorptionProfileReceipts
    ; profileReceiptCountProof =
        refl
    ; checks =
        canonicalPressureTailAbsorptionHarnessChecks
    ; checkCountProof =
        refl
    ; sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        jsonReceiptPath
    ; scope =
        receiptScope
    ; expectedRunCommand =
        expectedRunCommandText
    ; status =
        expectedStatusText
    ; statusDiagnosticOnlyIsTrue =
        refl
    ; parameters =
        defaultParameterText
    ; absorptionProxyFormula =
        absorptionProxyFormulaText
    ; goodLabel =
        goodSplitLabel
    ; badLabel =
        badSplitLabel
    ; splitSummary =
        splitSummaryText
    ; tolerance =
        toleranceObservedText
    ; maxGoodTailLoad =
        maxGoodTailLoadObservedText
    ; maxGoodAbsorptionRatio =
        maxGoodAbsorptionRatioObservedText
    ; minBadAbsorptionRatio =
        minBadAbsorptionRatioObservedText
    ; numericSummaryFields =
        summaryNumericFieldsText
    ; stringSummaryFields =
        summaryStringFieldsText
    ; hashLikeReceiptSummary =
        receiptHashLikeText
    ; hashLikeProfileSummary =
        profileHashLikeText
    ; hashLikeSummary =
        hashLikeSummaryText
    ; okObservedIsTrue =
        refl
    ; diagnosticOnlyIsTrue =
        refl
    ; promotionIsFalse =
        refl
    ; clayPromotedIsFalse =
        refl
    ; goodProfilesIncludedIsTrue =
        refl
    ; badProfilesIncludedIsTrue =
        refl
    ; allGoodProfilesPassIsTrue =
        refl
    ; badProfilesFailVisiblyIsTrue =
        refl
    ; toleranceSlotRecordedIsTrue =
        refl
    ; numericSummariesRecordedIsTrue =
        refl
    ; stringSummariesRecordedIsTrue =
        refl
    ; hashLikeSummariesRecordedIsTrue =
        refl
    ; pressureTailAbsorptionTheoremProvedFalse =
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
