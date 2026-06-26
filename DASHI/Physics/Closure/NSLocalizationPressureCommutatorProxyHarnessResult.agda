module DASHI.Physics.Closure.NSLocalizationPressureCommutatorProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ns_localization_pressure_commutator_proxy_harness.py
--
-- The harness is a finite diagnostic for the NS A6 localization pressure /
-- commutator bookkeeping target:
--
--   localized cutoff profile + pressure localization
--     -> pressure tail error + cutoff/pressure commutator error
--     -> refinement-decay proxy for good localized profiles
--
-- It records compact/Schwartz localized profiles passing the proxy tolerance
-- and deliberately bad pressure-tail/cutoff-commutator plateau profiles
-- failing visibly.  This module records that executable result only.  It does
-- not prove a localization theorem, prove a pressure commutator theorem, prove
-- A6, prove residual depletion, solve NS Clay, or promote terminal unification.

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
-- Harness identity and run configuration.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ns_localization_pressure_commutator_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_localization_pressure_commutator_proxy_harness.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ns_localization_pressure_commutator_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_synthetic_localization_pressure_commutator_proxy_not_pde_proof"

runCommandText : String
runCommandText =
  "python scripts/ns_localization_pressure_commutator_proxy_harness.py --json-output outputs/ns_localization_pressure_commutator_proxy_harness.json --json"

manifestCommandText : String
manifestCommandText =
  "python scripts/ns_localization_pressure_commutator_proxy_harness.py --json-output outputs/local_clay_harness_manifest_children/ns_localization_pressure_commutator_proxy_smoke.json --json"

defaultParameterText : String
defaultParameterText =
  "refinements=9, base_cutoff_radius=1.0, localization_width=0.36, tolerance=0.0025, good_decay_factor=0.35, bad_min_error=0.06"

pressureTailFormulaText : String
pressureTailFormulaText =
  "pressure_tail_error is a deterministic positive proxy error per refinement row"

cutoffCommutatorFormulaText : String
cutoffCommutatorFormulaText =
  "cutoff_commutator_error is a deterministic positive proxy error per refinement row"

combinedErrorFormulaText : String
combinedErrorFormulaText =
  "combined_error = max(pressure_tail_error, cutoff_commutator_error)"

------------------------------------------------------------------------
-- Imported localization/pressure boundary support.

localizationPressureBoundaryReference : String
localizationPressureBoundaryReference =
  "DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary"

localizationPressureBoundaryImported : Bool
localizationPressureBoundaryImported =
  true

record ImportedLocalizationPressureProxySupport : Set where
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

canonicalImportedLocalizationPressureProxySupport :
  ImportedLocalizationPressureProxySupport
canonicalImportedLocalizationPressureProxySupport =
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

data LocalizationPressureHarnessField : Set where
  harnessField :
    LocalizationPressureHarnessField
  okField :
    LocalizationPressureHarnessField
  promotionField :
    LocalizationPressureHarnessField
  parametersField :
    LocalizationPressureHarnessField
  toleranceField :
    LocalizationPressureHarnessField
  maxGoodErrorField :
    LocalizationPressureHarnessField
  minBadErrorField :
    LocalizationPressureHarnessField
  validationFlagsField :
    LocalizationPressureHarnessField
  goodCaseSummariesField :
    LocalizationPressureHarnessField
  badCaseSummariesField :
    LocalizationPressureHarnessField
  interpretationField :
    LocalizationPressureHarnessField

canonicalLocalizationPressureHarnessFields :
  List LocalizationPressureHarnessField
canonicalLocalizationPressureHarnessFields =
  harnessField
  ∷ okField
  ∷ promotionField
  ∷ parametersField
  ∷ toleranceField
  ∷ maxGoodErrorField
  ∷ minBadErrorField
  ∷ validationFlagsField
  ∷ goodCaseSummariesField
  ∷ badCaseSummariesField
  ∷ interpretationField
  ∷ []

localizationPressureHarnessFieldCount : Nat
localizationPressureHarnessFieldCount =
  listLength canonicalLocalizationPressureHarnessFields

localizationPressureHarnessFieldCountIs11 :
  localizationPressureHarnessFieldCount ≡ 11
localizationPressureHarnessFieldCountIs11 =
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

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

clay_promoted_is_false :
  clay_promoted ≡ false
clay_promoted_is_false =
  refl

------------------------------------------------------------------------
-- Profile observations.

data LocalizationPressureProxyProfile : Set where
  goodCompactPressureShell :
    LocalizationPressureProxyProfile
  goodSchwartzTailShell :
    LocalizationPressureProxyProfile
  badPressureTailPlateau :
    LocalizationPressureProxyProfile
  badCutoffCommutatorPlateau :
    LocalizationPressureProxyProfile

profileName : LocalizationPressureProxyProfile → String
profileName goodCompactPressureShell =
  "good_compact_pressure_shell"
profileName goodSchwartzTailShell =
  "good_schwartz_tail_shell"
profileName badPressureTailPlateau =
  "bad_pressure_tail_plateau"
profileName badCutoffCommutatorPlateau =
  "bad_cutoff_commutator_plateau"

profileDescription : LocalizationPressureProxyProfile → String
profileDescription goodCompactPressureShell =
  "Localized shell with compact pressure support after cutoff refinement."
profileDescription goodSchwartzTailShell =
  "Rapidly decaying pressure tail with a smooth cutoff transition."
profileDescription badPressureTailPlateau =
  "Deliberately bad profile: pressure tail remains large under refinement."
profileDescription badCutoffCommutatorPlateau =
  "Deliberately bad profile: cutoff commutator does not localize away."

expectedLocalizedGood : LocalizationPressureProxyProfile → Bool
expectedLocalizedGood goodCompactPressureShell =
  true
expectedLocalizedGood goodSchwartzTailShell =
  true
expectedLocalizedGood badPressureTailPlateau =
  false
expectedLocalizedGood badCutoffCommutatorPlateau =
  false

expectedProfilePasses : LocalizationPressureProxyProfile → Bool
expectedProfilePasses goodCompactPressureShell =
  true
expectedProfilePasses goodSchwartzTailShell =
  true
expectedProfilePasses badPressureTailPlateau =
  false
expectedProfilePasses badCutoffCommutatorPlateau =
  false

profileClassification : LocalizationPressureProxyProfile → String
profileClassification goodCompactPressureShell =
  "good_localized_shell_decay"
profileClassification goodSchwartzTailShell =
  "good_localized_shell_decay"
profileClassification badPressureTailPlateau =
  "bad_localization_obstruction_visible"
profileClassification badCutoffCommutatorPlateau =
  "bad_localization_obstruction_visible"

canonicalLocalizationPressureProfiles :
  List LocalizationPressureProxyProfile
canonicalLocalizationPressureProfiles =
  goodCompactPressureShell
  ∷ goodSchwartzTailShell
  ∷ badPressureTailPlateau
  ∷ badCutoffCommutatorPlateau
  ∷ []

canonicalGoodLocalizedProfiles :
  List LocalizationPressureProxyProfile
canonicalGoodLocalizedProfiles =
  goodCompactPressureShell
  ∷ goodSchwartzTailShell
  ∷ []

canonicalBadPlateauProfiles :
  List LocalizationPressureProxyProfile
canonicalBadPlateauProfiles =
  badPressureTailPlateau
  ∷ badCutoffCommutatorPlateau
  ∷ []

localizationPressureProfileCount : Nat
localizationPressureProfileCount =
  listLength canonicalLocalizationPressureProfiles

goodLocalizedProfileCount : Nat
goodLocalizedProfileCount =
  listLength canonicalGoodLocalizedProfiles

badPlateauProfileCount : Nat
badPlateauProfileCount =
  listLength canonicalBadPlateauProfiles

localizationPressureProfileCountIs4 :
  localizationPressureProfileCount ≡ 4
localizationPressureProfileCountIs4 =
  refl

goodLocalizedProfileCountIs2 :
  goodLocalizedProfileCount ≡ 2
goodLocalizedProfileCountIs2 =
  refl

badPlateauProfileCountIs2 :
  badPlateauProfileCount ≡ 2
badPlateauProfileCountIs2 =
  refl

record LocalizationPressureProfileReceipt : Set where
  field
    profile :
      LocalizationPressureProxyProfile
    name :
      String
    description :
      String
    expectedGoodLocalized :
      Bool
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
    initialError :
      String
    finalError :
      String
    maxError :
      String
    minError :
      String
    decayRatio :
      String
    pressureTailFinal :
      String
    cutoffCommutatorFinal :
      String
    promotionForProfile :
      Bool
    promotionForProfileIsFalse :
      promotionForProfile ≡ false

open LocalizationPressureProfileReceipt public

goodCompactPressureShellReceipt :
  LocalizationPressureProfileReceipt
goodCompactPressureShellReceipt =
  record
    { profile =
        goodCompactPressureShell
    ; name =
        profileName goodCompactPressureShell
    ; description =
        profileDescription goodCompactPressureShell
    ; expectedGoodLocalized =
        true
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification goodCompactPressureShell
    ; tolerance =
        "0.0025"
    ; initialError =
        "0.4"
    ; finalError =
        "0.0003619614641874121"
    ; maxError =
        "0.4"
    ; minError =
        "0.0003619614641874121"
    ; decayRatio =
        "0.0009049036604685302"
    ; pressureTailFinal =
        "0.0002544793838154021"
    ; cutoffCommutatorFinal =
        "0.0003619614641874121"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

goodSchwartzTailShellReceipt :
  LocalizationPressureProfileReceipt
goodSchwartzTailShellReceipt =
  record
    { profile =
        goodSchwartzTailShell
    ; name =
        profileName goodSchwartzTailShell
    ; description =
        profileDescription goodSchwartzTailShell
    ; expectedGoodLocalized =
        true
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification goodSchwartzTailShell
    ; tolerance =
        "0.0025"
    ; initialError =
        "0.021545027233536036"
    ; finalError =
        "5.586734481912861e-05"
    ; maxError =
        "0.021545027233536036"
    ; minError =
        "5.586734481912861e-05"
    ; decayRatio =
        "0.002593050554708419"
    ; pressureTailFinal =
        "3.2e-05"
    ; cutoffCommutatorFinal =
        "5.586734481912861e-05"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

badPressureTailPlateauReceipt :
  LocalizationPressureProfileReceipt
badPressureTailPlateauReceipt =
  record
    { profile =
        badPressureTailPlateau
    ; name =
        profileName badPressureTailPlateau
    ; description =
        profileDescription badPressureTailPlateau
    ; expectedGoodLocalized =
        false
    ; passedTolerance =
        false
    ; expectedPassedTolerance =
        false
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification badPressureTailPlateau
    ; tolerance =
        "0.0025"
    ; initialError =
        "0.115"
    ; finalError =
        "0.11639859045820593"
    ; maxError =
        "0.12699488323649807"
    ; minError =
        "0.10304602469396992"
    ; decayRatio =
        "1.0121616561583124"
    ; pressureTailFinal =
        "0.11639859045820593"
    ; cutoffCommutatorFinal =
        "0.005999999999999999"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

badCutoffCommutatorPlateauReceipt :
  LocalizationPressureProfileReceipt
badCutoffCommutatorPlateauReceipt =
  record
    { profile =
        badCutoffCommutatorPlateau
    ; name =
        profileName badCutoffCommutatorPlateau
    ; description =
        profileDescription badCutoffCommutatorPlateau
    ; expectedGoodLocalized =
        false
    ; passedTolerance =
        false
    ; expectedPassedTolerance =
        false
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification badCutoffCommutatorPlateau
    ; tolerance =
        "0.0025"
    ; initialError =
        "0.102"
    ; finalError =
        "0.0997556587851025"
    ; maxError =
        "0.102"
    ; minError =
        "0.08257777659331342"
    ; decayRatio =
        "0.9779966547559069"
    ; pressureTailFinal =
        "0.0009227636589744574"
    ; cutoffCommutatorFinal =
        "0.0997556587851025"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

canonicalLocalizationPressureProfileReceipts :
  List LocalizationPressureProfileReceipt
canonicalLocalizationPressureProfileReceipts =
  goodCompactPressureShellReceipt
  ∷ goodSchwartzTailShellReceipt
  ∷ badPressureTailPlateauReceipt
  ∷ badCutoffCommutatorPlateauReceipt
  ∷ []

localizationPressureProfileReceiptCount : Nat
localizationPressureProfileReceiptCount =
  listLength canonicalLocalizationPressureProfileReceipts

localizationPressureProfileReceiptCountIs4 :
  localizationPressureProfileReceiptCount ≡ 4
localizationPressureProfileReceiptCountIs4 =
  refl

goodCompactProfilePassed :
  passedTolerance goodCompactPressureShellReceipt ≡ true
goodCompactProfilePassed =
  refl

goodSchwartzProfilePassed :
  passedTolerance goodSchwartzTailShellReceipt ≡ true
goodSchwartzProfilePassed =
  refl

badPressureTailProfileFailed :
  passedTolerance badPressureTailPlateauReceipt ≡ false
badPressureTailProfileFailed =
  refl

badCutoffCommutatorProfileFailed :
  passedTolerance badCutoffCommutatorPlateauReceipt ≡ false
badCutoffCommutatorProfileFailed =
  refl

------------------------------------------------------------------------
-- Harness checks, tolerance, and error fields.

data LocalizationPressureHarnessCheck : Set where
  goodProfilesIncludedCheck :
    LocalizationPressureHarnessCheck
  badProfilesIncludedCheck :
    LocalizationPressureHarnessCheck
  goodProfilesDecayUnderRefinementCheck :
    LocalizationPressureHarnessCheck
  badProfilesStayLargeCheck :
    LocalizationPressureHarnessCheck
  maxGoodErrorWithinToleranceCheck :
    LocalizationPressureHarnessCheck
  minBadErrorAboveToleranceCheck :
    LocalizationPressureHarnessCheck
  finiteNonnegativeErrorsCheck :
    LocalizationPressureHarnessCheck
  allProfilesClassifiedAsExpectedCheck :
    LocalizationPressureHarnessCheck
  promotionFalseCheck :
    LocalizationPressureHarnessCheck

canonicalLocalizationPressureHarnessChecks :
  List LocalizationPressureHarnessCheck
canonicalLocalizationPressureHarnessChecks =
  goodProfilesIncludedCheck
  ∷ badProfilesIncludedCheck
  ∷ goodProfilesDecayUnderRefinementCheck
  ∷ badProfilesStayLargeCheck
  ∷ maxGoodErrorWithinToleranceCheck
  ∷ minBadErrorAboveToleranceCheck
  ∷ finiteNonnegativeErrorsCheck
  ∷ allProfilesClassifiedAsExpectedCheck
  ∷ promotionFalseCheck
  ∷ []

localizationPressureHarnessCheckCount : Nat
localizationPressureHarnessCheckCount =
  listLength canonicalLocalizationPressureHarnessChecks

localizationPressureHarnessCheckCountIs9 :
  localizationPressureHarnessCheckCount ≡ 9
localizationPressureHarnessCheckCountIs9 =
  refl

toleranceObservedText : String
toleranceObservedText =
  "0.0025"

maxGoodErrorObservedText : String
maxGoodErrorObservedText =
  "0.0003619614641874121"

minBadErrorObservedText : String
minBadErrorObservedText =
  "0.08257777659331342"

goodProfileFinalErrorsText : String
goodProfileFinalErrorsText =
  "good_compact_pressure_shell=0.0003619614641874121; good_schwartz_tail_shell=5.586734481912861e-05"

badProfileMinimumErrorsText : String
badProfileMinimumErrorsText =
  "bad_pressure_tail_plateau=0.10304602469396992; bad_cutoff_commutator_plateau=0.08257777659331342"

all_profiles_classified_as_expected : Bool
all_profiles_classified_as_expected =
  true

good_profiles_decay_under_refinement : Bool
good_profiles_decay_under_refinement =
  true

bad_profiles_stay_large : Bool
bad_profiles_stay_large =
  true

max_good_error_within_tolerance : Bool
max_good_error_within_tolerance =
  true

min_bad_error_above_tolerance : Bool
min_bad_error_above_tolerance =
  true

finite_nonnegative_errors : Bool
finite_nonnegative_errors =
  true

promotion_false_flag : Bool
promotion_false_flag =
  true

allProfilesClassifiedAsExpectedIsTrue :
  all_profiles_classified_as_expected ≡ true
allProfilesClassifiedAsExpectedIsTrue =
  refl

goodProfilesDecayUnderRefinementIsTrue :
  good_profiles_decay_under_refinement ≡ true
goodProfilesDecayUnderRefinementIsTrue =
  refl

badProfilesStayLargeIsTrue :
  bad_profiles_stay_large ≡ true
badProfilesStayLargeIsTrue =
  refl

maxGoodErrorWithinToleranceIsTrue :
  max_good_error_within_tolerance ≡ true
maxGoodErrorWithinToleranceIsTrue =
  refl

minBadErrorAboveToleranceIsTrue :
  min_bad_error_above_tolerance ≡ true
minBadErrorAboveToleranceIsTrue =
  refl

finiteNonnegativeErrorsIsTrue :
  finite_nonnegative_errors ≡ true
finiteNonnegativeErrorsIsTrue =
  refl

promotionFalseFlagIsTrue :
  promotion_false_flag ≡ true
promotionFalseFlagIsTrue =
  refl

------------------------------------------------------------------------
-- Explicit non-promotion theorem flags.

localization_theorem_proved : Bool
localization_theorem_proved =
  false

pressure_commutator_theorem_proved : Bool
pressure_commutator_theorem_proved =
  false

a6_proved : Bool
a6_proved =
  false

residual_depletion_proved : Bool
residual_depletion_proved =
  false

ns_clay_promoted : Bool
ns_clay_promoted =
  false

terminal_promotion : Bool
terminal_promotion =
  false

localizationTheoremProvedIsFalse :
  localization_theorem_proved ≡ false
localizationTheoremProvedIsFalse =
  refl

pressureCommutatorTheoremProvedIsFalse :
  pressure_commutator_theorem_proved ≡ false
pressureCommutatorTheoremProvedIsFalse =
  refl

a6ProvedIsFalse :
  a6_proved ≡ false
a6ProvedIsFalse =
  refl

residualDepletionProvedIsFalse :
  residual_depletion_proved ≡ false
residualDepletionProvedIsFalse =
  refl

nsClayPromotedIsFalse :
  ns_clay_promoted ≡ false
nsClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminal_promotion ≡ false
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

boundaryResidualDepletionStillFalse :
  Localization.residualDepletionProved ≡ false
boundaryResidualDepletionStillFalse =
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
-- Control card and interpretation.

controlO : String
controlO =
  "Lane 2 Hardy Agda receipt for the finite NS localization pressure/commutator proxy harness."

controlR : String
controlR =
  "Record good compact/Schwartz localized profiles passing and bad pressure-tail/cutoff-commutator plateau profiles failing."

controlC : String
controlC =
  "DASHI.Physics.Closure.NSLocalizationPressureCommutatorProxyHarnessResult imports DASHI.Physics.Closure.NSLocalizationPressureCommutatorBoundary and records scripts/ns_localization_pressure_commutator_proxy_harness.py output."

controlS : String
controlS =
  "Finite stdlib proxy receipt; localization theorem=false, pressure commutator theorem=false, A6=false, residual depletion=false, NS Clay=false, terminal promotion=false."

controlL : String
controlL =
  "Boundary false flags -> deterministic harness profile summaries -> tolerance/error receipt -> fail-closed interpretation."

controlP : String
controlP =
  "Promote nothing; use the receipt only as compact executable evidence that the synthetic proxy separates decaying localized cases from plateau obstructions."

controlG : String
controlG =
  "promotion=false; passing proxy rows do not certify a PDE pressure localization theorem or Clay progress."

controlF : String
controlF =
  "Missing analytic work: true Leray pressure localization estimates, cutoff commutator bounds, A6 leakage control, and residual depletion for Navier-Stokes fields."

supportsInterpretation : String
supportsInterpretation =
  "Finite proxy localized shell profiles can separate refinement-decaying pressure/cutoff errors from persistent obstructions."

rejectsInterpretation : String
rejectsInterpretation =
  "Profiles with persistent pressure tails or cutoff commutators are not acceptable localization witnesses in this proxy."

residualGapInterpretation : String
residualGapInterpretation =
  "A real proof still needs analytic pressure-tail estimates and cutoff commutator bounds for Navier-Stokes fields."

record NSLocalizationPressureCommutatorProxyHarnessReceipt : Set where
  field
    importedSupport :
      ImportedLocalizationPressureProxySupport
    sourceHarness :
      String
    jsonReceipt :
      String
    manifestChildReceipt :
      String
    scope :
      String
    defaultParameters :
      String
    ok :
      Bool
    okIsTrue :
      ok ≡ true
    diagnosticOnly :
      Bool
    diagnosticOnlyIsTrue :
      diagnosticOnly ≡ true
    promotionObserved :
      Bool
    promotionObservedIsFalse :
      promotionObserved ≡ false
    clayPromotedObserved :
      Bool
    clayPromotedObservedIsFalse :
      clayPromotedObserved ≡ false
    profileReceipts :
      List LocalizationPressureProfileReceipt
    profileReceiptCount :
      listLength profileReceipts ≡ 4
    harnessChecks :
      List LocalizationPressureHarnessCheck
    harnessCheckCount :
      listLength harnessChecks ≡ 9
    toleranceObserved :
      String
    maxGoodErrorObserved :
      String
    minBadErrorObserved :
      String
    localizationTheoremFalse :
      localization_theorem_proved ≡ false
    pressureCommutatorTheoremFalse :
      pressure_commutator_theorem_proved ≡ false
    a6False :
      a6_proved ≡ false
    residualDepletionFalse :
      residual_depletion_proved ≡ false
    nsClayFalse :
      ns_clay_promoted ≡ false
    terminalPromotionFalse :
      terminal_promotion ≡ false
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

canonicalNSLocalizationPressureCommutatorProxyHarnessReceipt :
  NSLocalizationPressureCommutatorProxyHarnessReceipt
canonicalNSLocalizationPressureCommutatorProxyHarnessReceipt =
  record
    { importedSupport =
        canonicalImportedLocalizationPressureProxySupport
    ; sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        jsonReceiptPath
    ; manifestChildReceipt =
        manifestChildReceiptPath
    ; scope =
        receiptScope
    ; defaultParameters =
        defaultParameterText
    ; ok =
        ok_observed
    ; okIsTrue =
        refl
    ; diagnosticOnly =
        diagnostic_only
    ; diagnosticOnlyIsTrue =
        refl
    ; promotionObserved =
        promotion
    ; promotionObservedIsFalse =
        refl
    ; clayPromotedObserved =
        clay_promoted
    ; clayPromotedObservedIsFalse =
        refl
    ; profileReceipts =
        canonicalLocalizationPressureProfileReceipts
    ; profileReceiptCount =
        refl
    ; harnessChecks =
        canonicalLocalizationPressureHarnessChecks
    ; harnessCheckCount =
        refl
    ; toleranceObserved =
        toleranceObservedText
    ; maxGoodErrorObserved =
        maxGoodErrorObservedText
    ; minBadErrorObserved =
        minBadErrorObservedText
    ; localizationTheoremFalse =
        refl
    ; pressureCommutatorTheoremFalse =
        refl
    ; a6False =
        refl
    ; residualDepletionFalse =
        refl
    ; nsClayFalse =
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
