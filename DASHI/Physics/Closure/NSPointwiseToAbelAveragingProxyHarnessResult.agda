module DASHI.Physics.Closure.NSPointwiseToAbelAveragingProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ns_pointwise_to_abel_averaging_proxy_harness.py
--
-- The harness is a finite diagnostic for the NS A6 bookkeeping target:
--
--   localized pointwise stretching omega dot S omega
--     -> shell diagonal mean lambda * (2 kappa^2 - 1)
--     -> Abel/log-window average with LLN-like residual
--
-- It records two LLN-like arcsine-neutral profiles passing the proxy
-- tolerance and a deliberately correlated positive-bias profile failing
-- visibly.  This module records that executable result only.  It does not
-- prove a PDE pointwise-to-Abel theorem, prove the A6 leakage identity,
-- prove residual depletion, solve NS Clay, or promote terminal unification.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary
  as Pointwise

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
  "scripts/ns_pointwise_to_abel_averaging_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_pointwise_to_abel_averaging_proxy_harness.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ns_pointwise_to_abel_averaging_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_synthetic_pointwise_to_abel_averaging_proxy_not_pde_proof"

runCommandText : String
runCommandText =
  "python scripts/ns_pointwise_to_abel_averaging_proxy_harness.py --json-output outputs/ns_pointwise_to_abel_averaging_proxy_harness.json --json"

manifestCommandText : String
manifestCommandText =
  "python scripts/ns_pointwise_to_abel_averaging_proxy_harness.py --json-output outputs/local_clay_harness_manifest_children/ns_pointwise_to_abel_averaging_proxy_smoke.json --json"

defaultParameterText : String
defaultParameterText =
  "shells=22, samples_per_shell=192, window=7, abel_rho=0.76, offdiag_scale=0.10, lln_multiplier=3.0, seed=20260608"

llnToleranceObservedText : String
llnToleranceObservedText =
  "lln_tolerance = 3 / sqrt(7 * 192) ~= 0.08183170883849715"

pointwiseProxyFormulaText : String
pointwiseProxyFormulaText =
  "pointwise_proxy_mean = mean(lambda * (2*kappa^2 - 1) + offdiag)"

abelWindowFormulaText : String
abelWindowFormulaText =
  "Abel window weights are proportional to rho ^ abs(index - center), rho=0.76"

------------------------------------------------------------------------
-- Imported A6 boundary support.

pointwiseToAbelBoundaryReference : String
pointwiseToAbelBoundaryReference =
  "DASHI.Physics.Closure.NSPointwiseToAbelAveragingBoundary"

pointwiseToAbelBoundaryImported : Bool
pointwiseToAbelBoundaryImported =
  true

record ImportedPointwiseToAbelProxySupport : Set where
  field
    pointwiseToAbelBoundary :
      Pointwise.NSPointwiseToAbelAveragingBoundary
    pointwiseToAbelBoundaryIsCanonical :
      pointwiseToAbelBoundary
        ≡ Pointwise.canonicalNSPointwiseToAbelAveragingBoundary
    pointwiseToAbelBoundaryImportedIsTrue :
      pointwiseToAbelBoundaryImported ≡ true
    importedBoundaryKeepsPointwiseToAbelOpen :
      Pointwise.pointwiseToAbelAveragingProved ≡ false
    importedBoundaryKeepsAbelLLNOpen :
      Pointwise.abelLLNMixingProved ≡ false
    importedBoundaryKeepsResidualDepletionOpen :
      Pointwise.residualDepletionProved ≡ false
    importedBoundaryKeepsClayFalse :
      Pointwise.clayNavierStokesPromoted ≡ false
    importedBoundaryKeepsTerminalFalse :
      Pointwise.terminalUnificationPromoted ≡ false

canonicalImportedPointwiseToAbelProxySupport :
  ImportedPointwiseToAbelProxySupport
canonicalImportedPointwiseToAbelProxySupport =
  record
    { pointwiseToAbelBoundary =
        Pointwise.canonicalNSPointwiseToAbelAveragingBoundary
    ; pointwiseToAbelBoundaryIsCanonical =
        refl
    ; pointwiseToAbelBoundaryImportedIsTrue =
        refl
    ; importedBoundaryKeepsPointwiseToAbelOpen =
        refl
    ; importedBoundaryKeepsAbelLLNOpen =
        refl
    ; importedBoundaryKeepsResidualDepletionOpen =
        refl
    ; importedBoundaryKeepsClayFalse =
        refl
    ; importedBoundaryKeepsTerminalFalse =
        refl
    }

------------------------------------------------------------------------
-- Top-level harness fields.

data PointwiseToAbelHarnessField : Set where
  harnessField :
    PointwiseToAbelHarnessField
  diagnosticOnlyField :
    PointwiseToAbelHarnessField
  promotionField :
    PointwiseToAbelHarnessField
  clayPromotedField :
    PointwiseToAbelHarnessField
  controlField :
    PointwiseToAbelHarnessField
  parametersField :
    PointwiseToAbelHarnessField
  summaryField :
    PointwiseToAbelHarnessField
  checksField :
    PointwiseToAbelHarnessField
  profilesField :
    PointwiseToAbelHarnessField
  interpretationField :
    PointwiseToAbelHarnessField

canonicalPointwiseToAbelHarnessFields :
  List PointwiseToAbelHarnessField
canonicalPointwiseToAbelHarnessFields =
  harnessField
  ∷ diagnosticOnlyField
  ∷ promotionField
  ∷ clayPromotedField
  ∷ controlField
  ∷ parametersField
  ∷ summaryField
  ∷ checksField
  ∷ profilesField
  ∷ interpretationField
  ∷ []

pointwiseToAbelHarnessFieldCount : Nat
pointwiseToAbelHarnessFieldCount =
  listLength canonicalPointwiseToAbelHarnessFields

pointwiseToAbelHarnessFieldCountIs10 :
  pointwiseToAbelHarnessFieldCount ≡ 10
pointwiseToAbelHarnessFieldCountIs10 =
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

data PointwiseToAbelProxyProfile : Set where
  llnExactArcsineCentered :
    PointwiseToAbelProxyProfile
  llnJitteredArcsineCentered :
    PointwiseToAbelProxyProfile
  badCorrelatedPositiveBias :
    PointwiseToAbelProxyProfile

profileName : PointwiseToAbelProxyProfile → String
profileName llnExactArcsineCentered =
  "lln_exact_arcsine_centered"
profileName llnJitteredArcsineCentered =
  "lln_jittered_arcsine_centered"
profileName badCorrelatedPositiveBias =
  "bad_correlated_positive_bias"

profileDescription : PointwiseToAbelProxyProfile → String
profileDescription llnExactArcsineCentered =
  "Arcsine-neutral kappa grid with exactly centered off-diagonal shell noise."
profileDescription llnJitteredArcsineCentered =
  "Stratified arcsine samples with shell-dependent jitter and centered off-diagonal noise."
profileDescription badCorrelatedPositiveBias =
  "Deliberately bad profile: kappa^2 is biased above 1/2 and off-diagonal drift is positive."

expectedLLNGood : PointwiseToAbelProxyProfile → Bool
expectedLLNGood llnExactArcsineCentered =
  true
expectedLLNGood llnJitteredArcsineCentered =
  true
expectedLLNGood badCorrelatedPositiveBias =
  false

expectedProfilePasses : PointwiseToAbelProxyProfile → Bool
expectedProfilePasses llnExactArcsineCentered =
  true
expectedProfilePasses llnJitteredArcsineCentered =
  true
expectedProfilePasses badCorrelatedPositiveBias =
  false

profileClassification : PointwiseToAbelProxyProfile → String
profileClassification llnExactArcsineCentered =
  "lln_like_abel_averaging_proxy"
profileClassification llnJitteredArcsineCentered =
  "lln_like_abel_averaging_proxy"
profileClassification badCorrelatedPositiveBias =
  "bad_correlated_counterprofile"

canonicalPointwiseToAbelProfiles :
  List PointwiseToAbelProxyProfile
canonicalPointwiseToAbelProfiles =
  llnExactArcsineCentered
  ∷ llnJitteredArcsineCentered
  ∷ badCorrelatedPositiveBias
  ∷ []

canonicalGoodLLNProfiles :
  List PointwiseToAbelProxyProfile
canonicalGoodLLNProfiles =
  llnExactArcsineCentered
  ∷ llnJitteredArcsineCentered
  ∷ []

canonicalBadProfiles :
  List PointwiseToAbelProxyProfile
canonicalBadProfiles =
  badCorrelatedPositiveBias
  ∷ []

pointwiseToAbelProfileCount : Nat
pointwiseToAbelProfileCount =
  listLength canonicalPointwiseToAbelProfiles

goodLLNProfileCount : Nat
goodLLNProfileCount =
  listLength canonicalGoodLLNProfiles

badProfileCount : Nat
badProfileCount =
  listLength canonicalBadProfiles

pointwiseToAbelProfileCountIs3 :
  pointwiseToAbelProfileCount ≡ 3
pointwiseToAbelProfileCountIs3 =
  refl

goodLLNProfileCountIs2 :
  goodLLNProfileCount ≡ 2
goodLLNProfileCountIs2 =
  refl

badProfileCountIs1 :
  badProfileCount ≡ 1
badProfileCountIs1 =
  refl

record PointwiseToAbelProfileReceipt : Set where
  field
    profile :
      PointwiseToAbelProxyProfile
    name :
      String
    description :
      String
    expectedLLNLikeGood :
      Bool
    passedTolerance :
      Bool
    expectedPassedTolerance :
      Bool
    passedToleranceIsExpected :
      passedTolerance ≡ expectedPassedTolerance
    classification :
      String
    llnTolerance :
      String
    maxAbsAbelPointwiseMean :
      String
    maxAbsAbelDiagonalMean :
      String
    maxAbsAbelOffdiagMean :
      String
    windowsWithinToleranceFraction :
      String
    promotionForProfile :
      Bool
    promotionForProfileIsFalse :
      promotionForProfile ≡ false

open PointwiseToAbelProfileReceipt public

llnExactArcsineCenteredReceipt :
  PointwiseToAbelProfileReceipt
llnExactArcsineCenteredReceipt =
  record
    { profile =
        llnExactArcsineCentered
    ; name =
        profileName llnExactArcsineCentered
    ; description =
        profileDescription llnExactArcsineCentered
    ; expectedLLNLikeGood =
        true
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification llnExactArcsineCentered
    ; llnTolerance =
        "0.08183170883849715"
    ; maxAbsAbelPointwiseMean =
        "3.242392691296249e-17"
    ; maxAbsAbelDiagonalMean =
        "3.32814655944353e-17"
    ; maxAbsAbelOffdiagMean =
        "7.650518842402487e-19"
    ; windowsWithinToleranceFraction =
        "1.0"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

llnJitteredArcsineCenteredReceipt :
  PointwiseToAbelProfileReceipt
llnJitteredArcsineCenteredReceipt =
  record
    { profile =
        llnJitteredArcsineCentered
    ; name =
        profileName llnJitteredArcsineCentered
    ; description =
        profileDescription llnJitteredArcsineCentered
    ; expectedLLNLikeGood =
        true
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification llnJitteredArcsineCentered
    ; llnTolerance =
        "0.08183170883849715"
    ; maxAbsAbelPointwiseMean =
        "0.0004341115060124321"
    ; maxAbsAbelDiagonalMean =
        "0.00043411150601243193"
    ; maxAbsAbelOffdiagMean =
        "9.649346489724173e-19"
    ; windowsWithinToleranceFraction =
        "1.0"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

badCorrelatedPositiveBiasReceipt :
  PointwiseToAbelProfileReceipt
badCorrelatedPositiveBiasReceipt =
  record
    { profile =
        badCorrelatedPositiveBias
    ; name =
        profileName badCorrelatedPositiveBias
    ; description =
        profileDescription badCorrelatedPositiveBias
    ; expectedLLNLikeGood =
        false
    ; passedTolerance =
        false
    ; expectedPassedTolerance =
        false
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification badCorrelatedPositiveBias
    ; llnTolerance =
        "0.08183170883849715"
    ; maxAbsAbelPointwiseMean =
        "0.239702004669976"
    ; maxAbsAbelDiagonalMean =
        "0.1614913980646996"
    ; maxAbsAbelOffdiagMean =
        "0.0782106066052764"
    ; windowsWithinToleranceFraction =
        "0.0"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

canonicalPointwiseToAbelProfileReceipts :
  List PointwiseToAbelProfileReceipt
canonicalPointwiseToAbelProfileReceipts =
  llnExactArcsineCenteredReceipt
  ∷ llnJitteredArcsineCenteredReceipt
  ∷ badCorrelatedPositiveBiasReceipt
  ∷ []

pointwiseToAbelProfileReceiptCount : Nat
pointwiseToAbelProfileReceiptCount =
  listLength canonicalPointwiseToAbelProfileReceipts

pointwiseToAbelProfileReceiptCountIs3 :
  pointwiseToAbelProfileReceiptCount ≡ 3
pointwiseToAbelProfileReceiptCountIs3 =
  refl

llnExactProfilePassed :
  passedTolerance llnExactArcsineCenteredReceipt ≡ true
llnExactProfilePassed =
  refl

llnJitteredProfilePassed :
  passedTolerance llnJitteredArcsineCenteredReceipt ≡ true
llnJitteredProfilePassed =
  refl

badCorrelatedProfileFailed :
  passedTolerance badCorrelatedPositiveBiasReceipt ≡ false
badCorrelatedProfileFailed =
  refl

------------------------------------------------------------------------
-- Harness checks, tolerance, and error fields.

data PointwiseToAbelHarnessCheck : Set where
  goodProfilesIncludedCheck :
    PointwiseToAbelHarnessCheck
  badProfileIncludedCheck :
    PointwiseToAbelHarnessCheck
  allGoodProfilesPassCheck :
    PointwiseToAbelHarnessCheck
  badProfileFailsVisiblyCheck :
    PointwiseToAbelHarnessCheck
  allProfileLocalChecksPassCheck :
    PointwiseToAbelHarnessCheck
  promotionFalseCheck :
    PointwiseToAbelHarnessCheck

canonicalPointwiseToAbelHarnessChecks :
  List PointwiseToAbelHarnessCheck
canonicalPointwiseToAbelHarnessChecks =
  goodProfilesIncludedCheck
  ∷ badProfileIncludedCheck
  ∷ allGoodProfilesPassCheck
  ∷ badProfileFailsVisiblyCheck
  ∷ allProfileLocalChecksPassCheck
  ∷ promotionFalseCheck
  ∷ []

pointwiseToAbelHarnessCheckCount : Nat
pointwiseToAbelHarnessCheckCount =
  listLength canonicalPointwiseToAbelHarnessChecks

pointwiseToAbelHarnessCheckCountIs6 :
  pointwiseToAbelHarnessCheckCount ≡ 6
pointwiseToAbelHarnessCheckCountIs6 =
  refl

good_profiles_included : Bool
good_profiles_included =
  true

bad_profile_included : Bool
bad_profile_included =
  true

all_good_profiles_pass : Bool
all_good_profiles_pass =
  true

bad_profile_fails_visibly : Bool
bad_profile_fails_visibly =
  true

all_profile_local_checks_pass : Bool
all_profile_local_checks_pass =
  true

finite_shell_rows_observed : Bool
finite_shell_rows_observed =
  true

window_rows_present_observed : Bool
window_rows_present_observed =
  true

lln_tolerance_recorded : Bool
lln_tolerance_recorded =
  true

abel_pointwise_error_fields_recorded : Bool
abel_pointwise_error_fields_recorded =
  true

diagonal_error_fields_recorded : Bool
diagonal_error_fields_recorded =
  true

offdiag_error_fields_recorded : Bool
offdiag_error_fields_recorded =
  true

good_profiles_included_is_true :
  good_profiles_included ≡ true
good_profiles_included_is_true =
  refl

bad_profile_included_is_true :
  bad_profile_included ≡ true
bad_profile_included_is_true =
  refl

all_good_profiles_pass_is_true :
  all_good_profiles_pass ≡ true
all_good_profiles_pass_is_true =
  refl

bad_profile_fails_visibly_is_true :
  bad_profile_fails_visibly ≡ true
bad_profile_fails_visibly_is_true =
  refl

all_profile_local_checks_pass_is_true :
  all_profile_local_checks_pass ≡ true
all_profile_local_checks_pass_is_true =
  refl

finite_shell_rows_observed_is_true :
  finite_shell_rows_observed ≡ true
finite_shell_rows_observed_is_true =
  refl

window_rows_present_observed_is_true :
  window_rows_present_observed ≡ true
window_rows_present_observed_is_true =
  refl

lln_tolerance_recorded_is_true :
  lln_tolerance_recorded ≡ true
lln_tolerance_recorded_is_true =
  refl

abel_pointwise_error_fields_recorded_is_true :
  abel_pointwise_error_fields_recorded ≡ true
abel_pointwise_error_fields_recorded_is_true =
  refl

diagonal_error_fields_recorded_is_true :
  diagonal_error_fields_recorded ≡ true
diagonal_error_fields_recorded_is_true =
  refl

offdiag_error_fields_recorded_is_true :
  offdiag_error_fields_recorded ≡ true
offdiag_error_fields_recorded_is_true =
  refl

summaryProfilesText : String
summaryProfilesText =
  "profiles=3, good_profiles=2, bad_profiles=1"

summaryToleranceText : String
summaryToleranceText =
  "lln_tolerance=0.08183170883849715"

summaryGoodErrorText : String
summaryGoodErrorText =
  "max_good_abs_abel_pointwise_mean=0.0004341115060124321 <= tolerance"

summaryBadErrorText : String
summaryBadErrorText =
  "max_bad_abs_abel_pointwise_mean=0.239702004669976 > 2 * tolerance"

goodProfileMeaningText : String
goodProfileMeaningText =
  "Arcsine-neutral kappa samples make lambda*(2*kappa^2-1) shell means small, and centered off-diagonal terms stay within a 1/sqrt(window*samples) proxy scale."

badProfileMeaningText : String
badProfileMeaningText =
  "The correlated profile biases kappa^2 above 1/2 and adds positive off-diagonal drift, so Abel averaging does not remove the pointwise stretching proxy."

------------------------------------------------------------------------
-- Explicit fail-closed theorem and promotion flags.

data PointwiseToAbelHarnessNonClaimBoundary : Set where
  syntheticProxyOnlyNotPDETheorem :
    PointwiseToAbelHarnessNonClaimBoundary
  noPDEPointwiseToAbelTheorem :
    PointwiseToAbelHarnessNonClaimBoundary
  noA6CompensatedLeakageIdentity :
    PointwiseToAbelHarnessNonClaimBoundary
  noResidualDepletionClosure :
    PointwiseToAbelHarnessNonClaimBoundary
  noNavierStokesClayPromotion :
    PointwiseToAbelHarnessNonClaimBoundary
  noTerminalUnificationPromotion :
    PointwiseToAbelHarnessNonClaimBoundary

canonicalPointwiseToAbelHarnessNonClaimBoundaries :
  List PointwiseToAbelHarnessNonClaimBoundary
canonicalPointwiseToAbelHarnessNonClaimBoundaries =
  syntheticProxyOnlyNotPDETheorem
  ∷ noPDEPointwiseToAbelTheorem
  ∷ noA6CompensatedLeakageIdentity
  ∷ noResidualDepletionClosure
  ∷ noNavierStokesClayPromotion
  ∷ noTerminalUnificationPromotion
  ∷ []

pointwiseToAbelHarnessNonClaimBoundaryCount : Nat
pointwiseToAbelHarnessNonClaimBoundaryCount =
  listLength canonicalPointwiseToAbelHarnessNonClaimBoundaries

pointwiseToAbelHarnessNonClaimBoundaryCountIs6 :
  pointwiseToAbelHarnessNonClaimBoundaryCount ≡ 6
pointwiseToAbelHarnessNonClaimBoundaryCountIs6 =
  refl

pde_pointwise_to_abel_theorem_proved : Bool
pde_pointwise_to_abel_theorem_proved =
  false

a6_leakage_identity_proved : Bool
a6_leakage_identity_proved =
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

pde_pointwise_to_abel_theorem_proved_is_false :
  pde_pointwise_to_abel_theorem_proved ≡ false
pde_pointwise_to_abel_theorem_proved_is_false =
  refl

a6_leakage_identity_proved_is_false :
  a6_leakage_identity_proved ≡ false
a6_leakage_identity_proved_is_false =
  refl

residual_depletion_proved_is_false :
  residual_depletion_proved ≡ false
residual_depletion_proved_is_false =
  refl

ns_clay_promoted_is_false :
  ns_clay_promoted ≡ false
ns_clay_promoted_is_false =
  refl

terminal_promotion_is_false :
  terminal_promotion ≡ false
terminal_promotion_is_false =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record NSPointwiseToAbelAveragingProxyHarnessResult : Set where
  field
    importedSupport :
      ImportedPointwiseToAbelProxySupport
    harnessFields :
      List PointwiseToAbelHarnessField
    harnessFieldCountProof :
      pointwiseToAbelHarnessFieldCount ≡ 10
    profileReceipts :
      List PointwiseToAbelProfileReceipt
    profileReceiptCountProof :
      pointwiseToAbelProfileReceiptCount ≡ 3
    checks :
      List PointwiseToAbelHarnessCheck
    checkCountProof :
      pointwiseToAbelHarnessCheckCount ≡ 6
    nonClaimBoundaries :
      List PointwiseToAbelHarnessNonClaimBoundary
    nonClaimBoundaryCountProof :
      pointwiseToAbelHarnessNonClaimBoundaryCount ≡ 6
    sourceHarness :
      String
    jsonReceipt :
      String
    manifestChildReceipt :
      String
    scope :
      String
    parameters :
      String
    tolerance :
      String
    pointwiseProxyFormula :
      String
    abelWindowFormula :
      String
    summaryProfiles :
      String
    summaryTolerance :
      String
    summaryGoodError :
      String
    summaryBadError :
      String
    goodProfileMeaning :
      String
    badProfileMeaning :
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
    badProfileIncludedIsTrue :
      bad_profile_included ≡ true
    allGoodProfilesPassIsTrue :
      all_good_profiles_pass ≡ true
    badProfileFailsVisiblyIsTrue :
      bad_profile_fails_visibly ≡ true
    allProfileLocalChecksPassIsTrue :
      all_profile_local_checks_pass ≡ true
    finiteShellRowsObservedIsTrue :
      finite_shell_rows_observed ≡ true
    windowRowsPresentObservedIsTrue :
      window_rows_present_observed ≡ true
    toleranceRecordedIsTrue :
      lln_tolerance_recorded ≡ true
    pointwiseErrorFieldsRecordedIsTrue :
      abel_pointwise_error_fields_recorded ≡ true
    diagonalErrorFieldsRecordedIsTrue :
      diagonal_error_fields_recorded ≡ true
    offdiagErrorFieldsRecordedIsTrue :
      offdiag_error_fields_recorded ≡ true
    pdePointwiseToAbelTheoremProvedIsFalse :
      pde_pointwise_to_abel_theorem_proved ≡ false
    a6LeakageIdentityProvedIsFalse :
      a6_leakage_identity_proved ≡ false
    residualDepletionProvedIsFalse :
      residual_depletion_proved ≡ false
    nsClayPromotedIsFalse :
      ns_clay_promoted ≡ false
    terminalPromotionIsFalse :
      terminal_promotion ≡ false

open NSPointwiseToAbelAveragingProxyHarnessResult public

canonicalNSPointwiseToAbelAveragingProxyHarnessResult :
  NSPointwiseToAbelAveragingProxyHarnessResult
canonicalNSPointwiseToAbelAveragingProxyHarnessResult =
  record
    { importedSupport =
        canonicalImportedPointwiseToAbelProxySupport
    ; harnessFields =
        canonicalPointwiseToAbelHarnessFields
    ; harnessFieldCountProof =
        refl
    ; profileReceipts =
        canonicalPointwiseToAbelProfileReceipts
    ; profileReceiptCountProof =
        refl
    ; checks =
        canonicalPointwiseToAbelHarnessChecks
    ; checkCountProof =
        refl
    ; nonClaimBoundaries =
        canonicalPointwiseToAbelHarnessNonClaimBoundaries
    ; nonClaimBoundaryCountProof =
        refl
    ; sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        jsonReceiptPath
    ; manifestChildReceipt =
        manifestChildReceiptPath
    ; scope =
        receiptScope
    ; parameters =
        defaultParameterText
    ; tolerance =
        llnToleranceObservedText
    ; pointwiseProxyFormula =
        pointwiseProxyFormulaText
    ; abelWindowFormula =
        abelWindowFormulaText
    ; summaryProfiles =
        summaryProfilesText
    ; summaryTolerance =
        summaryToleranceText
    ; summaryGoodError =
        summaryGoodErrorText
    ; summaryBadError =
        summaryBadErrorText
    ; goodProfileMeaning =
        goodProfileMeaningText
    ; badProfileMeaning =
        badProfileMeaningText
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
    ; badProfileIncludedIsTrue =
        refl
    ; allGoodProfilesPassIsTrue =
        refl
    ; badProfileFailsVisiblyIsTrue =
        refl
    ; allProfileLocalChecksPassIsTrue =
        refl
    ; finiteShellRowsObservedIsTrue =
        refl
    ; windowRowsPresentObservedIsTrue =
        refl
    ; toleranceRecordedIsTrue =
        refl
    ; pointwiseErrorFieldsRecordedIsTrue =
        refl
    ; diagonalErrorFieldsRecordedIsTrue =
        refl
    ; offdiagErrorFieldsRecordedIsTrue =
        refl
    ; pdePointwiseToAbelTheoremProvedIsFalse =
        refl
    ; a6LeakageIdentityProvedIsFalse =
        refl
    ; residualDepletionProvedIsFalse =
        refl
    ; nsClayPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    }

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F summary.

controlO : String
controlO =
  "O: Local NS A6 pointwise-to-Abel averaging proxy diagnostic."

controlR : String
controlR =
  "R: Simulate diagonal lambda*(2*kappa^2-1), off-diagonal terms, and Abel shell averages."

controlC : String
controlC =
  "C: scripts/ns_pointwise_to_abel_averaging_proxy_harness.py"

controlS : String
controlS =
  "S: Synthetic shell model only; no PDE Abel LLN or leakage identity is proved."

controlL : String
controlL =
  "L: shell samples -> diagonal/offdiag means -> Abel windows -> good/bad classification"

controlP : String
controlP =
  "P: LLN-like arcsine-neutral profiles pass; correlated positive-bias profile fails visibly."

controlG : String
controlG =
  "G: promotion=false, clay_promoted=false, terminal_promotion=false."

controlF : String
controlF =
  "F: Does not prove pointwise-to-Abel replacement, A6 leakage identity, residual depletion, NS Clay, or terminal promotion."

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
