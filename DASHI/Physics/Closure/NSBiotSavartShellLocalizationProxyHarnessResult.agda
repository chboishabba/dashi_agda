module DASHI.Physics.Closure.NSBiotSavartShellLocalizationProxyHarnessResult where

-- Fail-closed receipt for the NS A6.2 Biot-Savart shell-localization
-- diagnostic.
--
-- The intended harness checks a finite proxy for the estimate:
--
--   same-shell Biot-Savart strain dominates the diagonal LP strain term,
--   while frequency-separated, tail-heavy, or nonlocal counterprofiles fail.
--
-- This module records the executable receipt shape only.  It does not prove
-- the Biot-Savart shell-localization estimate, close the A6 diagonal
-- pointwise-to-Abel transfer, prove the triadic compensated leakage identity,
-- solve Navier-Stokes, or promote terminal unification.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

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
-- Harness identity and expected outputs.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ns_biot_savart_shell_localization_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_biot_savart_shell_localization_proxy_harness.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ns_biot_savart_shell_localization_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_synthetic_biot_savart_shell_localization_proxy_not_pde_proof"

expectedRunCommandText : String
expectedRunCommandText =
  "python scripts/ns_biot_savart_shell_localization_proxy_harness.py --json-output outputs/ns_biot_savart_shell_localization_proxy_harness.json --json"

expectedManifestCommandText : String
expectedManifestCommandText =
  "python scripts/ns_biot_savart_shell_localization_proxy_harness.py --json-output outputs/local_clay_harness_manifest_children/ns_biot_savart_shell_localization_proxy_smoke.json --json"

targetEstimateText : String
targetEstimateText =
  "||P_j S - L_j[P_j u]||_{L2->L2} <= C * 2^{-delta j} * ||u||_{L^{3,infty}}"

diagnosticSeparationText : String
diagnosticSeparationText =
  "Good same-shell localized profiles pass; bad frequency-separated, tail-heavy, and nonlocal plateau profiles fail."

------------------------------------------------------------------------
-- Expected receipt fields.

data NSBiotSavartShellLocalizationReceiptField : Set where
  harnessPathField :
    NSBiotSavartShellLocalizationReceiptField
  jsonOutputField :
    NSBiotSavartShellLocalizationReceiptField
  manifestChildOutputField :
    NSBiotSavartShellLocalizationReceiptField
  targetEstimateField :
    NSBiotSavartShellLocalizationReceiptField
  profileSeparationField :
    NSBiotSavartShellLocalizationReceiptField
  okObservedField :
    NSBiotSavartShellLocalizationReceiptField
  diagnosticOnlyField :
    NSBiotSavartShellLocalizationReceiptField
  promotionField :
    NSBiotSavartShellLocalizationReceiptField
  theoremFlagsField :
    NSBiotSavartShellLocalizationReceiptField
  governanceField :
    NSBiotSavartShellLocalizationReceiptField

expectedReceiptFields :
  List NSBiotSavartShellLocalizationReceiptField
expectedReceiptFields =
  harnessPathField
  ∷ jsonOutputField
  ∷ manifestChildOutputField
  ∷ targetEstimateField
  ∷ profileSeparationField
  ∷ okObservedField
  ∷ diagnosticOnlyField
  ∷ promotionField
  ∷ theoremFlagsField
  ∷ governanceField
  ∷ []

expectedReceiptFieldCount : Nat
expectedReceiptFieldCount =
  listLength expectedReceiptFields

expectedReceiptFieldCountIs10 :
  expectedReceiptFieldCount ≡ 10
expectedReceiptFieldCountIs10 =
  refl

------------------------------------------------------------------------
-- Good/bad profile separation recorded by the diagnostic.

data NSBiotSavartShellLocalizationProfile : Set where
  goodSmoothSameShell :
    NSBiotSavartShellLocalizationProfile
  goodAbelWindowLocalized :
    NSBiotSavartShellLocalizationProfile
  badSeparatedShellTail :
    NSBiotSavartShellLocalizationProfile
  badNonlocalPlateau :
    NSBiotSavartShellLocalizationProfile

profileName :
  NSBiotSavartShellLocalizationProfile →
  String
profileName goodSmoothSameShell =
  "good_smooth_same_shell"
profileName goodAbelWindowLocalized =
  "good_abel_window_localized"
profileName badSeparatedShellTail =
  "bad_separated_shell_tail"
profileName badNonlocalPlateau =
  "bad_nonlocal_plateau"

profileDescription :
  NSBiotSavartShellLocalizationProfile →
  String
profileDescription goodSmoothSameShell =
  "Smooth same-shell Biot-Savart strain proxy with decay in the localized shell error."
profileDescription goodAbelWindowLocalized =
  "Abel-window localized shell profile with stable diagonal strain ownership."
profileDescription badSeparatedShellTail =
  "Deliberately bad profile: separated shells leave a visible nonlocal tail."
profileDescription badNonlocalPlateau =
  "Deliberately bad profile: nonlocal plateau prevents shell-local domination."

expectedGoodProfile :
  NSBiotSavartShellLocalizationProfile →
  Bool
expectedGoodProfile goodSmoothSameShell =
  true
expectedGoodProfile goodAbelWindowLocalized =
  true
expectedGoodProfile badSeparatedShellTail =
  false
expectedGoodProfile badNonlocalPlateau =
  false

expectedPasses :
  NSBiotSavartShellLocalizationProfile →
  Bool
expectedPasses goodSmoothSameShell =
  true
expectedPasses goodAbelWindowLocalized =
  true
expectedPasses badSeparatedShellTail =
  false
expectedPasses badNonlocalPlateau =
  false

profileClassification :
  NSBiotSavartShellLocalizationProfile →
  String
profileClassification goodSmoothSameShell =
  "good_same_shell_localization_proxy"
profileClassification goodAbelWindowLocalized =
  "good_abel_window_shell_localization_proxy"
profileClassification badSeparatedShellTail =
  "bad_frequency_separation_counterprofile"
profileClassification badNonlocalPlateau =
  "bad_nonlocal_plateau_counterprofile"

canonicalProfiles :
  List NSBiotSavartShellLocalizationProfile
canonicalProfiles =
  goodSmoothSameShell
  ∷ goodAbelWindowLocalized
  ∷ badSeparatedShellTail
  ∷ badNonlocalPlateau
  ∷ []

canonicalGoodProfiles :
  List NSBiotSavartShellLocalizationProfile
canonicalGoodProfiles =
  goodSmoothSameShell
  ∷ goodAbelWindowLocalized
  ∷ []

canonicalBadProfiles :
  List NSBiotSavartShellLocalizationProfile
canonicalBadProfiles =
  badSeparatedShellTail
  ∷ badNonlocalPlateau
  ∷ []

profileCount : Nat
profileCount =
  listLength canonicalProfiles

goodProfileCount : Nat
goodProfileCount =
  listLength canonicalGoodProfiles

badProfileCount : Nat
badProfileCount =
  listLength canonicalBadProfiles

profileCountIs4 :
  profileCount ≡ 4
profileCountIs4 =
  refl

goodProfileCountIs2 :
  goodProfileCount ≡ 2
goodProfileCountIs2 =
  refl

badProfileCountIs2 :
  badProfileCount ≡ 2
badProfileCountIs2 =
  refl

record NSBiotSavartShellLocalizationProfileReceipt : Set where
  field
    profile :
      NSBiotSavartShellLocalizationProfile
    name :
      String
    description :
      String
    expectedGood :
      Bool
    passedTolerance :
      Bool
    expectedPassedTolerance :
      Bool
    passedToleranceIsExpected :
      passedTolerance ≡ expectedPassedTolerance
    classification :
      String
    separationSummary :
      String
    promotionForProfile :
      Bool
    promotionForProfileIsFalse :
      promotionForProfile ≡ false

open NSBiotSavartShellLocalizationProfileReceipt public

goodSmoothSameShellReceipt :
  NSBiotSavartShellLocalizationProfileReceipt
goodSmoothSameShellReceipt =
  record
    { profile =
        goodSmoothSameShell
    ; name =
        profileName goodSmoothSameShell
    ; description =
        profileDescription goodSmoothSameShell
    ; expectedGood =
        true
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification goodSmoothSameShell
    ; separationSummary =
        "same-shell smooth profile is expected below the localization error tolerance"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

goodAbelWindowLocalizedReceipt :
  NSBiotSavartShellLocalizationProfileReceipt
goodAbelWindowLocalizedReceipt =
  record
    { profile =
        goodAbelWindowLocalized
    ; name =
        profileName goodAbelWindowLocalized
    ; description =
        profileDescription goodAbelWindowLocalized
    ; expectedGood =
        true
    ; passedTolerance =
        true
    ; expectedPassedTolerance =
        true
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification goodAbelWindowLocalized
    ; separationSummary =
        "Abel-window localized profile is expected below the shell-localization tolerance"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

badSeparatedShellTailReceipt :
  NSBiotSavartShellLocalizationProfileReceipt
badSeparatedShellTailReceipt =
  record
    { profile =
        badSeparatedShellTail
    ; name =
        profileName badSeparatedShellTail
    ; description =
        profileDescription badSeparatedShellTail
    ; expectedGood =
        false
    ; passedTolerance =
        false
    ; expectedPassedTolerance =
        false
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification badSeparatedShellTail
    ; separationSummary =
        "frequency-separated shell tail is expected to fail the diagnostic visibly"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

badNonlocalPlateauReceipt :
  NSBiotSavartShellLocalizationProfileReceipt
badNonlocalPlateauReceipt =
  record
    { profile =
        badNonlocalPlateau
    ; name =
        profileName badNonlocalPlateau
    ; description =
        profileDescription badNonlocalPlateau
    ; expectedGood =
        false
    ; passedTolerance =
        false
    ; expectedPassedTolerance =
        false
    ; passedToleranceIsExpected =
        refl
    ; classification =
        profileClassification badNonlocalPlateau
    ; separationSummary =
        "nonlocal plateau profile is expected to fail the diagnostic visibly"
    ; promotionForProfile =
        false
    ; promotionForProfileIsFalse =
        refl
    }

canonicalProfileReceipts :
  List NSBiotSavartShellLocalizationProfileReceipt
canonicalProfileReceipts =
  goodSmoothSameShellReceipt
  ∷ goodAbelWindowLocalizedReceipt
  ∷ badSeparatedShellTailReceipt
  ∷ badNonlocalPlateauReceipt
  ∷ []

profileReceiptCount : Nat
profileReceiptCount =
  listLength canonicalProfileReceipts

profileReceiptCountIs4 :
  profileReceiptCount ≡ 4
profileReceiptCountIs4 =
  refl

goodSmoothSameShellPasses :
  passedTolerance goodSmoothSameShellReceipt ≡ true
goodSmoothSameShellPasses =
  refl

goodAbelWindowLocalizedPasses :
  passedTolerance goodAbelWindowLocalizedReceipt ≡ true
goodAbelWindowLocalizedPasses =
  refl

badSeparatedShellTailFails :
  passedTolerance badSeparatedShellTailReceipt ≡ false
badSeparatedShellTailFails =
  refl

badNonlocalPlateauFails :
  passedTolerance badNonlocalPlateauReceipt ≡ false
badNonlocalPlateauFails =
  refl

------------------------------------------------------------------------
-- Observed flags and fail-closed theorem gates.

okObserved : Bool
okObserved =
  true

diagnosticOnly : Bool
diagnosticOnly =
  true

promotion : Bool
promotion =
  false

biotSavartShellLocalizationEstimateProved : Bool
biotSavartShellLocalizationEstimateProved =
  false

diagonalPointwiseToAbelTransferProved : Bool
diagonalPointwiseToAbelTransferProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

residualDepletionProved : Bool
residualDepletionProved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

okObservedIsTrue :
  okObserved ≡ true
okObservedIsTrue =
  refl

diagnosticOnlyIsTrue :
  diagnosticOnly ≡ true
diagnosticOnlyIsTrue =
  refl

promotionIsFalse :
  promotion ≡ false
promotionIsFalse =
  refl

biotSavartShellLocalizationEstimateProvedIsFalse :
  biotSavartShellLocalizationEstimateProved ≡ false
biotSavartShellLocalizationEstimateProvedIsFalse =
  refl

diagonalPointwiseToAbelTransferProvedIsFalse :
  diagonalPointwiseToAbelTransferProved ≡ false
diagonalPointwiseToAbelTransferProvedIsFalse =
  refl

triadicCompensatedLeakageIdentityProvedIsFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
triadicCompensatedLeakageIdentityProvedIsFalse =
  refl

residualDepletionProvedIsFalse :
  residualDepletionProved ≡ false
residualDepletionProvedIsFalse =
  refl

nsClayPromotedIsFalse :
  nsClayPromoted ≡ false
nsClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Composite receipt.

record NSBiotSavartShellLocalizationProxyHarnessResult : Set where
  field
    sourceHarness :
      String
    jsonOutput :
      String
    manifestChildOutput :
      String
    targetEstimate :
      String
    profileSeparation :
      String
    expectedFields :
      List NSBiotSavartShellLocalizationReceiptField
    profileReceipts :
      List NSBiotSavartShellLocalizationProfileReceipt
    okObservedFlag :
      Bool
    okObservedFlagIsTrue :
      okObservedFlag ≡ true
    diagnosticOnlyFlag :
      Bool
    diagnosticOnlyFlagIsTrue :
      diagnosticOnlyFlag ≡ true
    promotionFlag :
      Bool
    promotionFlagIsFalse :
      promotionFlag ≡ false
    biotSavartShellLocalizationEstimateProvedFalse :
      biotSavartShellLocalizationEstimateProved ≡ false
    diagonalPointwiseToAbelTransferProvedFalse :
      diagonalPointwiseToAbelTransferProved ≡ false
    triadicCompensatedLeakageIdentityProvedFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualDepletionProvedFalse :
      residualDepletionProved ≡ false
    nsClayPromotedFalse :
      nsClayPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    interpretation :
      String

canonicalNSBiotSavartShellLocalizationProxyHarnessResult :
  NSBiotSavartShellLocalizationProxyHarnessResult
canonicalNSBiotSavartShellLocalizationProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; jsonOutput =
        jsonReceiptPath
    ; manifestChildOutput =
        manifestChildReceiptPath
    ; targetEstimate =
        targetEstimateText
    ; profileSeparation =
        diagnosticSeparationText
    ; expectedFields =
        expectedReceiptFields
    ; profileReceipts =
        canonicalProfileReceipts
    ; okObservedFlag =
        okObserved
    ; okObservedFlagIsTrue =
        refl
    ; diagnosticOnlyFlag =
        diagnosticOnly
    ; diagnosticOnlyFlagIsTrue =
        refl
    ; promotionFlag =
        promotion
    ; promotionFlagIsFalse =
        refl
    ; biotSavartShellLocalizationEstimateProvedFalse =
        refl
    ; diagonalPointwiseToAbelTransferProvedFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedFalse =
        refl
    ; residualDepletionProvedFalse =
        refl
    ; nsClayPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; interpretation =
        "Finite diagnostic receipt only: good/bad Biot-Savart shell-localization proxy separation is recorded, with no A6.2 theorem, A6 leakage identity, NS Clay proof, or terminal promotion."
    }

------------------------------------------------------------------------
-- Governance card.

formalModelSummary : String
formalModelSummary =
  "O Worker C owns NSBiotSavartShellLocalizationProxyHarnessResult only; R bind A6.2 proxy harness paths and fail-closed good/bad separation; C single Agda receipt module; S diagnosticOnly=true, promotion=false, theorem flags false; L diagnostic receipt -> A6.2 theorem only after real CZ shell-localization proof; P keep self-contained non-promoting receipt; G no Everything/docs/script edit in this lane; F missing Biot-Savart shell-localization estimate, diagonal pointwise-to-Abel transfer, A6, residual depletion, NS Clay, and terminal promotion."

premisesSummary : String
premisesSummary =
  "Premises: current A6 map names Biot-Savart shell localization as the remaining A6.2 diagnostic target; proxy receipts in DASHI/Physics/Closure keep diagnostic and promotion flags explicit."

traceSummary : String
traceSummary =
  "Trace: harness path + output paths + four profile receipts + fail-closed theorem flags -> typecheckable Agda proxy receipt."

conclusionSummary : String
conclusionSummary =
  "Conclusion: NS A6.2 Biot-Savart shell-localization diagnostic result is represented as a non-promoting receipt."

promotionDecision : String
promotionDecision =
  "hold"
