module DASHI.Physics.Closure.NSPressureLocalizationSubBudgetProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ns_pressure_localization_subbudget_proxy_harness.py
--
-- The harness is expected to aggregate the finite diagnostic pressure
-- localization sub-budget:
--
--   cutoff/Riesz commutator + local Calderon-Zygmund core
--     + harmonic pressure tail + pressure-tail absorption
--     + annular cutoff + epsilon-gradient absorption
--
-- into a good/bad synthetic split.  This module records only the executable
-- receipt shape and governance flags.  It does not prove the pressure
-- sub-budget, prove localization, prove the triadic compensated leakage
-- identity, prove residual nonpositivity, solve NS Clay, or promote terminal
-- unification.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary
  as ErrorBudget
import DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary
  as Contract
import DASHI.Physics.Closure.NSPressureLocalizationSubBudgetCompositeBoundary
  as SubBudget

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
  "scripts/ns_pressure_localization_subbudget_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_pressure_localization_subbudget_proxy_smoke.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ns_pressure_localization_subbudget_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_synthetic_pressure_localization_subbudget_proxy_not_pde_proof"

expectedRunCommandText : String
expectedRunCommandText =
  "python scripts/ns_pressure_localization_subbudget_proxy_harness.py --json-output outputs/ns_pressure_localization_subbudget_proxy_smoke.json --json"

expectedManifestCommandText : String
expectedManifestCommandText =
  "python scripts/ns_pressure_localization_subbudget_proxy_harness.py --json-output outputs/local_clay_harness_manifest_children/ns_pressure_localization_subbudget_proxy_smoke.json --json"

expectedStatusText : String
expectedStatusText =
  "diagnostic_only"

subBudgetFormulaText : String
subBudgetFormulaText =
  "pressure_localization_subbudget_proxy = cutoff_riesz + local_cz + harmonic_tail + pressure_tail + annular_cutoff + epsilon_gradient_absorption"

summaryNumericFieldsText : String
summaryNumericFieldsText =
  "tolerance, max_good_subbudget, min_bad_subbudget, component_count, profile_count"

summaryStringFieldsText : String
summaryStringFieldsText =
  "harness, output_path, status, good_split_labels, bad_split_labels, receipt_hash_like, profile_hash_like"

------------------------------------------------------------------------
-- Imported support.

pressureCommutatorContractReference : String
pressureCommutatorContractReference =
  "DASHI.Physics.Closure.NSPressureCommutatorEstimateContractBoundary"

nsa6ErrorBudgetCompositeReference : String
nsa6ErrorBudgetCompositeReference =
  "DASHI.Physics.Closure.NSA6ErrorBudgetCompositeBoundary"

pressureLocalizationSubBudgetCompositeReference : String
pressureLocalizationSubBudgetCompositeReference =
  "DASHI.Physics.Closure.NSPressureLocalizationSubBudgetCompositeBoundary"

pressureCommutatorContractImported : Bool
pressureCommutatorContractImported =
  true

nsa6ErrorBudgetCompositeImported : Bool
nsa6ErrorBudgetCompositeImported =
  true

pressureLocalizationSubBudgetCompositeImported : Bool
pressureLocalizationSubBudgetCompositeImported =
  true

record ImportedPressureLocalizationSubBudgetProxySupport : Set where
  field
    pressureCommutatorContract :
      Contract.NSPressureCommutatorEstimateContractBoundary
    pressureCommutatorContractIsCanonical :
      pressureCommutatorContract
        ≡ Contract.canonicalNSPressureCommutatorEstimateContractBoundary
    errorBudgetComposite :
      ErrorBudget.NSA6ErrorBudgetCompositeBoundary
    errorBudgetCompositeIsCanonical :
      errorBudgetComposite
        ≡ ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    pressureLocalizationSubBudgetComposite :
      SubBudget.NSPressureLocalizationSubBudgetCompositeBoundary
    pressureLocalizationSubBudgetCompositeIsCanonical :
      pressureLocalizationSubBudgetComposite
        ≡ SubBudget.canonicalNSPressureLocalizationSubBudgetCompositeBoundary
    pressureCommutatorContractImportedIsTrue :
      pressureCommutatorContractImported ≡ true
    nsa6ErrorBudgetCompositeImportedIsTrue :
      nsa6ErrorBudgetCompositeImported ≡ true
    pressureLocalizationSubBudgetCompositeImportedIsTrue :
      pressureLocalizationSubBudgetCompositeImported ≡ true
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
    importedBudgetKeepsResidualDepletionFalse :
      ErrorBudget.residualDepletionProved ≡ false
    importedBudgetKeepsNSClayFalse :
      ErrorBudget.nsClayPromoted ≡ false
    importedBudgetKeepsTerminalFalse :
      ErrorBudget.terminalPromotionPromoted ≡ false
    importedSubBudgetKeepsPressureSubBudgetFalse :
      SubBudget.pressureSubBudgetClosed ≡ false
    importedSubBudgetKeepsLocalizationFalse :
      SubBudget.localizationTheoremProved ≡ false
    importedSubBudgetKeepsA6False :
      SubBudget.triadicCompensatedLeakageIdentityProved ≡ false
    importedSubBudgetKeepsResidualFalse :
      SubBudget.residualNonPositiveProved ≡ false
    importedSubBudgetKeepsClayFalse :
      SubBudget.nsClayPromoted ≡ false
    importedSubBudgetKeepsTerminalFalse :
      SubBudget.terminalPromotion ≡ false

canonicalImportedPressureLocalizationSubBudgetProxySupport :
  ImportedPressureLocalizationSubBudgetProxySupport
canonicalImportedPressureLocalizationSubBudgetProxySupport =
  record
    { pressureCommutatorContract =
        Contract.canonicalNSPressureCommutatorEstimateContractBoundary
    ; pressureCommutatorContractIsCanonical =
        refl
    ; errorBudgetComposite =
        ErrorBudget.canonicalNSA6ErrorBudgetCompositeBoundary
    ; errorBudgetCompositeIsCanonical =
        refl
    ; pressureLocalizationSubBudgetComposite =
        SubBudget.canonicalNSPressureLocalizationSubBudgetCompositeBoundary
    ; pressureLocalizationSubBudgetCompositeIsCanonical =
        refl
    ; pressureCommutatorContractImportedIsTrue =
        refl
    ; nsa6ErrorBudgetCompositeImportedIsTrue =
        refl
    ; pressureLocalizationSubBudgetCompositeImportedIsTrue =
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
    ; importedBudgetKeepsResidualDepletionFalse =
        refl
    ; importedBudgetKeepsNSClayFalse =
        refl
    ; importedBudgetKeepsTerminalFalse =
        refl
    ; importedSubBudgetKeepsPressureSubBudgetFalse =
        refl
    ; importedSubBudgetKeepsLocalizationFalse =
        refl
    ; importedSubBudgetKeepsA6False =
        refl
    ; importedSubBudgetKeepsResidualFalse =
        refl
    ; importedSubBudgetKeepsClayFalse =
        refl
    ; importedSubBudgetKeepsTerminalFalse =
        refl
    }

------------------------------------------------------------------------
-- Expected harness fields.

data PressureLocalizationSubBudgetHarnessField : Set where
  harnessField :
    PressureLocalizationSubBudgetHarnessField
  outputPathField :
    PressureLocalizationSubBudgetHarnessField
  manifestChildPathField :
    PressureLocalizationSubBudgetHarnessField
  statusField :
    PressureLocalizationSubBudgetHarnessField
  diagnosticOnlyField :
    PressureLocalizationSubBudgetHarnessField
  okObservedField :
    PressureLocalizationSubBudgetHarnessField
  splitLabelsField :
    PressureLocalizationSubBudgetHarnessField
  componentBudgetField :
    PressureLocalizationSubBudgetHarnessField
  toleranceField :
    PressureLocalizationSubBudgetHarnessField
  numericSummaryField :
    PressureLocalizationSubBudgetHarnessField
  theoremFlagsField :
    PressureLocalizationSubBudgetHarnessField
  promotionFlagsField :
    PressureLocalizationSubBudgetHarnessField
  interpretationField :
    PressureLocalizationSubBudgetHarnessField

canonicalPressureLocalizationSubBudgetHarnessFields :
  List PressureLocalizationSubBudgetHarnessField
canonicalPressureLocalizationSubBudgetHarnessFields =
  harnessField
  ∷ outputPathField
  ∷ manifestChildPathField
  ∷ statusField
  ∷ diagnosticOnlyField
  ∷ okObservedField
  ∷ splitLabelsField
  ∷ componentBudgetField
  ∷ toleranceField
  ∷ numericSummaryField
  ∷ theoremFlagsField
  ∷ promotionFlagsField
  ∷ interpretationField
  ∷ []

pressureLocalizationSubBudgetHarnessFieldCount : Nat
pressureLocalizationSubBudgetHarnessFieldCount =
  listLength canonicalPressureLocalizationSubBudgetHarnessFields

pressureLocalizationSubBudgetHarnessFieldCountIs13 :
  pressureLocalizationSubBudgetHarnessFieldCount ≡ 13
pressureLocalizationSubBudgetHarnessFieldCountIs13 =
  refl

------------------------------------------------------------------------
-- Expected good/bad case names.

goodAllPressureComponentsAbsorbedLabel : String
goodAllPressureComponentsAbsorbedLabel =
  "good_all_pressure_components_absorbed"

goodTailAndCommutatorSeparatedLabel : String
goodTailAndCommutatorSeparatedLabel =
  "good_tail_and_commutator_separated"

goodEpsilonGradientAbsorptionLabel : String
goodEpsilonGradientAbsorptionLabel =
  "good_epsilon_gradient_absorption"

badCutoffRieszCommutatorLabel : String
badCutoffRieszCommutatorLabel =
  "bad_cutoff_riesz_commutator"

badHarmonicPressureTailLabel : String
badHarmonicPressureTailLabel =
  "bad_harmonic_pressure_tail"

badPressureTailUnabsorbedLabel : String
badPressureTailUnabsorbedLabel =
  "bad_pressure_tail_unabsorbed"

badEpsilonGradientOverspendLabel : String
badEpsilonGradientOverspendLabel =
  "bad_epsilon_gradient_overspend"

data PressureLocalizationSubBudgetProxyCase : Set where
  allPressureComponentsAbsorbedGood :
    PressureLocalizationSubBudgetProxyCase
  tailAndCommutatorSeparatedGood :
    PressureLocalizationSubBudgetProxyCase
  epsilonGradientAbsorptionGood :
    PressureLocalizationSubBudgetProxyCase
  cutoffRieszCommutatorBad :
    PressureLocalizationSubBudgetProxyCase
  harmonicPressureTailBad :
    PressureLocalizationSubBudgetProxyCase
  pressureTailUnabsorbedBad :
    PressureLocalizationSubBudgetProxyCase
  epsilonGradientOverspendBad :
    PressureLocalizationSubBudgetProxyCase

caseLabel : PressureLocalizationSubBudgetProxyCase → String
caseLabel allPressureComponentsAbsorbedGood =
  goodAllPressureComponentsAbsorbedLabel
caseLabel tailAndCommutatorSeparatedGood =
  goodTailAndCommutatorSeparatedLabel
caseLabel epsilonGradientAbsorptionGood =
  goodEpsilonGradientAbsorptionLabel
caseLabel cutoffRieszCommutatorBad =
  badCutoffRieszCommutatorLabel
caseLabel harmonicPressureTailBad =
  badHarmonicPressureTailLabel
caseLabel pressureTailUnabsorbedBad =
  badPressureTailUnabsorbedLabel
caseLabel epsilonGradientOverspendBad =
  badEpsilonGradientOverspendLabel

caseExpectedGood : PressureLocalizationSubBudgetProxyCase → Bool
caseExpectedGood allPressureComponentsAbsorbedGood =
  true
caseExpectedGood tailAndCommutatorSeparatedGood =
  true
caseExpectedGood epsilonGradientAbsorptionGood =
  true
caseExpectedGood cutoffRieszCommutatorBad =
  false
caseExpectedGood harmonicPressureTailBad =
  false
caseExpectedGood pressureTailUnabsorbedBad =
  false
caseExpectedGood epsilonGradientOverspendBad =
  false

caseExpectedBad : PressureLocalizationSubBudgetProxyCase → Bool
caseExpectedBad allPressureComponentsAbsorbedGood =
  false
caseExpectedBad tailAndCommutatorSeparatedGood =
  false
caseExpectedBad epsilonGradientAbsorptionGood =
  false
caseExpectedBad cutoffRieszCommutatorBad =
  true
caseExpectedBad harmonicPressureTailBad =
  true
caseExpectedBad pressureTailUnabsorbedBad =
  true
caseExpectedBad epsilonGradientOverspendBad =
  true

caseInterpretation : PressureLocalizationSubBudgetProxyCase → String
caseInterpretation allPressureComponentsAbsorbedGood =
  "Good synthetic row: every pressure/localization component remains below the aggregate sub-budget."
caseInterpretation tailAndCommutatorSeparatedGood =
  "Good synthetic row: cutoff/Riesz and pressure-tail pieces are separated and absorbed."
caseInterpretation epsilonGradientAbsorptionGood =
  "Good synthetic row: epsilon-gradient absorption stays within the finite proxy margin."
caseInterpretation cutoffRieszCommutatorBad =
  "Bad synthetic row: cutoff/Riesz commutator consumes the pressure-localization sub-budget."
caseInterpretation harmonicPressureTailBad =
  "Bad synthetic row: harmonic pressure tail remains too large for the absorption budget."
caseInterpretation pressureTailUnabsorbedBad =
  "Bad synthetic row: pressure tail is not absorbed into the lower-order route."
caseInterpretation epsilonGradientOverspendBad =
  "Bad synthetic row: epsilon-gradient absorption overspends the dissipation margin."

canonicalGoodPressureLocalizationSubBudgetCases :
  List PressureLocalizationSubBudgetProxyCase
canonicalGoodPressureLocalizationSubBudgetCases =
  allPressureComponentsAbsorbedGood
  ∷ tailAndCommutatorSeparatedGood
  ∷ epsilonGradientAbsorptionGood
  ∷ []

canonicalBadPressureLocalizationSubBudgetCases :
  List PressureLocalizationSubBudgetProxyCase
canonicalBadPressureLocalizationSubBudgetCases =
  cutoffRieszCommutatorBad
  ∷ harmonicPressureTailBad
  ∷ pressureTailUnabsorbedBad
  ∷ epsilonGradientOverspendBad
  ∷ []

canonicalPressureLocalizationSubBudgetCases :
  List PressureLocalizationSubBudgetProxyCase
canonicalPressureLocalizationSubBudgetCases =
  allPressureComponentsAbsorbedGood
  ∷ tailAndCommutatorSeparatedGood
  ∷ epsilonGradientAbsorptionGood
  ∷ cutoffRieszCommutatorBad
  ∷ harmonicPressureTailBad
  ∷ pressureTailUnabsorbedBad
  ∷ epsilonGradientOverspendBad
  ∷ []

goodPressureLocalizationSubBudgetCaseCount : Nat
goodPressureLocalizationSubBudgetCaseCount =
  listLength canonicalGoodPressureLocalizationSubBudgetCases

badPressureLocalizationSubBudgetCaseCount : Nat
badPressureLocalizationSubBudgetCaseCount =
  listLength canonicalBadPressureLocalizationSubBudgetCases

pressureLocalizationSubBudgetCaseCount : Nat
pressureLocalizationSubBudgetCaseCount =
  listLength canonicalPressureLocalizationSubBudgetCases

goodPressureLocalizationSubBudgetCaseCountIs3 :
  goodPressureLocalizationSubBudgetCaseCount ≡ 3
goodPressureLocalizationSubBudgetCaseCountIs3 =
  refl

badPressureLocalizationSubBudgetCaseCountIs4 :
  badPressureLocalizationSubBudgetCaseCount ≡ 4
badPressureLocalizationSubBudgetCaseCountIs4 =
  refl

pressureLocalizationSubBudgetCaseCountIs7 :
  pressureLocalizationSubBudgetCaseCount ≡ 7
pressureLocalizationSubBudgetCaseCountIs7 =
  refl

record PressureLocalizationSubBudgetCaseReceipt : Set where
  field
    profile :
      PressureLocalizationSubBudgetProxyCase
    label :
      String
    expectedGood :
      Bool
    expectedBad :
      Bool
    interpretation :
      String

canonicalCaseReceipt :
  PressureLocalizationSubBudgetProxyCase →
  PressureLocalizationSubBudgetCaseReceipt
canonicalCaseReceipt profile =
  record
    { profile =
        profile
    ; label =
        caseLabel profile
    ; expectedGood =
        caseExpectedGood profile
    ; expectedBad =
        caseExpectedBad profile
    ; interpretation =
        caseInterpretation profile
    }

------------------------------------------------------------------------
-- Observed and promotion flags.

ok_observed : Bool
ok_observed =
  true

diagnostic_only : Bool
diagnostic_only =
  true

promotion : Bool
promotion =
  false

pressureSubBudgetClosed : Bool
pressureSubBudgetClosed =
  false

localizationTheoremProved : Bool
localizationTheoremProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

residualNonpositiveProved : Bool
residualNonpositiveProved =
  false

nsClayPromoted : Bool
nsClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
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

pressureSubBudgetClosedIsFalse :
  pressureSubBudgetClosed ≡ false
pressureSubBudgetClosedIsFalse =
  refl

localizationTheoremProvedIsFalse :
  localizationTheoremProved ≡ false
localizationTheoremProvedIsFalse =
  refl

triadicCompensatedLeakageIdentityProvedIsFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
triadicCompensatedLeakageIdentityProvedIsFalse =
  refl

residualNonpositiveProvedIsFalse :
  residualNonpositiveProved ≡ false
residualNonpositiveProvedIsFalse =
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

record NSPressureLocalizationSubBudgetProxyHarnessResult : Set where
  field
    sourceHarness :
      String
    jsonOutput :
      String
    manifestChildOutput :
      String
    importedSupport :
      ImportedPressureLocalizationSubBudgetProxySupport
    expectedCases :
      List PressureLocalizationSubBudgetProxyCase
    goodCases :
      List PressureLocalizationSubBudgetProxyCase
    badCases :
      List PressureLocalizationSubBudgetProxyCase
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
    pressureSubBudgetClosedFalse :
      pressureSubBudgetClosed ≡ false
    localizationTheoremProvedFalse :
      localizationTheoremProved ≡ false
    triadicCompensatedLeakageIdentityProvedFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualNonpositiveProvedFalse :
      residualNonpositiveProved ≡ false
    nsClayPromotedFalse :
      nsClayPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    interpretation :
      String

canonicalNSPressureLocalizationSubBudgetProxyHarnessResult :
  NSPressureLocalizationSubBudgetProxyHarnessResult
canonicalNSPressureLocalizationSubBudgetProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; jsonOutput =
        jsonReceiptPath
    ; manifestChildOutput =
        manifestChildReceiptPath
    ; importedSupport =
        canonicalImportedPressureLocalizationSubBudgetProxySupport
    ; expectedCases =
        canonicalPressureLocalizationSubBudgetCases
    ; goodCases =
        canonicalGoodPressureLocalizationSubBudgetCases
    ; badCases =
        canonicalBadPressureLocalizationSubBudgetCases
    ; okObservedFlag =
        ok_observed
    ; okObservedFlagIsTrue =
        refl
    ; diagnosticOnlyFlag =
        diagnostic_only
    ; diagnosticOnlyFlagIsTrue =
        refl
    ; promotionFlag =
        promotion
    ; promotionFlagIsFalse =
        refl
    ; pressureSubBudgetClosedFalse =
        refl
    ; localizationTheoremProvedFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedFalse =
        refl
    ; residualNonpositiveProvedFalse =
        refl
    ; nsClayPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; interpretation =
        "Finite diagnostic receipt only: pressure/localization sub-budget proxy good/bad split observed, no PDE pressure sub-budget theorem or Clay promotion."
    }

------------------------------------------------------------------------
-- Governance card.

formalModelSummary : String
formalModelSummary =
  "O Lane 3 Curie pressure-localization sub-budget proxy receipt; R bind harness JSON and good/bad case names; C imports pressure commutator contract plus A6 error budget because sub-budget composite is not available; S ok_observed=true, diagnostic_only=true, promotion=false, pressureSubBudgetClosed=false, localizationTheoremProved=false, triadicCompensatedLeakageIdentityProved=false, residualNonpositiveProved=false, nsClayPromoted=false, terminalPromotion=false; L diagnostic receipt -> pressure sub-budget theorem only after real estimates; P keep fail-closed receipt; G no theorem/promotion flip; F pressure localization sub-budget remains analytic open work."

premisesSummary : String
premisesSummary =
  "Premises: README and UnifiedRoutesLanePlan keep NS A6 pressure/localization as fail-closed; NSPressureCommutatorEstimateContractBoundary and NSA6ErrorBudgetCompositeBoundary are stable imported support surfaces."

traceSummary : String
traceSummary =
  "Trace: harness path + output path + expected case split + imported false theorem flags -> checked Agda receipt."

conclusionSummary : String
conclusionSummary =
  "Conclusion: the Lane 3 receipt is normalized and non-promoting; it records executable diagnostic evidence only."

promotionDecision : String
promotionDecision =
  "hold"
