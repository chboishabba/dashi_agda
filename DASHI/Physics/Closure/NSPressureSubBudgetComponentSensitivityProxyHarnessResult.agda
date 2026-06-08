module DASHI.Physics.Closure.NSPressureSubBudgetComponentSensitivityProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ns_pressure_subbudget_component_sensitivity_harness.py
--
-- The harness is expected to sweep the pressure/localization A6 sub-budget
-- components one at a time and report which synthetic component dominates the
-- aggregate pressure-localization margin.  This module records only the
-- executable receipt shape and governance flags.  It does not prove component
-- sensitivity, close the pressure sub-budget, prove localization, prove the
-- triadic compensated leakage identity, prove residual nonpositivity, solve
-- NS Clay, or promote terminal unification.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSPressureLocalizationSubBudgetCompositeBoundary
  as SubBudget
import DASHI.Physics.Closure.NSPressureLocalizationSubBudgetProxyHarnessResult
  as SubBudgetProxy

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
  "scripts/ns_pressure_subbudget_component_sensitivity_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ns_pressure_subbudget_component_sensitivity_smoke.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ns_pressure_subbudget_component_sensitivity_smoke.json"

receiptScope : String
receiptScope =
  "finite_synthetic_pressure_subbudget_component_sensitivity_proxy_not_pde_proof"

expectedRunCommandText : String
expectedRunCommandText =
  "python scripts/ns_pressure_subbudget_component_sensitivity_harness.py --json-output outputs/ns_pressure_subbudget_component_sensitivity_smoke.json --json"

expectedManifestCommandText : String
expectedManifestCommandText =
  "python scripts/ns_pressure_subbudget_component_sensitivity_harness.py --json-output outputs/local_clay_harness_manifest_children/ns_pressure_subbudget_component_sensitivity_smoke.json --json"

------------------------------------------------------------------------
-- Imported support.

pressureLocalizationSubBudgetCompositeReference : String
pressureLocalizationSubBudgetCompositeReference =
  "DASHI.Physics.Closure.NSPressureLocalizationSubBudgetCompositeBoundary"

pressureLocalizationSubBudgetProxyHarnessResultReference : String
pressureLocalizationSubBudgetProxyHarnessResultReference =
  "DASHI.Physics.Closure.NSPressureLocalizationSubBudgetProxyHarnessResult"

pressureLocalizationSubBudgetCompositeImported : Bool
pressureLocalizationSubBudgetCompositeImported =
  true

pressureLocalizationSubBudgetProxyHarnessResultImported : Bool
pressureLocalizationSubBudgetProxyHarnessResultImported =
  true

record ImportedNSPressureSubBudgetComponentSensitivitySupport : Set where
  field
    pressureLocalizationSubBudgetComposite :
      SubBudget.NSPressureLocalizationSubBudgetCompositeBoundary
    pressureLocalizationSubBudgetCompositeIsCanonical :
      pressureLocalizationSubBudgetComposite
        ≡ SubBudget.canonicalNSPressureLocalizationSubBudgetCompositeBoundary
    pressureLocalizationSubBudgetProxyHarnessResult :
      SubBudgetProxy.NSPressureLocalizationSubBudgetProxyHarnessResult
    pressureLocalizationSubBudgetProxyHarnessResultIsCanonical :
      pressureLocalizationSubBudgetProxyHarnessResult
        ≡ SubBudgetProxy.canonicalNSPressureLocalizationSubBudgetProxyHarnessResult
    pressureLocalizationSubBudgetCompositeImportedIsTrue :
      pressureLocalizationSubBudgetCompositeImported ≡ true
    pressureLocalizationSubBudgetProxyHarnessResultImportedIsTrue :
      pressureLocalizationSubBudgetProxyHarnessResultImported ≡ true
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
    importedProxyKeepsPressureSubBudgetFalse :
      SubBudgetProxy.pressureSubBudgetClosed ≡ false
    importedProxyKeepsLocalizationFalse :
      SubBudgetProxy.localizationTheoremProved ≡ false
    importedProxyKeepsA6False :
      SubBudgetProxy.triadicCompensatedLeakageIdentityProved ≡ false
    importedProxyKeepsResidualFalse :
      SubBudgetProxy.residualNonpositiveProved ≡ false
    importedProxyKeepsClayFalse :
      SubBudgetProxy.nsClayPromoted ≡ false
    importedProxyKeepsTerminalFalse :
      SubBudgetProxy.terminalPromotion ≡ false

canonicalImportedNSPressureSubBudgetComponentSensitivitySupport :
  ImportedNSPressureSubBudgetComponentSensitivitySupport
canonicalImportedNSPressureSubBudgetComponentSensitivitySupport =
  record
    { pressureLocalizationSubBudgetComposite =
        SubBudget.canonicalNSPressureLocalizationSubBudgetCompositeBoundary
    ; pressureLocalizationSubBudgetCompositeIsCanonical =
        refl
    ; pressureLocalizationSubBudgetProxyHarnessResult =
        SubBudgetProxy.canonicalNSPressureLocalizationSubBudgetProxyHarnessResult
    ; pressureLocalizationSubBudgetProxyHarnessResultIsCanonical =
        refl
    ; pressureLocalizationSubBudgetCompositeImportedIsTrue =
        refl
    ; pressureLocalizationSubBudgetProxyHarnessResultImportedIsTrue =
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
    ; importedProxyKeepsPressureSubBudgetFalse =
        refl
    ; importedProxyKeepsLocalizationFalse =
        refl
    ; importedProxyKeepsA6False =
        refl
    ; importedProxyKeepsResidualFalse =
        refl
    ; importedProxyKeepsClayFalse =
        refl
    ; importedProxyKeepsTerminalFalse =
        refl
    }

------------------------------------------------------------------------
-- Components swept by the sensitivity diagnostic.

data NSPressureSubBudgetSensitivityComponent : Set where
  cutoffRieszCommutatorComponent :
    NSPressureSubBudgetSensitivityComponent
  localCalderonZygmundCoreComponent :
    NSPressureSubBudgetSensitivityComponent
  harmonicPressureTailComponent :
    NSPressureSubBudgetSensitivityComponent
  pressureTailAbsorptionComponent :
    NSPressureSubBudgetSensitivityComponent
  annularCutoffComponent :
    NSPressureSubBudgetSensitivityComponent
  epsilonGradientAbsorptionComponent :
    NSPressureSubBudgetSensitivityComponent
  abelRecenteringLowerOrderComponent :
    NSPressureSubBudgetSensitivityComponent

componentLabel : NSPressureSubBudgetSensitivityComponent → String
componentLabel cutoffRieszCommutatorComponent =
  "cutoff_riesz_commutator"
componentLabel localCalderonZygmundCoreComponent =
  "local_calderon_zygmund_core"
componentLabel harmonicPressureTailComponent =
  "harmonic_pressure_tail"
componentLabel pressureTailAbsorptionComponent =
  "pressure_tail_absorption"
componentLabel annularCutoffComponent =
  "annular_cutoff"
componentLabel epsilonGradientAbsorptionComponent =
  "epsilon_gradient_absorption"
componentLabel abelRecenteringLowerOrderComponent =
  "abel_recentering_lower_order"

componentRoute : NSPressureSubBudgetSensitivityComponent → String
componentRoute cutoffRieszCommutatorComponent =
  "pressure_commutator_budget"
componentRoute localCalderonZygmundCoreComponent =
  "pressure_commutator_budget"
componentRoute harmonicPressureTailComponent =
  "pressure_tail_budget"
componentRoute pressureTailAbsorptionComponent =
  "pressure_tail_budget"
componentRoute annularCutoffComponent =
  "localization_cutoff_budget"
componentRoute epsilonGradientAbsorptionComponent =
  "off_diagonal_absorption_budget"
componentRoute abelRecenteringLowerOrderComponent =
  "abel_tail_recentering_budget"

componentsSwept :
  List NSPressureSubBudgetSensitivityComponent
componentsSwept =
  cutoffRieszCommutatorComponent
  ∷ localCalderonZygmundCoreComponent
  ∷ harmonicPressureTailComponent
  ∷ pressureTailAbsorptionComponent
  ∷ annularCutoffComponent
  ∷ epsilonGradientAbsorptionComponent
  ∷ abelRecenteringLowerOrderComponent
  ∷ []

componentSensitivitySweepCount : Nat
componentSensitivitySweepCount =
  listLength componentsSwept

componentSensitivitySweepCountIs7 :
  componentSensitivitySweepCount ≡ 7
componentSensitivitySweepCountIs7 =
  refl

------------------------------------------------------------------------
-- Expected receipt fields.

data NSPressureSubBudgetComponentSensitivityField : Set where
  harnessField :
    NSPressureSubBudgetComponentSensitivityField
  outputPathField :
    NSPressureSubBudgetComponentSensitivityField
  manifestChildPathField :
    NSPressureSubBudgetComponentSensitivityField
  componentsSweptField :
    NSPressureSubBudgetComponentSensitivityField
  componentRoutesField :
    NSPressureSubBudgetComponentSensitivityField
  componentSensitivitySummaryField :
    NSPressureSubBudgetComponentSensitivityField
  okObservedField :
    NSPressureSubBudgetComponentSensitivityField
  diagnosticOnlyField :
    NSPressureSubBudgetComponentSensitivityField
  promotionField :
    NSPressureSubBudgetComponentSensitivityField
  theoremFlagsField :
    NSPressureSubBudgetComponentSensitivityField
  interpretationField :
    NSPressureSubBudgetComponentSensitivityField

expectedReceiptFields :
  List NSPressureSubBudgetComponentSensitivityField
expectedReceiptFields =
  harnessField
  ∷ outputPathField
  ∷ manifestChildPathField
  ∷ componentsSweptField
  ∷ componentRoutesField
  ∷ componentSensitivitySummaryField
  ∷ okObservedField
  ∷ diagnosticOnlyField
  ∷ promotionField
  ∷ theoremFlagsField
  ∷ interpretationField
  ∷ []

expectedReceiptFieldCount : Nat
expectedReceiptFieldCount =
  listLength expectedReceiptFields

expectedReceiptFieldCountIs11 :
  expectedReceiptFieldCount ≡ 11
expectedReceiptFieldCountIs11 =
  refl

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

componentSensitivityTheoremProved : Bool
componentSensitivityTheoremProved =
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

residualNonPositiveProved : Bool
residualNonPositiveProved =
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

componentSensitivityTheoremProvedIsFalse :
  componentSensitivityTheoremProved ≡ false
componentSensitivityTheoremProvedIsFalse =
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

residualNonPositiveProvedIsFalse :
  residualNonPositiveProved ≡ false
residualNonPositiveProvedIsFalse =
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

record NSPressureSubBudgetComponentSensitivityProxyHarnessResult : Set where
  field
    sourceHarness :
      String
    jsonOutput :
      String
    manifestChildOutput :
      String
    importedSupport :
      ImportedNSPressureSubBudgetComponentSensitivitySupport
    sweptComponents :
      List NSPressureSubBudgetSensitivityComponent
    expectedFields :
      List NSPressureSubBudgetComponentSensitivityField
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
    componentSensitivityTheoremProvedFalse :
      componentSensitivityTheoremProved ≡ false
    pressureSubBudgetClosedFalse :
      pressureSubBudgetClosed ≡ false
    localizationTheoremProvedFalse :
      localizationTheoremProved ≡ false
    triadicCompensatedLeakageIdentityProvedFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    residualNonPositiveProvedFalse :
      residualNonPositiveProved ≡ false
    nsClayPromotedFalse :
      nsClayPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    interpretation :
      String

canonicalNSPressureSubBudgetComponentSensitivityProxyHarnessResult :
  NSPressureSubBudgetComponentSensitivityProxyHarnessResult
canonicalNSPressureSubBudgetComponentSensitivityProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; jsonOutput =
        jsonReceiptPath
    ; manifestChildOutput =
        manifestChildReceiptPath
    ; importedSupport =
        canonicalImportedNSPressureSubBudgetComponentSensitivitySupport
    ; sweptComponents =
        componentsSwept
    ; expectedFields =
        expectedReceiptFields
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
    ; componentSensitivityTheoremProvedFalse =
        refl
    ; pressureSubBudgetClosedFalse =
        refl
    ; localizationTheoremProvedFalse =
        refl
    ; triadicCompensatedLeakageIdentityProvedFalse =
        refl
    ; residualNonPositiveProvedFalse =
        refl
    ; nsClayPromotedFalse =
        refl
    ; terminalPromotionFalse =
        refl
    ; interpretation =
        "Finite diagnostic receipt only: pressure sub-budget component-sensitivity sweep is recorded, with no component-sensitivity theorem, pressure sub-budget closure, A6 theorem, NS Clay, or terminal promotion."
    }

------------------------------------------------------------------------
-- Governance card.

formalModelSummary : String
formalModelSummary =
  "O Lane 4 Hilbert pressure-subbudget component-sensitivity receipt; R bind Lane 3 harness source, smoke output, manifest child output, and swept components; C imports NSPressureLocalizationSubBudgetCompositeBoundary and NSPressureLocalizationSubBudgetProxyHarnessResult; S ok_observed=true, diagnostic_only=true, promotion=false; L component sensitivity diagnostic -> pressure sub-budget theorem only after real estimates; P keep fail-closed receipt; G no theorem/promotion flip; F component sensitivity, pressure sub-budget, localization, A6, residual nonpositivity, NS Clay, and terminal promotion remain open."

premisesSummary : String
premisesSummary =
  "Premises: README and UnifiedRoutesLanePlan keep NS A6 pressure/localization fail-closed; the pressure sub-budget composite and proxy receipt are the imported support surfaces."

traceSummary : String
traceSummary =
  "Trace: expected harness path + output paths + seven swept components + imported false theorem flags -> checked Agda receipt."

conclusionSummary : String
conclusionSummary =
  "Conclusion: the component-sensitivity proxy receipt is normalized and non-promoting."

promotionDecision : String
promotionDecision =
  "hold"
