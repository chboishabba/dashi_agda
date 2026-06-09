module DASHI.Physics.Closure.YMSpectralMarginBoundarySensitivityProxyHarnessResult where

-- Fail-closed receipt for the YM spectral-margin boundary-sensitivity
-- diagnostic harness.
--
-- The harness sweeps finite proxy parameters around the spectral-margin
-- budget
--
--   H_d >= c_delta Delta_YM,d + c_hol Hol_d - E_d
--
-- and records whether boundary-sensitive changes in kinetic, holonomy,
-- error, and pollution budgets preserve the diagnostic separation.  This is
-- a receipt only: it does not prove boundary sensitivity, spectral margin,
-- Hamiltonian domination, reflection positivity, OS transfer, continuum
-- no-pollution, YM Clay, or terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary
  as Composite
import DASHI.Physics.Closure.YMDominationSpectralMarginProxyHarnessResult
  as SpectralProxy

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Harness identity and output paths.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ym_spectral_margin_boundary_sensitivity_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ym_spectral_margin_boundary_sensitivity_smoke.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ym_spectral_margin_boundary_sensitivity_smoke.json"

receiptScope : String
receiptScope =
  "ym_spectral_margin_boundary_sensitivity_proxy_diagnostic_only"

runCommandText : String
runCommandText =
  "python scripts/ym_spectral_margin_boundary_sensitivity_harness.py --json-output outputs/ym_spectral_margin_boundary_sensitivity_smoke.json --json"

manifestCommandText : String
manifestCommandText =
  "python scripts/ym_spectral_margin_boundary_sensitivity_harness.py --json-output outputs/local_clay_harness_manifest_children/ym_spectral_margin_boundary_sensitivity_smoke.json --json"

------------------------------------------------------------------------
-- Imported support surfaces.

compositeReference : String
compositeReference =
  "DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary"

spectralProxyReference : String
spectralProxyReference =
  "DASHI.Physics.Closure.YMDominationSpectralMarginProxyHarnessResult"

compositeImported : Bool
compositeImported =
  true

spectralProxyImported : Bool
spectralProxyImported =
  true

compositeImportedIsTrue :
  compositeImported ≡ true
compositeImportedIsTrue =
  refl

spectralProxyImportedIsTrue :
  spectralProxyImported ≡ true
spectralProxyImportedIsTrue =
  refl

importedCompositeSpectralMarginStillFalse :
  Composite.spectralMarginTheoremProved
    Composite.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedCompositeSpectralMarginStillFalse =
  Composite.spectralMarginTheoremProvedIsFalse

importedCompositeDominationStillFalse :
  Composite.hamiltonianDominationProved
    Composite.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedCompositeDominationStillFalse =
  Composite.hamiltonianDominationProvedIsFalse

importedCompositeReflectionStillFalse :
  Composite.reflectionPositiveTransferProved
    Composite.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedCompositeReflectionStillFalse =
  Composite.reflectionPositiveTransferProvedIsFalse

importedCompositeOSStillFalse :
  Composite.osContinuumTransferProved
    Composite.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedCompositeOSStillFalse =
  Composite.osContinuumTransferProvedIsFalse

importedCompositeNoPollutionStillFalse :
  Composite.noSpectralPollutionProved
    Composite.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedCompositeNoPollutionStillFalse =
  Composite.noSpectralPollutionProvedIsFalse

importedCompositeYMClayStillFalse :
  Composite.ymClayPromoted
    Composite.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedCompositeYMClayStillFalse =
  Composite.ymClayPromotedIsFalse

importedCompositeTerminalStillFalse :
  Composite.terminalPromotion
    Composite.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
  ≡
  false
importedCompositeTerminalStillFalse =
  Composite.terminalPromotionIsFalse

importedSpectralProxyOkObserved :
  SpectralProxy.ok_observed ≡ true
importedSpectralProxyOkObserved =
  SpectralProxy.ok_observed_is_true

importedSpectralProxyPromotionStillFalse :
  SpectralProxy.promotion ≡ false
importedSpectralProxyPromotionStillFalse =
  SpectralProxy.promotion_is_false

------------------------------------------------------------------------
-- Swept parameters requested by the lane contract.

data YMSpectralBoundarySensitivityParameter : Set where
  cDeltaSweep :
    YMSpectralBoundarySensitivityParameter

  cHolSweep :
    YMSpectralBoundarySensitivityParameter

  edSweep :
    YMSpectralBoundarySensitivityParameter

  holonomySweep :
    YMSpectralBoundarySensitivityParameter

  kineticSweep :
    YMSpectralBoundarySensitivityParameter

  pollutionSweep :
    YMSpectralBoundarySensitivityParameter

canonicalSweptParameters :
  List YMSpectralBoundarySensitivityParameter
canonicalSweptParameters =
  cDeltaSweep
  ∷ cHolSweep
  ∷ edSweep
  ∷ holonomySweep
  ∷ kineticSweep
  ∷ pollutionSweep
  ∷ []

sweptParameterCount : Nat
sweptParameterCount =
  listCount canonicalSweptParameters

sweptParameterCountIs6 :
  sweptParameterCount ≡ 6
sweptParameterCountIs6 =
  refl

sweptParameterText : String
sweptParameterText =
  "c_delta, c_hol, E_d, holonomy, kinetic, pollution"

------------------------------------------------------------------------
-- Harness receipt fields.

data YMSpectralBoundarySensitivityHarnessField : Set where
  sourceHarnessField :
    YMSpectralBoundarySensitivityHarnessField

  smokeOutputField :
    YMSpectralBoundarySensitivityHarnessField

  manifestChildOutputField :
    YMSpectralBoundarySensitivityHarnessField

  importedCompositeField :
    YMSpectralBoundarySensitivityHarnessField

  importedSpectralProxyField :
    YMSpectralBoundarySensitivityHarnessField

  sweptParametersField :
    YMSpectralBoundarySensitivityHarnessField

  observedFlagsField :
    YMSpectralBoundarySensitivityHarnessField

  theoremFlagsField :
    YMSpectralBoundarySensitivityHarnessField

  nonPromotionBoundaryField :
    YMSpectralBoundarySensitivityHarnessField

canonicalHarnessFields :
  List YMSpectralBoundarySensitivityHarnessField
canonicalHarnessFields =
  sourceHarnessField
  ∷ smokeOutputField
  ∷ manifestChildOutputField
  ∷ importedCompositeField
  ∷ importedSpectralProxyField
  ∷ sweptParametersField
  ∷ observedFlagsField
  ∷ theoremFlagsField
  ∷ nonPromotionBoundaryField
  ∷ []

harnessFieldCount : Nat
harnessFieldCount =
  listCount canonicalHarnessFields

harnessFieldCountIs9 :
  harnessFieldCount ≡ 9
harnessFieldCountIs9 =
  refl

------------------------------------------------------------------------
-- Observed flags and non-claims.

ok_observed : Bool
ok_observed =
  true

diagnostic_only : Bool
diagnostic_only =
  true

promotion : Bool
promotion =
  false

spectralBoundarySensitivityTheoremProved : Bool
spectralBoundarySensitivityTheoremProved =
  false

spectralMarginTheoremProved : Bool
spectralMarginTheoremProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

reflectionPositiveTransferProved : Bool
reflectionPositiveTransferProved =
  false

osTransferProved : Bool
osTransferProved =
  false

continuumNoPollutionProved : Bool
continuumNoPollutionProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
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

spectralBoundarySensitivityTheoremProvedIsFalse :
  spectralBoundarySensitivityTheoremProved ≡ false
spectralBoundarySensitivityTheoremProvedIsFalse =
  refl

spectralMarginTheoremProvedIsFalse :
  spectralMarginTheoremProved ≡ false
spectralMarginTheoremProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

reflectionPositiveTransferProvedIsFalse :
  reflectionPositiveTransferProved ≡ false
reflectionPositiveTransferProvedIsFalse =
  refl

osTransferProvedIsFalse :
  osTransferProved ≡ false
osTransferProvedIsFalse =
  refl

continuumNoPollutionProvedIsFalse :
  continuumNoPollutionProved ≡ false
continuumNoPollutionProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record YMSpectralMarginBoundarySensitivityProxyHarnessResult : Set where
  field
    sourceHarness :
      String

    smokeOutput :
      String

    manifestChildOutput :
      String

    scope :
      String

    sweptParameters :
      List YMSpectralBoundarySensitivityParameter

    okObserved :
      Bool

    diagnosticOnly :
      Bool

    promotionFlag :
      Bool

    spectralBoundarySensitivityTheoremFlag :
      Bool

    spectralMarginTheoremFlag :
      Bool

    hamiltonianDominationTheoremFlag :
      Bool

    reflectionPositiveTransferFlag :
      Bool

    osTransferFlag :
      Bool

    continuumNoPollutionFlag :
      Bool

    ymClayPromotionFlag :
      Bool

    terminalPromotionFlag :
      Bool

open YMSpectralMarginBoundarySensitivityProxyHarnessResult public

canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult :
  YMSpectralMarginBoundarySensitivityProxyHarnessResult
canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; smokeOutput =
        jsonReceiptPath
    ; manifestChildOutput =
        manifestChildReceiptPath
    ; scope =
        receiptScope
    ; sweptParameters =
        canonicalSweptParameters
    ; okObserved =
        true
    ; diagnosticOnly =
        true
    ; promotionFlag =
        false
    ; spectralBoundarySensitivityTheoremFlag =
        false
    ; spectralMarginTheoremFlag =
        false
    ; hamiltonianDominationTheoremFlag =
        false
    ; reflectionPositiveTransferFlag =
        false
    ; osTransferFlag =
        false
    ; continuumNoPollutionFlag =
        false
    ; ymClayPromotionFlag =
        false
    ; terminalPromotionFlag =
        false
    }

canonicalOkObservedTrue :
  okObserved canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  true
canonicalOkObservedTrue =
  refl

canonicalDiagnosticOnlyTrue :
  diagnosticOnly canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  true
canonicalDiagnosticOnlyTrue =
  refl

canonicalPromotionFalse :
  promotionFlag canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalPromotionFalse =
  refl

canonicalSpectralBoundarySensitivityFalse :
  spectralBoundarySensitivityTheoremFlag
    canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalSpectralBoundarySensitivityFalse =
  refl

canonicalSpectralMarginFalse :
  spectralMarginTheoremFlag
    canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalSpectralMarginFalse =
  refl

canonicalHamiltonianDominationFalse :
  hamiltonianDominationTheoremFlag
    canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalHamiltonianDominationFalse =
  refl

canonicalReflectionPositiveTransferFalse :
  reflectionPositiveTransferFlag
    canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalReflectionPositiveTransferFalse =
  refl

canonicalOSTransferFalse :
  osTransferFlag canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalOSTransferFalse =
  refl

canonicalContinuumNoPollutionFalse :
  continuumNoPollutionFlag
    canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalContinuumNoPollutionFalse =
  refl

canonicalYMClayFalse :
  ymClayPromotionFlag
    canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalYMClayFalse =
  refl

canonicalTerminalPromotionFalse :
  terminalPromotionFlag
    canonicalYMSpectralMarginBoundarySensitivityProxyHarnessResult
  ≡
  false
canonicalTerminalPromotionFalse =
  refl
