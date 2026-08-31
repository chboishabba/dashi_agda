module DASHI.Analysis.RiemannAnalyticModulationExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat

------------------------------------------------------------------------
-- MINIMAL ANALYTIC EXTENSION NEEDED FOR RH TARGET MODULATION
--
-- The canonical substrate owns complex addition/multiplication, Mellin,
-- admissibility and an opaque transform, but it does not currently expose
-- complex exponential, target modulation on tests, or a transform-shift law.
--
-- This record extends those SAME carriers.  It is not a replacement test
-- space and it does not import any finite Monster/Heisenberg carrier.
------------------------------------------------------------------------

record RiemannAnalyticModulationExtension
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space) : Set₁ where
  constructor riemann-analytic-modulation-extension
  field
    carrierAgreementUsed : Set

    Ordinate Frequency : Set

    -- Actual carrier operations needed to spell exp(- i t u).
    targetDifference : Ordinate → Ordinate → Ordinate
    targetDifferenceIsSubtract : Set

    Character : Set
    characterMultiply : Character → Character → Character
    targetCharacter : Frequency → Ordinate → Character
    zeroCharacter : Frequency → Ordinate → Character

    -- Test modulation stays on the canonical Weil/Mellin test carrier.
    modulateTest : Ordinate → Weil.WeilTestSpace.Test space → Weil.WeilTestSpace.Test space
    modulationPreservesAdmissibility :
      (t : Ordinate) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.admissible space f →
      Weil.WeilTestSpace.admissible space (modulateTest t f)

    -- Spectral-side shift law: target modulation induces target-relative phase.
    SpectralResponse : Set
    spectralResponse :
      Weil.WeilTestSpace.Test space → Ordinate → Frequency → SpectralResponse
    phaseAct : Character → SpectralResponse → SpectralResponse

    spectralModulationShift :
      (t b : Ordinate) →
      (u : Frequency) →
      (f : Weil.WeilTestSpace.Test space) →
      spectralResponse (modulateTest t f) b u
      ≡ phaseAct (targetCharacter u t) (spectralResponse f b u)

    -- The application must separately prove that this character is the actual
    -- analytic exp(- i t u), and that composing with the unshifted zero phase
    -- yields exp(i(b-t)u).  These are not inferred from names.
    targetCharacterIsExpMinusITU : Set
    zeroCharacterIsExpIBU : Set
    characterProductIsExpIGapU : Set

    extensionReference : String

open RiemannAnalyticModulationExtension public

------------------------------------------------------------------------
-- Boundary: exact missing primitive audit.
------------------------------------------------------------------------

record AnalyticModulationExtensionBoundary : Set where
  constructor analytic-modulation-extension-boundary
  field
    canonicalComplexCarrierAlreadyOwnsExponential : Bool
    canonicalComplexCarrierAlreadyOwnsExponentialIsFalse :
      canonicalComplexCarrierAlreadyOwnsExponential ≡ false

    canonicalWeilSpaceAlreadyOwnsModulation : Bool
    canonicalWeilSpaceAlreadyOwnsModulationIsFalse :
      canonicalWeilSpaceAlreadyOwnsModulation ≡ false

    canonicalWeilSpaceAlreadyOwnsTransformShiftLaw : Bool
    canonicalWeilSpaceAlreadyOwnsTransformShiftLawIsFalse :
      canonicalWeilSpaceAlreadyOwnsTransformShiftLaw ≡ false

    extensionMustReuseCanonicalCarriers : Bool
    extensionMustReuseCanonicalCarriersIsTrue :
      extensionMustReuseCanonicalCarriers ≡ true

    monsterFiniteCharacterCanInstantiateAnalyticCharacter : Bool
    monsterFiniteCharacterCanInstantiateAnalyticCharacterIsFalse :
      monsterFiniteCharacterCanInstantiateAnalyticCharacter ≡ false

    modulationExtensionClosed : Bool
    modulationExtensionClosedIsFalse : modulationExtensionClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalAnalyticModulationExtensionBoundary : AnalyticModulationExtensionBoundary
canonicalAnalyticModulationExtensionBoundary =
  analytic-modulation-extension-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
