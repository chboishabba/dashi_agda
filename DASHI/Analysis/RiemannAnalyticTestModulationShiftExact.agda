module DASHI.Analysis.RiemannAnalyticTestModulationShiftExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as Character

------------------------------------------------------------------------
-- H_A: ACTION OF THE TARGET CHARACTER ON THE CANONICAL WEIL TEST CARRIER
--
-- H_X supplies the actual analytic character exp(-itu).  H_A supplies its
-- action on the SAME Weil/Mellin test carrier and proves admissibility and the
-- spectral shift law for the SAME concrete explicit-formula object.
------------------------------------------------------------------------

record RiemannTestModulationShift
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    (H_X : Character.RiemannComplexCharacterExtension analytic) : Set₁ where
  constructor riemann-test-modulation-shift
  field
    carrierAgreementUsed : Set
    explicitFormulaAgreementUsed : Set
    characterAgreementUsed : Set

    Target : Set
    targetCarrierMatchesHXReal : Set

    modulateTest : Target → Weil.WeilTestSpace.Test space → Weil.WeilTestSpace.Test space

    modulationPreservesAdmissibility :
      (t : Target) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.admissible space f →
      Weil.WeilTestSpace.admissible space (modulateTest t f)

    -- The global spectral shift is tied to this exact formula.  The later
    -- H_W theorem still has to prove compatibility with finite near restriction.
    SpectralResponse : Set
    shiftedSpectralResponse :
      Target → Weil.WeilTestSpace.Test space → SpectralResponse
    unshiftedSpectralResponse :
      Weil.WeilTestSpace.Test space → SpectralResponse

    targetCharacterActsOnSpectralResponse : Set
    spectralShiftLaw : Set

    shiftedResponseBelongsToConcreteSpectralZeroForm : Set
    transformShiftUsesCanonicalWeilTransform : Set
    mellinCarrierCompatibilityUsed : Set

    actionReference : String

open RiemannTestModulationShift public

record TestModulationShiftBoundary : Set where
  constructor test-modulation-shift-boundary
  field
    H_XAloneProvesTestAdmissibility : Bool
    H_XAloneProvesTestAdmissibilityIsFalse :
      H_XAloneProvesTestAdmissibility ≡ false

    genericWeilTransformAloneProvesShiftLaw : Bool
    genericWeilTransformAloneProvesShiftLawIsFalse :
      genericWeilTransformAloneProvesShiftLaw ≡ false

    sameConcreteExplicitFormulaRequired : Bool
    sameConcreteExplicitFormulaRequiredIsTrue :
      sameConcreteExplicitFormulaRequired ≡ true

    H_AClosed : Bool
    H_AClosedIsFalse : H_AClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextTheorem : String

canonicalTestModulationShiftBoundary : TestModulationShiftBoundary
canonicalTestModulationShiftBoundary =
  test-modulation-shift-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    "Assuming the canonical complex target character H_X, define its action on the canonical Weil/Mellin test carrier, prove admissibility preservation, and prove the spectral transform-shift law for the same RiemannExplicitFormula object."
