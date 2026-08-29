module DASHI.Analysis.RiemannAristotleG2eTargetCenteredSymmetryNoGoExact where

------------------------------------------------------------------------
-- G2e / TARGET-CENTERED SYMMETRY NO-GO
--
-- The exact zeta symmetries currently owned in-repo are centered on the
-- critical line / real axis, not on an arbitrary target ordinate t.
--
-- Functional-equation reflection  rho -> 1-conj(rho)
-- preserves Im rho, so delta = Im rho - t is unchanged.
--
-- Complex conjugation rho -> conj(rho), where available, sends Im rho = b to
-- -b, hence sends the target-relative gap b-t to -b-t, not to -(b-t) = -b+t
-- unless t = 0.
--
-- Therefore the current symmetries do not pair the finite local gaps by
-- delta -> -delta around an arbitrary target t. Riemann-von Mangoldt local
-- counting controls multiplicity only and supplies no phase/sign information.
--
-- So the scalar cosine sum left by G2e requires a genuinely additional
-- target-centered zero-distribution / exponential-sum cancellation theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record G2eTargetCenteredSymmetryNoGo : Set where
  constructor g2e-target-centered-symmetry-no-go
  field
    functionalReflectionPreservesOrdinate : Bool
    functionalReflectionPreservesOrdinateIsTrue :
      functionalReflectionPreservesOrdinate ≡ true

    conjugationNegatesOrdinateAboutZero : Bool
    conjugationNegatesOrdinateAboutZeroIsTrue :
      conjugationNegatesOrdinateAboutZero ≡ true

    functionalReflectionNegatesGapAboutArbitraryTarget : Bool
    functionalReflectionNegatesGapAboutArbitraryTargetIsFalse :
      functionalReflectionNegatesGapAboutArbitraryTarget ≡ false

    conjugationNegatesGapAboutArbitraryTarget : Bool
    conjugationNegatesGapAboutArbitraryTargetIsFalse :
      conjugationNegatesGapAboutArbitraryTarget ≡ false

    localZeroCountControlsCosinePhase : Bool
    localZeroCountControlsCosinePhaseIsFalse :
      localZeroCountControlsCosinePhase ≡ false

    montgomeryVaughanOwnerDirectlyControlsThisLocalZeroCosineSum : Bool
    montgomeryVaughanOwnerDirectlyControlsThisLocalZeroCosineSumIsFalse :
      montgomeryVaughanOwnerDirectlyControlsThisLocalZeroCosineSum ≡ false

    requiredNewTheorem : String

    targetCenteredScalarCancellationClosed : Bool
    targetCenteredScalarCancellationClosedIsFalse :
      targetCenteredScalarCancellationClosed ≡ false

open G2eTargetCenteredSymmetryNoGo public

canonicalG2eTargetCenteredSymmetryNoGo : G2eTargetCenteredSymmetryNoGo
canonicalG2eTargetCenteredSymmetryNoGo =
  g2e-target-centered-symmetry-no-go
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "A target-centered local zero exponential-sum estimate controlling integral q(u) * sum_{sigma in near(t,J)} m_sigma cosh(a_sigma u) cos((b_sigma-t)u), uniformly strongly enough to beat the surviving cluster determinant margin after the explicit far error."
    false refl
