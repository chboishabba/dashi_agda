{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOSSelectedKetHamiltonianNonpromotionExact where

------------------------------------------------------------------------
-- P03/P07 BIDI NEGATIVE CONTROL: ONE SELECTED KET DOES NOT
-- IDENTIFY THE PHYSICAL HAMILTONIAN / SPECTRAL PROJECTIONS.
--
-- The ORIGINAL TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact
-- proves conditional H_OS / H_observer agreement on the selected
-- original TSVF forward ket and, separately, on any populated
-- observer generator domain. It does NOT build a physical dense core.
--
-- This finite rational two-coordinate model supplies two explicitly
-- different real-symmetric diagonal operator maps:
--   H0 = diag(0,0); H1 = diag(0,1).
-- They agree exactly on |e0>=(1,0), yet disagree on |e1>=(0,1).
-- Hence source-selected one-ket identity does not entail operator
-- equality, spectrum equality, spectral gap, Stone equivalence,
-- physical OS Hilbert or Euclidean-to-real-time analytic continuation.
--
-- Both are well-defined linear maps on an algebraic two-coordinate
-- rational carrier; the symmetric-bilinear identity is proved below.
-- This is an INDEPENDENT COUNTERMODEL, not the actual observer, OS
-- or Yang--Mills Hamiltonian. The true P07 needs a physically
-- justified COMMON DENSE CORE and continuity/self-adjointness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring

RationalTwoKet : Set
RationalTwoKet = ℚ × ℚ

selectedForwardControlKet : RationalTwoKet
selectedForwardControlKet = 1ℚ , 0ℚ

independentSecondControlKet : RationalTwoKet
independentSecondControlKet = 0ℚ , 1ℚ

zeroHamiltonian : RationalTwoKet → RationalTwoKet
zeroHamiltonian _ = 0ℚ , 0ℚ

positiveSecondModeHamiltonian :
  RationalTwoKet → RationalTwoKet
positiveSecondModeHamiltonian (a , b) = 0ℚ , b

controlHamiltoniansAgreeOnForwardKet :
  zeroHamiltonian selectedForwardControlKet
  ≡
  positiveSecondModeHamiltonian selectedForwardControlKet
controlHamiltoniansAgreeOnForwardKet = refl

positiveOneIsNotZero :
  0ℚ ≡ 1ℚ → ⊥
positiveOneIsNotZero zeroEqualsOne =
  ℚP.<-irrefl 0ℚ
    (subst
      (λ q → 0ℚ < q)
      (sym zeroEqualsOne)
      (ℚP.positive⁻¹ 1ℚ))

controlHamiltoniansDifferOnSecondMode :
  zeroHamiltonian independentSecondControlKet
    ≡
  positiveSecondModeHamiltonian independentSecondControlKet →
  ⊥
controlHamiltoniansDifferOnSecondMode equality =
  positiveOneIsNotZero (cong proj₂ equality)

-- Full pointwise operator equality is strictly stronger than
-- equality on ONE selected ket, even in a finite two-state system.
sameSelectedForwardKetDoesNotForceWholeHamiltonian :
  (∀ state →
    zeroHamiltonian state
    ≡ positiveSecondModeHamiltonian state) →
  ⊥
sameSelectedForwardKetDoesNotForceWholeHamiltonian allStates =
  controlHamiltoniansDifferOnSecondMode
    (allStates independentSecondControlKet)

-- Both finite operators are symmetric for the same rational dot
-- product; this is not a pathology caused by a non-symmetric map.
rationalTwoDot : RationalTwoKet → RationalTwoKet → ℚ
rationalTwoDot (a , b) (c , d) = a * c + b * d

zeroHamiltonianSymmetric :
  ∀ left right →
  rationalTwoDot left (zeroHamiltonian right)
  ≡ rationalTwoDot (zeroHamiltonian left) right
zeroHamiltonianSymmetric (a , b) (c , d) =
  Ring.solve-∀ a b c d

secondModeHamiltonianSymmetric :
  ∀ left right →
  rationalTwoDot left (positiveSecondModeHamiltonian right)
  ≡ rationalTwoDot
      (positiveSecondModeHamiltonian left) right
secondModeHamiltonianSymmetric (a , b) (c , d) =
  Ring.solve-∀ a b c d

-- P07 full physical energy intertwinement remains OPEN:
-- the ORIGINAL selected ket must be contained in a true common dense
-- invariant self-adjoint core, a source-complete Hilbert, one physical
-- hbar/time scaling and a justified OS/Wick spectral calculus.
