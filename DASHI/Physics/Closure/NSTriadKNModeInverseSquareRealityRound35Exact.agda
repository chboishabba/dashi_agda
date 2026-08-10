module DASHI.Physics.Closure.NSTriadKNModeInverseSquareRealityRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Close a hidden reality seam in the finite Fourier carrier.  The generic
-- `ModeInverseSquare` record stores |k|^2, its reciprocal, the literal
-- coordinate formula for |k|^2, and the nonzero inverse law, but it did not
-- separately assume
--
--   |-k|^-2 = |k|^-2.
--
-- That evenness is not an additional analytic axiom: it follows from the
-- existing geometry.  First the literal square norm is even because each
-- embedded coordinate changes sign and (-x)^2=x^2.  For k != 0 the two stored
-- inverse values are then right inverses of the same scalar, hence equal by
-- uniqueness of inverses in the commutative ring.  At k=0 the equality is
-- definitional because -0=0.
--
-- This supplies exactly the missing inverse-square reality law needed before
-- a literal nonlinear Fourier reality theorem can be constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ; -_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNSafeCanonicalTriadOrbitQuotientRound34Exact as Safe

embeddedSquareNegation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (z : ℤ) →
  C3.multiply F
    (C3.embedInteger E (- z))
    (C3.embedInteger E (- z))
  ≡ C3.multiply F
    (C3.embedInteger E z)
    (C3.embedInteger E z)
embeddedSquareNegation {F = F} E z
  rewrite C3.embedNegate E z =
  R.solve 1
    (λ x → (R.⊝ x R.⊗ R.⊝ x) R.⊜ (x R.⊗ x))
    refl
    (C3.embedInteger E z)
  where module R = Algebra.Solver F

normSquaredEven :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  C3.normSquared I (Z3.negateMode k)
  ≡ C3.normSquared I k
normSquaredEven {F = F} E I (Z3.mode kx ky kz) =
  trans
    (C3.normSquaredMeaning I
      (Z3.negateMode (Z3.mode kx ky kz)))
    (trans
      (cong₂ (C3.add F)
        (cong₂ (C3.add F)
          (embeddedSquareNegation E kx)
          (embeddedSquareNegation E ky))
        (embeddedSquareNegation E kz))
      (sym (C3.normSquaredMeaning I (Z3.mode kx ky kz))))

negateZeroMode : Z3.negateMode Z3.zeroMode ≡ Z3.zeroMode
negateZeroMode = refl

negateModeNonzero :
  ∀ {k} → Z3.NonZeroMode k →
  Z3.NonZeroMode (Z3.negateMode k)
negateModeNonzero {k} nonzero = record
  { Z3.NonZeroMode.notZero = λ negIsZero →
      Z3.NonZeroMode.notZero nonzero
        (trans
          (sym (Symmetry.negateModeInvolutive k))
          (trans
            (cong Z3.negateMode negIsZero)
            negateZeroMode))
  }

rightInverseUnique :
  ∀ {r} (F : C3.RealField r)
    (a b n : C3.Carrier F) →
  C3.multiply F a n ≡ C3.one F →
  C3.multiply F b n ≡ C3.one F →
  a ≡ b
rightInverseUnique F a b n aRightInverse bRightInverse =
  begin
    a
  ≡⟨ sym (Algebra.realMultiplyOneRight F a) ⟩
    C3.multiply F a (C3.one F)
  ≡⟨ cong (C3.multiply F a) (sym bRightInverse) ⟩
    C3.multiply F a (C3.multiply F b n)
  ≡⟨ R.solve 3
       (λ x y z →
         (x R.⊗ (y R.⊗ z)) R.⊜ ((x R.⊗ z) R.⊗ y))
       refl a b n ⟩
    C3.multiply F (C3.multiply F a n) b
  ≡⟨ cong (λ product → C3.multiply F product b) aRightInverse ⟩
    C3.multiply F (C3.one F) b
  ≡⟨ C3.multiplyOneLeft F b ⟩
    b
  ∎
  where
  module R = Algebra.Solver F
  open ≡-Reasoning

inverseNormSquaredEvenNonzero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  Z3.NonZeroMode k →
  C3.inverseNormSquared I (Z3.negateMode k)
  ≡ C3.inverseNormSquared I k
inverseNormSquaredEvenNonzero {F = F} E I k nonzero =
  rightInverseUnique F
    (C3.inverseNormSquared I (Z3.negateMode k))
    (C3.inverseNormSquared I k)
    (C3.normSquared I k)
    negatedRightInverse
    (C3.inverseLaw I k nonzero)
  where
  negatedRightInverse :
    C3.multiply F
      (C3.inverseNormSquared I (Z3.negateMode k))
      (C3.normSquared I k)
    ≡ C3.one F
  negatedRightInverse =
    trans
      (sym
        (cong
          (C3.multiply F
            (C3.inverseNormSquared I (Z3.negateMode k)))
          (normSquaredEven E I k)))
      (C3.inverseLaw I (Z3.negateMode k)
        (negateModeNonzero nonzero))

inverseNormSquaredEven :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode) →
  C3.inverseNormSquared I (Z3.negateMode k)
  ≡ C3.inverseNormSquared I k
inverseNormSquaredEven E I k with Safe.mode≟ k Z3.zeroMode
... | yes refl = refl
... | no kNonzero =
  inverseNormSquaredEvenNonzero E I k record
    { Z3.NonZeroMode.notZero = kNonzero }

record EvenModeInverseSquare
    {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) : Set r where
  field
    normEven : ∀ k →
      C3.normSquared I (Z3.negateMode k)
      ≡ C3.normSquared I k
    inverseEven : ∀ k →
      C3.inverseNormSquared I (Z3.negateMode k)
      ≡ C3.inverseNormSquared I k

open EvenModeInverseSquare public

canonicalEvenModeInverseSquare :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  EvenModeInverseSquare F E I
canonicalEvenModeInverseSquare E I = record
  { normEven = normSquaredEven E I
  ; inverseEven = inverseNormSquaredEven E I
  }

modeInverseSquareRealityClosed : Bool
modeInverseSquareRealityClosed = true

modeInverseSquareRealityClosedIsTrue :
  modeInverseSquareRealityClosed ≡ true
modeInverseSquareRealityClosedIsTrue = refl
