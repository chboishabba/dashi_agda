{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinRationalCayleyToOriginalComplexExact where

------------------------------------------------------------------------
-- K05-PI SAME-OBJECT BRIDGE: ORIGINAL Q[i] -> ORIGINAL BISHOP C.
--
-- Existing rational Gaussian carrier:
--   CayleyDicksonRationalComplexQuaternionExact.RationalComplex
-- Existing Bishop setoid complex:
--   BishopSetoidComplexExact.BishopComplex
--
-- The map is the LITERAL pinned Bishop rational embedding
--   q : Q (normalized) -> toQ-unormalized(q) -> Real._⋆ q.
-- The bridge proves that this same map preserves addition, subtraction
-- and multiplication, componentwise in the vendored Bishop setoid.
-- Hence the prior rational Cayley Machin certificate =i transports
-- to the actual Bishop complex imaginary unit without a second
-- complex carrier, fake equality, or arbitrary external field.
--
-- It still does not assert that exp_C(2i atan_B(t)) equals the
-- corresponding rational Cayley phase: THAT analytic series
-- evaluation is the sole independent PI.1 same-object gate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Real as R
import RealProperties as RP
open import Data.Rational.Base as Q using (ℚ; 0ℚ; 1ℚ; toℚᵘ)
import Data.Rational.Properties as QP

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinExistingCayleyReuseExact as Cayley

embedQ : ℚ → R.ℝ
embedQ q = R._⋆ (toℚᵘ q)

embedAdd :
  ∀ p q →
  R._≃_
    (embedQ (Q._+_ p q))
    (R._+_ (embedQ p) (embedQ q))
embedAdd p q =
  RP.≃-trans
    (RP.⋆-cong (QP.toℚᵘ-homo-+ p q))
    (RP.⋆-distrib-+ (toℚᵘ p) (toℚᵘ q))

embedMultiply :
  ∀ p q →
  R._≃_
    (embedQ (Q._*_ p q))
    (R._*_ (embedQ p) (embedQ q))
embedMultiply p q =
  RP.≃-trans
    (RP.⋆-cong (QP.toℚᵘ-homo-* p q))
    (RP.⋆-distrib-* (toℚᵘ p) (toℚᵘ q))

embedNegate :
  ∀ q →
  R._≃_
    (embedQ (Q.-_ q))
    (R.-_ (embedQ q))
embedNegate q =
  RP.≃-trans
    (RP.⋆-cong (QP.toℚᵘ-homo‿- q))
    (RP.⋆-distrib-neg (toℚᵘ q))

embedSubtract :
  ∀ p q →
  R._≃_
    (embedQ (Q._-_ p q))
    (R._-_ (embedQ p) (embedQ q))
embedSubtract p q =
  RP.≃-trans
    (embedAdd p (Q.-_ q))
    (RP.+-cong RP.≃-refl (embedNegate q))

-- Literal original rational complex -> literal original Bishop complex.
embedOriginalComplex : CD.RationalComplex → C.BishopComplex
embedOriginalComplex (CD.complex a b) =
  C.complex (embedQ a) (embedQ b)

embedOriginalComplexAdd :
  (z w : CD.RationalComplex) →
  C._≈C_
    (embedOriginalComplex (CD._+c_ z w))
    (C._+C_ (embedOriginalComplex z) (embedOriginalComplex w))
embedOriginalComplexAdd (CD.complex a b) (CD.complex c d) =
  C.complex-equivalent
    (embedAdd a c)
    (embedAdd b d)

embedOriginalComplexSubtract :
  (z w : CD.RationalComplex) →
  C._≈C_
    (embedOriginalComplex (CD._-c_ z w))
    (C._-C_ (embedOriginalComplex z) (embedOriginalComplex w))
embedOriginalComplexSubtract (CD.complex a b) (CD.complex c d) =
  C.complex-equivalent
    (embedSubtract a c)
    (embedSubtract b d)

embedOriginalComplexMultiply :
  (z w : CD.RationalComplex) →
  C._≈C_
    (embedOriginalComplex (CD._*c_ z w))
    (C._*C_ (embedOriginalComplex z) (embedOriginalComplex w))
embedOriginalComplexMultiply
  (CD.complex a b) (CD.complex c d) =
  C.complex-equivalent
    (RP.≃-trans
      (embedSubtract (Q._*_ a c) (Q._*_ b d))
      (RP.+-cong
        (embedMultiply a c)
        (RP.-‿cong (embedMultiply b d))))
    (RP.≃-trans
      (embedAdd (Q._*_ a d) (Q._*_ b c))
      (RP.+-cong
        (embedMultiply a d)
        (embedMultiply b c)))

embedOriginalComplexCongruent :
  ∀ {z w : CD.RationalComplex} →
  z ≡ w →
  C._≈C_ (embedOriginalComplex z) (embedOriginalComplex w)
embedOriginalComplexCongruent {z} refl =
  C.≈C-refl (embedOriginalComplex z)

embedRationalImaginaryUnit :
  C._≈C_
    (embedOriginalComplex (CD.complex 0ℚ 1ℚ))
    C.imaginaryUnit
embedRationalImaginaryUnit =
  C.complex-equivalent RP.≃-refl RP.≃-refl

-- Original rational-CD Machin phase becomes an equality on the
-- selected pinned Bishop setoid complex carrier, without choosing
-- an additional imaginary-unit parameter or pi normalization.
originalMachinRationalCayleyIsBishopImaginaryUnit :
  C._≈C_
    (embedOriginalComplex Cayley.machinQuarterCayleyPhase)
    C.imaginaryUnit
originalMachinRationalCayleyIsBishopImaginaryUnit =
  C.≈C-trans
    (embedOriginalComplexCongruent
      Cayley.originalComplexMachinQuarterCayleyIsImaginaryUnit)
    embedRationalImaginaryUnit
