module DASHI.Foundations.BishopSquareNonnegativeExact where

------------------------------------------------------------------------
-- EVERY VENDORED BISHOP REAL SQUARE IS NONNEGATIVE
--
-- This closes a generic scalar seam that several Yang--Mills owners had kept
-- in their square-root interfaces.  The proof descends to the concrete
-- `Real.nonNeg*` representation: every sampled value of x*x is a rational
-- square, hence >= 0, which is stronger than the required >= -1/n bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Nat.Base as Nat using (NonZero; z≤n)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _*_; -_; _≤_; NonNegative; nonNegative)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₁; inj₂)
import NonReflectiveQ as ℚSolver
import Real as BishopReal

open import DASHI.Physics.YangMills.CompactLieProofLevel

zeroRationalNonnegative : NonNegative 0ℚᵘ
zeroRationalNonnegative =
  ℚ.nonNegative ℚP.≤-refl

rationalSquareNonnegative :
  (value : ℚᵘ) → 0ℚᵘ ℚ.≤ (value ℚ.* value)
rationalSquareNonnegative value with ℚP.≤-total 0ℚᵘ value
... | inj₁ zero≤value =
  let
    instance
      zeroNN : NonNegative 0ℚᵘ
      zeroNN = zeroRationalNonnegative
      valueNN : NonNegative value
      valueNN = ℚ.nonNegative zero≤value
    raw : (0ℚᵘ ℚ.* 0ℚᵘ) ℚ.≤ (value ℚ.* value)
    raw = ℚP.*-mono-≤-nonNeg zero≤value zero≤value
  in
  ℚP.≤-respˡ-≃ (ℚP.*-zeroˡ 0ℚᵘ) raw
... | inj₂ value≤zero =
  let
    negValue = ℚ.- value
    zero≤negValue : 0ℚᵘ ℚ.≤ negValue
    zero≤negValue =
      ℚP.≤-respˡ-≃
        (ℚP.≃-sym (ℚP.neg-involutive 0ℚᵘ))
        (ℚP.neg-mono-≤ value≤zero)
    instance
      zeroNN : NonNegative 0ℚᵘ
      zeroNN = zeroRationalNonnegative
      negNN : NonNegative negValue
      negNN = ℚ.nonNegative zero≤negValue
    negSquare : 0ℚᵘ ℚ.≤ (negValue ℚ.* negValue)
    negSquare =
      ℚP.≤-respˡ-≃ (ℚP.*-zeroˡ 0ℚᵘ)
        (ℚP.*-mono-≤-nonNeg zero≤negValue zero≤negValue)
    squareEquivalent :
      (negValue ℚ.* negValue) ℚ.≃ (value ℚ.* value)
    squareEquivalent =
      let open ℚSolver in
      solve 1
        (λ x → ((⊝ x) ⊗ (⊝ x)) ⊜ (x ⊗ x))
        ℚP.≃-refl value
  in
  ℚP.≤-respʳ-≃ squareEquivalent negSquare

negativeOneOverBelowZero :
  (n : Nat.ℕ) → .{{_ : NonZero n}} →
  ℚ.- (+ 1 / n) ℚ.≤ 0ℚᵘ
negativeOneOverBelowZero n =
  ℚP.p≤q⇒p-q≤0
    (ℚP.nonNegative⁻¹ (+ 1 / n))

bishopSquareNonnegative :
  (value : BishopReal.ℝ) →
  BishopReal.NonNegative (BishopReal._*_ value value)
bishopSquareNonnegative value =
  BishopReal.nonNeg* λ n {n≢0} →
    let
      instance
        nNonZero : NonZero n
        nNonZero = Nat.≢-nonZero n≢0
      sampled = BishopReal.seq (BishopReal._*_ value value) n
    in
    ℚP.≤-trans
      (negativeOneOverBelowZero n)
      (rationalSquareNonnegative sampled)

bishopSquareNonnegativeLevel : ProofLevel
bishopSquareNonnegativeLevel = machineChecked
