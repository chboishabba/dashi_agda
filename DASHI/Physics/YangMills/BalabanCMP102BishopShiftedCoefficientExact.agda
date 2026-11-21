module DASHI.Physics.YangMills.BalabanCMP102BishopShiftedCoefficientExact where

-- Original CMP109 coefficients, with the sign carried by X = -w.
-- Finite endpoint extraction and coefficient targets; the actual
-- signed-row to factorial-interior identification is still an obligation.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as B
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as Sum
import DASHI.Foundations.BishopSignedFactorialConvolutionExact as Signed
import DASHI.Foundations.BishopFiniteEvenOddSeriesReindexExact as Parity
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as S

-- Both endpoints of a row of length n+2, with a length-n interior.
finiteTwoEndpointSplit :
  (f : Nat → B.ℝ) → ∀ n →
  B._≃_
    (Sum.finSum f (suc (suc n)))
    (B._+_ (B._+_ (f zero) (Sum.finSum (Row.shift f) n))
           (f (suc n)))
finiteTwoEndpointSplit f n =
  P.≃-trans
    (Row.finSumHead f (suc n))
    (P.≃-trans
      (P.+-cong P.≃-refl (Sum.finSumSuccessor (Row.shift f) n))
      (P.≃-symm
        (P.+-assoc (f zero) (Sum.finSum (Row.shift f) n) (f (suc n)))))

two : B.ℝ
two = B._⋆ (+ 2 / 1)

evenPart oddPart : Nat → B.ℝ
evenPart zero = B._*_ two (S.aCoefficient zero)
evenPart (suc n) =
  B._+_ (B._*_ two (S.aCoefficient (suc n)))
    (Row.cauchyCoefficient S.aCoefficient S.aCoefficient n)
oddPart zero = B.1ℝ
oddPart (suc zero) = B._*_ two (S.bCoefficient zero)
oddPart (suc (suc n)) =
  B._+_ (B._*_ two (S.bCoefficient (suc n)))
    (Row.cauchyCoefficient S.bCoefficient S.bCoefficient n)

shiftedBracketCoefficient : Nat → B.ℝ
shiftedBracketCoefficient n = B._-_ (oddPart n) (evenPart n)

shiftedBracketBaseZero :
  B._≃_ (shiftedBracketCoefficient zero) B.0ℝ
shiftedBracketBaseZero =
  let open P.ℝ-Solver
  in solve 0 (Κ 1ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ Κ (+ 1 / 2)) ⊜ Κ 0ℚᵘ)
    P.≃-refl

-- The exact original signed inclusive row (not a new coefficient family).
signedEvenRow signedOddRow : Nat → B.ℝ
signedEvenRow n =
  let m = E.evenExponent (suc n)
      f = Signed.signedTerm m
  in B._+_ (B.∑₀ (Parity.evenTerms f) (suc n)) (f m)
signedOddRow n =
  let m = E.evenExponent (suc n)
  in B.∑₀ (Parity.oddTerms (Signed.signedTerm m)) (suc n)

signedRowsCancel : ∀ n →
  B._≃_ (B._+_ (signedEvenRow n) (signedOddRow n)) B.0ℝ
signedRowsCancel n =
  let m = E.evenExponent (suc n)
      f = Signed.signedTerm m
      e = B.∑₀ (Parity.evenTerms f) (suc n)
      o = B.∑₀ (Parity.oddTerms f) (suc n)
      open P.ℝ-Solver
  in P.≃-trans
    (solve 3 (λ x y z → (x ⊕ z) ⊕ y ⊜ (x ⊕ y) ⊕ z)
      P.≃-refl e o (f m))
    (Signed.signedInclusiveEvenDegreeZero n)

-- Consumer only: both same-row boundary/interior identities remain to prove.
shiftedBracketZeroFromOriginalRows : ∀ n →
  B._≃_ (signedEvenRow n) (evenPart n) →
  B._≃_ (signedOddRow n) (B.- (oddPart n)) →
  B._≃_ (shiftedBracketCoefficient n) B.0ℝ
shiftedBracketZeroFromOriginalRows n ev od =
  let e = evenPart n
      o = oddPart n
      open P.ℝ-Solver
  in P.≃-trans
    (solve 2 (λ x y → y ⊖ x ⊜ ⊝ (x ⊕ (⊝ y)))
      P.≃-refl e o)
    (P.≃-trans
      (P.-‿cong (P.≃-trans (P.+-cong (P.≃-symm ev) (P.≃-symm od))
                            (signedRowsCancel n)))
      P.0≃-0)
