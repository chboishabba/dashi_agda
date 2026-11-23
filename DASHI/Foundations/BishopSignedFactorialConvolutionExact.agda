module DASHI.Foundations.BishopSignedFactorialConvolutionExact where

-- Specialization of the existing Bishop finite exponential convolution.
-- Original coefficient, zero-term and parity owners are retained.
-- Finite source only: no analytic limit or physical CMP102 claim.

open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as N
import Real as B
import RealProperties as P
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialFiniteCauchyCoefficientExact as C
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as Cong
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Positive
import DASHI.Foundations.BishopFiniteEvenOddSeriesReindexExact as Parity
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E

signedTerm : Nat → Nat → B.ℝ
signedTerm m j =
  B._*_ (Exp.expTerm B.1ℝ j)
    (Exp.expTerm (B.- B.1ℝ) (m N.∸ j))

signedPositiveDegreeZero :
  ∀ n → B._≃_
    (C.cauchyCoefficient B.1ℝ (B.- B.1ℝ) (suc n)) B.0ℝ
signedPositiveDegreeZero n =
  P.≃-trans
    (C.finiteExponentialCauchyCoefficient B.1ℝ (B.- B.1ℝ) (suc n))
    (P.≃-trans
      (Cong.expTermCongruent (P.+-inverseʳ B.1ℝ) (suc n))
      (Positive.expTermZeroAtPositive n))

-- The parity donor is exclusive; this adapter explicitly retains the endpoint.
inclusiveParity :
  (f : Nat → B.ℝ) → ∀ n →
  B._≃_
    (B.∑₀ f (suc (E.evenExponent n)))
    (B._+_
      (B._+_ (B.∑₀ (Parity.evenTerms f) n)
             (B.∑₀ (Parity.oddTerms f) n))
      (f (E.evenExponent n)))
inclusiveParity f n =
  P.+-cong (Parity.originalBishopFiniteEvenOddSumReindex f n) P.≃-refl

signedInclusiveEvenDegreeZero :
  ∀ n →
  let m = E.evenExponent (suc n)
      f = signedTerm m
  in B._≃_
    (B._+_
      (B._+_ (B.∑₀ (Parity.evenTerms f) (suc n))
             (B.∑₀ (Parity.oddTerms f) (suc n)))
      (f m))
    B.0ℝ
signedInclusiveEvenDegreeZero n =
  let m = E.evenExponent (suc n)
      f = signedTerm m
  in P.≃-trans
    (P.≃-symm (inclusiveParity f (suc n)))
    (P.≃-trans
      (P.≃-symm (FinSum.finSumIsSeriesOf f (suc m)))
      (signedPositiveDegreeZero (suc (E.evenExponent n))))
