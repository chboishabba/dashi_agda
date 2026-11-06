{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalExponentialFiniteFactorDerivativeExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY/LOG: FINITE DERIVATIVES OF LITERAL SOURCE exp_B.
--
-- Uses the actual Exp.expTerm x n = x^n / n!, original Bishop power
-- factor derivative and the previously proven exact embedded
-- inverse-factorial coefficient cancellation:
--   (n+1)/(n+1)! = 1/n!.
--
-- For every n:
--   d/dx expTerm(x,0) = 0;
--   d/dx expTerm(x,n+1) = expTerm(x,n).
-- Every finite source exponential partial has the corresponding
-- actual finite source derivative, as BishopFactorDerivativeAt.
-- No generic calculus authority, abstract exponential, or division
-- by a nonzero perturbation is introduced.
--
-- The *infinite* exponential derivative/continuity still requires
-- a native uniform factorial quotient-tail estimate. This file
-- does NOT supply a false analytical-limit interchange theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as Scale
import DASHI.Analysis.BishopInverseFactorialDerivativeCoefficientExact as Coeff
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal

sourceExponentialDerivativeTerm : R.ℝ → Nat → R.ℝ
sourceExponentialDerivativeTerm x zero = R.0ℝ
sourceExponentialDerivativeTerm x (suc n) = Exp.expTerm x n

originalSourceExpSuccessorCoefficientDerivative :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (R._*_
      (Exp.embed (Exp.inverseFactorial (suc n)))
      (Power.powerDerivative (suc n) x))
    (Exp.expTerm x n)
originalSourceExpSuccessorCoefficientDerivative x n =
  let
    coeff = Exp.embed (Exp.inverseFactorial (suc n))
    older = Exp.embed (Exp.inverseFactorial n)
    natural = NatReal.natReal (suc n)
    power = R.pow x n
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.*-cong RP.≃-refl
      (Power.powerDerivativeNatScale n x))
    (RP.≃-trans
      (RP.*-cong RP.≃-refl
        (Scale.recursiveScaleIsEmbeddedNaturalMultiply
          (suc n) power))
      (RP.≃-trans
        (solve 3
          (λ c n′ p →
            c ⊗ (n′ ⊗ p)
            ⊜ (n′ ⊗ c) ⊗ p)
          RP.≃-refl coeff natural power)
        (RP.≃-trans
          (RP.*-cong
            (RP.≃-symm
              (Scale.recursiveScaleIsEmbeddedNaturalMultiply
                (suc n) coeff))
            RP.≃-refl)
          (RP.≃-trans
            (RP.*-cong
              (Coeff.scaledInverseFactorialSuccessor n)
              RP.≃-refl)
            (RP.*-comm older power)))))

originalSourceExpTermFactorDerivative :
  (x : R.ℝ) (n : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → Exp.expTerm y n)
    x
    (sourceExponentialDerivativeTerm x n)
originalSourceExpTermFactorDerivative x zero =
  Factor.factorDerivativeCongruence
    (λ y →
      RP.*-comm
        (R.pow y zero)
        (Exp.embed (Exp.inverseFactorial zero)))
    (RP.*-zeroʳ (Exp.embed (Exp.inverseFactorial zero)))
    (Factor.factorDerivativeScale
      (Exp.embed (Exp.inverseFactorial zero))
      (Factor.powerFactorDerivative zero x))
originalSourceExpTermFactorDerivative x (suc n) =
  Factor.factorDerivativeCongruence
    (λ y →
      RP.*-comm
        (R.pow y (suc n))
        (Exp.embed (Exp.inverseFactorial (suc n))))
    (originalSourceExpSuccessorCoefficientDerivative x n)
    (Factor.factorDerivativeScale
      (Exp.embed (Exp.inverseFactorial (suc n)))
      (Factor.powerFactorDerivative (suc n) x))

sourceExponentialFinitePartial : R.ℝ → Nat → R.ℝ
sourceExponentialFinitePartial x count =
  Seq.SeriesOf (Exp.expTerm x) count

sourceExponentialFiniteDerivativePartial : R.ℝ → Nat → R.ℝ
sourceExponentialFiniteDerivativePartial x count =
  Seq.SeriesOf (sourceExponentialDerivativeTerm x) count

originalSourceExpFinitePartialFactorDerivative :
  (x : R.ℝ) (count : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → sourceExponentialFinitePartial y count)
    x
    (sourceExponentialFiniteDerivativePartial x count)
originalSourceExpFinitePartialFactorDerivative x zero =
  Factor.factorDerivativeZero x
originalSourceExpFinitePartialFactorDerivative x (suc count) =
  Factor.factorDerivativeAdd
    (originalSourceExpFinitePartialFactorDerivative x count)
    (originalSourceExpTermFactorDerivative x count)
