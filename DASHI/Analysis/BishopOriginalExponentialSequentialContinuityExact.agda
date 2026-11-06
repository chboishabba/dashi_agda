{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalExponentialSequentialContinuityExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: GENUINE ORIGINAL BISHOP REAL EXPONENTIAL
-- IS SEQUENTIALLY CONTINUOUS AT EVERY PINNED BISHOP REAL.
--
-- No exp-continuity axiom or second function carrier. Use:
--
-- 1. The ACTUAL literal expTerm(x,n)=x^n/n! finite sums.
-- 2. Existing BishopFinitePowerSeriesSequentialContinuityExact.
-- 3. NEW source compact-uniform original exp factorial majorant.
-- 4. Vendored Sequence.convergent⇒bounded: every convergent input
--    history has a BISHOP-real bound on its positive indices.
-- 5. Existing exact Bishop uniform-limit three-leg triangle
--    and inverse-precision splitting.
--
-- The selected common radius M=max(bound input,|limit|) is
-- NONNEGATIVE; the same source exp cutoff works at each positive
-- history index and at the target limit. The finite approximant
-- is continuous and the three-leg inequality proves source exp
-- continuity directly, without any derivative-limit interchange.
--
-- This closes original real exp_B CONTINUITY at source level,
-- pending Agda 2.9 --safe kernel elaboration.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as R
import RealProperties as RP
import Sequence as S

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Analysis.BishopFinitePowerSeriesSequentialContinuityExact as Finite
import DASHI.Analysis.BishopOriginalExponentialUniformCompactTailExact as Tail
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform

sourceExpFinitePartial : (point : R.ℝ) → Nat → R.ℝ
sourceExpFinitePartial point count =
  S.SeriesOf (Exp.expTerm point) count

sourceExpOriginalCoefficient : Nat → R.ℝ
sourceExpOriginalCoefficient degree =
  Exp.embed (Exp.inverseFactorial degree)

sourceExpFinitePartialIsNativePowerSeries :
  (point : R.ℝ) (count : Nat) →
  R._≃_
    (sourceExpFinitePartial point count)
    (Finite.finiteOriginalBishopPowerSeries
      sourceExpOriginalCoefficient point count)
sourceExpFinitePartialIsNativePowerSeries point count =
  Ext.seriesPartialSumsCongruent
    (λ degree →
      RP.*-comm
        (R.pow point degree)
        (sourceExpOriginalCoefficient degree))
    count

sourceExpFinitePartialSequentiallyContinuous :
  (input : Nat → R.ℝ) →
  (limit : R.ℝ) →
  S._ConvergesTo_ input limit →
  (count : Nat) →
  S._ConvergesTo_
    (λ n → sourceExpFinitePartial (input n) count)
    (sourceExpFinitePartial limit count)
sourceExpFinitePartialSequentiallyContinuous
    input limit inputConverges count =
  S.xₙ→x∧x≃y⇒xₙ→y
    (S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc n) →
        RP.≃-symm
          (sourceExpFinitePartialIsNativePowerSeries (input (suc n)) count)})
      (Finite.finiteOriginalBishopPowerSeries
        sourceExpOriginalCoefficient limit count ,
        Finite.bishopFinitePowerSeriesSequentiallyContinuous
          sourceExpOriginalCoefficient input limit
          inputConverges count))
    (RP.≃-symm
      (sourceExpFinitePartialIsNativePowerSeries limit count))

-- The original vendor boundedness witness only covers nonzero
-- history indices. This is ENOUGH, since Sequence.con* tests
-- convergence only at indices n past its positive cutoff; we do
-- not need a fake value for the zero-th input.
originalBishopExpSequentiallyContinuous :
  Uniform.SequentiallyContinuous Exp.bishopExp
originalBishopExpSequentiallyContinuous
    input limit inputConverges
    with S.convergent⇒bounded (limit , inputConverges)
... | sequenceBound , S.bound* positiveIndexBound =
  let
    bound = R._⊔_ sequenceBound (R.∣ limit ∣)

    pointBounded : (n : Nat) → .{{_ : S.NonZero n}} →
      R._≤_ (R.∣ input n ∣) bound
    pointBounded n =
      RP.≤-trans
        (positiveIndexBound n)
        (RP.x≤x⊔y sequenceBound (R.∣ limit ∣))

    limitBounded : R._≤_ (R.∣ limit ∣) bound
    limitBounded =
      RP.x≤y⊔x (R.∣ limit ∣) sequenceBound

    boundNonnegative : R.NonNegative bound
    boundNonnegative =
      RP.0≤x⇒nonNegx
        (RP.≤-trans
          (RP.nonNegx⇒0≤x (RP.nonNeg∣x∣ limit))
          limitBounded)

    open RP.ℝ-Solver
  in
  S.con*
    (λ
      { (suc k-1) →
        let
          k = suc k-1
          fine = 2 * (2 * k)
          cutoffIndex = Tail.sourceExpUniformTailCutoff bound fine
          finiteConverges =
            sourceExpFinitePartialSequentiallyContinuous
              input limit inputConverges cutoffIndex
          receipt =
            S.convergence-getter
              (sourceExpFinitePartial limit cutoffIndex , finiteConverges)
              (2 * k)
          cutoff = suc (proj₁ receipt)
          quarter = Uniform.inversePrecision fine
          half = Uniform.inversePrecision (2 * k)
          whole = Uniform.inversePrecision k
        in
        proj₁ receipt ,
        (λ
          { (suc n-1) n≥cutoff →
            let
              n = suc n-1

              tailAtInput =
                Tail.sourceExpUniformApproximationOnBall
                  bound boundNonnegative fine
                  (input n) (pointBounded n)

              tailAtLimit =
                Tail.sourceExpUniformApproximationOnBall
                  bound boundNonnegative fine
                  limit limitBounded

              middle =
                proj₂ receipt n n≥cutoff

              reversedFirst =
                RP.≤-respˡ-≃
                  (RP.∣x-y∣≃∣y-x∣
                    (sourceExpFinitePartial (input n) cutoffIndex)
                    (Exp.bishopExp (input n)))
                  tailAtInput
            in
            let open RP.≤-Reasoning
            in begin
              R.∣ R._-_
                (Exp.bishopExp (input n))
                (Exp.bishopExp limit) ∣
                ≤⟨ Uniform.threeLegTriangle
                      (Exp.bishopExp (input n))
                      (sourceExpFinitePartial (input n) cutoffIndex)
                      (sourceExpFinitePartial limit cutoffIndex)
                      (Exp.bishopExp limit) ⟩
              R._+_
                (R.∣ R._-_
                  (Exp.bishopExp (input n))
                  (sourceExpFinitePartial (input n) cutoffIndex) ∣)
                (R._+_
                  (R.∣ R._-_
                    (sourceExpFinitePartial (input n) cutoffIndex)
                    (sourceExpFinitePartial limit cutoffIndex) ∣)
                  (R.∣ R._-_
                    (sourceExpFinitePartial limit cutoffIndex)
                    (Exp.bishopExp limit) ∣))
                ≤⟨ RP.+-mono-≤ reversedFirst
                      (RP.+-mono-≤ middle tailAtLimit) ⟩
              R._+_ quarter (R._+_ half quarter)
                ≈⟨ solve 3
                      (λ q h q′ →
                        q ⊕ (h ⊕ q′) ⊜ (q ⊕ q′) ⊕ h)
                      RP.≃-refl quarter half quarter ⟩
              R._+_ (R._+_ quarter quarter) half
                ≈⟨ RP.+-congˡ half (Uniform.halfPlusHalf (2 * k)) ⟩
              R._+_ half half
                ≈⟨ Uniform.halfPlusHalf k ⟩
              whole ∎
          })
      })
