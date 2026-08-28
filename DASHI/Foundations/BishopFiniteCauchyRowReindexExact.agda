module DASHI.Foundations.BishopFiniteCauchyRowReindexExact where

------------------------------------------------------------------------
-- FINITE CAUCHY TRIANGLE <-> MERTENS ROW FORM
--
-- For finite Bishop-real sequences define
--
--   c_n = sum_{k=0}^n a_k b_{n-k}
--   T_N = sum_{n<N} c_n
--   M_N = sum_{k<N} a_k B_{N-k},  B_m = sum_{j<m} b_j.
--
-- Then T_N ~= M_N for every N.  The proof uses the head recursion of stdlib
-- Fin-sums; no analytic convergence and no quotient/rearrangement authority is
-- involved.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Nat.Base as ℕ

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
open import DASHI.Physics.YangMills.CompactLieProofLevel

module BishopSum = SemiringSum BishopP.+-*-semiring

shift : (Nat → BishopReal.ℝ) → Nat → BishopReal.ℝ
shift terms n = terms (suc n)

cauchyCoefficient :
  (Nat → BishopReal.ℝ) →
  (Nat → BishopReal.ℝ) →
  Nat → BishopReal.ℝ
cauchyCoefficient left right n =
  BishopSum.sum
    (λ index →
      BishopReal._*_
        (left (toℕ index))
        (right (n ℕ.∸ toℕ index)))

trianglePartial :
  (Nat → BishopReal.ℝ) →
  (Nat → BishopReal.ℝ) →
  Nat → BishopReal.ℝ
trianglePartial left right count =
  FinSum.finSum (cauchyCoefficient left right) count

mertensRowPartial :
  (Nat → BishopReal.ℝ) →
  (Nat → BishopReal.ℝ) →
  Nat → BishopReal.ℝ
mertensRowPartial left right count =
  BishopSum.sum
    (λ index →
      BishopReal._*_
        (left (toℕ index))
        (FinSum.finSum right (count ℕ.∸ toℕ index)))

cauchyCoefficientZero :
  ∀ left right →
  BishopReal._≃_
    (cauchyCoefficient left right zero)
    (BishopReal._*_ (left zero) (right zero))
cauchyCoefficientZero left right =
  BishopP.+-identityʳ
    (BishopReal._*_ (left zero) (right zero))

cauchyCoefficientSuccessor :
  ∀ left right n →
  BishopReal._≃_
    (cauchyCoefficient left right (suc n))
    (BishopReal._+_
      (BishopReal._*_ (left zero) (right (suc n)))
      (cauchyCoefficient (shift left) right n))
cauchyCoefficientSuccessor left right n = BishopP.≃-refl

finSumHead :
  ∀ terms count →
  BishopReal._≃_
    (FinSum.finSum terms (suc count))
    (BishopReal._+_
      (terms zero)
      (FinSum.finSum (shift terms) count))
finSumHead terms count = BishopP.≃-refl

mertensRowHead :
  ∀ left right count →
  BishopReal._≃_
    (mertensRowPartial left right (suc count))
    (BishopReal._+_
      (BishopReal._*_
        (left zero)
        (FinSum.finSum right (suc count)))
      (mertensRowPartial (shift left) right count))
mertensRowHead left right count = BishopP.≃-refl

shiftedCoefficientSum :
  ∀ left right count →
  BishopReal._≃_
    (FinSum.finSum
      (λ n → cauchyCoefficient left right (suc n))
      count)
    (BishopReal._+_
      (FinSum.finSum
        (λ n → BishopReal._*_ (left zero) (right (suc n)))
        count)
      (trianglePartial (shift left) right count))
shiftedCoefficientSum left right count =
  BishopP.≃-trans
    (BishopSum.sum-cong-≋
      (λ index →
        cauchyCoefficientSuccessor
          left right (toℕ index)))
    (BishopSum.∑-distrib-+
      (λ index →
        BishopReal._*_ (left zero) (right (suc (toℕ index))))
      (λ index →
        cauchyCoefficient (shift left) right (toℕ index)))

scaledShiftedRightSum :
  ∀ left right count →
  BishopReal._≃_
    (FinSum.finSum
      (λ n → BishopReal._*_ (left zero) (right (suc n)))
      count)
    (BishopReal._*_
      (left zero)
      (FinSum.finSum (shift right) count))
scaledShiftedRightSum left right count =
  BishopP.≃-symm
    (BishopSum.*-distribˡ-sum
      (left zero)
      (λ index → right (suc (toℕ index))))

headAndShiftedRightIsPrefix :
  ∀ left right count →
  BishopReal._≃_
    (BishopReal._+_
      (BishopReal._*_ (left zero) (right zero))
      (BishopReal._*_
        (left zero)
        (FinSum.finSum (shift right) count)))
    (BishopReal._*_
      (left zero)
      (FinSum.finSum right (suc count)))
headAndShiftedRightIsPrefix left right count =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.*-distribˡ-+
        (left zero)
        (right zero)
        (FinSum.finSum (shift right) count)))
    (BishopP.*-congˡ
      (BishopP.≃-symm (finSumHead right count)))

triangleIsMertensRow :
  ∀ left right count →
  BishopReal._≃_
    (trianglePartial left right count)
    (mertensRowPartial left right count)
triangleIsMertensRow left right zero = BishopP.≃-refl
triangleIsMertensRow left right (suc count) =
  let
    a0 = left zero
    b0 = right zero
    shiftedRightSum = FinSum.finSum (shift right) count
    shiftedTriangle = trianglePartial (shift left) right count
    shiftedRow = mertensRowPartial (shift left) right count
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (finSumHead (cauchyCoefficient left right) count)
    (BishopP.≃-trans
      (BishopP.+-cong
        (cauchyCoefficientZero left right)
        (shiftedCoefficientSum left right count))
      (BishopP.≃-trans
        (BishopP.+-congˡ
          shiftedTriangle
          (BishopP.+-congˡ
            (FinSum.finSum
              (λ n → BishopReal._*_ a0 (right (suc n))) count)
            BishopP.≃-refl))
        (BishopP.≃-trans
          (solve 4
            (λ head scaled tail →
              head ⊕ (scaled ⊕ tail)
              ⊜ (head ⊕ scaled) ⊕ tail)
            BishopP.≃-refl
            (BishopReal._*_ a0 b0)
            (FinSum.finSum
              (λ n → BishopReal._*_ a0 (right (suc n))) count)
            shiftedTriangle
            BishopReal.0ℝ)
          (BishopP.≃-trans
            (BishopP.+-cong
              (BishopP.≃-trans
                (BishopP.+-congˡ
                  (BishopReal._*_ a0 b0)
                  (scaledShiftedRightSum left right count))
                (headAndShiftedRightIsPrefix left right count))
              (triangleIsMertensRow (shift left) right count))
            (BishopP.≃-symm
              (mertensRowHead left right count))))))

bishopFiniteCauchyRowReindexLevel : ProofLevel
bishopFiniteCauchyRowReindexLevel = machineChecked
