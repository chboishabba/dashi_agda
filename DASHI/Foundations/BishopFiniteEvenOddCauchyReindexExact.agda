{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopFiniteEvenOddCauchyReindexExact where

------------------------------------------------------------------------
-- ALL-N FINITE PARITY REINDEX ON THE ORIGINAL BISHOP REAL CARRIER.
--
-- For any f : Nat -> BishopReal, let E_n = Σ(k<n) f(2k)
-- and O_n = Σ(k<n) f(2k+1). Then
--   Σ(k<2n)   f(k) = E_n + O_n
--   Σ(k<2n+1) f(k) = E_(n+1) + O_n.
--
-- The same identities split EVERY original finite Cauchy coefficient
-- by parity, with no factorial, scalar, or analytic hypothesis.
--
-- This pays the universal index reindexing part of the K05 grouped
-- signed-factorial coefficient identity. The sign identities and the
-- all-degree factorial-to-Round11 signed-term transport remain.
--
-- Cauchy/binomial; Bishop and Bridges; Murray/Csimma Bishop library.
-- DASHI finite sum parity constructor. Agda kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as N

import Real as R
import RealProperties as RP
import Sequence as S

import DASHI.Analysis.BishopConvergentDoubleTailExact as D
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row

evenPartial oddPartial : (Nat → R.ℝ) → Nat → R.ℝ
evenPartial f n =
  S.SeriesOf (λ k → f (D.double k)) n
oddPartial f n =
  S.SeriesOf (λ k → f (suc (D.double k))) n

finiteEvenOddSplit :
  (f : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (S.SeriesOf f (D.double n))
    (R._+_ (evenPartial f n) (oddPartial f n))
finiteEvenOddSplit f zero =
  RP.≃-symm (RP.+-identityʳ R.0ℝ)
finiteEvenOddSplit f (suc n) =
  let
    e = evenPartial f n
    o = oddPartial f n
    a = f (D.double n)
    b = f (suc (D.double n))
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-congʳ b
      (RP.+-congʳ a
        (finiteEvenOddSplit f n)))
    (solve 4
      (λ e o a b →
        ((e ⊕ o) ⊕ a) ⊕ b
        ⊜ (e ⊕ a) ⊕ (o ⊕ b))
      RP.≃-refl e o a b)

finiteOddLengthSplit :
  (f : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (S.SeriesOf f (suc (D.double n)))
    (R._+_ (evenPartial f (suc n)) (oddPartial f n))
finiteOddLengthSplit f n =
  let
    e = evenPartial f n
    o = oddPartial f n
    a = f (D.double n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-congʳ a (finiteEvenOddSplit f n))
    (solve 3
      (λ e o a → (e ⊕ o) ⊕ a ⊜ (e ⊕ a) ⊕ o)
      RP.≃-refl e o a)

cauchySummand :
  (left right : Nat → R.ℝ) →
  (degree : Nat) →
  Nat → R.ℝ
cauchySummand left right degree k =
  R._*_ (left k) (right (degree N.∸ k))

finiteCauchyEvenDegreeSplit :
  (left right : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (Row.cauchyCoefficient left right (D.double n))
    (R._+_
      (evenPartial
        (cauchySummand left right (D.double n))
        (suc n))
      (oddPartial
        (cauchySummand left right (D.double n))
        n))
finiteCauchyEvenDegreeSplit left right n =
  RP.≃-trans
    (FinSum.finSumIsSeriesOf
      (cauchySummand left right (D.double n))
      (suc (D.double n)))
    (finiteOddLengthSplit
      (cauchySummand left right (D.double n)) n)

finiteCauchyOddDegreeSplit :
  (left right : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (Row.cauchyCoefficient left right (suc (D.double n)))
    (R._+_
      (evenPartial
        (cauchySummand left right (suc (D.double n)))
        (suc n))
      (oddPartial
        (cauchySummand left right (suc (D.double n)))
        (suc n)))
finiteCauchyOddDegreeSplit left right n =
  RP.≃-trans
    (FinSum.finSumIsSeriesOf
      (cauchySummand left right (suc (D.double n)))
      (suc (suc (D.double n))))
    (finiteEvenOddSplit
      (cauchySummand left right (suc (D.double n))) (suc n))
