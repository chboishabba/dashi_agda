{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopGroupedCauchyParityTelescopeExact where

------------------------------------------------------------------------
-- K05: UNIVERSAL FINITE GROUPED-COEFFICIENT TELESCOPE, ON THE
-- ACTUAL BISHOP REAL SEQUENCE / SETOID RING.
--
-- Abstract only the two degree-by-degree EVEN and ODD binomial
-- equalities. The boundary/telescope consequences are proved by
-- induction for ALL N. This identifies the exact index needed by
-- the original complex Round11 identity, rather than invoking a
-- false uncorrected grouped Cauchy identity.
--
-- Let E_n = even/even, O_n = odd/odd, and P_n = original cosine.
-- Source even-degree identity: E_n - O_(n-1) = P_n (O_(-1)=0).
-- Then
--   Sum_(k<N) (E_k-O_k) - Sum_(k<N) P_k = -O_(N-1)
-- for every N, with no limits or triangle-inequality majorants.
--
-- This proof is agnostic to factorial sources; paying the original
-- even/odd source degree-split binomial identities remains a separate
-- explicit Agda obligation. It does NOT assume the final product.
--
-- Source: Newton/binomial; Cauchy; Bishop/Bridges; Murray/Csimma;
-- original DASHI finite Cauchy row and real setoid ring solver.
-- Exact-head Agda-2.9 acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as R
import RealProperties as RP
import Sequence as S

import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext

previousCoefficient : (Nat → R.ℝ) → Nat → R.ℝ
previousCoefficient coefficients zero = R.0ℝ
previousCoefficient coefficients (suc n) = coefficients n

realGroupedResidual :
  (evenEven oddOdd sourceEven : Nat → R.ℝ) →
  Nat → R.ℝ
realGroupedResidual evenEven oddOdd sourceEven count =
  R._-_
    (S.SeriesOf (λ degree →
      R._-_ (evenEven degree) (oddOdd degree)) count)
    (S.SeriesOf sourceEven count)

recoverEvenEven :
  (evenEven oddOdd sourceEven : Nat → R.ℝ) →
  (sourceDegree :
    ∀ n →
      R._≃_
        (R._-_ (evenEven n)
          (previousCoefficient oddOdd n))
        (sourceEven n)) →
  (n : Nat) →
  R._≃_
    (evenEven n)
    (R._+_ (sourceEven n)
      (previousCoefficient oddOdd n))
recoverEvenEven ee oo source sourceDegree n =
  let open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 2
      (λ e o → e ⊜ (e ⊖ o) ⊕ o)
      RP.≃-refl
      (ee n) (previousCoefficient oo n))
    (RP.+-congʳ
      (previousCoefficient oo n)
      (sourceDegree n))

realDegreeDefect :
  (evenEven oddOdd sourceEven : Nat → R.ℝ) →
  (sourceDegree :
    ∀ n →
      R._≃_
        (R._-_ (evenEven n)
          (previousCoefficient oddOdd n))
        (sourceEven n)) →
  (n : Nat) →
  R._≃_
    (R._-_
      (R._-_ (evenEven n) (oddOdd n))
      (sourceEven n))
    (R._-_ (previousCoefficient oddOdd n) (oddOdd n))
realDegreeDefect ee oo source sourceDegree n =
  let
    old = previousCoefficient oo n
    b = oo n
    v = source n
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-congʳ
      (R.-_ v)
      (RP.+-congʳ
        (R.-_ b)
        (recoverEvenEven ee oo source sourceDegree n)))
    (solve 3
      (λ v′ o′ b′ →
        ((v′ ⊕ o′) ⊖ b′) ⊖ v′
        ⊜ o′ ⊖ b′)
      RP.≃-refl v old b)

universalFiniteRealGroupedTelescope :
  (evenEven oddOdd sourceEven : Nat → R.ℝ) →
  (sourceDegree :
    ∀ n →
      R._≃_
        (R._-_ (evenEven n)
          (previousCoefficient oddOdd n))
        (sourceEven n)) →
  (count : Nat) →
  R._≃_
    (realGroupedResidual evenEven oddOdd sourceEven count)
    (R.-_ (previousCoefficient oddOdd count))
universalFiniteRealGroupedTelescope ee oo source sourceDegree zero =
  let open RP.ℝ-Solver
  in
  solve 0
    ((Κ 0ℚᵘ ⊖ Κ 0ℚᵘ) ⊜ (⊝ Κ 0ℚᵘ))
    RP.≃-refl
universalFiniteRealGroupedTelescope ee oo source sourceDegree (suc count) =
  let
    leftPrefix = S.SeriesOf
      (λ degree → R._-_ (ee degree) (oo degree)) count
    sourcePrefix = S.SeriesOf source count
    a = ee count
    b = oo count
    v = source count
    old = previousCoefficient oo count
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 5
      (λ left′ right′ e′ o′ v′ →
        (left′ ⊕ (e′ ⊖ o′)) ⊖ (right′ ⊕ v′)
        ⊜ (left′ ⊖ right′) ⊕ ((e′ ⊖ o′) ⊖ v′))
      RP.≃-refl leftPrefix sourcePrefix a b v)
    (RP.≃-trans
      (RP.+-cong
        (universalFiniteRealGroupedTelescope
          ee oo source sourceDegree count)
        (realDegreeDefect ee oo source sourceDegree count))
      (solve 2
        (λ o′ b′ →
          (⊝ o′) ⊕ (o′ ⊖ b′) ⊜ ⊝ b′)
        RP.≃-refl old b))

imagGroupedResidual :
  (evenOdd oddEven sourceOdd : Nat → R.ℝ) →
  Nat → R.ℝ
imagGroupedResidual evenOdd oddEven sourceOdd count =
  R._-_
    (S.SeriesOf (λ degree →
      R._+_ (evenOdd degree) (oddEven degree)) count)
    (S.SeriesOf sourceOdd count)

universalFiniteImagGroupedEquality :
  (evenOdd oddEven sourceOdd : Nat → R.ℝ) →
  (sourceDegree :
    ∀ n →
      R._≃_
        (R._+_ (evenOdd n) (oddEven n))
        (sourceOdd n)) →
  (count : Nat) →
  R._≃_
    (imagGroupedResidual evenOdd oddEven sourceOdd count)
    R.0ℝ
universalFiniteImagGroupedEquality evenOdd oddEven sourceOdd degree count =
  RP.≃-trans
    (RP.+-congʳ
      (R.-_ (S.SeriesOf sourceOdd count))
      (Ext.seriesPartialSumsCongruent degree count))
    (RP.+-inverseʳ
      (S.SeriesOf sourceOdd count))
