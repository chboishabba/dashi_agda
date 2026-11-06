{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMonotoneDoubleSubsequenceLimitExact where

------------------------------------------------------------------------
-- EXACT COFINALITY / INTERLEAVING BRIDGE FOR BISHOP REAL SEQUENCES.
--
-- If a Bishop-real history is nondecreasing and its genuine doubled
-- subsequence converges to L, the ENTIRE history converges to L.
-- No classically assumed monotone-convergence theorem, no floor or
-- division of Nat, and no choice of a new real is needed.
--
-- K05 uses this to promote positive factorial Cauchy triangles from
-- the even cutoffs bracketed between finite square products.
--
-- Bishop and Bridges; Murray (2022); Csimma pinned Bishop Sequence.
-- DASHI exact-sequence adaptation. Kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Product.Base using (proj₁; proj₂)

import Real as R
import RealProperties as RP
import Sequence as S

import DASHI.Analysis.BishopConvergentDoubleTailExact as D
import DASHI.Foundations.BishopExponentialCauchyProductExact as Exp

indexBelowDouble : (n : Nat) → n N.≤ D.double n
indexBelowDouble n rewrite Exp.doubleIsAddSelf n =
  NP.m≤m+n n n

doubleHistoryIncreasing :
  (history : Nat → R.ℝ) →
  S._isIncreasing history →
  S._isIncreasing (λ n → history (D.double n))
doubleHistoryIncreasing history increasing n =
  S.isIncreasing⇒isIncreasing₂ increasing
    (D.double (suc n))
    (D.double n)
    (NP.<⇒≤ (D.doubleStrict n))

historyBelowLimitFromDouble :
  (history : Nat → R.ℝ) →
  (limit : R.ℝ) →
  S._isIncreasing history →
  S._ConvergesTo_ (λ n → history (D.double n)) limit →
  (n : Nat) → R._≤_ (history n) limit
historyBelowLimitFromDouble history limit increasing converges n =
  RP.≤-trans
    (S.isIncreasing⇒isIncreasing₂ increasing
      (D.double n) n (indexBelowDouble n))
    (S.xₙisIncreasing⇒xₙ≤limxₙ
      (doubleHistoryIncreasing history increasing)
      (limit , converges) n)

distanceDecreasesBelowUpper :
  (x y limit : R.ℝ) →
  R._≤_ x y →
  R._≤_ y limit →
  R._≤_
    (R.∣ R._-_ y limit ∣)
    (R.∣ R._-_ x limit ∣)
distanceDecreasesBelowUpper x y limit x≤y y≤limit =
  let
    x≤limit = RP.≤-trans x≤y y≤limit
    absY =
      RP.≃-trans
        (RP.∣x-y∣≃∣y-x∣ y limit)
        (RP.nonNegx⇒∣x∣≃x
          (RP.0≤x⇒nonNegx
            (RP.nonNegx⇒0≤x y≤limit)))
    absX =
      RP.≃-trans
        (RP.∣x-y∣≃∣y-x∣ x limit)
        (RP.nonNegx⇒∣x∣≃x
          (RP.0≤x⇒nonNegx
            (RP.nonNegx⇒0≤x x≤limit)))
  in
  RP.≤-respˡ-≃ (RP.≃-symm absY)
    (RP.≤-respʳ-≃ (RP.≃-symm absX)
      (RP.+-monoʳ-≤ limit (RP.neg-mono-≤ x≤y)))

monotoneDoubleConvergesImpliesFullConverges :
  (history : Nat → R.ℝ) →
  (limit : R.ℝ) →
  S._isIncreasing history →
  S._ConvergesTo_ (λ n → history (D.double n)) limit →
  S._ConvergesTo_ history limit
monotoneDoubleConvergesImpliesFullConverges
    history limit increasing (S.con* doubleConverges) =
  S.con* (λ
    { (suc k-1) →
      let
        k = suc k-1
        receipt = doubleConverges k
        N = suc (proj₁ receipt)
        atN = proj₂ receipt N NP.≤-refl
        sourceAtN = history (D.double N)
        sourceBelowLimit =
          historyBelowLimitFromDouble
            history limit increasing (S.con* doubleConverges)
        cutoff = suc (D.double N)
      in
      D.double N ,
      (λ
        { (suc n-1) n≥cutoff →
          let
            n = suc n-1
            doubleN≤n =
              NP.≤-trans
                (NP.n≤1+n (D.double N))
                n≥cutoff
            atDoubleN≤atN =
              S.isIncreasing⇒isIncreasing₂ increasing
                n (D.double N) doubleN≤n
          in
          RP.≤-trans
            (distanceDecreasesBelowUpper
              sourceAtN (history n) limit
              atDoubleN≤atN (sourceBelowLimit n))
            atN
        })
    })
