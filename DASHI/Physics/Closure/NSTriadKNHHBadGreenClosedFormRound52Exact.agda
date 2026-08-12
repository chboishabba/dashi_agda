module DASHI.Physics.Closure.NSTriadKNHHBadGreenClosedFormRound52Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Expose the exact finite Green forcing series without requiring alpha_q <= 1.
-- At depth n the list `weightedForcingTerms n` contains every earlier beta_k,
-- multiplied once by each later alpha_j encountered on its way to shell n.
-- Thus its sum is literally
--
--   sum_{k<n} beta_k prod_{k<j<n} alpha_j.
--
-- The recursive theorem below is deliberately list-based: it is constructive,
-- finite, and avoids importing a separate finite-product/indexed-sum library.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (map; _++_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadShellBarrierRound52Exact as Barrier

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (x ∷ xs) = x + sumℚ xs

sumAppend :
  ∀ xs ys → sumℚ (xs ++ ys) ≡ sumℚ xs + sumℚ ys
sumAppend [] ys = solve (sumℚ ys ∷ [])
sumAppend (x ∷ xs) ys =
  trans
    (cong (x +_) (sumAppend xs ys))
    (solve (x ∷ sumℚ xs ∷ sumℚ ys ∷ []))

sumScaled :
  ∀ a xs → sumℚ (map (a *_) xs) ≡ a * sumℚ xs
sumScaled a [] = solve (a ∷ [])
sumScaled a (x ∷ xs) =
  trans
    (cong (a * x +_) (sumScaled a xs))
    (solve (a ∷ x ∷ sumℚ xs ∷ []))

weightedForcingTerms :
  Barrier.GeneralHHBadRecurrence → Nat → List ℚ
weightedForcingTerms input zero = []
weightedForcingTerms input (suc n) =
  map (Barrier.alpha input n *_) (weightedForcingTerms input n)
  ++ (Barrier.forcing input n ∷ [])

forcingGreenResponse :
  Barrier.GeneralHHBadRecurrence → Nat → ℚ
forcingGreenResponse input zero = 0ℚ
forcingGreenResponse input (suc n) =
  Barrier.alpha input n * forcingGreenResponse input n
  + Barrier.forcing input n

weightedForcingTermsSumExact :
  (input : Barrier.GeneralHHBadRecurrence) →
  ∀ n →
  sumℚ (weightedForcingTerms input n) ≡ forcingGreenResponse input n
weightedForcingTermsSumExact input zero = refl
weightedForcingTermsSumExact input (suc n) =
  trans
    (sumAppend
      (map (Barrier.alpha input n *_) (weightedForcingTerms input n))
      (Barrier.forcing input n ∷ []))
    (trans
      (cong
        (λ left → left + sumℚ (Barrier.forcing input n ∷ []))
        (sumScaled (Barrier.alpha input n) (weightedForcingTerms input n)))
      (trans
        (cong
          (λ previous →
            Barrier.alpha input n * previous
            + sumℚ (Barrier.forcing input n ∷ []))
          (weightedForcingTermsSumExact input n))
        (solve
          ( Barrier.alpha input n
          ∷ forcingGreenResponse input n
          ∷ Barrier.forcing input n
          ∷ []))))

forcingGreenResponseNonnegative :
  (input : Barrier.GeneralHHBadRecurrence) →
  ∀ n → 0ℚ ≤ forcingGreenResponse input n
forcingGreenResponseNonnegative input zero = ℚP.≤-refl
forcingGreenResponseNonnegative input (suc n) =
  let instance
    alphaNNI = nonNegative (Barrier.alphaNonnegative input n)
    previousNNI = nonNegative (forcingGreenResponseNonnegative input n)
    inheritedNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg
        (Barrier.alpha input n) (forcingGreenResponse input n)
  in
  ℚP.+-mono-≤
    (ℚP.nonNegative⁻¹
      (Barrier.alpha input n * forcingGreenResponse input n))
    (Barrier.forcingNonnegative input n)

finiteGreenClosedFormConstructed : Bool
finiteGreenClosedFormConstructed = true

closedFormNeedsNoAlphaAtMostOne : Bool
closedFormNeedsNoAlphaAtMostOne = true

finiteGreenClosedFormConstructedIsTrue :
  finiteGreenClosedFormConstructed ≡ true
finiteGreenClosedFormConstructedIsTrue = refl
