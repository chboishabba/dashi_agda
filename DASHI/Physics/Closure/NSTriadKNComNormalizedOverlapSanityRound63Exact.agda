module DASHI.Physics.Closure.NSTriadKNComNormalizedOverlapSanityRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 63 / B1.5
--
-- Before asking for the special six-three constants, test whether the physical
-- Gram object is normalized in the ordinary Cauchy sense.
--
-- The existing `GramInterferenceCell` is NOT sufficient: it constrains the two
-- outer factors by <=1 but only assumes overlap>=0.  This file constructs an
-- explicit valid cell whose overlap is 2, proving that
--
--     GramInterferenceCell -> overlap <= 1
--
-- is false as a structural theorem.
--
-- The minimal honest repair is a `NormalizedGramInterferenceCell` carrying the
-- extra overlap contraction.  On that refined object the diagnostic ladder
--
--     0 <= overlap <= 1
--
-- is theorem-level, and the later six-three estimate is a genuine sharpening
-- rather than a hidden normalization assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram

record NormalizedGramInterferenceCell (gap : Nat) : Set where
  constructor normalized-gram-interference-cell
  field
    gramCell : Gram.GramInterferenceCell gap
    overlapContraction : Gram.overlap gramCell ≤ 1ℚ

open NormalizedGramInterferenceCell public

normalizedOverlapNonnegative :
  ∀ {gap} (cell : NormalizedGramInterferenceCell gap) →
  0ℚ ≤ Gram.overlap (gramCell cell)
normalizedOverlapNonnegative cell = Gram.overlapNonnegative (gramCell cell)

normalizedOverlapBelowOne :
  ∀ {gap} (cell : NormalizedGramInterferenceCell gap) →
  Gram.overlap (gramCell cell) ≤ 1ℚ
normalizedOverlapBelowOne = overlapContraction

normalizedPairProductBelowOne :
  ∀ {gap} (cell : NormalizedGramInterferenceCell gap) →
  Gram.pairProduct (gramCell cell) ≤ 1ℚ
normalizedPairProductBelowOne cell =
  ℚP.≤-trans
    (Gram.outerContractionsRemove (gramCell cell))
    (overlapContraction cell)

two : ℚ
two = 1ℚ + 1ℚ

twoNonnegative : 0ℚ ≤ two
twoNonnegative =
  let
    summed : 0ℚ + 0ℚ ≤ 1ℚ + 1ℚ
    summed = ℚP.+-mono-≤ ℚP.0≤1 ℚP.0≤1
    zeroPlusZero : 0ℚ + 0ℚ ≡ 0ℚ
    zeroPlusZero = solve []
  in
  subst (λ lower → lower ≤ two) zeroPlusZero summed

oneStrictTwo : 1ℚ < two
oneStrictTwo =
  let
    onePositive : 0ℚ < 1ℚ
    onePositive = ℚP.positive⁻¹ 1ℚ
    shifted : 1ℚ + 0ℚ < 1ℚ + 1ℚ
    shifted = ℚP.+-monoʳ-< 1ℚ onePositive
    leftMeaning : 1ℚ + 0ℚ ≡ 1ℚ
    leftMeaning = solve []
  in
  subst (λ left → left < two) leftMeaning shifted

zeroProductMeaning : 0ℚ * two * 0ℚ ≡ 0ℚ
zeroProductMeaning = solve (two ∷ [])

unnormalizedOverlapTwoCell : Gram.GramInterferenceCell zero
unnormalizedOverlapTwoCell =
  Gram.gram-interference-cell
    0ℚ two 0ℚ 0ℚ
    ℚP.≤-refl
    twoNonnegative
    ℚP.≤-refl
    ℚP.≤-refl
    ℚP.0≤1
    ℚP.0≤1
    (subst (λ upper → 0ℚ ≤ upper)
      (sym zeroProductMeaning) ℚP.≤-refl)

unnormalizedOverlapTwoMeaning :
  Gram.overlap unnormalizedOverlapTwoCell ≡ two
unnormalizedOverlapTwoMeaning = refl

unnormalizedGramDoesNotForceOverlapBelowOne :
  ¬ (Gram.overlap unnormalizedOverlapTwoCell ≤ 1ℚ)
unnormalizedGramDoesNotForceOverlapBelowOne overlapBelowOne =
  ℚP.<-irrefl 1ℚ
    (ℚP.<-≤-trans oneStrictTwo overlapBelowOne)

b15RawGramOverlapContractionRejected : Bool
b15RawGramOverlapContractionRejected = true

b15NormalizedGramSanityBoundConstructed : Bool
b15NormalizedGramSanityBoundConstructed = true

b15RawGramOverlapContractionRejectedIsTrue :
  b15RawGramOverlapContractionRejected ≡ true
b15RawGramOverlapContractionRejectedIsTrue = refl

b15NormalizedGramSanityBoundConstructedIsTrue :
  b15NormalizedGramSanityBoundConstructed ≡ true
b15NormalizedGramSanityBoundConstructedIsTrue = refl
