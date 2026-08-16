module DASHI.Physics.Closure.NSTriadKNComGenericGramUnitOverlapNoGoRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical Cauchy--Schwarz inequality; no DOI assigned to the original
-- nineteenth-century sources.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 63 B1.5 FALSIFIER
--
-- A correctly NORMALIZED Gram overlap should satisfy overlap <= 1.  However
-- Round35's `GramInterferenceCell` is deliberately more general: it requires
-- only nonnegative overlap, unit-bounded OUTER factors, and a factorization
-- bound for the pair product.  Those hypotheses do not normalize the overlap.
--
-- This file exhibits a literal legal GramInterferenceCell with
--
--   leftOuter = rightOuter = 1,
--   overlap = pairProduct = 2.
--
-- Hence `overlap <= 1` cannot be derived from the current generic cell type.
-- B1 must construct normalization from the physical vectors/masses (or a
-- mathematically equivalent normalized Gram object) before the six-three
-- sharpening is meaningful.  We do not patch this by adding the desired bound
-- as a receipt field to the old cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram

two : ℚ
two = 1ℚ + 1ℚ

twoNonnegative : 0ℚ ≤ two
twoNonnegative = L2.addNonnegative ℚP.0≤1 ℚP.0≤1

unitTimesTwoTimesUnit : 1ℚ * two * 1ℚ ≡ two
unitTimesTwoTimesUnit = solve ([])

unnormalizedOverlapTwoCell : Gram.GramInterferenceCell zero
unnormalizedOverlapTwoCell = Gram.gram-interference-cell
  1ℚ
  two
  1ℚ
  two
  ℚP.0≤1
  twoNonnegative
  ℚP.0≤1
  twoNonnegative
  ℚP.≤-refl
  ℚP.≤-refl
  (subst (λ upper → two ≤ upper) (sym unitTimesTwoTimesUnit) ℚP.≤-refl)
  where
  open import Relation.Binary.PropositionalEquality using (sym)

oneStrictlyBelowTwo : 1ℚ < two
oneStrictlyBelowTwo =
  subst
    (λ left → left < two)
    (ℚP.+-identityʳ 1ℚ)
    (ℚP.+-monoʳ-< 1ℚ ℚP.0<1)

genericGramOverlapAtMostOneRefuted :
  ¬ (Gram.overlap unnormalizedOverlapTwoCell ≤ 1ℚ)
genericGramOverlapAtMostOneRefuted overlapAtMostOne =
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans oneStrictlyBelowTwo overlapAtMostOne)

genericGramCellIsNotYetNormalized : Bool
genericGramCellIsNotYetNormalized = true

b15MustFollowPhysicalNormalization : Bool
b15MustFollowPhysicalNormalization = true

genericGramCellIsNotYetNormalizedIsTrue :
  genericGramCellIsNotYetNormalized ≡ true
genericGramCellIsNotYetNormalizedIsTrue = refl

b15MustFollowPhysicalNormalizationIsTrue :
  b15MustFollowPhysicalNormalization ≡ true
b15MustFollowPhysicalNormalizationIsTrue = refl
