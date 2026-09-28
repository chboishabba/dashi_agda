{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceGapFactorRound753Exact where

------------------------------------------------------------------------
-- ROUND753 / EXACT GAP FACTORIZATION OF THE R748 DYADIC DIFFERENCES
--
-- For nonzero modes, the selected R748 weight is exactly
--
--   lambda~(m) = Q(2 ^ shellIndex(m)).
--
-- If
--
--   shellIndex(high) = shellIndex(low) + gap,
--
-- then exact power/addition arithmetic gives
--
--   lambda~(high) - lambda~(low)
--     = lambda~(low) * ( Q(2^gap) - 1 ).
--
-- This preserves the SIGNED difference and exposes its scale factor directly.
-- It is not a dyadic-to-Euclidean replacement and introduces no estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Rational.Base using (ℚ; 1ℚ; _-_; _*_)
import Data.Nat.Properties as NatP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as NatQ
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceSupportRound750Exact as R750

pow2Add753 :
  (left right : Nat) →
  Shell.pow2 (left + right)
  ≡ Shell.pow2 left * Shell.pow2 right
pow2Add753 zero right =
  sym (NatP.*-identityˡ (Shell.pow2 right))
pow2Add753 (suc left) right
  rewrite pow2Add753 left right =
  sym
    (NatP.*-assoc
      (suc (suc zero))
      (Shell.pow2 left)
      (Shell.pow2 right))

shellWeight : Nat → ℚ
shellWeight shell =
  Fold.natAsRational (Shell.pow2 shell)

selectedDyadicWeightIsShellWeight :
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  R748.selectedDyadicWeight mode
  ≡ shellWeight (Shell.shellIndex mode)
selectedDyadicWeightIsShellWeight mode nonzero
  rewrite R750.modeEqualZeroFalseFromNonzero mode nonzero =
  refl

shellWeightAdd :
  (base gap : Nat) →
  shellWeight (base + gap)
  ≡ shellWeight base * shellWeight gap
shellWeightAdd base gap =
  trans
    (cong Fold.natAsRational (pow2Add753 base gap))
    (NatQ.natAsRationalMul
      (Shell.pow2 base)
      (Shell.pow2 gap))

shellWeightDifferenceFactor :
  (base gap : Nat) →
  shellWeight (base + gap) - shellWeight base
  ≡ shellWeight base * (shellWeight gap - 1ℚ)
shellWeightDifferenceFactor base gap =
  trans
    (cong
      (_- shellWeight base)
      (shellWeightAdd base gap))
    (solve (shellWeight base ∷ shellWeight gap ∷ []))

selectedDyadicWeightDifferenceGapFactor :
  (low high : Z3.FourierMode) →
  Z3.NonZeroMode low →
  Z3.NonZeroMode high →
  (gap : Nat) →
  Shell.shellIndex high ≡ Shell.shellIndex low + gap →
  R748.selectedDyadicWeight high
    - R748.selectedDyadicWeight low
  ≡
  R748.selectedDyadicWeight low * (shellWeight gap - 1ℚ)
selectedDyadicWeightDifferenceGapFactor
    low high lowNonzero highNonzero gap shellGap =
  let
    lowMeaning =
      selectedDyadicWeightIsShellWeight low lowNonzero
    highMeaning =
      selectedDyadicWeightIsShellWeight high highNonzero
  in
  trans
    (cong₂ _-_
      highMeaning
      lowMeaning)
    (trans
      (cong
        (_- shellWeight (Shell.shellIndex low))
        (cong shellWeight shellGap))
      (trans
        (shellWeightDifferenceFactor
          (Shell.shellIndex low) gap)
        (cong
          (λ value → value * (shellWeight gap - 1ℚ))
          (sym lowMeaning))))

oneShellGapFactor :
  shellWeight (suc zero) - 1ℚ ≡ 1ℚ
oneShellGapFactor = refl

threeShellGapFactor :
  shellWeight (suc (suc (suc zero))) - 1ℚ
  ≡ Fold.natAsRational 7
threeShellGapFactor = refl

selectedDyadicWeightOneShellDifference :
  (low high : Z3.FourierMode) →
  Z3.NonZeroMode low →
  Z3.NonZeroMode high →
  Shell.shellIndex high ≡ suc (Shell.shellIndex low) →
  R748.selectedDyadicWeight high
    - R748.selectedDyadicWeight low
  ≡ R748.selectedDyadicWeight low
selectedDyadicWeightOneShellDifference
    low high lowNonzero highNonzero shellGap =
  trans
    (selectedDyadicWeightDifferenceGapFactor
      low high lowNonzero highNonzero
      (suc zero)
      (trans shellGap
        (sym
          (NatP.+-identityʳ (suc (Shell.shellIndex low))))))
    (trans
      (cong
        (R748.selectedDyadicWeight low *_)
        oneShellGapFactor)
      (NatPHelper low))
  where
  NatPHelper :
    (mode : Z3.FourierMode) →
    R748.selectedDyadicWeight mode * 1ℚ
    ≡ R748.selectedDyadicWeight mode
  NatPHelper mode =
    Data.Rational.Properties.*-identityʳ
      (R748.selectedDyadicWeight mode)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round753SignedDyadicDifferenceHasExactGapFactor : Bool
round753SignedDyadicDifferenceHasExactGapFactor = true

round753OneShellDifferenceEqualsLowerSelectedWeight : Bool
round753OneShellDifferenceEqualsLowerSelectedWeight = true

round753ThreeShellGapMultiplierIsSeven : Bool
round753ThreeShellGapMultiplierIsSeven = true

round753IntroducesEstimate : Bool
round753IntroducesEstimate = false

round753ReplacesDyadicWeightByEuclideanModeNorm : Bool
round753ReplacesDyadicWeightByEuclideanModeNorm = false

round753ClayPromotion : Bool
round753ClayPromotion = false

round753SignedDyadicDifferenceHasExactGapFactorIsTrue :
  round753SignedDyadicDifferenceHasExactGapFactor ≡ true
round753SignedDyadicDifferenceHasExactGapFactorIsTrue = refl

round753OneShellDifferenceEqualsLowerSelectedWeightIsTrue :
  round753OneShellDifferenceEqualsLowerSelectedWeight ≡ true
round753OneShellDifferenceEqualsLowerSelectedWeightIsTrue = refl

round753ThreeShellGapMultiplierIsSevenIsTrue :
  round753ThreeShellGapMultiplierIsSeven ≡ true
round753ThreeShellGapMultiplierIsSevenIsTrue = refl

round753IntroducesEstimateIsFalse :
  round753IntroducesEstimate ≡ false
round753IntroducesEstimateIsFalse = refl

round753ReplacesDyadicWeightByEuclideanModeNormIsFalse :
  round753ReplacesDyadicWeightByEuclideanModeNorm ≡ false
round753ReplacesDyadicWeightByEuclideanModeNormIsFalse = refl

round753ClayPromotionIsFalse :
  round753ClayPromotion ≡ false
round753ClayPromotionIsFalse = refl
