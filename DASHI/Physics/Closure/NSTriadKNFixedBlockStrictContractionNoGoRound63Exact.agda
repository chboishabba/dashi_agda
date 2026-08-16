module DASHI.Physics.Closure.NSTriadKNFixedBlockStrictContractionNoGoRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 FIXED-BLOCK SEMANTIC FALSIFIER
--
-- `RationalFixedBlockDecay` proves the induction
--
--   A_n <= C r^n
--
-- from q<=r and the correction budget, but its type does NOT require r<1.
-- Therefore the record by itself is not a strict decay certificate.
--
-- This file constructs the exact legal witness
--
--   q=r=C=1,  A_n=1,  correction_n=0.
--
-- Every field of `RationalFixedBlockDecay` is satisfied and the resulting
-- target is identically one.  Hence any later use that needs genuine geometric
-- decay must separately construct a strict contraction 0<=r<1 (or an
-- equivalent summability/vanishing statement).  The existing induction theorem
-- remains correct; only the semantic promotion "bounded by C r^n => decays"
-- is rejected without r<1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block

onePower : (n : Nat) → Block.power 1ℚ n ≡ 1ℚ
onePower zero = refl
onePower (suc n) =
  trans
    (cong (1ℚ *_) (onePower n))
    (ℚP.*-identityˡ 1ℚ)

constantOneSequence : Nat → ℚ
constantOneSequence n = 1ℚ

zeroCorrection : Nat → ℚ
zeroCorrection n = 0ℚ

unitRatioFixedBlock : Block.RationalFixedBlockDecay
unitRatioFixedBlock = record
  { Block.RationalFixedBlockDecay.sequence = constantOneSequence
  ; Block.RationalFixedBlockDecay.correction = zeroCorrection
  ; Block.RationalFixedBlockDecay.q = 1ℚ
  ; Block.RationalFixedBlockDecay.r = 1ℚ
  ; Block.RationalFixedBlockDecay.constant = 1ℚ
  ; Block.RationalFixedBlockDecay.qNonnegative = ℚP.0≤1
  ; Block.RationalFixedBlockDecay.rNonnegative = ℚP.0≤1
  ; Block.RationalFixedBlockDecay.constantNonnegative = ℚP.0≤1
  ; Block.RationalFixedBlockDecay.qBelowR = ℚP.≤-refl
  ; Block.RationalFixedBlockDecay.initialBound = ℚP.≤-refl
  ; Block.RationalFixedBlockDecay.recursion = λ n →
      let
        endpoint : 1ℚ * 1ℚ + 0ℚ ≡ 1ℚ
        endpoint = solve []
      in
      substUpper endpoint ℚP.≤-refl
  ; Block.RationalFixedBlockDecay.correctionBudget = λ n →
      let
        target = Block.scaledTarget 1ℚ 1ℚ n
        endpoint : (1ℚ - 1ℚ) * target ≡ 0ℚ
        endpoint = solve (target ∷ [])
      in
      substUpper endpoint ℚP.≤-refl
  }
  where
  substUpper : ∀ {left right upper : ℚ} →
    upper ≡ right → left ≤ upper → left ≤ right
  substUpper refl proof = proof

unitRatioTargetIsOne :
  (n : Nat) →
  Block.scaledTarget
    (Block.constant unitRatioFixedBlock)
    (Block.r unitRatioFixedBlock) n
  ≡ 1ℚ
unitRatioTargetIsOne n =
  trans
    (cong (1ℚ *_) (onePower n))
    (ℚP.*-identityˡ 1ℚ)

unitRatioSequenceIsOne :
  (n : Nat) → Block.sequence unitRatioFixedBlock n ≡ 1ℚ
unitRatioSequenceIsOne n = refl

fixedBlockInductionDoesNotImplyStrictDecay : Bool
fixedBlockInductionDoesNotImplyStrictDecay = true

strictContractionMustBeConstructedSeparately : Bool
strictContractionMustBeConstructedSeparately = true

fixedBlockInductionDoesNotImplyStrictDecayIsTrue :
  fixedBlockInductionDoesNotImplyStrictDecay ≡ true
fixedBlockInductionDoesNotImplyStrictDecayIsTrue = refl

strictContractionMustBeConstructedSeparatelyIsTrue :
  strictContractionMustBeConstructedSeparately ≡ true
strictContractionMustBeConstructedSeparatelyIsTrue = refl
