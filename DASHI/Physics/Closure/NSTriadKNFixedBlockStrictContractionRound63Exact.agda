module DASHI.Physics.Closure.NSTriadKNFixedBlockStrictContractionRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 63 FIXED-BLOCK REPAIR
--
-- The base rational block induction does not require r<1.  This module adds
-- the exact physical property needed whenever the argument uses genuine
-- geometric decay:
--
--   C>0,  0<r<1.
--
-- It then proves the literal target sequence C r^n strictly decreases at every
-- step.  This wrapper is intentionally separate from the algebraic induction:
-- a physical producer must construct the contraction rather than obtaining it
-- from the name `RationalFixedBlockDecay`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _<_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNCriticalScaleNormalizedBlockRound63Exact as C0

record StrictContractiveFixedBlock
    (block : Block.RationalFixedBlockDecay) : Set where
  constructor strict-contractive-fixed-block
  field
    positiveScale : C0.PositiveCriticalBlockScale block
    ratioBelowOne : Block.r block < 1ℚ

open StrictContractiveFixedBlock public

targetPositive :
  (block : Block.RationalFixedBlockDecay) →
  StrictContractiveFixedBlock block →
  (n : Nat) →
  0ℚ < Block.scaledTarget (Block.constant block) (Block.r block) n
targetPositive block strict n =
  C0.blockTargetPositive block (positiveScale strict) n

nextTargetStrictlyBelow :
  (block : Block.RationalFixedBlockDecay) →
  (strict : StrictContractiveFixedBlock block) →
  (n : Nat) →
  Block.scaledTarget (Block.constant block) (Block.r block) (suc n)
  < Block.scaledTarget (Block.constant block) (Block.r block) n
nextTargetStrictlyBelow block strict n =
  let
    C = Block.constant block
    r = Block.r block
    p = Block.power r n
    target = C * p

    targetPos : 0ℚ < target
    targetPos = targetPositive block strict n

    instance
      targetPositiveI = positive targetPos

    scaledRatio : r * target < 1ℚ * target
    scaledRatio = ℚP.*-monoʳ-<-pos target (ratioBelowOne strict)

    leftMeaning :
      Block.scaledTarget C r (suc n) ≡ r * target
    leftMeaning = solve (C ∷ r ∷ p ∷ [])

    rightMeaning : 1ℚ * target ≡ Block.scaledTarget C r n
    rightMeaning = ℚP.*-identityˡ target
  in
  subst
    (λ left → left < Block.scaledTarget C r n)
    (sym leftMeaning)
    (subst
      (λ right → r * target < right)
      rightMeaning
      scaledRatio)

strictBlockContractionExplicit : Bool
strictBlockContractionExplicit = true

strictBlockTargetDecreases : Bool
strictBlockTargetDecreases = true

strictBlockContractionExplicitIsTrue :
  strictBlockContractionExplicit ≡ true
strictBlockContractionExplicitIsTrue = refl

strictBlockTargetDecreasesIsTrue :
  strictBlockTargetDecreases ≡ true
strictBlockTargetDecreasesIsTrue = refl
