module DASHI.Analysis.CollatzSyracuseUnalignedIntervalTailCompilerExact where

------------------------------------------------------------------------
-- UNALIGNED FINITE-INTERVAL TAIL COMPILER
--
-- An arbitrary integer interval can be split at aligned 2^m boundaries into
--
--   left fragment + consecutive complete aligned blocks + right fragment.
--
-- This file pays everything after that literal partition.  The aligned middle
-- block family inherits the parametric Syracuse tail recursively.  Boundary
-- fragments are charged by their lengths.  The only source-specific seam left
-- is the exact interval/count split itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Core.BinaryWordIntegerChernoffExact as Chernoff
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseRationalAlignedBlockTailExact as Aligned

horizon : Nat → Nat → Nat
horizon b n = b * n + 1

------------------------------------------------------------------------
-- Exact sum over q consecutive aligned literal blocks.
------------------------------------------------------------------------

middleAlignedNonDescentCount :
  (b n firstBlock blockCount : Nat) → Nat
middleAlignedNonDescentCount b n firstBlock zero = zero
middleAlignedNonDescentCount b n firstBlock (suc q) =
  Aligned.alignedBlockNonDescentCount b n firstBlock
  + middleAlignedNonDescentCount b n (suc firstBlock) q

nextBlockThreshold :
  (b n block : Nat) →
  Affine.powNat 3 (horizon b n)
    ≤ block * Cylinder.pow2 (horizon b n) →
  Affine.powNat 3 (horizon b n)
    ≤ suc block * Cylinder.pow2 (horizon b n)
nextBlockThreshold b n block threshold =
  NatP.≤-trans
    threshold
    (NatP.*-monoˡ-≤
      (Cylinder.pow2 (horizon b n))
      (NatP.n≤1+n block))

middleAlignedScaledTail :
  (a b n firstBlock blockCount : Nat) →
  (step : Affine.powNat 3 a ≤ Affine.powNat 2 b) →
  Affine.powNat 3 (horizon b n)
    ≤ firstBlock * Cylinder.pow2 (horizon b n) →
  Chernoff.powNat 2 (a * n + 1)
    * middleAlignedNonDescentCount b n firstBlock blockCount
  ≤ blockCount * Chernoff.powNat 3 (horizon b n)
middleAlignedScaledTail a b n firstBlock zero step threshold = NatP.≤-refl
middleAlignedScaledTail a b n firstBlock (suc q) step threshold =
  let
    scale = Chernoff.powNat 2 (a * n + 1)
    power = Chernoff.powNat 3 (horizon b n)
    head = Aligned.alignedBlockNonDescentCount b n firstBlock
    tail = middleAlignedNonDescentCount b n (suc firstBlock) q

    headBound : scale * head ≤ power
    headBound =
      Aligned.rationalAlignedBlockNonDescentBound
        a b n firstBlock step threshold

    tailBound : scale * tail ≤ q * power
    tailBound =
      middleAlignedScaledTail
        a b n (suc firstBlock) q step
        (nextBlockThreshold b n firstBlock threshold)

    added : scale * head + scale * tail ≤ power + q * power
    added = NatP.+-mono-≤ headBound tailBound

    leftEquation : scale * (head + tail) ≡ scale * head + scale * tail
    leftEquation = NatP.*-distribˡ-+ scale head tail

    rightEquation : power + q * power ≡ suc q * power
    rightEquation = refl
  in
  subst
    (λ left → left ≤ suc q * power)
    (sym leftEquation)
    (subst
      (scale * head + scale * tail ≤_)
      rightEquation
      added)

------------------------------------------------------------------------
-- Arbitrary interval split boundary.
------------------------------------------------------------------------

record UnalignedIntervalSplit
    (a b n firstBlock completeBlocks : Nat) : Set₁ where
  field
    intervalNonDescentCount : Nat
    leftFragmentLength : Nat
    leftFragmentNonDescentCount : Nat
    rightFragmentLength : Nat
    rightFragmentNonDescentCount : Nat

    leftFragmentCountBound :
      leftFragmentNonDescentCount ≤ leftFragmentLength

    rightFragmentCountBound :
      rightFragmentNonDescentCount ≤ rightFragmentLength

    exactCountSplit :
      intervalNonDescentCount
      ≡ leftFragmentNonDescentCount
        + middleAlignedNonDescentCount b n firstBlock completeBlocks
        + rightFragmentNonDescentCount

open UnalignedIntervalSplit public

unalignedIntervalScaledTail :
  (a b n firstBlock completeBlocks : Nat) →
  (step : Affine.powNat 3 a ≤ Affine.powNat 2 b) →
  Affine.powNat 3 (horizon b n)
    ≤ firstBlock * Cylinder.pow2 (horizon b n) →
  (split : UnalignedIntervalSplit a b n firstBlock completeBlocks) →
  Chernoff.powNat 2 (a * n + 1)
    * intervalNonDescentCount split
  ≤ completeBlocks * Chernoff.powNat 3 (horizon b n)
    + Chernoff.powNat 2 (a * n + 1)
      * (leftFragmentLength split + rightFragmentLength split)
unalignedIntervalScaledTail a b n firstBlock completeBlocks step threshold split =
  let
    scale = Chernoff.powNat 2 (a * n + 1)
    power = Chernoff.powNat 3 (horizon b n)
    leftBad = leftFragmentNonDescentCount split
    middleBad = middleAlignedNonDescentCount b n firstBlock completeBlocks
    rightBad = rightFragmentNonDescentCount split
    leftLength = leftFragmentLength split
    rightLength = rightFragmentLength split

    leftBound : scale * leftBad ≤ scale * leftLength
    leftBound = NatP.*-monoʳ-≤ scale (leftFragmentCountBound split)

    middleBound : scale * middleBad ≤ completeBlocks * power
    middleBound =
      middleAlignedScaledTail
        a b n firstBlock completeBlocks step threshold

    rightBound : scale * rightBad ≤ scale * rightLength
    rightBound = NatP.*-monoʳ-≤ scale (rightFragmentCountBound split)

    combined :
      scale * leftBad + scale * middleBad + scale * rightBad
      ≤ scale * leftLength + completeBlocks * power + scale * rightLength
    combined =
      NatP.+-mono-≤
        (NatP.+-mono-≤ leftBound middleBound)
        rightBound

    distributeLeft :
      scale * (leftBad + middleBad + rightBad)
      ≡ scale * leftBad + scale * middleBad + scale * rightBad
    distributeLeft =
      trans
        (NatP.*-distribˡ-+ scale (leftBad + middleBad) rightBad)
        (cong (_+ scale * rightBad)
          (NatP.*-distribˡ-+ scale leftBad middleBad))

    rearrangeRight :
      scale * leftLength + completeBlocks * power + scale * rightLength
      ≡ completeBlocks * power + scale * (leftLength + rightLength)
    rearrangeRight =
      solve 4
        (λ s l q r →
          (s :* l) :+ q :+ (s :* r)
          := q :+ (s :* (l :+ r)))
        refl
        scale
        leftLength
        (completeBlocks * power)
        rightLength

    splitScaled :
      scale * intervalNonDescentCount split
      ≡ scale * (leftBad + middleBad + rightBad)
    splitScaled = cong (scale *_) (exactCountSplit split)
  in
  subst
    (λ left →
      left
      ≤ completeBlocks * power + scale * (leftLength + rightLength))
    (sym splitScaled)
    (subst
      (scale * (leftBad + middleBad + rightBad) ≤_)
      rearrangeRight
      (subst
        (λ left → left ≤ scale * leftLength + completeBlocks * power + scale * rightLength)
        (sym distributeLeft)
        combined))

record UnalignedIntervalTailBoundary : Set where
  constructor unalignedIntervalTailBoundary
  field
    consecutiveAlignedBlockSumOwned : Nat
    fragmentCountChargedByLength : Nat
    scaledBoundaryPenaltyOwned : Nat
    exactArbitraryIntervalSplitStillRequired : Nat
    universalStoppingOwned : Nat

canonicalUnalignedIntervalTailBoundary : UnalignedIntervalTailBoundary
canonicalUnalignedIntervalTailBoundary =
  unalignedIntervalTailBoundary 1 1 1 1 0
