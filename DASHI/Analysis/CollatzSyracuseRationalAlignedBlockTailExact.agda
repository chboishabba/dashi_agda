module DASHI.Analysis.CollatzSyracuseRationalAlignedBlockTailExact where

------------------------------------------------------------------------
-- PARAMETRIC LITERAL NON-DESCENT TAIL ON LARGE ALIGNED BLOCKS
--
-- For horizon m = b*n+1 and an integer power comparison 3^a <= 2^b,
-- every sufficiently high aligned 2^m-block satisfies
--
--   2^(a*n+1) * nonDescentCount <= 3^m.
--
-- The count is over actual shortcut-Syracuse starts.  The proof pulls the
-- literal block through the exact parity-word bijection, uses the deterministic
-- affine descent theorem, and finally consumes the parametric integer Chernoff
-- tail.  It is not a universal stopping theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.Nat using (_≤_; _<_ ; z≤n)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.BinaryWordIntegerChernoffExact as Chernoff
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseCompleteBlockBijectionExact as Block
import DASHI.Analysis.CollatzSyracuseAlignedBlockUniformityExact as Aligned
import DASHI.Analysis.CollatzSyracuseParityDescentEventExact as Event
import DASHI.Analysis.CollatzSyracuseRationalDriftTailExact as Rational

horizon : Nat → Nat → Nat
horizon b n = b * n + 1

wordIndex :
  {b n : Nat} →
  Binary.BinaryWord (horizon b n) →
  Fin (Cylinder.pow2 (horizon b n))
wordIndex = Block.inverseWordIndex

wordStart :
  (b n block : Nat) →
  Binary.BinaryWord (horizon b n) →
  Syracuse.PositiveNat
wordStart b n block word =
  Aligned.alignedBlockStart block (wordIndex word)

wordItineraryRoundTrip :
  (b n block : Nat) →
  (word : Binary.BinaryWord (horizon b n)) →
  Aligned.alignedBlockWord block (wordIndex word) ≡ word
wordItineraryRoundTrip b n block word =
  trans
    (Aligned.alignedBlockWordEqualsCanonical block (wordIndex word))
    (Block.inverseWordRoundTrip word)

blockThresholdAllStartsLarge :
  (b n block : Nat) →
  Affine.powNat 3 (horizon b n)
    ≤ block * Cylinder.pow2 (horizon b n) →
  (word : Binary.BinaryWord (horizon b n)) →
  Affine.powNat 3 (horizon b n)
    ≤ Syracuse.toNat (wordStart b n block word)
blockThresholdAllStartsLarge b n block threshold word =
  let
    index = wordIndex word
    shift = block * Cylinder.pow2 (horizon b n)
    base = Syracuse.toNat (Block.blockStart index)

    shift≤startSum : shift ≤ base + shift
    shift≤startSum = NatP.m≤n+m shift base

    threshold≤sum : Affine.powNat 3 (horizon b n) ≤ base + shift
    threshold≤sum = NatP.≤-trans threshold shift≤startSum

    startEquation :
      Syracuse.toNat (wordStart b n block word) ≡ base + shift
    startEquation =
      Aligned.shiftPositiveByToNat shift (Block.blockStart index)
  in
  subst
    (Affine.powNat 3 (horizon b n) ≤_)
    (sym startEquation)
    threshold≤sum

blockWordGoodImpliesDescent :
  (b n block : Nat) →
  Affine.powNat 3 (horizon b n)
    ≤ block * Cylinder.pow2 (horizon b n) →
  (word : Binary.BinaryWord (horizon b n)) →
  Event.parityDriftGood word →
  Syracuse.toNat
      (Syracuse.syracuseIterate (horizon b n) (wordStart b n block word))
    < Syracuse.toNat (wordStart b n block word)
blockWordGoodImpliesDescent b n block threshold word good =
  Event.goodParityWordImpliesDescent
    (horizon b n)
    (wordStart b n block word)
    (blockThresholdAllStartsLarge b n block threshold word)
    (subst Event.parityDriftGood
      (sym (wordItineraryRoundTrip b n block word))
      good)

nonDescentIndicator :
  (b n block : Nat) →
  Binary.BinaryWord (horizon b n) →
  Nat
nonDescentIndicator b n block word
  with NatP._<?_
    (Syracuse.toNat
      (Syracuse.syracuseIterate
        (horizon b n)
        (wordStart b n block word)))
    (Syracuse.toNat (wordStart b n block word))
... | yes _ = 0
... | no _ = 1

alignedBlockNonDescentCount : Nat → Nat → Nat → Nat
alignedBlockNonDescentCount b n block =
  Chernoff.wordFold (nonDescentIndicator b n block)

nonDescentIndicatorLeBadIndicator :
  (b n block : Nat) →
  Affine.powNat 3 (horizon b n)
    ≤ block * Cylinder.pow2 (horizon b n) →
  (word : Binary.BinaryWord (horizon b n)) →
  nonDescentIndicator b n block word ≤ Event.badIndicator word
nonDescentIndicatorLeBadIndicator b n block threshold word
  with NatP._<?_
    (Syracuse.toNat
      (Syracuse.syracuseIterate
        (horizon b n)
        (wordStart b n block word)))
    (Syracuse.toNat (wordStart b n block word))
... | yes descent = z≤n
... | no nonDescent
  with Event.parityDriftGoodᵇ word in goodDecision
...   | false = NatP.≤-refl
...   | true =
  let
    good = Event.parityDriftGoodᵇTrue word goodDecision
    descent = blockWordGoodImpliesDescent b n block threshold word good
  in
  contradiction descent nonDescent

alignedBlockNonDescentCountLeBadWordCount :
  (b n block : Nat) →
  Affine.powNat 3 (horizon b n)
    ≤ block * Cylinder.pow2 (horizon b n) →
  alignedBlockNonDescentCount b n block
    ≤ Event.badWordCount (horizon b n)
alignedBlockNonDescentCountLeBadWordCount b n block threshold =
  Chernoff.foldMono
    (nonDescentIndicator b n block)
    Event.badIndicator
    (nonDescentIndicatorLeBadIndicator b n block threshold)

rationalAlignedBlockNonDescentBound :
  (a b n block : Nat) →
  (step : Affine.powNat 3 a ≤ Affine.powNat 2 b) →
  Affine.powNat 3 (horizon b n)
    ≤ block * Cylinder.pow2 (horizon b n) →
  Chernoff.powNat 2 (a * n + 1)
    * alignedBlockNonDescentCount b n block
  ≤ Chernoff.powNat 3 (horizon b n)
rationalAlignedBlockNonDescentBound a b n block step threshold =
  NatP.≤-trans
    (NatP.*-monoʳ-≤
      (Chernoff.powNat 2 (a * n + 1))
      (alignedBlockNonDescentCountLeBadWordCount b n block threshold))
    (Rational.rationalBadWordBound a b n step)

record RationalAlignedBlockTailBoundary : Set where
  constructor rationalAlignedBlockTailBoundary
  field
    literalStartCountOwned : Nat
    parametricPowerComparisonOwned : Nat
    rationalIntegerTailOwned : Nat
    blockThresholdExplicit : Nat
    logarithmRequired : Nat
    universalStoppingOwned : Nat

canonicalRationalAlignedBlockTailBoundary : RationalAlignedBlockTailBoundary
canonicalRationalAlignedBlockTailBoundary =
  rationalAlignedBlockTailBoundary 1 1 1 1 0 0
