module DASHI.Analysis.CollatzSyracuseAlignedBlockTailExact where

------------------------------------------------------------------------
-- EXACT LITERAL NON-DESCENT TAIL ON LARGE ALIGNED BLOCKS
--
-- For horizon m = 8n+1, the aligned 2^m-block is in exact bijection with all
-- binary parity words of length m.  Pull each word back to its unique literal
-- Syracuse start in the block.  If the whole block is above the affine
-- correction threshold 3^m, every non-descending start has a bad parity word.
-- The exact five-eighths integer Chernoff theorem then gives
--
--   2^(5n+1) * nonDescentCount <= 3^(8n+1).
--
-- This is a theorem about actual shortcut-Syracuse starts in a finite aligned
-- integer block.  It is not a promotion to universal stopping.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
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
import DASHI.Analysis.CollatzSyracuseFiveEightTailExact as FiveEight
import DASHI.Analysis.CollatzSyracuseAlignedBlockDescentExact as Descent

horizon : Nat → Nat
horizon n = 8 * n + 1

wordIndex :
  {n : Nat} →
  Binary.BinaryWord (horizon n) →
  Data.Fin.Base.Fin (Cylinder.pow2 (horizon n))
wordIndex = Block.inverseWordIndex
  where
  import Data.Fin.Base

wordStart :
  (n block : Nat) →
  Binary.BinaryWord (horizon n) →
  Syracuse.PositiveNat
wordStart n block word =
  Descent.alignedStart n block (wordIndex word)

wordItineraryRoundTrip :
  (n block : Nat) →
  (word : Binary.BinaryWord (horizon n)) →
  Descent.alignedWord n block (wordIndex word) ≡ word
wordItineraryRoundTrip n block word =
  trans
    (Aligned.alignedBlockWordEqualsCanonical block (wordIndex word))
    (Block.inverseWordRoundTrip word)

------------------------------------------------------------------------
-- A simple block-level sufficient condition for every start in the block to
-- lie above the affine correction threshold.
------------------------------------------------------------------------

blockThresholdAllStartsLarge :
  (n block : Nat) →
  Affine.powNat 3 (horizon n)
    ≤ block * Cylinder.pow2 (horizon n) →
  (word : Binary.BinaryWord (horizon n)) →
  Affine.powNat 3 (horizon n)
    ≤ Syracuse.toNat (wordStart n block word)
blockThresholdAllStartsLarge n block threshold word =
  let
    index = wordIndex word
    shift = block * Cylinder.pow2 (horizon n)
    base = Syracuse.toNat (Block.blockStart index)

    shift≤startSum : shift ≤ base + shift
    shift≤startSum = NatP.m≤n+m shift base

    threshold≤sum : Affine.powNat 3 (horizon n) ≤ base + shift
    threshold≤sum = NatP.≤-trans threshold shift≤startSum

    startEquation :
      Syracuse.toNat (wordStart n block word) ≡ base + shift
    startEquation =
      Aligned.shiftPositiveByToNat shift (Block.blockStart index)
  in
  subst
    (Affine.powNat 3 (horizon n) ≤_)
    (sym startEquation)
    threshold≤sum

blockWordGoodImpliesDescent :
  (n block : Nat) →
  Affine.powNat 3 (horizon n)
    ≤ block * Cylinder.pow2 (horizon n) →
  (word : Binary.BinaryWord (horizon n)) →
  Event.parityDriftGood word →
  Syracuse.toNat
      (Syracuse.syracuseIterate (horizon n) (wordStart n block word))
    < Syracuse.toNat (wordStart n block word)
blockWordGoodImpliesDescent n block threshold word good =
  let
    index = wordIndex word
    large = blockThresholdAllStartsLarge n block threshold word
    alignedGood : Event.parityDriftGood (Descent.alignedWord n block index)
    alignedGood =
      subst Event.parityDriftGood
        (sym (wordItineraryRoundTrip n block word))
        good
  in
  Descent.largeAlignedStartGoodImpliesDescent
    n block index large alignedGood

------------------------------------------------------------------------
-- Count non-descending literal starts through the word carrier.  The inverse
-- word index is a proved bijection, so this fold counts each start exactly once.
------------------------------------------------------------------------

nonDescentIndicator :
  (n block : Nat) →
  Binary.BinaryWord (horizon n) →
  Nat
nonDescentIndicator n block word
  with NatP._<?_
    (Syracuse.toNat
      (Syracuse.syracuseIterate (horizon n) (wordStart n block word)))
    (Syracuse.toNat (wordStart n block word))
... | yes _ = 0
... | no _ = 1

alignedBlockNonDescentCount : Nat → Nat → Nat
alignedBlockNonDescentCount n block =
  Chernoff.wordFold (nonDescentIndicator n block)

nonDescentIndicatorLeBadIndicator :
  (n block : Nat) →
  Affine.powNat 3 (horizon n)
    ≤ block * Cylinder.pow2 (horizon n) →
  (word : Binary.BinaryWord (horizon n)) →
  nonDescentIndicator n block word ≤ Event.badIndicator word
nonDescentIndicatorLeBadIndicator n block threshold word
  with NatP._<?_
    (Syracuse.toNat
      (Syracuse.syracuseIterate (horizon n) (wordStart n block word)))
    (Syracuse.toNat (wordStart n block word))
... | yes descent = z≤n
... | no nonDescent
  with Event.parityDriftGoodᵇ word in goodDecision
...   | false = NatP.≤-refl
...   | true =
  let
    good = Event.parityDriftGoodᵇTrue word goodDecision
    descent = blockWordGoodImpliesDescent n block threshold word good
  in
  contradiction descent nonDescent

alignedBlockNonDescentCountLeBadWordCount :
  (n block : Nat) →
  Affine.powNat 3 (horizon n)
    ≤ block * Cylinder.pow2 (horizon n) →
  alignedBlockNonDescentCount n block
    ≤ Event.badWordCount (horizon n)
alignedBlockNonDescentCountLeBadWordCount n block threshold =
  Chernoff.foldMono
    (nonDescentIndicator n block)
    Event.badIndicator
    (nonDescentIndicatorLeBadIndicator n block threshold)

alignedBlockFiveEightNonDescentBound :
  (n block : Nat) →
  Affine.powNat 3 (horizon n)
    ≤ block * Cylinder.pow2 (horizon n) →
  Chernoff.powNat 2 (5 * n + 1)
    * alignedBlockNonDescentCount n block
  ≤ Chernoff.powNat 3 (horizon n)
alignedBlockFiveEightNonDescentBound n block threshold =
  NatP.≤-trans
    (NatP.*-monoʳ-≤
      (Chernoff.powNat 2 (5 * n + 1))
      (alignedBlockNonDescentCountLeBadWordCount n block threshold))
    (FiveEight.fiveEightBadWordBound n)

record AlignedBlockTailBoundary : Set where
  constructor alignedBlockTailBoundary
  field
    literalStartCountOwned : Nat
    exactWordPullbackOwned : Nat
    nonDescentSubsetBadWordsOwned : Nat
    integerExponentialTailOwned : Nat
    largeBlockThresholdExplicit : Nat
    universalStoppingOwned : Nat

canonicalAlignedBlockTailBoundary : AlignedBlockTailBoundary
canonicalAlignedBlockTailBoundary =
  alignedBlockTailBoundary 1 1 1 1 1 0
