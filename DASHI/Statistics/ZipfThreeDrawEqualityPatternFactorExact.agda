module DASHI.Statistics.ZipfThreeDrawEqualityPatternFactorExact where

------------------------------------------------------------------------
-- Source-owned 27-code -> five value-equality patterns -> four Heaps
-- histories. This is an ACTUAL factor map, not a cardinality weld.
--
-- Mathematical roots: classical partitions/restricted-growth strings,
-- finite S3 orbit actions (Cauchy/Frobenius/Burnside), first-discovery
-- statistics (Heaps/Herdan). Existing DASHI 27-code, S3 and Heaps
-- proof owners are imported unchanged. The polynomial monodromy S3/C3
-- and quaternion spin work in PR #1414 retains SEPARATE ownership.
--
-- New finite adapter: Johl Brown-directed with OpenAI ChatGPT, 2026-10-28.
-- All Agda proof terms SOURCE-WRITTEN, NOT KERNEL-CHECKED.
-- No ESD edits, no new postulates, no C6/S3 or Monster identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Statistics.ZipfTernary27ActionHeapsExact as TwentySeven
import DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact as Hist

-- This is an OBSERVATION QUOTIENT. It is not a new three-valued
-- carrier or a replacement for the existing six S3 transformations.
data EqualityPattern5 : Set where
  allSame firstTwoSame firstThirdSame lastTwoSame allDifferent :
    EqualityPattern5

-- Codes represent functions f: {low,mid,high}->TriTruth.
-- Here, deliberately, their ordered outputs are interpreted as a word.
equalityPattern : Tower.LevelTwoCode → EqualityPattern5
equalityPattern (Base.tri-low , (Base.tri-low , Base.tri-low)) = allSame
equalityPattern (Base.tri-low , (Base.tri-low , Base.tri-mid)) = firstTwoSame
equalityPattern (Base.tri-low , (Base.tri-low , Base.tri-high)) = firstTwoSame
equalityPattern (Base.tri-low , (Base.tri-mid , Base.tri-low)) = firstThirdSame
equalityPattern (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = lastTwoSame
equalityPattern (Base.tri-low , (Base.tri-mid , Base.tri-high)) = allDifferent
equalityPattern (Base.tri-low , (Base.tri-high , Base.tri-low)) = firstThirdSame
equalityPattern (Base.tri-low , (Base.tri-high , Base.tri-mid)) = allDifferent
equalityPattern (Base.tri-low , (Base.tri-high , Base.tri-high)) = lastTwoSame
equalityPattern (Base.tri-mid , (Base.tri-low , Base.tri-low)) = lastTwoSame
equalityPattern (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = firstThirdSame
equalityPattern (Base.tri-mid , (Base.tri-low , Base.tri-high)) = allDifferent
equalityPattern (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = firstTwoSame
equalityPattern (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = allSame
equalityPattern (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = firstTwoSame
equalityPattern (Base.tri-mid , (Base.tri-high , Base.tri-low)) = allDifferent
equalityPattern (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = firstThirdSame
equalityPattern (Base.tri-mid , (Base.tri-high , Base.tri-high)) = lastTwoSame
equalityPattern (Base.tri-high , (Base.tri-low , Base.tri-low)) = lastTwoSame
equalityPattern (Base.tri-high , (Base.tri-low , Base.tri-mid)) = allDifferent
equalityPattern (Base.tri-high , (Base.tri-low , Base.tri-high)) = firstThirdSame
equalityPattern (Base.tri-high , (Base.tri-mid , Base.tri-low)) = allDifferent
equalityPattern (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = lastTwoSame
equalityPattern (Base.tri-high , (Base.tri-mid , Base.tri-high)) = firstThirdSame
equalityPattern (Base.tri-high , (Base.tri-high , Base.tri-low)) = firstTwoSame
equalityPattern (Base.tri-high , (Base.tri-high , Base.tri-mid)) = firstTwoSame
equalityPattern (Base.tri-high , (Base.tri-high , Base.tri-high)) = allSame

-- Canonical restricted-growth words on the ORIGINAL LevelTwoCode.
patternToCode : EqualityPattern5 → Tower.LevelTwoCode
patternToCode allSame =
  Base.tri-low , (Base.tri-low , Base.tri-low)
patternToCode firstTwoSame =
  Base.tri-low , (Base.tri-low , Base.tri-mid)
patternToCode firstThirdSame =
  Base.tri-low , (Base.tri-mid , Base.tri-low)
patternToCode lastTwoSame =
  Base.tri-low , (Base.tri-mid , Base.tri-mid)
patternToCode allDifferent =
  Base.tri-low , (Base.tri-mid , Base.tri-high)

patternRepresentativeRoundTrip :
  (pattern : EqualityPattern5) →
  equalityPattern (patternToCode pattern) ≡ pattern
patternRepresentativeRoundTrip allSame = refl
patternRepresentativeRoundTrip firstTwoSame = refl
patternRepresentativeRoundTrip firstThirdSame = refl
patternRepresentativeRoundTrip lastTwoSame = refl
patternRepresentativeRoundTrip allDifferent = refl

-- The source Heaps observable FACTORS through this quotient:
-- 27 source states -> five value-S3 equality classes -> four Heaps curves.
patternHeapsCurve : EqualityPattern5 → List Nat
patternHeapsCurve pattern = TwentySeven.codeHeaps (patternToCode pattern)

heapsFactorsThroughEqualityPattern :
  (code : Tower.LevelTwoCode) →
  TwentySeven.codeHeaps code ≡ patternHeapsCurve (equalityPattern code)
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
heapsFactorsThroughEqualityPattern (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

-- The action already exists: original S3 on the three TriTruth labels.
-- Unlike axis swapping or conjugation, it preserves equality patterns.
equalityPatternInvariantUnderExistingValueS3 :
  (action : Perm.TriPermutation) (code : Tower.LevelTwoCode) →
  equalityPattern (TwentySeven.valueRelabelCode action code)
    ≡ equalityPattern code
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permIdentity (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permRotate2 (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowMid (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapLowHigh (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
equalityPatternInvariantUnderExistingValueS3 Perm.permSwapMidHigh (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

-- Full Heaps merges ABA and ABB; it does not recover equality structure.
twoDifferentPatternsSameFullHeaps :
  patternHeapsCurve firstThirdSame ≡ patternHeapsCurve lastTwoSame
twoDifferentPatternsSameFullHeaps = refl

firstThirdNotLastTwo :
  firstThirdSame ≡ lastTwoSame → Hist.⊥
firstThirdNotLastTwo ()

noUniversalEqualityPatternRecoveryFromHeaps :
  (recover : List Nat → EqualityPattern5) →
  ((pattern : EqualityPattern5) →
    recover (patternHeapsCurve pattern) ≡ pattern) → Hist.⊥
noUniversalEqualityPatternRecoveryFromHeaps recover correct =
  firstThirdNotLastTwo
    (trans (sym (correct firstThirdSame))
      (trans (cong recover twoDifferentPatternsSameFullHeaps)
        (correct lastTwoSame)))

-- Both the original 27-code and statistical Heaps source definitions
-- remain unchanged. The fine observation is 5, the coarser one 4;
-- no isomorphism is asserted, and temporal order is kept explicit.
