module DASHI.Computation.SSSPBMSSPConsumerContractExact where

-- Pathfinding-centred composition surface for the Duan--Mao--Mao--Shu--Yin
-- 2025 BMSSP architecture.  This owner does not reimplement the graph
-- algorithm.  It states the exact consumer-facing dependencies already
-- isolated in this branch: Pull exposes only a prefix; FindPivots supplies
-- coverage plus compression; recursion consumes those interfaces without a
-- global total-order obligation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Computation.SSSPGeneralPullPrefixQuotientExact as Pull
import DASHI.Computation.SSSPFindPivotsCoverageCompressionExact as Pivot

record BMSSPStageContract : Set₁ where
  constructor bmsspStageContract
  field
    pullFactorisation : Pull.PullPrefixFactorisation
    pullTailQuotient : Pull.TailSymmetryQuotient pullFactorisation
    pullTailInvariant : Pull.PullTailInvariance pullFactorisation pullTailQuotient
    findPivots : Pivot.FindPivotsCertificate

    recursiveConsumerRequiresPrefix : Bool
    recursiveConsumerRequiresPrefixIsTrue : recursiveConsumerRequiresPrefix ≡ true
    recursiveConsumerRequiresPivotCoverage : Bool
    recursiveConsumerRequiresPivotCoverageIsTrue : recursiveConsumerRequiresPivotCoverage ≡ true
    recursiveConsumerRequiresPivotCompression : Bool
    recursiveConsumerRequiresPivotCompressionIsTrue : recursiveConsumerRequiresPivotCompression ≡ true
    recursiveConsumerRequiresGlobalTailSort : Bool
    recursiveConsumerRequiresGlobalTailSortIsFalse : recursiveConsumerRequiresGlobalTailSort ≡ false

open BMSSPStageContract public

recursiveConsumerInvariantUnderTailSymmetry :
  (C : BMSSPStageContract) →
  (consumer : Pull.PrefixConsumer (pullFactorisation C)) →
  (g : Pull.Symmetry (pullTailQuotient C)) →
  (x : Pull.FullState (pullFactorisation C)) →
  Pull.consumeFull consumer (Pull.actFull (pullTailQuotient C) g x)
  ≡ Pull.consumeFull consumer x
recursiveConsumerInvariantUnderTailSymmetry C consumer g x =
  Pull.consumerInvariantUnderTailSymmetry
    (pullFactorisation C)
    (pullTailQuotient C)
    (pullTailInvariant C)
    consumer g x

record BMSSPBidiBoundary : Set where
  constructor bmsspBidiBoundary
  field
    pullPrefixNeeded : Bool
    pullPrefixNeededIsTrue : pullPrefixNeeded ≡ true
    pivotCoverageNeeded : Bool
    pivotCoverageNeededIsTrue : pivotCoverageNeeded ≡ true
    pivotCompressionNeeded : Bool
    pivotCompressionNeededIsTrue : pivotCompressionNeeded ≡ true
    fullLinearExtensionNeeded : Bool
    fullLinearExtensionNeededIsFalse : fullLinearExtensionNeeded ≡ false
    base369CarrierNeededForCorrectness : Bool
    base369CarrierNeededForCorrectnessIsFalse : base369CarrierNeededForCorrectness ≡ false

canonicalBMSSPBidiBoundary : BMSSPBidiBoundary
canonicalBMSSPBidiBoundary =
  bmsspBidiBoundary true refl true refl true refl false refl false refl
