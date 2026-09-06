module DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannWeilPairKernelFrobeniusExact as Pair
import DASHI.Analysis.RiemannHermitianDetectabilityGapExact as Detect
import DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact as AFLocal
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap

------------------------------------------------------------------------
-- TARGET-LOCAL SECOND-MOMENT REDUCTION FOR THE LIVE GAP-SPLIT CLUSTERING LEAF
--
-- Live consumer (checked Lean 8894/8896 lane):
--
--   (4/pi^2) * highGapMass < lowGapMass,
--   D = pi/(3 Lambda).
--
-- Elementary search reduction:
--
--   highGapMass <= normalizedSecondMoment
--   normalizedSecondMoment < 2 * lowGapMass
--
-- imply
--
--   highGapMass < 2 * lowGapMass.
--
-- Since 4/pi^2 < 1/2, that strict ratio is sufficient for the exact clustering
-- inequality.  This Agda module proves the discrete/slack part exactly and keeps
-- the real coefficient bridge explicit rather than pretending pi arithmetic is
-- available on this Nat carrier.
--
-- The reduction is motivated by the already-existing pair/Hermitian lane:
-- `RiemannWeilPairKernelFrobeniusExact` explicitly exposes a weighted transverse
-- moment coordinate, and `RiemannHermitianDetectabilityGapExact` explicitly
-- exposes localization as an unpaid producer.  No new external analytic source
-- claim is introduced here; the reduction itself is elementary DASHI-owned
-- arithmetic.
------------------------------------------------------------------------

congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
congSuc refl = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = congSuc (+-assoc a b c)

record NormalizedLocalSecondMomentLedger : Set where
  constructor normalized-local-second-moment-ledger
  field
    lowGapMass : Nat
    highGapMass : Nat
    normalizedSecondMoment : Nat

    highToMomentSlack : Nat
    momentToTwiceLowGapPredecessor : Nat

    highMassPlusSlackIsMoment :
      highGapMass + highToMomentSlack ≡ normalizedSecondMoment

    momentPlusPositiveGapIsTwiceLow :
      normalizedSecondMoment + suc momentToTwiceLowGapPredecessor
        ≡ lowGapMass + lowGapMass

open NormalizedLocalSecondMomentLedger public

record HighMassStrictlyBelowTwiceLow
    (l : NormalizedLocalSecondMomentLedger) : Set where
  constructor high-mass-strictly-below-twice-low
  field
    strictGapPredecessor : Nat
    highPlusPositiveGapIsTwiceLow :
      highGapMass l + suc strictGapPredecessor
        ≡ lowGapMass l + lowGapMass l

open HighMassStrictlyBelowTwiceLow public

localSecondMomentForcesTwoToOneMassRatio :
  (l : NormalizedLocalSecondMomentLedger) →
  HighMassStrictlyBelowTwiceLow l
localSecondMomentForcesTwoToOneMassRatio l =
  high-mass-strictly-below-twice-low
    (highToMomentSlack l + momentToTwiceLowGapPredecessor l)
    proof
  where
  proof :
    highGapMass l
      + suc (highToMomentSlack l + momentToTwiceLowGapPredecessor l)
      ≡ lowGapMass l + lowGapMass l
  proof
    rewrite highMassPlusSlackIsMoment l
          | momentPlusPositiveGapIsTwiceLow l = refl

------------------------------------------------------------------------
-- Existing-owner audit.
------------------------------------------------------------------------

pairKernelWeightedMomentStillOpen :
  Pair.PairKernelFrobeniusBoundary.weightedTransverseMomentBoundProvedHere
    Pair.pairKernelFrobeniusBoundary ≡ false
pairKernelWeightedMomentStillOpen = refl

hermitianLocalizationProducerStillOpen :
  Detect.HermitianDetectabilityBoundary.localizationProducerConstructedHere
    Detect.hermitianDetectabilityBoundary ≡ false
hermitianLocalizationProducerStillOpen = refl

globalSimpleProportionStillNeedsLocalization :
  AFLocal.GlobalSimpleToLocalClusteringBoundary.additionalLocalizationTheoremRequired
    AFLocal.canonicalGlobalSimpleToLocalClusteringBoundary ≡ true
globalSimpleProportionStillNeedsLocalization = refl

existingGapSplitStillRoutesToClustering :
  Gap.currentGapSplitRouteState ≡ Gap.clusteringRequired
existingGapSplitStillRoutesToClustering = refl

------------------------------------------------------------------------
-- Precise next producer boundary.
------------------------------------------------------------------------

record LocalMomentClusteringBoundary : Set where
  constructor local-moment-clustering-boundary
  field
    natMomentToTwoToOneRatioCompilerClosedInAgda : Bool
    natMomentToTwoToOneRatioCompilerClosedInAgdaIsTrue :
      natMomentToTwoToOneRatioCompilerClosedInAgda ≡ true

    elementaryCoefficientFactFourOverPiSqLtHalfNeeded : Bool
    elementaryCoefficientFactFourOverPiSqLtHalfNeededIsTrue :
      elementaryCoefficientFactFourOverPiSqLtHalfNeeded ≡ true

    coefficientBridgeProvedOnThisNatCarrier : Bool
    coefficientBridgeProvedOnThisNatCarrierIsFalse :
      coefficientBridgeProvedOnThisNatCarrier ≡ false

    exactSelectedTargetLocalSecondMomentProducerOwned : Bool
    exactSelectedTargetLocalSecondMomentProducerOwnedIsFalse :
      exactSelectedTargetLocalSecondMomentProducerOwned ≡ false

    existingPairKernelMomentLaneIsRelevant : Bool
    existingPairKernelMomentLaneIsRelevantIsTrue :
      existingPairKernelMomentLaneIsRelevant ≡ true

    existingHermitianLocalizationLaneIsRelevant : Bool
    existingHermitianLocalizationLaneIsRelevantIsTrue :
      existingHermitianLocalizationLaneIsRelevant ≡ true

    globalSimpleZeroProportionDirectlySufficient : Bool
    globalSimpleZeroProportionDirectlySufficientIsFalse :
      globalSimpleZeroProportionDirectlySufficient ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

open LocalMomentClusteringBoundary public

canonicalLocalMomentClusteringBoundary : LocalMomentClusteringBoundary
canonicalLocalMomentClusteringBoundary =
  local-moment-clustering-boundary
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The live clustering theorem can be attacked through a target-local second moment rather than another coarse count. Normalize the radius-D second moment so every high-gap zero contributes at least one unit. If that moment is strictly below twice the low-gap mass, Agda mechanically gives highGapMass < 2*lowGapMass. The remaining coefficient bridge is the elementary real fact 4/pi^2 < 1/2. The actual unpaid analytic producer is therefore a SAME-target, SAME-window second-moment bound; existing pair-kernel and Hermitian-localization owners are relevant donors, while the global >2/3 simple-zero proportion is not a direct substitute."
