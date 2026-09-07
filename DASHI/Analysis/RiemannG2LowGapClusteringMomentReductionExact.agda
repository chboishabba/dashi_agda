module DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase
import DASHI.Analysis.RiemannG2TransverseVsOrdinateMomentNonDescentExact as Coord
import DASHI.Analysis.RiemannG2AlpogeFurmanClusteringNonDescentExact as AFLocal
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap

------------------------------------------------------------------------
-- TARGET-LOCAL ORDINATE SECOND-MOMENT REDUCTION
--
-- Diagnostic consumer (checked Lean 8894/8896 lane):
--
--   (4/pi^2) * highGapMass < lowGapMass,
--   D = pi/(3 Lambda).
--
-- Here the moment coordinate is explicitly the target-relative ORDINATE gap
--
--   delta = Im(rho) - t,
--
-- not the transverse/off-critical-line coordinate alpha = Re(rho)-1/2.
-- The correct in-repo carrier is therefore
-- PoleNearPhaseStatistic.targetRelativeGap.
--
-- Later x-pollination now owns the concrete phase-statistic VIEW as compiler
-- output from DirectFinitePoleNearProducer. That does not own the analytic local
-- second moment itself; it only removes the old need for a second phase carrier.
------------------------------------------------------------------------

congSuc : {x y : Nat} → x ≡ y → suc x ≡ suc y
congSuc refl = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = congSuc (+-assoc a b c)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

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
    nonnegativePrefix : Nat
    positiveTailPredecessor : Nat
    highPlusStrictSlackIsTwiceLow :
      highGapMass l + (nonnegativePrefix + suc positiveTailPredecessor)
        ≡ lowGapMass l + lowGapMass l

open HighMassStrictlyBelowTwiceLow public

localSecondMomentForcesTwoToOneMassRatio :
  (l : NormalizedLocalSecondMomentLedger) →
  HighMassStrictlyBelowTwiceLow l
localSecondMomentForcesTwoToOneMassRatio l =
  high-mass-strictly-below-twice-low
    (highToMomentSlack l)
    (momentToTwiceLowGapPredecessor l)
    proof
  where
  proof :
    highGapMass l
      + (highToMomentSlack l + suc (momentToTwiceLowGapPredecessor l))
      ≡ lowGapMass l + lowGapMass l
  proof =
    trans
      (sym (+-assoc
        (highGapMass l)
        (highToMomentSlack l)
        (suc (momentToTwiceLowGapPredecessor l))))
      (trans
        (congTail (highMassPlusSlackIsMoment l)
          (suc (momentToTwiceLowGapPredecessor l)))
        (momentPlusPositiveGapIsTwiceLow l))
    where
    congTail : {a b : Nat} → a ≡ b → (c : Nat) → a + c ≡ b + c
    congTail refl c = refl

------------------------------------------------------------------------
-- Existing-owner / coordinate audit.
------------------------------------------------------------------------

transverseMomentDoesNotDetermineOrdinateMoment :
  Coord.TransverseVsOrdinateMomentBoundary.transverseMomentDeterminesTargetOrdinateMoment
    Coord.canonicalTransverseVsOrdinateMomentBoundary ≡ false
transverseMomentDoesNotDetermineOrdinateMoment = refl

targetRelativeGapIsCorrectCarrier :
  Coord.TransverseVsOrdinateMomentBoundary.targetRelativePhaseGapCoordinateIsCorrectCarrier
    Coord.canonicalTransverseVsOrdinateMomentBoundary ≡ true
targetRelativeGapIsCorrectCarrier = refl

concreteTargetRelativePhaseStatisticOwned :
  Phase.PoleNearPhaseStatisticBoundary.repositoryAlreadyOwnsConcretePoleNearPhaseStatistic
    Phase.canonicalPoleNearPhaseStatisticBoundary ≡ true
concreteTargetRelativePhaseStatisticOwned = refl

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

    targetRelativeGapLaneIsCorrectAnalyticCarrier : Bool
    targetRelativeGapLaneIsCorrectAnalyticCarrierIsTrue :
      targetRelativeGapLaneIsCorrectAnalyticCarrier ≡ true

    transverseHermitianMomentIsDirectAnalyticDonor : Bool
    transverseHermitianMomentIsDirectAnalyticDonorIsFalse :
      transverseHermitianMomentIsDirectAnalyticDonor ≡ false

    concreteTargetPhaseStatisticAlreadyOwned : Bool
    concreteTargetPhaseStatisticAlreadyOwnedIsTrue :
      concreteTargetPhaseStatisticAlreadyOwned ≡ true

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
    false refl
    true refl
    false refl
    false refl
    "The target-relative phase-statistic VIEW is now compiler-owned from the existing direct finite producer; do not construct a second phase carrier. The actual target-relative second-moment estimate remains uninhabited, and this lane remains a clustering/obstruction diagnostic rather than a terminal RH payment. If a same-window moment is later supplied, the Nat two-to-one ratio compiler remains reusable. Do not schedule this moment producer ahead of the direct universal pole-quotient Off allowance theorem merely to recreate phase information already present there. RH is not derived."
