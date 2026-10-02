{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ThreeClassAnalyticWallRound768Exact where

------------------------------------------------------------------------
-- ROUND768 / CURRENT W2 ANALYTIC WALL AFTER SWAP PAIRING
--
-- R757 exposed four R25 channels on the actual R749 residual.
-- R758-R765 use the physical p/q partner involution without assuming the
-- unsymmetrized residual is pointwise invariant:
--
--   * the dyadic production correction is swap invariant;
--   * all raw swap asymmetry is nested;
--   * division-free pairing gives PairD(beta)=D(beta)+D(swap beta);
--   * PairD is swap invariant;
--   * the authoritative R25/R130 classifier exchanges LH <-> HL;
--   * therefore PairD_LH = PairD_HL exactly.
--
-- R766 integrates the resulting three-class carrier and R767 proves exact
-- equivalence to W2.
--
-- The preferred W2 analytic obligation is therefore:
--
--   0 <= integral [
--          2 LH_pair
--          + CC_pair
--          + HH_pair
--          + 6 (2 nu-delta) d_N
--        ] dt,
--   delta > 0.
--
-- No sign is currently proved for the three signed triadic channels.
-- CC has no generic pointwise half-derivative gain (existing R232 no-go).
-- HH has older radial/Pluecker donor machinery, but no same-object weld to
-- this paired residual is claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR650FiveClassResidualPartitionRound757Exact as R757
import DASHI.Physics.Closure.NSTriadKNR650DyadicProductionSwapInvariantRound758Exact as R758
import DASHI.Physics.Closure.NSTriadKNR650ResidualSwapDefectRound759Exact as R759
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNR650CommutatorSwapPairProductRuleRound761Exact as R761
import DASHI.Physics.Closure.NSTriadKNR650NestedSwapPairProductRuleRound762Exact as R762
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedNestedOrbitNormalFormRound763Exact as R763
import DASHI.Physics.Closure.NSTriadKNR650SwapInvariantFourClassScalarRound764Exact as R764
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedThreeClassW2Round765Exact as R765
import DASHI.Physics.Closure.NSTriadKNR650IntegratedThreeClassW2Round766Exact as R766
import DASHI.Physics.Closure.NSTriadKNR650ThreeClassW2PaymentRound767Exact as R767

round768ActualR749CarrierClassifiedExactly : Bool
round768ActualR749CarrierClassifiedExactly =
  R757.round757ActualR749ResidualPartitionedByR25

round768ProductionCorrectionSwapInvariant : Bool
round768ProductionCorrectionSwapInvariant =
  R758.round758TwoDifferenceProductionSwapInvariant

round768RawSwapAsymmetryLocalizedToNestedOrbit : Bool
round768RawSwapAsymmetryLocalizedToNestedOrbit =
  R759.round759LHHLAsymmetryLocalizedToNestedOrbit

round768DivisionFreeSwapPairCarrierClosed : Bool
round768DivisionFreeSwapPairCarrierClosed =
  R760.round760CompleteSwapPairedFoldIsTwiceR749Fold

round768SwapPairedCommutatorIsProductRule : Bool
round768SwapPairedCommutatorIsProductRule =
  R761.round761CommutatorSwapPairIsProductRuleSwapPair

round768NestedSwapPairProductRuleLiftClosed : Bool
round768NestedSwapPairProductRuleLiftClosed =
  R762.round762NestedSwapPairIsFourProductRuleCopies

round768NestedOrbitSwapPairNormalFormClosed : Bool
round768NestedOrbitSwapPairNormalFormClosed =
  R763.round763NestedOrbitSwapPairNormalFormClosed

round768GenericSwapInvariantLHEqualsHL : Bool
round768GenericSwapInvariantLHEqualsHL =
  R764.round764GenericSwapInvariantLHHLExactEquality

round768PairedLHEqualsHL : Bool
round768PairedLHEqualsHL =
  R765.round765PairedLHEqualsHL

round768IntegratedThreeClassCarrierExact : Bool
round768IntegratedThreeClassCarrierExact =
  R766.round766IntegratedThreeClassIsTwiceCanonicalR746Residual

round768W2ExactlyEquivalentToThreeClassPayment : Bool
round768W2ExactlyEquivalentToThreeClassPayment =
  R767.round767ThreeClassPaymentExactlyEquivalentToW2

round768PreferredW2TriadicChannelCountIsThree : Bool
round768PreferredW2TriadicChannelCountIsThree = true

round768IndependentLHHLLeaves : Bool
round768IndependentLHHLLeaves = false

round768ThreeClassSignsClosed : Bool
round768ThreeClassSignsClosed = false

round768W1Closed : Bool
round768W1Closed = false

round768W2Closed : Bool
round768W2Closed =
  R767.round767IntegratedThreeClassPaymentClosed

round768IntroducesEstimate : Bool
round768IntroducesEstimate = false

round768ClayPromotion : Bool
round768ClayPromotion = false

round768ActualR749CarrierClassifiedExactlyIsTrue :
  round768ActualR749CarrierClassifiedExactly ≡ true
round768ActualR749CarrierClassifiedExactlyIsTrue =
  R757.round757ActualR749ResidualPartitionedByR25IsTrue

round768ProductionCorrectionSwapInvariantIsTrue :
  round768ProductionCorrectionSwapInvariant ≡ true
round768ProductionCorrectionSwapInvariantIsTrue =
  R758.round758TwoDifferenceProductionSwapInvariantIsTrue

round768RawSwapAsymmetryLocalizedToNestedOrbitIsTrue :
  round768RawSwapAsymmetryLocalizedToNestedOrbit ≡ true
round768RawSwapAsymmetryLocalizedToNestedOrbitIsTrue =
  R759.round759LHHLAsymmetryLocalizedToNestedOrbitIsTrue

round768DivisionFreeSwapPairCarrierClosedIsTrue :
  round768DivisionFreeSwapPairCarrierClosed ≡ true
round768DivisionFreeSwapPairCarrierClosedIsTrue =
  R760.round760CompleteSwapPairedFoldIsTwiceR749FoldIsTrue

round768SwapPairedCommutatorIsProductRuleIsTrue :
  round768SwapPairedCommutatorIsProductRule ≡ true
round768SwapPairedCommutatorIsProductRuleIsTrue =
  R761.round761CommutatorSwapPairIsProductRuleSwapPairIsTrue

round768NestedSwapPairProductRuleLiftClosedIsTrue :
  round768NestedSwapPairProductRuleLiftClosed ≡ true
round768NestedSwapPairProductRuleLiftClosedIsTrue =
  R762.round762NestedSwapPairIsFourProductRuleCopiesIsTrue

round768NestedOrbitSwapPairNormalFormClosedIsTrue :
  round768NestedOrbitSwapPairNormalFormClosed ≡ true
round768NestedOrbitSwapPairNormalFormClosedIsTrue =
  R763.round763NestedOrbitSwapPairNormalFormClosedIsTrue

round768GenericSwapInvariantLHEqualsHLIsTrue :
  round768GenericSwapInvariantLHEqualsHL ≡ true
round768GenericSwapInvariantLHEqualsHLIsTrue =
  R764.round764GenericSwapInvariantLHHLExactEqualityIsTrue

round768PairedLHEqualsHLIsTrue :
  round768PairedLHEqualsHL ≡ true
round768PairedLHEqualsHLIsTrue =
  R765.round765PairedLHEqualsHLIsTrue

round768IntegratedThreeClassCarrierExactIsTrue :
  round768IntegratedThreeClassCarrierExact ≡ true
round768IntegratedThreeClassCarrierExactIsTrue =
  R766.round766IntegratedThreeClassIsTwiceCanonicalR746ResidualIsTrue

round768W2ExactlyEquivalentToThreeClassPaymentIsTrue :
  round768W2ExactlyEquivalentToThreeClassPayment ≡ true
round768W2ExactlyEquivalentToThreeClassPaymentIsTrue =
  R767.round767ThreeClassPaymentExactlyEquivalentToW2IsTrue

round768PreferredW2TriadicChannelCountIsThreeIsTrue :
  round768PreferredW2TriadicChannelCountIsThree ≡ true
round768PreferredW2TriadicChannelCountIsThreeIsTrue = refl

round768IndependentLHHLLeavesIsFalse :
  round768IndependentLHHLLeaves ≡ false
round768IndependentLHHLLeavesIsFalse = refl

round768ThreeClassSignsClosedIsFalse :
  round768ThreeClassSignsClosed ≡ false
round768ThreeClassSignsClosedIsFalse = refl

round768W1ClosedIsFalse :
  round768W1Closed ≡ false
round768W1ClosedIsFalse = refl

round768W2ClosedIsFalse :
  round768W2Closed ≡ false
round768W2ClosedIsFalse =
  R767.round767IntegratedThreeClassPaymentClosedIsFalse

round768IntroducesEstimateIsFalse :
  round768IntroducesEstimate ≡ false
round768IntroducesEstimateIsFalse = refl

round768ClayPromotionIsFalse :
  round768ClayPromotion ≡ false
round768ClayPromotionIsFalse = refl
