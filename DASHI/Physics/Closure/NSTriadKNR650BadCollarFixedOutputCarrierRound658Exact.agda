{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarFixedOutputCarrierRound658Exact where

------------------------------------------------------------------------
-- ROUND658 / BAD COLLAR -> SAME HEAT-NESTED / UNWEIGHTED FIXED-OUTPUT CARRIER
--
-- R656/R657 isolate the only adverse purely spectral region to the low-radius
-- part of one exact max-norm collar:
--
--     badCollarPacket K.
--
-- This selector depends only on the final output k.  Therefore the already-
-- generic R419/R294 machinery applies literally:
--
--   * on an R329 heat-nested outer cell, the bad-collar packet scalar is the
--     SAME R98 selected outer-incidence scalar;
--   * R336 sameFinalOutput preserves the bad-collar selector bit;
--   * the output-local 0/1 commutator weight is p/q-swap invariant;
--   * on an active bad-collar fixed-output fibre, that weight disappears and
--     the weighted commutator is the ordinary unweighted R230 commutator;
--   * on an inactive fibre, the weighted commutator is exactly zero.
--
-- Thus the surviving local quantitative theorem may be searched directly on
-- the existing unweighted fixed-output coherent-covariance/pair-difference
-- carrier, restricted only by the output predicate badCollarPacket K.
--
-- No quantitative payment, pair-difference lower separation, cutoff-uniform
-- aggregation, boundary-flux estimate, or Clay promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPreTTStarAdapterRound336Exact as R336
import DASHI.Physics.Closure.NSTriadKNHeatNestedOuterPacketCarrierRound419Exact as R419
import DASHI.Physics.Closure.NSTriadKNOutputLocalSelectorFixedOutputReductionExact as OutputLocal
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact as R656

F : C3.RealField _
F = Rational.rationalRealField

badCollarNestedOuterPacketPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (K : Nat) →
  R329.StrongLowLiteralNestedCell E I O system S L H W →
  ℚ
badCollarNestedOuterPacketPower E I O system S L H W K =
  R419.nestedOuterPacketPower
    E I O system S L H W (R656.badCollarPacket K)

badCollarNestedOuterPacketPowerIsLiteralR98OnSameOuter :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (K : Nat) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  badCollarNestedOuterPacketPower E I O system S L H W K C
  ≡ R419.nestedOuterPacketPower
      E I O system S L H W (R656.badCollarPacket K) C
badCollarNestedOuterPacketPowerIsLiteralR98OnSameOuter
    E I O system S L H W K C = refl

sameFinalOutputImpliesSameBadCollarSelectorBit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (K : Nat) →
  (P : R336.HeatWeightedNestedPairwiseOverlap E I O system S L H W) →
  R656.badCollarPacket K
      (Physical.k (R329.outer (R336.left P)))
  ≡ R656.badCollarPacket K
      (Physical.k (R329.outer (R336.right P)))
sameFinalOutputImpliesSameBadCollarSelectorBit
    E I O system S L H W K P =
  R419.sameFinalOutputImpliesSamePacketSelectorBit
    E I O system S L H W (R656.badCollarPacket K) P

badCollarActiveFixedOutputReduction :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (K : Nat) →
  (output : Z3.FourierMode) →
  R656.badCollarPacket K output ≡ true →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (OutputLocal.outputLocalSwapInvariantWeight F (R656.badCollarPacket K))
      S velocity forcing)
    (Output.physicalOutputFiber
      cutoff output)
  ≡
  R224.foldVector
    (OutputLocal.unweightedCommutatorCell S velocity forcing)
    (Output.physicalOutputFiber
      cutoff output)
badCollarActiveFixedOutputReduction K output active =
  OutputLocal.outputLocalActiveFixedOutputReduction
    (R656.badCollarPacket K) output active

badCollarInactiveFixedOutputReduction :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (K : Nat) →
  (output : Z3.FourierMode) →
  R656.badCollarPacket K output ≡ false →
  (S : Helical.HelicalModeScalars F) →
  (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  R224.foldVector
    (R294.weightedCommutatorCell
      (OutputLocal.outputLocalSwapInvariantWeight F (R656.badCollarPacket K))
      S velocity forcing)
    (Output.physicalOutputFiber
      cutoff output)
  ≡ C3.complex3Zero F
badCollarInactiveFixedOutputReduction K output inactive =
  OutputLocal.outputLocalInactiveFixedOutputReduction
    (R656.badCollarPacket K) output inactive

round658BadCollarUsesSameR98HeatNestedOuterCarrier : Bool
round658BadCollarUsesSameR98HeatNestedOuterCarrier = true

round658SameOutputPreservesBadCollarSelector : Bool
round658SameOutputPreservesBadCollarSelector = true

round658BadCollarActiveFibreIsUnweightedCommutator : Bool
round658BadCollarActiveFibreIsUnweightedCommutator = true

round658BadCollarInactiveFibreIsZero : Bool
round658BadCollarInactiveFibreIsZero = true

round658QuantitativeBadCollarPaymentClosed : Bool
round658QuantitativeBadCollarPaymentClosed = false

round658PhysicalPairDifferenceLowerSeparationClosed : Bool
round658PhysicalPairDifferenceLowerSeparationClosed = false

round658CutoffUniformBadCollarAggregationClosed : Bool
round658CutoffUniformBadCollarAggregationClosed = false

round658IntroducesNewClayLeaf : Bool
round658IntroducesNewClayLeaf = false

round658C2Closed : Bool
round658C2Closed = false

round658ClayPromotion : Bool
round658ClayPromotion = false

round658BadCollarUsesSameR98HeatNestedOuterCarrierIsTrue :
  round658BadCollarUsesSameR98HeatNestedOuterCarrier ≡ true
round658BadCollarUsesSameR98HeatNestedOuterCarrierIsTrue = refl

round658SameOutputPreservesBadCollarSelectorIsTrue :
  round658SameOutputPreservesBadCollarSelector ≡ true
round658SameOutputPreservesBadCollarSelectorIsTrue = refl

round658BadCollarActiveFibreIsUnweightedCommutatorIsTrue :
  round658BadCollarActiveFibreIsUnweightedCommutator ≡ true
round658BadCollarActiveFibreIsUnweightedCommutatorIsTrue = refl

round658BadCollarInactiveFibreIsZeroIsTrue :
  round658BadCollarInactiveFibreIsZero ≡ true
round658BadCollarInactiveFibreIsZeroIsTrue = refl

round658QuantitativeBadCollarPaymentClosedIsFalse :
  round658QuantitativeBadCollarPaymentClosed ≡ false
round658QuantitativeBadCollarPaymentClosedIsFalse = refl

round658PhysicalPairDifferenceLowerSeparationClosedIsFalse :
  round658PhysicalPairDifferenceLowerSeparationClosed ≡ false
round658PhysicalPairDifferenceLowerSeparationClosedIsFalse = refl

round658CutoffUniformBadCollarAggregationClosedIsFalse :
  round658CutoffUniformBadCollarAggregationClosed ≡ false
round658CutoffUniformBadCollarAggregationClosedIsFalse = refl

round658IntroducesNewClayLeafIsFalse :
  round658IntroducesNewClayLeaf ≡ false
round658IntroducesNewClayLeafIsFalse = refl

round658C2ClosedIsFalse :
  round658C2Closed ≡ false
round658C2ClosedIsFalse = refl

round658ClayPromotionIsFalse :
  round658ClayPromotion ≡ false
round658ClayPromotionIsFalse = refl
