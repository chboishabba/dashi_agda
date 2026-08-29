{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowAAugmentedCanonicalChoiceExact where

------------------------------------------------------------------------
-- ROW A: b,C,L,H FINITE -> CANONICAL CAP FOR THE HISTORY-AUGMENTED GATE
--
-- The previous theorem shows that if
--
--   q_history <= H gamma
--
-- then the honest direct+history shooting condition follows from
--
--   (C + L + b H) gamma < b.
--
-- There is again no scalar existence problem.  Feed the effective derivative
-- constant
--
--   L_eff = L + b H
--
-- into the existing canonical small-coupling theorem and choose
--
--   gamma* = b / (2 (C + L_eff + 1)).
--
-- This file proves the exact adapter.  Thus the final physical Row-A sensitivity
-- seam is not "choose gamma" but the source theorem q_history <= H gamma with
-- finite H on the same literal trajectory.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact as Choice
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedCanonicalHistoryGateExact as HistoryGate

record FiniteAugmentedRowASourceConstants : Set where
  field
    gaussianFloor interactionConstant localDerivative historySlope : ℚ
    gaussianFloorPositive : 0ℚ < gaussianFloor
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    localDerivativeNonnegative : 0ℚ ≤ localDerivative
    historySlopeNonnegative : 0ℚ ≤ historySlope

open FiniteAugmentedRowASourceConstants public

effectiveDerivative : FiniteAugmentedRowASourceConstants → ℚ
effectiveDerivative dataSet =
  localDerivative dataSet + gaussianFloor dataSet * historySlope dataSet

effectiveDerivativeNonnegative :
  (dataSet : FiniteAugmentedRowASourceConstants) →
  0ℚ ≤ effectiveDerivative dataSet
effectiveDerivativeNonnegative dataSet =
  let
    bNN = ℚP.<⇒≤ (gaussianFloorPositive dataSet)
    bHNN : 0ℚ ≤ gaussianFloor dataSet * historySlope dataSet
    bHNN =
      let instance bNonnegative = ℚ.nonNegative bNN
          hNonnegative = ℚ.nonNegative (historySlopeNonnegative dataSet)
      in ℚP.nonNegative⁻¹
        (gaussianFloor dataSet * historySlope dataSet)
  in
  ℚP.+-mono-≤ (localDerivativeNonnegative dataSet) bHNN

asFiniteRowASourceConstants :
  FiniteAugmentedRowASourceConstants → Choice.FiniteRowASourceConstants
asFiniteRowASourceConstants dataSet = record
  { Choice.FiniteRowASourceConstants.gaussianFloor = gaussianFloor dataSet
  ; Choice.FiniteRowASourceConstants.interactionConstant =
      interactionConstant dataSet
  ; Choice.FiniteRowASourceConstants.derivativeBound =
      effectiveDerivative dataSet
  ; Choice.FiniteRowASourceConstants.gaussianFloorPositive =
      gaussianFloorPositive dataSet
  ; Choice.FiniteRowASourceConstants.interactionConstantNonnegative =
      interactionConstantNonnegative dataSet
  ; Choice.FiniteRowASourceConstants.derivativeBoundNonnegative =
      effectiveDerivativeNonnegative dataSet
  }

canonicalAugmentedGamma : FiniteAugmentedRowASourceConstants → ℚ
canonicalAugmentedGamma dataSet =
  Choice.canonicalGamma (asFiniteRowASourceConstants dataSet)

canonicalAugmentedGammaPositive :
  (dataSet : FiniteAugmentedRowASourceConstants) →
  0ℚ < canonicalAugmentedGamma dataSet
canonicalAugmentedGammaPositive dataSet =
  Choice.canonicalGammaPositive (asFiniteRowASourceConstants dataSet)

canonicalAugmentedGammaPaysCombinedSmallness :
  (dataSet : FiniteAugmentedRowASourceConstants) →
  (interactionConstant dataSet + localDerivative dataSet
    + gaussianFloor dataSet * historySlope dataSet)
    * canonicalAugmentedGamma dataSet
  < gaussianFloor dataSet
canonicalAugmentedGammaPaysCombinedSmallness dataSet =
  Choice.canonicalGammaPaysCombinedSmallness
    (asFiniteRowASourceConstants dataSet)

record CanonicalAugmentedHistoryInputs
    (source : FiniteAugmentedRowASourceConstants) : Set where
  field
    tubeWidth historyConstant : ℚ
    tubeWidthNonnegative : 0ℚ ≤ tubeWidth
    historyConstantNonnegative : 0ℚ ≤ historyConstant
    tubeWidthBelowCanonicalGamma :
      tubeWidth ≤ canonicalAugmentedGamma source
    historyBelowSlopeTimesCanonicalGamma :
      historyConstant
      ≤ historySlope source * canonicalAugmentedGamma source

open CanonicalAugmentedHistoryInputs public

asAugmentedHistoryGate :
  (source : FiniteAugmentedRowASourceConstants) →
  CanonicalAugmentedHistoryInputs source →
  HistoryGate.AugmentedHistorySmallCouplingGate
asAugmentedHistoryGate source inputs = record
  { HistoryGate.AugmentedHistorySmallCouplingGate.gaussianFloor =
      gaussianFloor source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.interactionConstant =
      interactionConstant source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.localDerivative =
      localDerivative source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.historySlope =
      historySlope source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.couplingCap =
      canonicalAugmentedGamma source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.tubeWidth =
      tubeWidth inputs
  ; HistoryGate.AugmentedHistorySmallCouplingGate.historyConstant =
      historyConstant inputs
  ; HistoryGate.AugmentedHistorySmallCouplingGate.gaussianFloorPositive =
      gaussianFloorPositive source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.interactionConstantNonnegative =
      interactionConstantNonnegative source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.localDerivativeNonnegative =
      localDerivativeNonnegative source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.historySlopeNonnegative =
      historySlopeNonnegative source
  ; HistoryGate.AugmentedHistorySmallCouplingGate.couplingCapNonnegative =
      ℚP.<⇒≤ (canonicalAugmentedGammaPositive source)
  ; HistoryGate.AugmentedHistorySmallCouplingGate.tubeWidthNonnegative =
      tubeWidthNonnegative inputs
  ; HistoryGate.AugmentedHistorySmallCouplingGate.historyConstantNonnegative =
      historyConstantNonnegative inputs
  ; HistoryGate.AugmentedHistorySmallCouplingGate.tubeWidthBelowCap =
      tubeWidthBelowCanonicalGamma inputs
  ; HistoryGate.AugmentedHistorySmallCouplingGate.historyBelowSlopeTimesCap =
      historyBelowSlopeTimesCanonicalGamma inputs
  ; HistoryGate.AugmentedHistorySmallCouplingGate.combinedSmallness =
      canonicalAugmentedGammaPaysCombinedSmallness source
  }

canonicalAugmentedHistoryGate :
  (source : FiniteAugmentedRowASourceConstants) →
  (inputs : CanonicalAugmentedHistoryInputs source) →
  let gate = asAugmentedHistoryGate source inputs
  in
  HistoryGate.localDerivative gate * HistoryGate.tubeWidth gate
    + HistoryGate.betaMargin gate * HistoryGate.historyConstant gate
  < HistoryGate.betaMargin gate
canonicalAugmentedHistoryGate source inputs =
  HistoryGate.augmentedHistoryGate (asAugmentedHistoryGate source inputs)

rowAAugmentedCanonicalChoiceLevel : ProofLevel
rowAAugmentedCanonicalChoiceLevel = machineChecked

rowAAugmentedCanonicalHistoryGateLevel : ProofLevel
rowAAugmentedCanonicalHistoryGateLevel = machineChecked

-- Physical seam: produce finite H and q_history <= H gamma from the literal
-- irrelevant/polymer response to the shooting input.  The scalar cap and strict
-- combined gate are now theorem-generated.
literalRowAHistorySlopeInstantiationLevel : ProofLevel
literalRowAHistorySlopeInstantiationLevel = conditional
