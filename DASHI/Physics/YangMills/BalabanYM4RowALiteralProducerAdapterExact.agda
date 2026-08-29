{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowALiteralProducerAdapterExact where

------------------------------------------------------------------------
-- ROW A: ONE SOURCE-FACING PRODUCER FOR b, C, L_local, H AND gamma*
--
-- The current Row-A machinery has four quantitatively meaningful producer
-- outputs:
--
--   b       : positive Gaussian floor (Ward-patch lane),
--   C       : finite nonlinear interaction coefficient,
--   L_local : direct current-coupling derivative coefficient,
--   H       : irrelevant-history sensitivity slope, q_history <= H gamma.
--
-- The first three already come from the fixed Ward rational and one literal
-- normalized-interaction mixed-Cauchy package.  H comes from one contractive
-- irrelevant coordinate, one Lipschitz beta projection and the single source
-- estimate saying that the initial irrelevant response to the shooting input is
-- O(gamma).
--
-- This module welds those producers into the history-augmented canonical-choice
-- carrier.  It does not introduce a fifth constant or a second small-coupling
-- choice.  After this adapter, the physical Row-A data can be requested in
-- exactly the source-native pieces above.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4InteractionMixedCouplingDerivativeGateExact as Mixed
import DASHI.Physics.YangMills.BalabanIrrelevantRGMemoryContractionExact as Memory
import DASHI.Physics.YangMills.BalabanYM4RowAIrrelevantHistoryInputSensitivityExact as Input
import DASHI.Physics.YangMills.BalabanYM4RowAIrrelevantHistoryLinearCouplingExact as Linear
import DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact as Cauchy
import DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact as Ward
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedCanonicalChoiceExact as Choice

zeroHistorySource :
  Mixed.MixedInteractionCauchyData → Cauchy.RowACauchySourceConstants
zeroHistorySource mixed = record
  { Cauchy.RowACauchySourceConstants.gaussianFloor = Ward.wardGaussianFloor
  ; Cauchy.RowACauchySourceConstants.gaussianFloorPositive =
      Ward.wardGaussianFloorPositive
  ; Cauchy.RowACauchySourceConstants.mixedInteraction = mixed
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstant = 0ℚ
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstantNonnegative =
      ℚP.≤-refl
  }

record LiteralRowAProducerPieces : Set₁ where
  field
    mixedInteraction : Mixed.MixedInteractionCauchyData

    irrelevantMemory : Memory.ContractiveIrrelevantMemory
    betaProjection : Memory.LipschitzIrrelevantBetaProjection irrelevantMemory
    inputResponse : Input.IrrelevantHistoryInputResponse betaProjection
    linearResponse : Linear.InitialResponseLinearInCoupling inputResponse

open LiteralRowAProducerPieces public

interactionConstant : LiteralRowAProducerPieces → ℚ
interactionConstant dataSet =
  Cauchy.sourceInteractionConstant (zeroHistorySource (mixedInteraction dataSet))

localDerivativeConstant : LiteralRowAProducerPieces → ℚ
localDerivativeConstant dataSet =
  Cauchy.sourceLocalDerivativeConstant
    (zeroHistorySource (mixedInteraction dataSet))

historySlope : LiteralRowAProducerPieces → ℚ
historySlope dataSet = Linear.historySlope (linearResponse dataSet)

interactionConstantNonnegative :
  (dataSet : LiteralRowAProducerPieces) →
  0ℚ ≤ interactionConstant dataSet
interactionConstantNonnegative dataSet =
  Cauchy.sourceInteractionConstantNonnegative
    (zeroHistorySource (mixedInteraction dataSet))

localDerivativeConstantNonnegative :
  (dataSet : LiteralRowAProducerPieces) →
  0ℚ ≤ localDerivativeConstant dataSet
localDerivativeConstantNonnegative dataSet =
  Cauchy.sourceLocalDerivativeConstantNonnegative
    (zeroHistorySource (mixedInteraction dataSet))

historySlopeNonnegative :
  (dataSet : LiteralRowAProducerPieces) → 0ℚ ≤ historySlope dataSet
historySlopeNonnegative dataSet =
  Linear.historySlopeNonnegative (linearResponse dataSet)

asFiniteAugmentedSource :
  LiteralRowAProducerPieces → Choice.FiniteAugmentedRowASourceConstants
asFiniteAugmentedSource dataSet = record
  { Choice.FiniteAugmentedRowASourceConstants.gaussianFloor =
      Ward.wardGaussianFloor
  ; Choice.FiniteAugmentedRowASourceConstants.interactionConstant =
      interactionConstant dataSet
  ; Choice.FiniteAugmentedRowASourceConstants.localDerivative =
      localDerivativeConstant dataSet
  ; Choice.FiniteAugmentedRowASourceConstants.historySlope =
      historySlope dataSet
  ; Choice.FiniteAugmentedRowASourceConstants.gaussianFloorPositive =
      Ward.wardGaussianFloorPositive
  ; Choice.FiniteAugmentedRowASourceConstants.interactionConstantNonnegative =
      interactionConstantNonnegative dataSet
  ; Choice.FiniteAugmentedRowASourceConstants.localDerivativeNonnegative =
      localDerivativeConstantNonnegative dataSet
  ; Choice.FiniteAugmentedRowASourceConstants.historySlopeNonnegative =
      historySlopeNonnegative dataSet
  }

canonicalLiteralGamma : LiteralRowAProducerPieces → ℚ
canonicalLiteralGamma dataSet =
  Choice.canonicalAugmentedGamma (asFiniteAugmentedSource dataSet)

canonicalLiteralGammaPositive :
  (dataSet : LiteralRowAProducerPieces) →
  0ℚ < canonicalLiteralGamma dataSet
canonicalLiteralGammaPositive dataSet =
  Choice.canonicalAugmentedGammaPositive (asFiniteAugmentedSource dataSet)

canonicalLiteralGammaPaysAugmentedSmallness :
  (dataSet : LiteralRowAProducerPieces) →
  (interactionConstant dataSet + localDerivativeConstant dataSet
    + Ward.wardGaussianFloor * historySlope dataSet)
    * canonicalLiteralGamma dataSet
  < Ward.wardGaussianFloor
canonicalLiteralGammaPaysAugmentedSmallness dataSet =
  Choice.canonicalAugmentedGammaPaysCombinedSmallness
    (asFiniteAugmentedSource dataSet)

sourceHistorySensitivityLinearInDeclaredCoupling :
  (dataSet : LiteralRowAProducerPieces) →
  Input.historySensitivityConstant (inputResponse dataSet)
  ≤ historySlope dataSet * Linear.couplingCap (linearResponse dataSet)
sourceHistorySensitivityLinearInDeclaredCoupling dataSet =
  Linear.historySensitivityLinearInCoupling (linearResponse dataSet)

rowALiteralProducerFiniteConstantsLevel : ProofLevel
rowALiteralProducerFiniteConstantsLevel = machineChecked

rowALiteralProducerCanonicalGammaLevel : ProofLevel
rowALiteralProducerCanonicalGammaLevel = machineChecked

rowALiteralProducerHistorySlopeLevel : ProofLevel
rowALiteralProducerHistorySlopeLevel = machineChecked

literalRowAProducerSameObjectIdentificationLevel : ProofLevel
literalRowAProducerSameObjectIdentificationLevel = conditional
