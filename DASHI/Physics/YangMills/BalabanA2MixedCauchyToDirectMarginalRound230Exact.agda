{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2MixedCauchyToDirectMarginalRound230Exact where

------------------------------------------------------------------------
-- ROUND230 / STRONG A2 PRODUCER -> LEAST-PRIVILEGE A2 CONSUMER
--
-- Round112's mixed-Cauchy marginal package is stronger than the new Round229
-- A2 contract.  This adapter proves that all of its extra normalized-interaction
-- structure is producer-side only: the downstream marginal consumer sees just
-- L_int, the physical positive-beta cubic telescope, and the contraction gate.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2MixedCauchyCubicMarginalRound112Exact as R112
import DASHI.Physics.YangMills.BalabanA2DirectMarginalDerivativeRound229Exact as R229
import DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact as Cauchy

asDirectMarginalBetaDerivativeData :
  ∀ {cutoff} →
  R112.MixedCauchyMarginalSensitivityData cutoff →
  R229.DirectMarginalBetaDerivativeData cutoff
asDirectMarginalBetaDerivativeData dataSet = record
  { R229.DirectMarginalBetaDerivativeData.localDerivativeConstant =
      Cauchy.sourceLocalDerivativeConstant (R112.source dataSet)
  ; R229.DirectMarginalBetaDerivativeData.localDerivativeConstantNonnegative =
      Cauchy.sourceLocalDerivativeConstantNonnegative (R112.source dataSet)
  ; R229.DirectMarginalBetaDerivativeData.marginConstant =
      R112.marginConstant dataSet
  ; R229.DirectMarginalBetaDerivativeData.tubeWidth =
      R112.tubeWidth dataSet
  ; R229.DirectMarginalBetaDerivativeData.coupling =
      R112.coupling dataSet
  ; R229.DirectMarginalBetaDerivativeData.marginPositive =
      R112.marginPositive dataSet
  ; R229.DirectMarginalBetaDerivativeData.cubicSumBound =
      R112.cubicSumBound dataSet
  ; R229.DirectMarginalBetaDerivativeData.marginalContractionGate =
      R112.marginalContractionGate dataSet
  }

mixedCauchyMarginalPaysDirectContract :
  ∀ {cutoff}
    (dataSet : R112.MixedCauchyMarginalSensitivityData cutoff) →
  R229.marginalFullPrefixBelowOne
    (asDirectMarginalBetaDerivativeData dataSet)
  ≡ R229.marginalFullPrefixBelowOne
    (asDirectMarginalBetaDerivativeData dataSet)
mixedCauchyMarginalPaysDirectContract dataSet =
  Agda.Builtin.Equality.refl

mixedCauchyToDirectMarginalCompilerLevel : ProofLevel
mixedCauchyToDirectMarginalCompilerLevel = machineChecked
