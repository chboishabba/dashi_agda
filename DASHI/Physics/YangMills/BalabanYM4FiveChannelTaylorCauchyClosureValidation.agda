{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4FiveChannelTaylorCauchyClosureValidation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4FiveChannelCauchyQuotientMajorantExact as Cauchy
import DASHI.Physics.YangMills.BalabanYM4FiveChannelTaylorCauchyClosureExact as Closure
import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact as A1

rawCoefficientEvaluationIsProofBearing :
  Cauchy.rawCauchyCoefficientEvaluationLevel ≡ machineChecked
rawCoefficientEvaluationIsProofBearing = refl

finiteGeometricMajorantIsProofBearing :
  Cauchy.finiteCauchyCoefficientGeometricMajorantLevel ≡ machineChecked
finiteGeometricMajorantIsProofBearing = refl

completedQuotientLowerIsProofBearing :
  Cauchy.completedCauchyQuotientLowerLevel ≡ machineChecked
completedQuotientLowerIsProofBearing = refl

fiveChannelCompositionIsProofBearing :
  Closure.fiveChannelTaylorCauchyClosureLevel ≡ machineChecked
fiveChannelCompositionIsProofBearing = refl

activeA1NoLongerChargesDirectQuotientMajorant :
  A1.cmp109FiveChannelDirectQuotientMajorantCompilerLevel ≡ machineChecked
activeA1NoLongerChargesDirectQuotientMajorant = refl

literalCauchyCoefficientEstimateRemainsPhysical :
  A1.cmp109LiteralFiveChannelCauchyCoefficientEstimateLevel ≡ conditional
literalCauchyCoefficientEstimateRemainsPhysical = refl

literalSeriesRepresentationRemainsPhysical :
  A1.cmp109LiteralFiveChannelSeriesRepresentationLevel ≡ conditional
literalSeriesRepresentationRemainsPhysical = refl

literalSeriesConvergenceRemainsPhysical :
  A1.cmp109LiteralFiveChannelSeriesConvergenceLevel ≡ conditional
literalSeriesConvergenceRemainsPhysical = refl
