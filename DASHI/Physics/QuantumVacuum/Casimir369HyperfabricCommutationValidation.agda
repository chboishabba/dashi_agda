module DASHI.Physics.QuantumVacuum.Casimir369HyperfabricCommutationValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.Casimir369HyperfabricCommutationExact as Bridge
import DASHI.Physics.QuantumVacuum.ParallelPlatePhysicalModeClassExact as Class
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as Hyper

------------------------------------------------------------------------
-- RED-first regression surface for the Casimir <-> 369 hyperfabric weld.
------------------------------------------------------------------------

temAxisRegression :
  Bridge.modeClassAxis Class.TEM ≡ Hyper.axis₁
temAxisRegression = refl

teAxisRegression :
  ∀ n → Bridge.modeClassAxis (Class.TE+ n) ≡ Hyper.axis₂
teAxisRegression n = refl

tmAxisRegression :
  ∀ n → Bridge.modeClassAxis (Class.TM+ n) ≡ Hyper.axis₃
tmAxisRegression n = refl

modeClassCodecRegression :
  ∀ c → Bridge.decodeModeClass (Bridge.encodeModeClass c) ≡ c
modeClassCodecRegression = Bridge.decodeEncodeModeClass

axisCountTimes240Regression :
  Hyper.axisCarrierCount * 240 ≡ 720
axisCountTimes240Regression = Bridge.axisCountTimes240Is720

axisLiftCountTimes120Regression :
  Hyper.axisLiftCarrierCount * 120 ≡ 720
axisLiftCountTimes120Regression = Bridge.axisLiftCountTimes120Is720

operatorSheetTimes80Regression :
  Hyper.operatorSheetCount * 80 ≡ 720
operatorSheetTimes80Regression = Bridge.operatorSheetTimes80Is720

liftedOperatorSheetTimes40Regression :
  Hyper.liftedOperatorSheetCount * 40 ≡ 720
liftedOperatorSheetTimes40Regression = Bridge.liftedOperatorSheetTimes40Is720

axisCountTimes80Regression :
  Hyper.axisCarrierCount * 80 ≡ 240
axisCountTimes80Regression = Bridge.axisCountTimes80Is240

axisLiftCountTimes40Regression :
  Hyper.axisLiftCarrierCount * 40 ≡ 240
axisLiftCountTimes40Regression = Bridge.axisLiftCountTimes40Is240

naiveSixToThreeFixed120Regression :
  Hyper.axisCarrierCount * 120 ≡ 240 → ⊥
naiveSixToThreeFixed120Regression =
  Bridge.naiveSixToThreeFixed120CannotProduce240

operatorContractionRegression :
  ∀ output input →
  Bridge.contractOperatorSlot (output , input) ≡ output
operatorContractionRegression output input = refl

liftedOperatorContractionRegression :
  ∀ output input polarity →
  Bridge.contractLiftedOperatorPoint ((output , input) , polarity)
  ≡ (output , polarity)
liftedOperatorContractionRegression output input polarity = refl
