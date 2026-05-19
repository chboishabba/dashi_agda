module FascisticContractionBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)

import Contraction as C
import FascisticSystem as F
import Ultrametric as UMetric

StabilizesFrom : F.S → Set
StabilizesFrom s =
  Σ ℕ (λ n → F.Ktotal (F.iterate n s) ≡ F.iterate n s)

attractorFromStabilization :
  (s : F.S) →
  StabilizesFrom s →
  F.Attractor
attractorFromStabilization s (n , fixed) =
  F.iterate n s , fixed

record FixedPointExistenceByDescent : Set where
  constructor fixedPointExistenceByDescent
  field
    seed : F.S
    stabilizes : StabilizesFrom seed

attractorFromDescent :
  FixedPointExistenceByDescent →
  F.Attractor
attractorFromDescent descent =
  attractorFromStabilization
    (FixedPointExistenceByDescent.seed descent)
    (FixedPointExistenceByDescent.stabilizes descent)

record FascisticStrictContractionBridge : Set₁ where
  constructor fascisticStrictContractionBridge
  field
    ultrametric : UMetric.Ultrametric F.S
    strictContraction : C.StrictContraction ultrametric F.Ktotal

attractorFromStrictContraction :
  FascisticStrictContractionBridge →
  F.Attractor
attractorFromStrictContraction bridge =
  C.StrictContraction.fp strict ,
  C.StrictContraction.fixed strict
  where
    strict : C.StrictContraction
      (FascisticStrictContractionBridge.ultrametric bridge)
      F.Ktotal
    strict = FascisticStrictContractionBridge.strictContraction bridge

record FascisticMetricDescentGap : Set₂ where
  constructor fascisticMetricDescentGap
  field
    cardinalityOnly : ℕ
    missingUltrametric : Set₁
    missingStrictContraction :
      (U : UMetric.Ultrametric F.S) →
      Set
    missingConstructiveStabilization :
      F.S →
      Set

currentFascisticMetricDescentGap : FascisticMetricDescentGap
currentFascisticMetricDescentGap =
  fascisticMetricDescentGap
    F.finiteS
    (UMetric.Ultrametric F.S)
    (λ U → C.StrictContraction U F.Ktotal)
    StabilizesFrom
