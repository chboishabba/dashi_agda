module DASHI.Physics.YangMills.BalabanSU2GaugeFixedConstraintSpace where

open import Agda.Builtin.Equality using (_≡_)

record GaugeFixedConstraintSpace (Fine Gauge Coarse : Set) : Set₁ where
  field
    divergence : Fine → Gauge
    average : Fine → Coarse
    gaugeZero : Gauge
    coarseZero : Coarse
    gaugeProjector : Fine → Fine
    gaugeFixed : ∀ fine → divergence (gaugeProjector fine) ≡ gaugeZero
    averagePreserved : ∀ fine → average (gaugeProjector fine) ≡ average fine

open GaugeFixedConstraintSpace public
