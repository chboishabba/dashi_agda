module DASHI.Physics.YangMills.BalabanSU2ConstraintTangentSpace where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

record ConstraintTangentVector
  {f g c : Level}
  (Fine : Set f) (Gauge : Set g) (Coarse : Set c)
  (divergence : Fine → Gauge)
  (average : Fine → Coarse)
  (gaugeZero : Gauge)
  (coarseZero : Coarse) : Set (f ⊔ g ⊔ c) where
  constructor tangentVector
  field
    vector : Fine
    gaugeTangent : divergence vector ≡ gaugeZero
    averageTangent : average vector ≡ coarseZero
open ConstraintTangentVector public

projectKernelToTangent :
  ∀ {f g c}
  {Fine : Set f} {Gauge : Set g} {Coarse : Set c}
  (divergence : Fine → Gauge)
  (average : Fine → Coarse)
  (gaugeZero : Gauge)
  (coarseZero : Coarse)
  (gaugeProjector : Fine → Fine) →
  (∀ fine → divergence (gaugeProjector fine) ≡ gaugeZero) →
  (∀ fine → average (gaugeProjector fine) ≡ average fine) →
  ∀ fine → average fine ≡ coarseZero →
  ConstraintTangentVector
    Fine Gauge Coarse divergence average gaugeZero coarseZero
projectKernelToTangent
  divergence average gaugeZero coarseZero gaugeProjector
  gaugeFixed averagePreserved fine fineInKernel =
  tangentVector
    (gaugeProjector fine)
    (gaugeFixed fine)
    (trans (averagePreserved fine) fineInKernel)

-- The tangent constraint is stable under a map once both linearized constraints
-- are preserved.  This is the exact closure condition used by a nonlinear
-- critical-point iteration in kernel coordinates.
tangentMap :
  ∀ {f g c}
  {Fine : Set f} {Gauge : Set g} {Coarse : Set c}
  (divergence : Fine → Gauge)
  (average : Fine → Coarse)
  (gaugeZero : Gauge)
  (coarseZero : Coarse)
  (step : Fine → Fine) →
  (∀ fine → divergence fine ≡ gaugeZero → divergence (step fine) ≡ gaugeZero) →
  (∀ fine → average fine ≡ coarseZero → average (step fine) ≡ coarseZero) →
  ConstraintTangentVector Fine Gauge Coarse divergence average gaugeZero coarseZero →
  ConstraintTangentVector Fine Gauge Coarse divergence average gaugeZero coarseZero
tangentMap
  divergence average gaugeZero coarseZero step
  preservesGauge preservesAverage tangent =
  tangentVector
    (step (vector tangent))
    (preservesGauge (vector tangent) (gaugeTangent tangent))
    (preservesAverage (vector tangent) (averageTangent tangent))
