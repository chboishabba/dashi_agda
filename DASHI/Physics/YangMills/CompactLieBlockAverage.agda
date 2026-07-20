module DASHI.Physics.YangMills.CompactLieBlockAverage where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Structural covariance theorem for transported-log block averages.
-- The analytic chart, path choice, and Lipschitz estimates remain separate;
-- once transport and reconstruction are equivariant, the block map is too.
------------------------------------------------------------------------

record CovariantBlockAverageData
    (Field Gauge Block CoarseField CoarseGauge Algebra : Set) : Set₁ where
  field
    gaugeAction : Gauge → Field → Field
    restrictGauge : Gauge → CoarseGauge
    transportedLogAverage : Block → Field → Algebra
    reconstruct : Algebra → CoarseField
    blockAverage : Block → Field → CoarseField
    coarseGaugeAction : CoarseGauge → CoarseField → CoarseField
    algebraGaugeAction : CoarseGauge → Algebra → Algebra

    blockAverageDefinition : ∀ block field →
      blockAverage block field
      ≡ reconstruct (transportedLogAverage block field)

    transportedLogCovariant : ∀ block gauge field →
      transportedLogAverage block (gaugeAction gauge field)
      ≡ algebraGaugeAction (restrictGauge gauge)
          (transportedLogAverage block field)

    reconstructionCovariant : ∀ coarseGauge algebra →
      reconstruct (algebraGaugeAction coarseGauge algebra)
      ≡ coarseGaugeAction coarseGauge (reconstruct algebra)

open CovariantBlockAverageData public

blockAverageEquivariant :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set} →
  (data : CovariantBlockAverageData
    Field Gauge Block CoarseField CoarseGauge Algebra) →
  ∀ block gauge field →
  blockAverage data block (gaugeAction data gauge field)
  ≡
  coarseGaugeAction data (restrictGauge data gauge)
    (blockAverage data block field)
blockAverageEquivariant data block gauge field =
  trans
    (blockAverageDefinition data block (gaugeAction data gauge field))
    (trans
      (congReconstruct
        (transportedLogCovariant data block gauge field))
      (trans
        (reconstructionCovariant data
          (restrictGauge data gauge)
          (transportedLogAverage data block field))
        (congCoarse
          (symDefinition data block field))))
  where
    congReconstruct : ∀ {x y} → x ≡ y → reconstruct data x ≡ reconstruct data y
    congReconstruct refl = refl

    congCoarse : ∀ {x y} → x ≡ y →
      coarseGaugeAction data (restrictGauge data gauge) x
      ≡ coarseGaugeAction data (restrictGauge data gauge) y
    congCoarse refl = refl

    symDefinition :
      ∀ data block field →
      reconstruct data (transportedLogAverage data block field)
      ≡ blockAverage data block field
    symDefinition data block field =
      sym (blockAverageDefinition data block field)
