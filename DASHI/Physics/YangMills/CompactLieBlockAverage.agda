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

    blockAverageDefinition : ∀ block input →
      blockAverage block input
      ≡ reconstruct (transportedLogAverage block input)

    transportedLogCovariant : ∀ block gauge input →
      transportedLogAverage block (gaugeAction gauge input)
      ≡ algebraGaugeAction (restrictGauge gauge)
          (transportedLogAverage block input)

    reconstructionCovariant : ∀ coarseGauge algebra →
      reconstruct (algebraGaugeAction coarseGauge algebra)
      ≡ coarseGaugeAction coarseGauge (reconstruct algebra)

open CovariantBlockAverageData public

blockAverageEquivariant :
  ∀ {Field Gauge Block CoarseField CoarseGauge Algebra : Set} →
  (bundle : CovariantBlockAverageData
    Field Gauge Block CoarseField CoarseGauge Algebra) →
  ∀ block gauge input →
  blockAverage bundle block (gaugeAction bundle gauge input)
  ≡
  coarseGaugeAction bundle (restrictGauge bundle gauge)
    (blockAverage bundle block input)
blockAverageEquivariant bundle block gauge input =
  trans
    (blockAverageDefinition bundle block (gaugeAction bundle gauge input))
    (trans
      (congReconstruct
        (transportedLogCovariant bundle block gauge input))
      (trans
        (reconstructionCovariant bundle
          (restrictGauge bundle gauge)
          (transportedLogAverage bundle block input))
        (congCoarse symDefinition)))
  where
    congReconstruct : ∀ {x y} → x ≡ y → reconstruct bundle x ≡ reconstruct bundle y
    congReconstruct refl = refl

    congCoarse : ∀ {x y} → x ≡ y →
      coarseGaugeAction bundle (restrictGauge bundle gauge) x
      ≡ coarseGaugeAction bundle (restrictGauge bundle gauge) y
    congCoarse refl = refl

    symDefinition :
      reconstruct bundle (transportedLogAverage bundle block input)
      ≡ blockAverage bundle block input
    symDefinition = sym (blockAverageDefinition bundle block input)
