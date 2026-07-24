module DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian

------------------------------------------------------------------------
-- Exact quadratic-form ownership for the literal finite gauge-fixed Hessian.
--
-- BalabanSU2GaugeFixedHessian already defines the operator
--
--   H = H_W + div* div + Q* Q.
--
-- This module adds the three inner products and the two adjoint laws required
-- to identify the last two operator terms with squared norms.  The equalities
-- below are derived from those adjoint laws; positivity is not substituted for
-- the stronger operator identity.
------------------------------------------------------------------------

record GaugeFixedHessianQuadraticData
    {f g c s : Level}
    (Fine : Set f) (Gauge : Set g) (Coarse : Set c) (Scalar : Set s)
    : Set (lsuc (f ⊔ g ⊔ c ⊔ s)) where
  field
    hessianData : GaugeFixedHessianData Fine Gauge Coarse

    innerFine : Fine → Fine → Scalar
    innerGauge : Gauge → Gauge → Scalar
    innerCoarse : Coarse → Coarse → Scalar
    addScalar : Scalar → Scalar → Scalar

    scalarZero : Scalar
    gaugeZero : Gauge
    coarseZero : Coarse

    innerFineAddRight : ∀ fine left right →
      innerFine fine (addFine hessianData left right)
      ≡ addScalar (innerFine fine left) (innerFine fine right)

    divergenceAdjoint : ∀ fine gauge →
      innerFine fine (divergenceStar hessianData gauge)
      ≡ innerGauge (divergence hessianData fine) gauge

    averageAdjoint : ∀ fine coarse →
      innerFine fine (averageStar hessianData coarse)
      ≡ innerCoarse (average hessianData fine) coarse

    innerGaugeZero : innerGauge gaugeZero gaugeZero ≡ scalarZero
    innerCoarseZero : innerCoarse coarseZero coarseZero ≡ scalarZero

    Nonnegative : Scalar → Set s
    gaugeNormNonnegative : ∀ gauge → Nonnegative (innerGauge gauge gauge)
    coarseNormNonnegative : ∀ coarse → Nonnegative (innerCoarse coarse coarse)

open GaugeFixedHessianQuadraticData public

gaugeFixingQuadraticForm :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s} →
  GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar →
  Fine → Scalar
gaugeFixingQuadraticForm dataSet fine =
  innerFine dataSet fine (gaugePenalty (hessianData dataSet) fine)

gaugeFixingNormSq :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s} →
  GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar →
  Fine → Scalar
gaugeFixingNormSq dataSet fine =
  innerGauge dataSet
    (divergence (hessianData dataSet) fine)
    (divergence (hessianData dataSet) fine)

physicalGaugeFixingQuadraticFormExact :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s}
    (dataSet : GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar)
    fine →
  gaugeFixingQuadraticForm dataSet fine
  ≡ gaugeFixingNormSq dataSet fine
physicalGaugeFixingQuadraticFormExact dataSet fine =
  divergenceAdjoint dataSet fine (divergence (hessianData dataSet) fine)

blockPenaltyQuadraticForm :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s} →
  GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar →
  Fine → Scalar
blockPenaltyQuadraticForm dataSet fine =
  innerFine dataSet fine (averagePenalty (hessianData dataSet) fine)

blockAverageNormSq :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s} →
  GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar →
  Fine → Scalar
blockAverageNormSq dataSet fine =
  innerCoarse dataSet
    (average (hessianData dataSet) fine)
    (average (hessianData dataSet) fine)

physicalBlockPenaltyQuadraticFormExact :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s}
    (dataSet : GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar)
    fine →
  blockPenaltyQuadraticForm dataSet fine
  ≡ blockAverageNormSq dataSet fine
physicalBlockPenaltyQuadraticFormExact dataSet fine =
  averageAdjoint dataSet fine (average (hessianData dataSet) fine)

physicalGaugeFixingQuadraticFormNonnegative :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s}
    (dataSet : GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar)
    fine →
  Nonnegative dataSet (gaugeFixingQuadraticForm dataSet fine)
physicalGaugeFixingQuadraticFormNonnegative dataSet fine
  rewrite physicalGaugeFixingQuadraticFormExact dataSet fine =
  gaugeNormNonnegative dataSet (divergence (hessianData dataSet) fine)

physicalBlockPenaltyQuadraticFormNonnegative :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s}
    (dataSet : GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar)
    fine →
  Nonnegative dataSet (blockPenaltyQuadraticForm dataSet fine)
physicalBlockPenaltyQuadraticFormNonnegative dataSet fine
  rewrite physicalBlockPenaltyQuadraticFormExact dataSet fine =
  coarseNormNonnegative dataSet (average (hessianData dataSet) fine)

blockConstrainedImpliesPenaltyZero :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s}
    (dataSet : GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar)
    fine →
  average (hessianData dataSet) fine ≡ coarseZero dataSet →
  blockAverageNormSq dataSet fine ≡ scalarZero dataSet
blockConstrainedImpliesPenaltyZero dataSet fine averageZero =
  trans
    (cong₂ (innerCoarse dataSet) averageZero averageZero)
    (innerCoarseZero dataSet)

gaugeConstrainedImpliesGaugePenaltyZero :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s}
    (dataSet : GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar)
    fine →
  divergence (hessianData dataSet) fine ≡ gaugeZero dataSet →
  gaugeFixingNormSq dataSet fine ≡ scalarZero dataSet
gaugeConstrainedImpliesGaugePenaltyZero dataSet fine divergenceZero =
  trans
    (cong₂ (innerGauge dataSet) divergenceZero divergenceZero)
    (innerGaugeZero dataSet)

wilsonHessianQuadraticForm :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s} →
  GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar →
  Fine → Scalar
wilsonHessianQuadraticForm dataSet fine =
  innerFine dataSet fine (wilsonHessian (hessianData dataSet) fine)

gaugeFixedHessianQuadraticForm :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s} →
  GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar →
  Fine → Scalar
gaugeFixedHessianQuadraticForm dataSet fine =
  innerFine dataSet fine (gaugeFixedHessian (hessianData dataSet) fine)

gaugeFixedHessianQuadraticFormExact :
  ∀ {f g c s}
    {Fine : Set f} {Gauge : Set g} {Coarse : Set c} {Scalar : Set s}
    (dataSet : GaugeFixedHessianQuadraticData Fine Gauge Coarse Scalar)
    fine →
  gaugeFixedHessianQuadraticForm dataSet fine
  ≡ addScalar dataSet (wilsonHessianQuadraticForm dataSet fine)
      (addScalar dataSet
        (gaugeFixingNormSq dataSet fine)
        (blockAverageNormSq dataSet fine))
gaugeFixedHessianQuadraticFormExact dataSet fine =
  trans
    (innerFineAddRight dataSet fine
      (wilsonHessian (hessianData dataSet) fine)
      (addFine (hessianData dataSet)
        (gaugePenalty (hessianData dataSet) fine)
        (averagePenalty (hessianData dataSet) fine)))
    (cong₂ (addScalar dataSet) refl
      (trans
        (innerFineAddRight dataSet fine
          (gaugePenalty (hessianData dataSet) fine)
          (averagePenalty (hessianData dataSet) fine))
        (cong₂ (addScalar dataSet)
          (physicalGaugeFixingQuadraticFormExact dataSet fine)
          (physicalBlockPenaltyQuadraticFormExact dataSet fine))))

physicalGaugeFixingQuadraticFormExactLevel : ProofLevel
physicalGaugeFixingQuadraticFormExactLevel = machineChecked

physicalBlockPenaltyQuadraticFormExactLevel : ProofLevel
physicalBlockPenaltyQuadraticFormExactLevel = machineChecked

gaugeFixedHessianQuadraticFormExactLevel : ProofLevel
gaugeFixedHessianQuadraticFormExactLevel = machineChecked
