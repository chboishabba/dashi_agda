module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintGluingExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- The block-average and gauge-fixing constraint charts are required to be
-- views of one perturbation carrier.  Their combined operator is therefore
-- the product pairing forced by that common source.  The projection and
-- pointwise uniqueness theorems rule out assembly from independently chosen
-- row families.
--
-- This module supplies the exact gluing architecture.  It does not fabricate
-- the still-missing physical selected-background block-average derivative.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; _⊔_)
open import DASHI.Physics.Common.SameSourceGluedProducerExact

record SelectedConstraintCharts
    {p a g : Level} : Set (p ⊔ a ⊔ g) where
  field
    Perturbation : Set p
    AverageRows : Set a
    GaugeRows : Set g
    averageConstraint : Perturbation → AverageRows
    gaugeConstraint : Perturbation → GaugeRows
open SelectedConstraintCharts public

selectedBackgroundCombinedConstraint :
  ∀ {p a g} →
  (charts : SelectedConstraintCharts {p} {a} {g}) →
  Perturbation charts → AverageRows charts × GaugeRows charts
selectedBackgroundCombinedConstraint charts =
  sameSourceCombined
    (averageConstraint charts)
    (gaugeConstraint charts)

selectedBackgroundCombinedConstraintGluedProducer :
  ∀ {p a g} →
  (charts : SelectedConstraintCharts {p} {a} {g}) →
  SameSourceGluedProducer
    (Perturbation charts)
    (AverageRows charts)
    (GaugeRows charts)
    (averageConstraint charts)
    (gaugeConstraint charts)
selectedBackgroundCombinedConstraintGluedProducer charts =
  literalSameSourceGluedProducer
    (averageConstraint charts)
    (gaugeConstraint charts)

selectedBackgroundCombinedConstraintAverageExact :
  ∀ {p a g}
    (charts : SelectedConstraintCharts {p} {a} {g})
    (variation : Perturbation charts) →
  fst (selectedBackgroundCombinedConstraint charts variation)
    ≡ averageConstraint charts variation
selectedBackgroundCombinedConstraintAverageExact charts =
  sameSourceCombinedLeftExact
    (averageConstraint charts)
    (gaugeConstraint charts)

selectedBackgroundCombinedConstraintGaugeExact :
  ∀ {p a g}
    (charts : SelectedConstraintCharts {p} {a} {g})
    (variation : Perturbation charts) →
  snd (selectedBackgroundCombinedConstraint charts variation)
    ≡ gaugeConstraint charts variation
selectedBackgroundCombinedConstraintGaugeExact charts =
  sameSourceCombinedRightExact
    (averageConstraint charts)
    (gaugeConstraint charts)

selectedBackgroundCombinedConstraintCommutesWithProjections :
  ∀ {p a g}
    (charts : SelectedConstraintCharts {p} {a} {g}) →
  (∀ variation →
      fst (selectedBackgroundCombinedConstraint charts variation)
        ≡ averageConstraint charts variation)
  ×
  (∀ variation →
      snd (selectedBackgroundCombinedConstraint charts variation)
        ≡ gaugeConstraint charts variation)
selectedBackgroundCombinedConstraintCommutesWithProjections charts =
  selectedBackgroundCombinedConstraintAverageExact charts ,
  selectedBackgroundCombinedConstraintGaugeExact charts

selectedBackgroundCombinedConstraintUnique :
  ∀ {p a g}
    (charts : SelectedConstraintCharts {p} {a} {g})
    (candidate : Perturbation charts →
      AverageRows charts × GaugeRows charts)
    (variation : Perturbation charts) →
  fst (candidate variation) ≡ averageConstraint charts variation →
  snd (candidate variation) ≡ gaugeConstraint charts variation →
  candidate variation
    ≡ selectedBackgroundCombinedConstraint charts variation
selectedBackgroundCombinedConstraintUnique charts =
  sameSourceCombinedUniquePointwise
    (averageConstraint charts)
    (gaugeConstraint charts)

record SelectedConstraintOperatorLayer
    {p a g : Level}
    (charts : SelectedConstraintCharts {p} {a} {g}) :
    Set (p ⊔ a ⊔ g) where
  field
    combined : Perturbation charts →
      AverageRows charts × GaugeRows charts
    averageProjectionExact :
      ∀ variation →
      fst (combined variation) ≡ averageConstraint charts variation
    gaugeProjectionExact :
      ∀ variation →
      snd (combined variation) ≡ gaugeConstraint charts variation
open SelectedConstraintOperatorLayer public

literalSelectedConstraintOperatorLayer :
  ∀ {p a g} →
  (charts : SelectedConstraintCharts {p} {a} {g}) →
  SelectedConstraintOperatorLayer charts
literalSelectedConstraintOperatorLayer charts = record
  { combined = selectedBackgroundCombinedConstraint charts
  ; averageProjectionExact =
      selectedBackgroundCombinedConstraintAverageExact charts
  ; gaugeProjectionExact =
      selectedBackgroundCombinedConstraintGaugeExact charts
  }

selectedConstraintOperatorLayerForced :
  ∀ {p a g}
    {charts : SelectedConstraintCharts {p} {a} {g}} →
  (layer : SelectedConstraintOperatorLayer charts) →
  (variation : Perturbation charts) →
  combined layer variation
    ≡ selectedBackgroundCombinedConstraint charts variation
selectedConstraintOperatorLayerForced {charts = charts} layer variation =
  selectedBackgroundCombinedConstraintUnique
    charts
    (combined layer)
    variation
    (averageProjectionExact layer variation)
    (gaugeProjectionExact layer variation)
