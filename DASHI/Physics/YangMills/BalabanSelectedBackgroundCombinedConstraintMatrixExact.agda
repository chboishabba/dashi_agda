module DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numerique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Put the literal P33 block-average rows and the literal selected-background
-- gauge rows on one tagged multiplier carrier.  Both row families act on the
-- same 3072-coordinate perturbation vector.  The combined matrix is defined
-- by cases, its action reduces exactly to each physical component, and its
-- Gram matrix is the literal L_A L_A*.  Block identities and a generic
-- pointwise-disjointness theorem close finite range without assuming an
-- independently supplied compatible block matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as Gauge
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramFiniteRangeExact as GaugeGram
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintGluingExact as Gluing

------------------------------------------------------------------------
-- One tagged multiplier carrier.
------------------------------------------------------------------------

data SelectedConstraintRow4 : Set where
  averageConstraintRow : Average.SelectedBlockAverageRow4 → SelectedConstraintRow4
  gaugeConstraintRow : FlatGauge.GaugeCoordinate4 → SelectedConstraintRow4

selectedBackgroundLinearizedConstraintMatrix :
  Physical.RationalSU2Background4 →
  Rect.RectangularMatrix SelectedConstraintRow4 KKT.State
selectedBackgroundLinearizedConstraintMatrix background
    (averageConstraintRow row) column =
  Average.selectedBackgroundBlockAverageConstraintMatrix row column
selectedBackgroundLinearizedConstraintMatrix background
    (gaugeConstraintRow row) column =
  Gauge.selectedBackgroundGaugeConstraintMatrix background row column

selectedBackgroundLinearizedConstraintMatrixExact :
  ∀ background row column →
  selectedBackgroundLinearizedConstraintMatrix background row column
  ≡
  (case row of λ where
    (averageConstraintRow averageRow) →
      Average.selectedBackgroundBlockAverageConstraintMatrix averageRow column
    (gaugeConstraintRow gaugeRow) →
      Gauge.selectedBackgroundGaugeConstraintMatrix background gaugeRow column)
selectedBackgroundLinearizedConstraintMatrixExact
  background (averageConstraintRow row) column = refl
selectedBackgroundLinearizedConstraintMatrixExact
  background (gaugeConstraintRow row) column = refl

selectedBackgroundCombinedConstraintApply :
  Physical.RationalSU2Background4 →
  KKT.StateVector → SelectedConstraintRow4 → ℚ
selectedBackgroundCombinedConstraintApply background =
  Rect.applyRectangular KKT.physicalStateCarrier
    (selectedBackgroundLinearizedConstraintMatrix background)

selectedBackgroundCombinedConstraintApplyExact :
  ∀ background vector row →
  selectedBackgroundCombinedConstraintApply background vector row
  ≡
  (case row of λ where
    (averageConstraintRow averageRow) →
      Average.physicalSelectedBlockAverage
        (PhysicalField vector) averageRow
    (gaugeConstraintRow gaugeRow) →
      GaugePhysical background vector gaugeRow)
  where
    PhysicalField : KKT.StateVector →
      DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact.PhysicalSU2BondField4
    PhysicalField =
      DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact.decodePhysicalSU2

    GaugePhysical :
      Physical.RationalSU2Background4 → KKT.StateVector →
      FlatGauge.GaugeCoordinate4 → ℚ
    GaugePhysical selectedBackground selectedVector =
      DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact.backgroundGaugeFirst
        selectedBackground (PhysicalField selectedVector)
selectedBackgroundCombinedConstraintApplyExact
  background vector (averageConstraintRow row) =
  Average.selectedBackgroundBlockAverageConstraintPhysicalExact vector row
selectedBackgroundCombinedConstraintApplyExact
  background vector (gaugeConstraintRow row) =
  Gauge.selectedBackgroundGaugeConstraintMatrixApplyExact background vector row

------------------------------------------------------------------------
-- Same-source product form.  This is the exact bridge to the generic gluing
-- architecture already used by Round 41.
------------------------------------------------------------------------

selectedConstraintCharts :
  Physical.RationalSU2Background4 →
  Gluing.SelectedConstraintCharts
selectedConstraintCharts background = record
  { Gluing.SelectedConstraintCharts.Perturbation = KKT.StateVector
  ; Gluing.SelectedConstraintCharts.AverageRows =
      Average.SelectedBlockAverageRow4 → ℚ
  ; Gluing.SelectedConstraintCharts.GaugeRows =
      FlatGauge.GaugeCoordinate4 → ℚ
  ; Gluing.SelectedConstraintCharts.averageConstraint =
      Average.selectedBackgroundBlockAverageConstraintApply
  ; Gluing.SelectedConstraintCharts.gaugeConstraint =
      λ vector →
        Rect.applyRectangular KKT.physicalStateCarrier
          (Gauge.selectedBackgroundGaugeConstraintMatrix background) vector
  }

selectedBackgroundCombinedConstraint :
  Physical.RationalSU2Background4 → KKT.StateVector →
  (Average.SelectedBlockAverageRow4 → ℚ)
    DASHI.Physics.Common.SameSourceGluedProducerExact.×
  (FlatGauge.GaugeCoordinate4 → ℚ)
selectedBackgroundCombinedConstraint background =
  Gluing.selectedBackgroundCombinedConstraint
    (selectedConstraintCharts background)

selectedBackgroundCombinedConstraintCommutesWithProjections :
  ∀ background →
  (∀ vector →
    DASHI.Physics.Common.SameSourceGluedProducerExact.fst
      (selectedBackgroundCombinedConstraint background vector)
    ≡ Average.selectedBackgroundBlockAverageConstraintApply vector)
  DASHI.Physics.Common.SameSourceGluedProducerExact.×
  (∀ vector →
    DASHI.Physics.Common.SameSourceGluedProducerExact.snd
      (selectedBackgroundCombinedConstraint background vector)
    ≡ Rect.applyRectangular KKT.physicalStateCarrier
        (Gauge.selectedBackgroundGaugeConstraintMatrix background) vector)
selectedBackgroundCombinedConstraintCommutesWithProjections background =
  Gluing.selectedBackgroundCombinedConstraintCommutesWithProjections
    (selectedConstraintCharts background)

selectedBackgroundCombinedConstraintUnique :
  ∀ background
    (candidate : KKT.StateVector →
      (Average.SelectedBlockAverageRow4 → ℚ)
        DASHI.Physics.Common.SameSourceGluedProducerExact.×
      (FlatGauge.GaugeCoordinate4 → ℚ))
    vector →
  DASHI.Physics.Common.SameSourceGluedProducerExact.fst (candidate vector)
    ≡ Average.selectedBackgroundBlockAverageConstraintApply vector →
  DASHI.Physics.Common.SameSourceGluedProducerExact.snd (candidate vector)
    ≡ Rect.applyRectangular KKT.physicalStateCarrier
        (Gauge.selectedBackgroundGaugeConstraintMatrix background) vector →
  candidate vector ≡ selectedBackgroundCombinedConstraint background vector
selectedBackgroundCombinedConstraintUnique background =
  Gluing.selectedBackgroundCombinedConstraintUnique
    (selectedConstraintCharts background)

------------------------------------------------------------------------
-- Literal full Gram matrix.
------------------------------------------------------------------------

selectedBackgroundConstraintGram :
  Physical.RationalSU2Background4 →
  Rect.RectangularMatrix SelectedConstraintRow4 SelectedConstraintRow4
selectedBackgroundConstraintGram background =
  Rect.composeRectangular KKT.physicalStateCarrier
    (selectedBackgroundLinearizedConstraintMatrix background)
    (Rect.transposeRectangular
      (selectedBackgroundLinearizedConstraintMatrix background))

selectedBackgroundConstraintGramExact :
  ∀ background left right →
  selectedBackgroundConstraintGram background left right
  ≡ Sums.sumRational (Matrix.coordinates KKT.physicalStateCarrier)
      (λ column →
        selectedBackgroundLinearizedConstraintMatrix
          background left column
        * selectedBackgroundLinearizedConstraintMatrix
          background right column)
selectedBackgroundConstraintGramExact background left right = refl

selectedBackgroundConstraintGramGaugeBlockExact :
  ∀ background left right →
  selectedBackgroundConstraintGram background
    (gaugeConstraintRow left) (gaugeConstraintRow right)
  ≡ GaugeGram.selectedBackgroundGaugeGram background left right
selectedBackgroundConstraintGramGaugeBlockExact background left right = refl

selectedBackgroundConstraintGramAverageBlockExact :
  ∀ background left right →
  selectedBackgroundConstraintGram background
    (averageConstraintRow left) (averageConstraintRow right)
  ≡ Rect.composeRectangular KKT.physicalStateCarrier
      Average.selectedBackgroundBlockAverageConstraintMatrix
      (Rect.transposeRectangular
        Average.selectedBackgroundBlockAverageConstraintMatrix)
      left right
selectedBackgroundConstraintGramAverageBlockExact background left right = refl

record ConstraintRowsPointwiseDisjoint
    (background : Physical.RationalSU2Background4)
    (left right : SelectedConstraintRow4) : Set where
  field
    productZero : ∀ column →
      selectedBackgroundLinearizedConstraintMatrix background left column
      * selectedBackgroundLinearizedConstraintMatrix background right column
      ≡ 0ℚ
open ConstraintRowsPointwiseDisjoint public

selectedBackgroundConstraintGramOutsideRangeZero :
  ∀ background left right →
  ConstraintRowsPointwiseDisjoint background left right →
  selectedBackgroundConstraintGram background left right ≡ 0ℚ
selectedBackgroundConstraintGramOutsideRangeZero
    background left right separation =
  trans
    (Sums.sumRationalCong
      (Matrix.coordinates KKT.physicalStateCarrier)
      (λ column →
        selectedBackgroundLinearizedConstraintMatrix background left column
        * selectedBackgroundLinearizedConstraintMatrix background right column)
      (λ _ → 0ℚ)
      (productZero separation))
    (Fubini.sumRationalZero
      (Matrix.coordinates KKT.physicalStateCarrier))

selectedCombinedConstraintMatrixLevel : ProofLevel
selectedCombinedConstraintMatrixLevel = machineChecked

selectedCombinedConstraintGramLevel : ProofLevel
selectedCombinedConstraintGramLevel = machineChecked
