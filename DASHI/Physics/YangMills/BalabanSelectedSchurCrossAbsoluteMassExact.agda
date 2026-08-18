module DASHI.Physics.YangMills.BalabanSelectedSchurCrossAbsoluteMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Balaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Quantify the defect-only cross matrix left by the exact 12-average / gauge
-- Schur decomposition.  On an average basis vector e_a, A^* e_a is literally
-- a 0/1 constant bond field.  The selected gauge defect D_A already satisfies
--
--   rowMass(D_A) <= 3/128.
--
-- Therefore every cross entry
--
--   C_A(r,a) = [D_A A^* e_a](r)
--
-- obeys |C_A(r,a)| <= 3/128.  The deliberately conservative cardinality
-- bounds then give
--
--   rowMass(C_A)    <= 12  * 3/128 = 9/32,
--   columnMass(C_A) <= 768 * 3/128 = 18.
--
-- These are already strong enough for the 1/256 finite-rank Schur correction;
-- no optimized cancellation is needed merely to establish Neumann smallness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact as AverageSection
import DASHI.Physics.YangMills.BalabanSelectedBlockAverageRowCarrierExact as AverageRows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as CombinedRows
import DASHI.Physics.YangMills.BalabanSelectedConstraintDimensionTowerExact as Dimensions
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeDefectAbsoluteMassExact as DefectMass
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteApplyExact as Apply

AverageRow : Set
AverageRow = Average.SelectedBlockAverageRow4

GaugeRow : Set
GaugeRow = Defect.GaugeRow

averageRows : List AverageRow
averageRows = Basis.elements AverageRows.selectedBlockAverageRowFiniteSelector

gaugeRows : List GaugeRow
gaugeRows = Basis.elements CombinedRows.selectedGaugeRowFiniteSelector

averageBasisMultiplier : AverageRow → AverageRow → ℚ
averageBasisMultiplier target = AverageRows.selectedBlockAverageRowDelta target

averageBasisState : AverageRow → Coordinates.PhysicalSU2Coordinate4 → ℚ
averageBasisState target =
  AverageSection.selectedBlockAverageAdjointLift (averageBasisMultiplier target)

averageBasisStateUnitBound : ∀ target column →
  ∣ averageBasisState target column ∣ ≤ 1ℚ
averageBasisStateUnitBound target (pair coordinate (pair axis site))
  with Basis.decide AverageRows.selectedBlockAverageRowFiniteSelector
      (pair coordinate axis) target
... | yes _ = ℚP.≤-refl
... | no _ = ℚP.0≤1

selectedSchurCrossMatrix :
  Physical.RationalSU2Background4 → GaugeRow → AverageRow → ℚ
selectedSchurCrossMatrix background gaugeRow averageRow =
  Apply.rectApply Coordinates.physicalSU2Coordinates4
    (Defect.gaugeDefectMatrix background)
    (averageBasisState averageRow) gaugeRow

selectedSchurCrossIsDefectOnAverageBasis :
  ∀ background gaugeRow averageRow →
  selectedSchurCrossMatrix background gaugeRow averageRow
  ≡ DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeOperatorDecompositionExact.gaugeDefectForwardApply
      background (averageBasisState averageRow) gaugeRow
selectedSchurCrossIsDefectOnAverageBasis background gaugeRow averageRow = refl

selectedSchurCrossEntryAbsoluteBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ gaugeRow averageRow →
  ∣ selectedSchurCrossMatrix background gaugeRow averageRow ∣
  ≤ DefectMass.defectRowMassBound
selectedSchurCrossEntryAbsoluteBound background radius gaugeRow averageRow =
  ℚP.≤-trans
    (Apply.rectApplyAbsoluteUnitBound
      Coordinates.physicalSU2Coordinates4
      (Defect.gaugeDefectMatrix background)
      (averageBasisState averageRow)
      (averageBasisStateUnitBound averageRow)
      gaugeRow)
    (DefectMass.selectedGaugeDefectAbsoluteRowMassBound
      background radius gaugeRow)

crossRowMassBound crossColumnMassBound : ℚ
crossRowMassBound = + 9 / 32
crossColumnMassBound = + 18 / 1

averageRowsCountExact : length averageRows ≡ 12
averageRowsCountExact = Dimensions.selectedBlockAverageRowCount

gaugeRowsArePhysicalGaugeRows : gaugeRows ≡ FlatGauge.flatGaugeCoordinates
gaugeRowsArePhysicalGaugeRows = refl

gaugeRowsCountExact : length gaugeRows ≡ 768
gaugeRowsCountExact =
  trans (cong length gaugeRowsArePhysicalGaugeRows)
    Dimensions.selectedGaugeRowCount

sumCrossEntryBoundOverAverageRows :
  Sums.sumRational averageRows (λ _ → DefectMass.defectRowMassBound)
  ≡ crossRowMassBound
sumCrossEntryBoundOverAverageRows =
  trans
    (AverageSection.sumConstantAsLength
      averageRows DefectMass.defectRowMassBound)
    (trans
      (cong (λ count → count * DefectMass.defectRowMassBound)
        (cong Sums.natAsRational averageRowsCountExact))
      (ℚRing.solve []))

sumCrossEntryBoundOverGaugeRows :
  Sums.sumRational gaugeRows (λ _ → DefectMass.defectRowMassBound)
  ≡ crossColumnMassBound
sumCrossEntryBoundOverGaugeRows =
  trans
    (AverageSection.sumConstantAsLength
      gaugeRows DefectMass.defectRowMassBound)
    (trans
      (cong (λ count → count * DefectMass.defectRowMassBound)
        (cong Sums.natAsRational gaugeRowsCountExact))
      (ℚRing.solve []))

selectedSchurCrossAbsoluteRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ gaugeRow →
  Mass.absoluteRectRowMass averageRows
    (selectedSchurCrossMatrix background) gaugeRow
  ≤ crossRowMassBound
selectedSchurCrossAbsoluteRowMassBound background radius gaugeRow =
  let
    pointwise =
      DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact.sumPointwiseBelow
        averageRows
        (λ averageRow → ∣ selectedSchurCrossMatrix background gaugeRow averageRow ∣)
        (λ _ → DefectMass.defectRowMassBound)
        (selectedSchurCrossEntryAbsoluteBound background radius gaugeRow)
  in
  subst
    (λ upper →
      Mass.absoluteRectRowMass averageRows
        (selectedSchurCrossMatrix background) gaugeRow ≤ upper)
    sumCrossEntryBoundOverAverageRows pointwise

selectedSchurCrossAbsoluteColumnMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ averageRow →
  Mass.absoluteRectColumnMass gaugeRows
    (selectedSchurCrossMatrix background) averageRow
  ≤ crossColumnMassBound
selectedSchurCrossAbsoluteColumnMassBound background radius averageRow =
  let
    pointwise =
      DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact.sumPointwiseBelow
        gaugeRows
        (λ gaugeRow → ∣ selectedSchurCrossMatrix background gaugeRow averageRow ∣)
        (λ _ → DefectMass.defectRowMassBound)
        (λ gaugeRow →
          selectedSchurCrossEntryAbsoluteBound
            background radius gaugeRow averageRow)
  in
  subst
    (λ upper →
      Mass.absoluteRectColumnMass gaugeRows
        (selectedSchurCrossMatrix background) averageRow ≤ upper)
    sumCrossEntryBoundOverGaugeRows pointwise

selectedSchurCrossEntryLevel : ProofLevel
selectedSchurCrossEntryLevel = machineChecked

selectedSchurCrossAbsoluteMassLevel : ProofLevel
selectedSchurCrossAbsoluteMassLevel = machineChecked
