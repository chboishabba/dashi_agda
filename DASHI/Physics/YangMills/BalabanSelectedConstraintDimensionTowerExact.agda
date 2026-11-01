module DASHI.Physics.YangMills.BalabanSelectedConstraintDimensionTowerExact where

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
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Make the selected multiplier dimension explicit before any rank reduction.
-- The literal P33 zero-mode block-average carrier has 3*4 = 12 rows; the
-- covariant gauge carrier has 3*4^4 = 768 rows; and their tagged sum has 780
-- rows.  No reduction in dimension is accepted without a separately supplied
-- redundancy theorem.  The module also proves symmetry of the full literal
-- Gram matrix directly from the finite sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List.Base using (map; _++_; length)
import Data.List.Properties as ListP
open import Data.Rational.Base using (_*_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact as Count
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Calibration
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCombinedConstraintMatrixExact as Combined

selectedConstraintRows4 : List Combined.SelectedConstraintRow4
selectedConstraintRows4 =
  map Combined.averageConstraintRow Average.selectedBlockAverageRows4
  ++ map Combined.gaugeConstraintRow FlatGauge.flatGaugeCoordinates

selectedBlockAverageRowCount :
  length Average.selectedBlockAverageRows4 ≡ 12
selectedBlockAverageRowCount
  rewrite Count.lengthCartesian
    Coordinates.lieCoordinates3 Gauge.axes4 = refl

selectedGaugeRowCount :
  length FlatGauge.flatGaugeCoordinates ≡ 768
selectedGaugeRowCount
  rewrite Count.lengthCartesian
    Coordinates.lieCoordinates3
    (Block.physicalBlockSites Path4.side4)
  | Calibration.periodicSide4SiteCount = refl

selectedCombinedConstraintRowCount :
  length selectedConstraintRows4 ≡ 780
selectedCombinedConstraintRowCount
  rewrite ListP.length-++
    (map Combined.averageConstraintRow Average.selectedBlockAverageRows4)
  | ListP.length-map
      Combined.averageConstraintRow Average.selectedBlockAverageRows4
  | ListP.length-map
      Combined.gaugeConstraintRow FlatGauge.flatGaugeCoordinates
  | selectedBlockAverageRowCount
  | selectedGaugeRowCount = refl

record SelectedConstraintRawDimensionLedger : Set where
  field
    averageRows : Nat
    gaugeRows : Nat
    totalRows : Nat
    averageRowsExact : averageRows ≡ 12
    gaugeRowsExact : gaugeRows ≡ 768
    totalRowsExact : totalRows ≡ 780
    enumeratorExact : length selectedConstraintRows4 ≡ totalRows
open SelectedConstraintRawDimensionLedger public

selectedConstraintRawDimensionLedger :
  SelectedConstraintRawDimensionLedger
selectedConstraintRawDimensionLedger = record
  { averageRows = 12
  ; gaugeRows = 768
  ; totalRows = 780
  ; averageRowsExact = refl
  ; gaugeRowsExact = refl
  ; totalRowsExact = refl
  ; enumeratorExact = selectedCombinedConstraintRowCount
  }

selectedBackgroundConstraintGramSymmetric :
  ∀ background left right →
  Combined.selectedBackgroundConstraintGram background left right
  ≡ Combined.selectedBackgroundConstraintGram background right left
selectedBackgroundConstraintGramSymmetric background left right =
  Sums.sumRationalCong
    (Matrix.coordinates KKT.physicalStateCarrier)
    (λ column →
      Combined.selectedBackgroundLinearizedConstraintMatrix
        background left column
      * Combined.selectedBackgroundLinearizedConstraintMatrix
        background right column)
    (λ column →
      Combined.selectedBackgroundLinearizedConstraintMatrix
        background right column
      * Combined.selectedBackgroundLinearizedConstraintMatrix
        background left column)
    (λ column → ℚP.*-comm
      (Combined.selectedBackgroundLinearizedConstraintMatrix
        background left column)
      (Combined.selectedBackgroundLinearizedConstraintMatrix
        background right column))

record SelectedReducedCarrierDimensionClaim : Set₁ where
  field
    reducedDimension : Nat
    redundancyDimension : Nat
    dimensionBalance :
      reducedDimension + redundancyDimension ≡ 780
open SelectedReducedCarrierDimensionClaim public

-- A future reduced carrier must pay for every deleted row through this exact
-- balance.  No canonical value is fabricated here because the physical
-- redundancy projection and rank-stability theorem remain the next producer.

selectedConstraintDimensionLevel : ProofLevel
selectedConstraintDimensionLevel = machineChecked

selectedConstraintReducedDimensionLevel : ProofLevel
selectedConstraintReducedDimensionLevel = conditional
