module DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintSchurCrossDefectOnlyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- The exact 12-average / reduced-gauge block decomposition leaves the Schur
-- cross term
--
--   A G_A^* gamma.
--
-- The flat piece vanishes exactly: a periodic gradient has zero block average.
-- Since
--
--   G_A^* gamma = G_0^* gamma + D_A^* gamma,
--
-- the complete average/gauge cross map is therefore not an O(1) coupling but
-- the literal background defect
--
--   A G_A^* gamma = A D_A^* gamma.
--
-- This is the structural fact needed before estimating the finite-rank Schur
-- correction.  It avoids paying for the large flat gauge gradient in the
-- 12-dimensional average coupling and makes the correction quadratic in the
-- selected-background defect once paired with its transpose.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as GaugeReduced
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedCombinedMultiplierSplitExact as Split
import DASHI.Physics.YangMills.BalabanSelectedReducedCombinedConstraintFloorExact as Floor
import DASHI.Physics.YangMills.BalabanSelectedCombinedStableMultiplierFloorExact as Stable
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintGramBlockSchurExact as BlockSchur

ReducedMultiplier : Set
ReducedMultiplier = Split.SelectedReducedCombinedMultiplier

averageGaugeDefectCross :
  ∀ {background : DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact.RationalSU2Background4} →
  ReducedMultiplier → Average.SelectedBlockAverageRow4 → ℚ
averageGaugeDefectCross {background} selected =
  Average.selectedBackgroundBlockAverageConstraintApply
    (Defect.gaugeAdjointDefectApply background (Split.gaugeMultiplier selected))

averageGaugeCrossDefectOnly :
  ∀ background selected row →
  BlockSchur.averageGaugeCross background selected row
  ≡ averageGaugeDefectCross {background} selected row
averageGaugeCrossDefectOnly background selected row =
  let
    gauge = Split.gaugeMultiplier selected
    flat = FlatAdjoint.actualFlatGaugeAdjoint gauge
    defect = Defect.gaugeAdjointDefectApply background gauge
    full = Floor.backgroundGaugeAdjoint background selected

    fullSplitsPointwise : ∀ coordinate →
      full coordinate ≡ Rect.vectorAdd flat defect coordinate
    fullSplitsPointwise coordinate =
      GaugeReduced.backgroundGaugeAdjointSplits background gauge coordinate

    moveToSplit :
      Average.selectedBackgroundBlockAverageConstraintApply full row
      ≡ Average.selectedBackgroundBlockAverageConstraintApply
          (Rect.vectorAdd flat defect) row
    moveToSplit =
      Rect.applyRectangularVectorCong
        StateCarrier.physicalStateCarrier
        Average.selectedBackgroundBlockAverageConstraintMatrix
        fullSplitsPointwise row

    splitApply :
      Average.selectedBackgroundBlockAverageConstraintApply
          (Rect.vectorAdd flat defect) row
      ≡ Average.selectedBackgroundBlockAverageConstraintApply flat row
        + Average.selectedBackgroundBlockAverageConstraintApply defect row
    splitApply =
      Rect.applyRectangularAddExact
        StateCarrier.physicalStateCarrier
        Average.selectedBackgroundBlockAverageConstraintMatrix
        flat defect row

    flatZero :
      Average.selectedBackgroundBlockAverageConstraintApply flat row ≡ 0ℚ
    flatZero = Stable.flatGaugeAverageConstraintZero gauge row
  in
  trans moveToSplit
    (trans splitApply
      (trans
        (cong
          (_+ Average.selectedBackgroundBlockAverageConstraintApply defect row)
          flatZero)
        (ℚRing.solve-∀
          (Average.selectedBackgroundBlockAverageConstraintApply defect row))))

selectedAverageGaugeSchurCrossDefectOnlyLevel : ProofLevel
selectedAverageGaugeSchurCrossDefectOnlyLevel = machineChecked

-- The transpose cross map is the same finite Gram block viewed from the gauge
-- side.  A subsequent theorem should use Gram symmetry to avoid re-estimating
-- it independently, then combine both with the exact 1/256 average inverse.
selectedGaugeAverageSchurCrossTransposeLevel : ProofLevel
selectedGaugeAverageSchurCrossTransposeLevel = conditional
