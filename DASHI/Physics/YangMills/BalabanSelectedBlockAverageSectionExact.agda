module DASHI.Physics.YangMills.BalabanSelectedBlockAverageSectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
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
-- Construct an exact right inverse of the literal side-four P33 block-average
-- constraint.  Each requested Lie-coordinate/direction average is spread
-- uniformly over the 256 physical sites with coefficient 1/256.  The finite
-- sum then recovers the requested multiplier value exactly.  The unnormalised
-- constant lift is proved to be the exact finite adjoint under the literal row
-- and state dot products.  Consequently its normal operator is 256 I, with
-- exact two-sided inverse (1/256) I.  This is a constructive full-row-rank
-- certificate for the twelve-row average component before coupling to gauge
-- rows; no rank fact is inferred from dimensions alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (pair; cartesian)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Cell
import DASHI.Physics.YangMills.BalabanP33LiteralResidualKernelNumericalCalibrationExact as Count
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge
import DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact as Average

oneOverSiteCount : ℚ
oneOverSiteCount = + 1 / 256

siteCount : ℚ
siteCount = + 256 / 1

sumConstantAsLength :
  ∀ {A : Set} (values : List A) constant →
  Sums.sumRational values (λ _ → constant)
  ≡ Sums.natAsRational (length values) * constant
sumConstantAsLength [] constant =
  ℚRing.solve-∀ constant
sumConstantAsLength (_ ∷ values) constant
  rewrite sumConstantAsLength values constant =
  ℚRing.solve-∀ constant (Sums.natAsRational (length values))

natAsRationalSideFourSiteCountExact :
  Sums.natAsRational 256 ≡ siteCount
natAsRationalSideFourSiteCountExact = ℚRing.solve []

sideFourSumConstantExact : ∀ constant →
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ _ → constant)
  ≡ siteCount * constant
sideFourSumConstantExact constant =
  trans
    (sumConstantAsLength
      (Block.physicalBlockSites Path4.side4) constant)
    (cong (_* constant)
      (trans
        (cong Sums.natAsRational Count.periodicSide4SiteCount)
        natAsRationalSideFourSiteCountExact))

------------------------------------------------------------------------
-- Exact section and surjectivity.
------------------------------------------------------------------------

selectedBlockAverageSection :
  (Average.SelectedBlockAverageRow4 → ℚ) → KKT.StateVector
selectedBlockAverageSection multiplier
    (pair coordinate (pair axis site)) =
  oneOverSiteCount * multiplier (pair coordinate axis)

selectedBlockAverageSectionExact :
  ∀ multiplier row →
  Average.selectedBackgroundBlockAverageConstraintApply
    (selectedBlockAverageSection multiplier) row
  ≡ multiplier row
selectedBlockAverageSectionExact multiplier (pair coordinate axis) =
  trans
    (Average.selectedBackgroundBlockAverageConstraintMatrixApplyExact
      (selectedBlockAverageSection multiplier)
      (pair coordinate axis))
    (trans
      (sideFourSumConstantExact
        (oneOverSiteCount * multiplier (pair coordinate axis)))
      (ℚRing.solve-∀ (multiplier (pair coordinate axis))))

record SelectedBlockAveragePreimage
    (multiplier : Average.SelectedBlockAverageRow4 → ℚ) : Set where
  field
    state : KKT.StateVector
    mapsExactly : ∀ row →
      Average.selectedBackgroundBlockAverageConstraintApply state row
      ≡ multiplier row
open SelectedBlockAveragePreimage public

selectedBlockAverageConstraintSurjective :
  ∀ multiplier → SelectedBlockAveragePreimage multiplier
selectedBlockAverageConstraintSurjective multiplier = record
  { state = selectedBlockAverageSection multiplier
  ; mapsExactly = selectedBlockAverageSectionExact multiplier
  }

------------------------------------------------------------------------
-- Exact finite adjoint identity.
------------------------------------------------------------------------

selectedBlockAverageRowDot :
  (Average.SelectedBlockAverageRow4 → ℚ) →
  (Average.SelectedBlockAverageRow4 → ℚ) → ℚ
selectedBlockAverageRowDot left right =
  Sums.sumRational Average.selectedBlockAverageRows4
    (λ row → left row * right row)

selectedBlockAverageAdjointLift :
  (Average.SelectedBlockAverageRow4 → ℚ) → KKT.StateVector
selectedBlockAverageAdjointLift multiplier
    (pair coordinate (pair axis site)) =
  multiplier (pair coordinate axis)

selectedBlockAverageNestedPairing :
  KKT.StateVector →
  (Average.SelectedBlockAverageRow4 → ℚ) → ℚ
selectedBlockAverageNestedPairing state multiplier =
  Sums.sumRational Coordinates.lieCoordinates3
    (λ coordinate →
      Sums.sumRational Gauge.axes4
        (λ axis →
          Sums.sumRational (Block.physicalBlockSites Path4.side4)
            (λ site →
              state (pair coordinate (pair axis site))
              * multiplier (pair coordinate axis))))

selectedBlockAverageRowPairingExpand :
  ∀ state multiplier coordinate axis →
  Average.selectedBackgroundBlockAverageConstraintApply state
      (pair coordinate axis)
    * multiplier (pair coordinate axis)
  ≡ Sums.sumRational (Block.physicalBlockSites Path4.side4)
      (λ site →
        state (pair coordinate (pair axis site))
        * multiplier (pair coordinate axis))
selectedBlockAverageRowPairingExpand
    state multiplier coordinate axis =
  let
    rowValue = multiplier (pair coordinate axis)
    siteTerm = λ site → state (pair coordinate (pair axis site))
  in
  trans
    (cong (_* rowValue)
      (Average.selectedBackgroundBlockAverageConstraintMatrixApplyExact
        state (pair coordinate axis)))
    (trans
      (ℚRing.solve-∀
        (Sums.sumRational (Block.physicalBlockSites Path4.side4) siteTerm)
        rowValue)
      (trans
        (sym (Sums.sumRationalScale rowValue
          (Block.physicalBlockSites Path4.side4) siteTerm))
        (Sums.sumRationalCong
          (Block.physicalBlockSites Path4.side4)
          (λ site → rowValue * siteTerm site)
          (λ site → siteTerm site * rowValue)
          (λ site → ℚRing.solve-∀ rowValue (siteTerm site)))))

selectedBlockAverageRowPairingAsNested :
  ∀ state multiplier →
  selectedBlockAverageRowDot
    (Average.selectedBackgroundBlockAverageConstraintApply state)
    multiplier
  ≡ selectedBlockAverageNestedPairing state multiplier
selectedBlockAverageRowPairingAsNested state multiplier =
  trans
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3 Gauge.axes4
      (λ row →
        Average.selectedBackgroundBlockAverageConstraintApply state row
        * multiplier row))
    (Sums.sumRationalCong
      Coordinates.lieCoordinates3
      (λ coordinate →
        Sums.sumRational Gauge.axes4
          (λ axis →
            Average.selectedBackgroundBlockAverageConstraintApply state
              (pair coordinate axis)
            * multiplier (pair coordinate axis)))
      (λ coordinate →
        Sums.sumRational Gauge.axes4
          (λ axis →
            Sums.sumRational (Block.physicalBlockSites Path4.side4)
              (λ site →
                state (pair coordinate (pair axis site))
                * multiplier (pair coordinate axis))))
      (λ coordinate →
        Sums.sumRationalCong Gauge.axes4
          (λ axis →
            Average.selectedBackgroundBlockAverageConstraintApply state
              (pair coordinate axis)
            * multiplier (pair coordinate axis))
          (λ axis →
            Sums.sumRational (Block.physicalBlockSites Path4.side4)
              (λ site →
                state (pair coordinate (pair axis site))
                * multiplier (pair coordinate axis)))
          (λ axis →
            selectedBlockAverageRowPairingExpand
              state multiplier coordinate axis)))

selectedBlockAverageStatePairingAsNested :
  ∀ state multiplier →
  Coordinates.physicalCoordinateDot state
    (selectedBlockAverageAdjointLift multiplier)
  ≡ selectedBlockAverageNestedPairing state multiplier
selectedBlockAverageStatePairingAsNested state multiplier =
  trans
    (Fubini.sumCartesian
      Coordinates.lieCoordinates3 Cell.bondCells4
      (λ selected →
        state selected * selectedBlockAverageAdjointLift multiplier selected))
    (Sums.sumRationalCong
      Coordinates.lieCoordinates3
      (λ coordinate →
        Sums.sumRational Cell.bondCells4
          (λ cell →
            state (pair coordinate cell)
            * selectedBlockAverageAdjointLift multiplier
                (pair coordinate cell)))
      (λ coordinate →
        Sums.sumRational Gauge.axes4
          (λ axis →
            Sums.sumRational (Block.physicalBlockSites Path4.side4)
              (λ site →
                state (pair coordinate (pair axis site))
                * multiplier (pair coordinate axis))))
      (λ coordinate →
        Fubini.sumCartesian
          Gauge.axes4
          (Block.physicalBlockSites Path4.side4)
          (λ cell →
            state (pair coordinate cell)
            * selectedBlockAverageAdjointLift multiplier
                (pair coordinate cell))))

selectedBlockAverageAdjointExact :
  ∀ state multiplier →
  selectedBlockAverageRowDot
    (Average.selectedBackgroundBlockAverageConstraintApply state)
    multiplier
  ≡ Coordinates.physicalCoordinateDot state
      (selectedBlockAverageAdjointLift multiplier)
selectedBlockAverageAdjointExact state multiplier =
  trans
    (selectedBlockAverageRowPairingAsNested state multiplier)
    (sym (selectedBlockAverageStatePairingAsNested state multiplier))

------------------------------------------------------------------------
-- Exact normal operator and inverse.
------------------------------------------------------------------------

selectedBlockAverageNormalApply :
  (Average.SelectedBlockAverageRow4 → ℚ) →
  Average.SelectedBlockAverageRow4 → ℚ
selectedBlockAverageNormalApply multiplier =
  Average.selectedBackgroundBlockAverageConstraintApply
    (selectedBlockAverageAdjointLift multiplier)

selectedBlockAverageNormalExact :
  ∀ multiplier row →
  selectedBlockAverageNormalApply multiplier row
  ≡ siteCount * multiplier row
selectedBlockAverageNormalExact multiplier (pair coordinate axis) =
  trans
    (Average.selectedBackgroundBlockAverageConstraintMatrixApplyExact
      (selectedBlockAverageAdjointLift multiplier)
      (pair coordinate axis))
    (sideFourSumConstantExact (multiplier (pair coordinate axis)))

selectedBlockAverageNormalInverseApply :
  (Average.SelectedBlockAverageRow4 → ℚ) →
  Average.SelectedBlockAverageRow4 → ℚ
selectedBlockAverageNormalInverseApply multiplier row =
  oneOverSiteCount * multiplier row

selectedBlockAverageNormalInverseLeftExact :
  ∀ multiplier row →
  selectedBlockAverageNormalInverseApply
    (selectedBlockAverageNormalApply multiplier) row
  ≡ multiplier row
selectedBlockAverageNormalInverseLeftExact multiplier row =
  trans
    (cong (oneOverSiteCount *_) (selectedBlockAverageNormalExact multiplier row))
    (ℚRing.solve-∀ (multiplier row))

selectedBlockAverageNormalInverseRightExact :
  ∀ multiplier row →
  selectedBlockAverageNormalApply
    (selectedBlockAverageNormalInverseApply multiplier) row
  ≡ multiplier row
selectedBlockAverageNormalInverseRightExact multiplier row =
  trans
    (selectedBlockAverageNormalExact
      (selectedBlockAverageNormalInverseApply multiplier) row)
    (ℚRing.solve-∀ (multiplier row))

selectedBlockAverageSectionLevel : ProofLevel
selectedBlockAverageSectionLevel = machineChecked

selectedBlockAverageAdjointLevel : ProofLevel
selectedBlockAverageAdjointLevel = machineChecked

selectedBlockAverageNormalOperatorLevel : ProofLevel
selectedBlockAverageNormalOperatorLevel = machineChecked
