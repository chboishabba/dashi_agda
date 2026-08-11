module DASHI.Physics.YangMills.BalabanSelectedBackgroundBlockAverageConstraintMatrixExact where

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
-- Construct the literal zero-mode/block-average component consumed by the
-- side-four selected-background P33 coercivity theorem.  A row is one Lie
-- coordinate and one positive bond direction.  Its value is the exact finite
-- sum of that component over all physical sites.  The rectangular matrix is
-- not supplied by a caller: its (row,column) entry is this physical functional
-- evaluated on the literal state basis vector.  The finite-coordinate theorem
-- then proves matrix application equals the same physical block average.
--
-- This is the exact finite P33 block-average constraint.  The more elaborate
-- transported CMP98 averaging derivative remains a distinct multiscale
-- producer and is not silently identified with this zero-mode constraint.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; Axis4; cartesian)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeFirstExact as Gauge

SelectedBlockAverageRow4 : Set
SelectedBlockAverageRow4 = Product Coordinates.LieCoordinate3 Axis4

selectedBlockAverageRows4 : List SelectedBlockAverageRow4
selectedBlockAverageRows4 =
  cartesian Coordinates.lieCoordinates3 Gauge.axes4

selectedBlockAverageFunctional :
  SelectedBlockAverageRow4 → KKT.StateVector → ℚ
selectedBlockAverageFunctional (pair coordinate axis) vector =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site → vector (pair coordinate (pair axis site)))

sumZeroExact : ∀ {A : Set} (values : List A) →
  Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumZeroExact [] = refl
sumZeroExact (_ ∷ values)
  rewrite sumZeroExact values = ℚRing.solve []

selectedBlockAverageZeroExact : ∀ row →
  selectedBlockAverageFunctional row Linear.zeroVector ≡ 0ℚ
selectedBlockAverageZeroExact (pair coordinate axis) =
  sumZeroExact (Block.physicalBlockSites Path4.side4)

selectedBlockAverageAddExact : ∀ row left right →
  selectedBlockAverageFunctional row (Linear.addVector left right)
  ≡ selectedBlockAverageFunctional row left
    + selectedBlockAverageFunctional row right
selectedBlockAverageAddExact (pair coordinate axis) left right =
  Fubini.sumRationalAdd
    (Block.physicalBlockSites Path4.side4)
    (λ site → left (pair coordinate (pair axis site)))
    (λ site → right (pair coordinate (pair axis site)))

selectedBlockAverageScaleExact : ∀ row coefficient vector →
  selectedBlockAverageFunctional row
    (Linear.scaleVector coefficient vector)
  ≡ coefficient * selectedBlockAverageFunctional row vector
selectedBlockAverageScaleExact (pair coordinate axis) coefficient vector =
  Sums.sumRationalScale coefficient
    (Block.physicalBlockSites Path4.side4)
    (λ site → vector (pair coordinate (pair axis site)))

selectedBlockAveragePointwiseCong : ∀ row left right →
  (∀ selected → left selected ≡ right selected) →
  selectedBlockAverageFunctional row left
  ≡ selectedBlockAverageFunctional row right
selectedBlockAveragePointwiseCong (pair coordinate axis) left right equal =
  Sums.sumRationalCong
    (Block.physicalBlockSites Path4.side4)
    (λ site → left (pair coordinate (pair axis site)))
    (λ site → right (pair coordinate (pair axis site)))
    (λ site → equal (pair coordinate (pair axis site)))

selectedBlockAverageLinearFunctional :
  SelectedBlockAverageRow4 →
  Linear.FiniteLinearFunctional KKT.physicalStateCarrier
selectedBlockAverageLinearFunctional row = record
  { Linear.FiniteLinearFunctional.functional =
      selectedBlockAverageFunctional row
  ; Linear.FiniteLinearFunctional.zeroExact =
      selectedBlockAverageZeroExact row
  ; Linear.FiniteLinearFunctional.addExact =
      selectedBlockAverageAddExact row
  ; Linear.FiniteLinearFunctional.scaleExact =
      selectedBlockAverageScaleExact row
  ; Linear.FiniteLinearFunctional.pointwiseCong =
      selectedBlockAveragePointwiseCong row
  }

selectedBackgroundBlockAverageConstraintMatrix :
  Rect.RectangularMatrix SelectedBlockAverageRow4 KKT.State
selectedBackgroundBlockAverageConstraintMatrix row column =
  selectedBlockAverageFunctional row
    (Linear.basisVector KKT.physicalStateCarrier column)

selectedBackgroundBlockAverageConstraintMatrixExact :
  ∀ row column →
  selectedBackgroundBlockAverageConstraintMatrix row column
  ≡ selectedBlockAverageFunctional row
      (Linear.basisVector KKT.physicalStateCarrier column)
selectedBackgroundBlockAverageConstraintMatrixExact row column = refl

selectedBackgroundBlockAverageConstraintApply :
  KKT.StateVector → SelectedBlockAverageRow4 → ℚ
selectedBackgroundBlockAverageConstraintApply =
  Rect.applyRectangular
    KKT.physicalStateCarrier
    selectedBackgroundBlockAverageConstraintMatrix

selectedBackgroundBlockAverageConstraintMatrixApplyExact :
  ∀ vector row →
  selectedBackgroundBlockAverageConstraintApply vector row
  ≡ selectedBlockAverageFunctional row vector
selectedBackgroundBlockAverageConstraintMatrixApplyExact vector row =
  Linear.finiteLinearFunctionalCoordinateExpansion
    (selectedBlockAverageLinearFunctional row) vector

physicalSelectedBlockAverage :
  Coordinates.PhysicalSU2BondField4 → SelectedBlockAverageRow4 → ℚ
physicalSelectedBlockAverage field (pair coordinate axis) =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site → field coordinate (pair site axis))

selectedBackgroundBlockAverageConstraintPhysicalExact :
  ∀ vector row →
  selectedBackgroundBlockAverageConstraintApply vector row
  ≡ physicalSelectedBlockAverage
      (Coordinates.decodePhysicalSU2 vector) row
selectedBackgroundBlockAverageConstraintPhysicalExact
    vector (pair coordinate axis) =
  trans
    (selectedBackgroundBlockAverageConstraintMatrixApplyExact
      vector (pair coordinate axis))
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4)
      (λ site → vector (pair coordinate (pair axis site)))
      (λ site →
        Coordinates.decodePhysicalSU2 vector coordinate (pair site axis))
      (λ site → refl))

record SelectedBlockAverageKernel (vector : KKT.StateVector) : Set where
  field
    blockAverageZero : ∀ row →
      selectedBackgroundBlockAverageConstraintApply vector row ≡ 0ℚ
open SelectedBlockAverageKernel public

selectedBackgroundBlockAverageMatrixLevel : ProofLevel
selectedBackgroundBlockAverageMatrixLevel = machineChecked

selectedBackgroundBlockAveragePhysicalLevel : ProofLevel
selectedBackgroundBlockAveragePhysicalLevel = machineChecked
