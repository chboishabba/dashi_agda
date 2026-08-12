module DASHI.Physics.YangMills.BalabanPhysicalBlockAverageConstraintMatrixExact where

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
-- DASHI CONTRIBUTION
--
-- Arbitrary-side finite-matrix realization of the physical zero-mode/block
-- average.  The old selected module was hard-wired to side four through its
-- 3072-coordinate KKT state.  Here both the state carrier and the physical
-- site fold are parameterized by L.  Consequently the L=13 migration has a
-- literal 342732-column block-average matrix on the same state object as the
-- new source-scale Poincare theorem.
--
-- This remains the linear zero-mode constraint, not an identification with the
-- full transported nonlinear CMP98/CMP109 derivative; that same-object
-- Fréchet identification is handled separately.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact as Coordinates

SelectedBlockAverageRow : Set
SelectedBlockAverageRow = Product Physical.LieCoordinate3 Axis4

selectedBlockAverageRows : List SelectedBlockAverageRow
selectedBlockAverageRows =
  cartesian Physical.lieCoordinates3 (allCyclicIndices four)

State : Nat → Set
State L = Physical.PhysicalSU2Coordinate L

StateVector : Nat → Set
StateVector L = State L → ℚ

physicalStateCarrier : ∀ L → Matrix.FiniteRationalCoordinates (State L)
physicalStateCarrier = Coordinates.physicalFiniteRationalCoordinates

selectedBlockAverageFunctional :
  ∀ {L} → SelectedBlockAverageRow → StateVector L → ℚ
selectedBlockAverageFunctional {L} (pair coordinate axis) vector =
  Sums.sumRational (Block.physicalBlockSites L)
    (λ site → vector (pair coordinate (pair axis site)))

sumZeroExact : ∀ {A : Set} (values : List A) →
  Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumZeroExact [] = refl
sumZeroExact (_ ∷ values)
  rewrite sumZeroExact values = ℚRing.solve []

selectedBlockAverageZeroExact :
  ∀ {L} row →
  selectedBlockAverageFunctional {L} row Linear.zeroVector ≡ 0ℚ
selectedBlockAverageZeroExact {L} (pair coordinate axis) =
  sumZeroExact (Block.physicalBlockSites L)

selectedBlockAverageAddExact :
  ∀ {L} row left right →
  selectedBlockAverageFunctional {L} row (Linear.addVector left right)
  ≡ selectedBlockAverageFunctional row left
    + selectedBlockAverageFunctional row right
selectedBlockAverageAddExact {L} (pair coordinate axis) left right =
  Fubini.sumRationalAdd
    (Block.physicalBlockSites L)
    (λ site → left (pair coordinate (pair axis site)))
    (λ site → right (pair coordinate (pair axis site)))

selectedBlockAverageScaleExact :
  ∀ {L} row coefficient vector →
  selectedBlockAverageFunctional {L} row
    (Linear.scaleVector coefficient vector)
  ≡ coefficient * selectedBlockAverageFunctional row vector
selectedBlockAverageScaleExact {L} (pair coordinate axis) coefficient vector =
  Sums.sumRationalScale coefficient
    (Block.physicalBlockSites L)
    (λ site → vector (pair coordinate (pair axis site)))

selectedBlockAveragePointwiseCong :
  ∀ {L} row left right →
  (∀ selected → left selected ≡ right selected) →
  selectedBlockAverageFunctional {L} row left
  ≡ selectedBlockAverageFunctional row right
selectedBlockAveragePointwiseCong {L} (pair coordinate axis) left right equal =
  Sums.sumRationalCong
    (Block.physicalBlockSites L)
    (λ site → left (pair coordinate (pair axis site)))
    (λ site → right (pair coordinate (pair axis site)))
    (λ site → equal (pair coordinate (pair axis site)))

selectedBlockAverageLinearFunctional :
  ∀ {L} → SelectedBlockAverageRow →
  Linear.FiniteLinearFunctional (physicalStateCarrier L)
selectedBlockAverageLinearFunctional {L} row = record
  { Linear.FiniteLinearFunctional.functional =
      selectedBlockAverageFunctional {L} row
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
  ∀ {L} → Rect.RectangularMatrix SelectedBlockAverageRow (State L)
selectedBackgroundBlockAverageConstraintMatrix {L} row column =
  selectedBlockAverageFunctional {L} row
    (Linear.basisVector (physicalStateCarrier L) column)

selectedBackgroundBlockAverageConstraintApply :
  ∀ {L} → StateVector L → SelectedBlockAverageRow → ℚ
selectedBackgroundBlockAverageConstraintApply {L} =
  Rect.applyRectangular
    (physicalStateCarrier L)
    selectedBackgroundBlockAverageConstraintMatrix

selectedBackgroundBlockAverageConstraintMatrixApplyExact :
  ∀ {L} vector row →
  selectedBackgroundBlockAverageConstraintApply {L} vector row
  ≡ selectedBlockAverageFunctional row vector
selectedBackgroundBlockAverageConstraintMatrixApplyExact {L} vector row =
  Linear.finiteLinearFunctionalCoordinateExpansion
    (selectedBlockAverageLinearFunctional {L} row) vector

physicalSelectedBlockAverage :
  ∀ {L} → Physical.PhysicalSU2BondField L → SelectedBlockAverageRow → ℚ
physicalSelectedBlockAverage {L} bondField (pair coordinate axis) =
  Sums.sumRational (Block.physicalBlockSites L)
    (λ site → bondField coordinate (pair site axis))

selectedBackgroundBlockAverageConstraintPhysicalExact :
  ∀ {L} vector row →
  selectedBackgroundBlockAverageConstraintApply {L} vector row
  ≡ physicalSelectedBlockAverage
      (Physical.decodePhysicalSU2 vector) row
selectedBackgroundBlockAverageConstraintPhysicalExact
    {L} vector (pair coordinate axis) =
  trans
    (selectedBackgroundBlockAverageConstraintMatrixApplyExact
      vector (pair coordinate axis))
    refl

physicalBlockAverageConstraintArbitrarySideLevel : ProofLevel
physicalBlockAverageConstraintArbitrarySideLevel = machineChecked

physicalBlockAverageConstraintMatrixArbitrarySideLevel : ProofLevel
physicalBlockAverageConstraintMatrixArbitrarySideLevel = machineChecked
