module DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
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
-- Remove the accidental side-four specialization from the physical su(2)
-- finite-coordinate carrier.  For every finite side L, a tangent gauge field
-- is exactly three scalar coordinates on every positive bond,
--
--        {x,y,z} x ({sites of L^4} x {four positive axes}).
--
-- Encoding/decoding are pointwise inverse and the coordinate-square sum is
-- definitionally the three-component bond norm.  This supplies the literal
-- 3*4*L^4 state carrier needed to rebuild the reduced normal/KKT machinery at
-- the source-admissible L=13 scale rather than reusing the old 3072-coordinate
-- side-four object.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using (sumCartesian)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)

------------------------------------------------------------------------
-- Literal Lie and bond coordinates.
------------------------------------------------------------------------

data LieCoordinate3 : Set where
  coordinateX coordinateY coordinateZ : LieCoordinate3

lieCoordinates3 : List LieCoordinate3
lieCoordinates3 = coordinateX ∷ coordinateY ∷ coordinateZ ∷ []

PhysicalBondCell : Nat → Set
PhysicalBondCell L = Product Axis4 (PhysicalBlockL L)

physicalBondCells : (L : Nat) → List (PhysicalBondCell L)
physicalBondCells L =
  cartesian (allCyclicIndices four) (physicalBlockSites L)

PhysicalSU2BondField : Nat → Set
PhysicalSU2BondField L = LieCoordinate3 → BondField L ℚ

PhysicalSU2Coordinate : Nat → Set
PhysicalSU2Coordinate L = Product LieCoordinate3 (PhysicalBondCell L)

physicalSU2Coordinates : (L : Nat) → List (PhysicalSU2Coordinate L)
physicalSU2Coordinates L = cartesian lieCoordinates3 (physicalBondCells L)

bondCellValue : ∀ {L} → BondField L ℚ → PhysicalBondCell L → ℚ
bondCellValue field (pair axis site) = field (pair site axis)

encodePhysicalSU2 :
  ∀ {L} → PhysicalSU2BondField L → PhysicalSU2Coordinate L → ℚ
encodePhysicalSU2 field (pair coordinate cell) =
  bondCellValue (field coordinate) cell

decodePhysicalSU2 :
  ∀ {L} → (PhysicalSU2Coordinate L → ℚ) → PhysicalSU2BondField L
decodePhysicalSU2 coordinates coordinate (pair site axis) =
  coordinates (pair coordinate (pair axis site))

decodeAfterEncodePointwise :
  ∀ {L} (field : PhysicalSU2BondField L) coordinate bond →
  decodePhysicalSU2 (encodePhysicalSU2 field) coordinate bond
  ≡ field coordinate bond
decodeAfterEncodePointwise field coordinate (pair site axis) = refl

encodeAfterDecodePointwise :
  ∀ {L} coordinates (physicalCoordinate : PhysicalSU2Coordinate L) →
  encodePhysicalSU2 (decodePhysicalSU2 coordinates) physicalCoordinate
  ≡ coordinates physicalCoordinate
encodeAfterDecodePointwise coordinates (pair coordinate (pair axis site)) = refl

------------------------------------------------------------------------
-- Exact arbitrary-side norm realization.
------------------------------------------------------------------------

bondNormSq : ∀ {L} → BondField L ℚ → ℚ
bondNormSq {L} field =
  sumRational (physicalBondCells L)
    (λ cell → sq (bondCellValue field cell))

physicalSU2BondNormSq : ∀ {L} → PhysicalSU2BondField L → ℚ
physicalSU2BondNormSq field =
  sumRational lieCoordinates3
    (λ coordinate → bondNormSq (field coordinate))

physicalSU2CoordinateNormSq :
  ∀ {L} → (PhysicalSU2Coordinate L → ℚ) → ℚ
physicalSU2CoordinateNormSq {L} coordinates =
  sumRational (physicalSU2Coordinates L)
    (λ coordinate → sq (coordinates coordinate))

encodePhysicalSU2NormSqExact :
  ∀ {L} (field : PhysicalSU2BondField L) →
  physicalSU2CoordinateNormSq (encodePhysicalSU2 field)
  ≡ physicalSU2BondNormSq field
encodePhysicalSU2NormSqExact {L} field =
  trans
    (sumCartesian lieCoordinates3 (physicalBondCells L)
      (λ coordinate → sq (encodePhysicalSU2 field coordinate)))
    refl

------------------------------------------------------------------------
-- Finite matrices and physical operator realization at arbitrary side.
------------------------------------------------------------------------

PhysicalSU2Matrix : Nat → Set
PhysicalSU2Matrix L =
  PhysicalSU2Coordinate L → PhysicalSU2Coordinate L → ℚ

physicalMatrixApply :
  ∀ {L} → PhysicalSU2Matrix L →
  (PhysicalSU2Coordinate L → ℚ) → PhysicalSU2Coordinate L → ℚ
physicalMatrixApply {L} matrix vector row =
  sumRational (physicalSU2Coordinates L)
    (λ column → matrix row column * vector column)

physicalCoordinateDot :
  ∀ {L} → (PhysicalSU2Coordinate L → ℚ) →
  (PhysicalSU2Coordinate L → ℚ) → ℚ
physicalCoordinateDot {L} left right =
  sumRational (physicalSU2Coordinates L)
    (λ coordinate → left coordinate * right coordinate)

physicalMatrixQuadratic :
  ∀ {L} → PhysicalSU2Matrix L →
  (PhysicalSU2Coordinate L → ℚ) → ℚ
physicalMatrixQuadratic matrix vector =
  physicalCoordinateDot vector (physicalMatrixApply matrix vector)

physicalOperatorFromMatrix :
  ∀ {L} → PhysicalSU2Matrix L →
  PhysicalSU2BondField L → PhysicalSU2BondField L
physicalOperatorFromMatrix matrix field =
  decodePhysicalSU2 (physicalMatrixApply matrix (encodePhysicalSU2 field))

physicalSU2CoordinateRoundTripLevel : ProofLevel
physicalSU2CoordinateRoundTripLevel = machineChecked

physicalSU2CoordinateNormLevel : ProofLevel
physicalSU2CoordinateNormLevel = machineChecked

physicalSU2FiniteMatrixRealizationLevel : ProofLevel
physicalSU2FiniteMatrixRealizationLevel = machineChecked
