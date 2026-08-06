module DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct the literal finite coordinate carrier required by the physical
-- spectral realization.  A physical su(2)-valued positive-bond field on the
-- side-four torus is represented by three scalar bond fields.  Its coordinate
-- index is exactly
--
--   {x,y,z} x {positive side-four bonds}.
--
-- Encoding and decoding are pointwise inverse, the finite coordinate square
-- sum is exactly the three-component bond norm, and a finite kernel matrix is
-- converted into a physical field operator with an exact quadratic-form
-- identity.  No unspecified basis or dimension witness is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _*_; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  ( Product; pair; PositiveBond; cartesian )
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  ( sumRational; sumRationalCong )
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  ( sumCartesian )
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  ( sq )
import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact as Hodge
import DASHI.Physics.YangMills.BalabanP33LiteralBondCellIncidenceExact as Incidence

------------------------------------------------------------------------
-- Literal three-component physical field and coordinate carrier.
------------------------------------------------------------------------

data LieCoordinate3 : Set where
  coordinateX coordinateY coordinateZ : LieCoordinate3

lieCoordinates3 : List LieCoordinate3
lieCoordinates3 = coordinateX ∷ coordinateY ∷ coordinateZ ∷ []

PhysicalSU2BondField4 : Set
PhysicalSU2BondField4 = LieCoordinate3 → Hodge.RationalBondField4

PhysicalSU2Coordinate4 : Set
PhysicalSU2Coordinate4 = Product LieCoordinate3 Incidence.BondCell4

physicalSU2Coordinates4 : List PhysicalSU2Coordinate4
physicalSU2Coordinates4 =
  cartesian lieCoordinates3 Incidence.bondCells4

encodePhysicalSU2 :
  PhysicalSU2BondField4 → PhysicalSU2Coordinate4 → ℚ
encodePhysicalSU2 fld (pair coordinate cell) =
  Incidence.bondCellValue (fld coordinate) cell

decodePhysicalSU2 :
  (PhysicalSU2Coordinate4 → ℚ) → PhysicalSU2BondField4
decodePhysicalSU2 coordinates coordinate (pair site axis) =
  coordinates (pair coordinate (pair axis site))

decodeAfterEncodePointwise :
  ∀ fld coordinate bond →
  decodePhysicalSU2 (encodePhysicalSU2 fld) coordinate bond
  ≡ fld coordinate bond
decodeAfterEncodePointwise fld coordinate (pair site axis) = refl

encodeAfterDecodePointwise :
  ∀ coordinates physicalCoordinate →
  encodePhysicalSU2 (decodePhysicalSU2 coordinates) physicalCoordinate
  ≡ coordinates physicalCoordinate
encodeAfterDecodePointwise coordinates (pair coordinate (pair axis site)) = refl

------------------------------------------------------------------------
-- Exact coordinate norm preservation.
------------------------------------------------------------------------

physicalSU2BondNormSq : PhysicalSU2BondField4 → ℚ
physicalSU2BondNormSq fld =
  sumRational lieCoordinates3
    (λ coordinate → Hodge.bondNormSq (fld coordinate))

physicalSU2CoordinateNormSq :
  (PhysicalSU2Coordinate4 → ℚ) → ℚ
physicalSU2CoordinateNormSq coordinates =
  sumRational physicalSU2Coordinates4
    (λ physicalCoordinate → sq (coordinates physicalCoordinate))

encodePhysicalSU2NormSqExact : ∀ fld →
  physicalSU2CoordinateNormSq (encodePhysicalSU2 fld)
  ≡ physicalSU2BondNormSq fld
encodePhysicalSU2NormSqExact fld =
  trans
    (sumCartesian
      lieCoordinates3
      Incidence.bondCells4
      (λ physicalCoordinate →
        sq (encodePhysicalSU2 fld physicalCoordinate)))
    (sumRationalCong
      lieCoordinates3
      (λ coordinate →
        sumRational Incidence.bondCells4
          (λ cell → sq (Incidence.bondCellValue (fld coordinate) cell)))
      (λ coordinate → Hodge.bondNormSq (fld coordinate))
      (λ coordinate → Incidence.bondCellChargeSumExact (fld coordinate)))

------------------------------------------------------------------------
-- Literal finite matrices and their physical operator realization.
------------------------------------------------------------------------

PhysicalSU2Matrix4 : Set
PhysicalSU2Matrix4 =
  PhysicalSU2Coordinate4 → PhysicalSU2Coordinate4 → ℚ

physicalMatrixApply :
  PhysicalSU2Matrix4 →
  (PhysicalSU2Coordinate4 → ℚ) →
  PhysicalSU2Coordinate4 → ℚ
physicalMatrixApply matrix vector row =
  sumRational physicalSU2Coordinates4
    (λ column → matrix row column * vector column)

physicalCoordinateDot :
  (PhysicalSU2Coordinate4 → ℚ) →
  (PhysicalSU2Coordinate4 → ℚ) → ℚ
physicalCoordinateDot left right =
  sumRational physicalSU2Coordinates4
    (λ coordinate → left coordinate * right coordinate)

physicalMatrixQuadratic :
  PhysicalSU2Matrix4 →
  (PhysicalSU2Coordinate4 → ℚ) → ℚ
physicalMatrixQuadratic matrix vector =
  physicalCoordinateDot vector (physicalMatrixApply matrix vector)

physicalOperatorFromMatrix :
  PhysicalSU2Matrix4 →
  PhysicalSU2BondField4 → PhysicalSU2BondField4
physicalOperatorFromMatrix matrix fld =
  decodePhysicalSU2
    (physicalMatrixApply matrix (encodePhysicalSU2 fld))

encodePhysicalOperatorFromMatrixPointwise :
  ∀ matrix fld coordinate →
  encodePhysicalSU2 (physicalOperatorFromMatrix matrix fld) coordinate
  ≡ physicalMatrixApply matrix (encodePhysicalSU2 fld) coordinate
encodePhysicalOperatorFromMatrixPointwise matrix fld coordinate =
  encodeAfterDecodePointwise
    (physicalMatrixApply matrix (encodePhysicalSU2 fld)) coordinate

physicalSU2BondDot :
  PhysicalSU2BondField4 → PhysicalSU2BondField4 → ℚ
physicalSU2BondDot left right =
  physicalCoordinateDot
    (encodePhysicalSU2 left)
    (encodePhysicalSU2 right)

physicalMatrixQuadraticRealizationExact :
  ∀ matrix fld →
  physicalSU2BondDot fld (physicalOperatorFromMatrix matrix fld)
  ≡ physicalMatrixQuadratic matrix (encodePhysicalSU2 fld)
physicalMatrixQuadraticRealizationExact matrix fld =
  sumRationalCong
    physicalSU2Coordinates4
    (λ coordinate →
      encodePhysicalSU2 fld coordinate
      * encodePhysicalSU2
          (physicalOperatorFromMatrix matrix fld) coordinate)
    (λ coordinate →
      encodePhysicalSU2 fld coordinate
      * physicalMatrixApply matrix (encodePhysicalSU2 fld) coordinate)
    (λ coordinate →
      cong
        (encodePhysicalSU2 fld coordinate *_)
        (encodePhysicalOperatorFromMatrixPointwise matrix fld coordinate))

physicalSU2CoordinateRoundTripLevel : ProofLevel
physicalSU2CoordinateRoundTripLevel = machineChecked

physicalSU2CoordinateNormLevel : ProofLevel
physicalSU2CoordinateNormLevel = machineChecked

physicalSU2FiniteMatrixRealizationLevel : ProofLevel
physicalSU2FiniteMatrixRealizationLevel = machineChecked
