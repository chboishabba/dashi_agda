module DASHI.Physics.YangMills.BalabanP33PhysicalProjectorCompositionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Volker Bach, Thomas Chen, Juerg Froehlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- DASHI CONTRIBUTION
--
-- Give the exact finite composition law for diagonal physical-coordinate
-- projectors.  Boolean intersection is the order-independent composition of
-- two coordinate masks, so the corresponding projectors commute, remain
-- idempotent and self-adjoint, and their image is exactly the intersection of
-- the two component images.  Iterating once supplies the concrete
-- gauge/tangent/boundary projector shape requested by the selected-variation
-- lane without assuming that arbitrary non-diagonal projectors commute.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector

infixr 5 _and_

_and_ : Bool → Bool → Bool
false and right = false
true and right = right

andCommutative : ∀ left right → left and right ≡ right and left
andCommutative false false = refl
andCommutative false true = refl
andCommutative true false = refl
andCommutative true true = refl

andAssociative : ∀ first second third →
  (first and second) and third ≡ first and (second and third)
andAssociative false second third = refl
andAssociative true second third = refl

andIdempotent : ∀ selected → selected and selected ≡ selected
andIdempotent false = refl
andIdempotent true = refl

intersectMask :
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalCoordinateMask
intersectMask left right coordinate = left coordinate and right coordinate

intersectMaskCommutative : ∀ left right coordinate →
  intersectMask left right coordinate ≡ intersectMask right left coordinate
intersectMaskCommutative left right coordinate =
  andCommutative (left coordinate) (right coordinate)

intersectMaskAssociative : ∀ first second third coordinate →
  intersectMask (intersectMask first second) third coordinate
  ≡ intersectMask first (intersectMask second third) coordinate
intersectMaskAssociative first second third coordinate =
  andAssociative
    (first coordinate) (second coordinate) (third coordinate)

intersectMaskIdempotent : ∀ mask coordinate →
  intersectMask mask mask coordinate ≡ mask coordinate
intersectMaskIdempotent mask coordinate = andIdempotent (mask coordinate)

maskIntersectionSelectExact : ∀ left right value →
  Projector.maskSelect (left and right) value
  ≡ Projector.maskSelect left (Projector.maskSelect right value)
maskIntersectionSelectExact false right value = refl
maskIntersectionSelectExact true false value = refl
maskIntersectionSelectExact true true value = refl

physicalCoordinateProjectCompositionExact :
  ∀ left right vector coordinate →
  Projector.physicalCoordinateProject
    (intersectMask left right) vector coordinate
  ≡ Projector.physicalCoordinateProject left
      (Projector.physicalCoordinateProject right vector) coordinate
physicalCoordinateProjectCompositionExact left right vector coordinate =
  maskIntersectionSelectExact
    (left coordinate) (right coordinate) (vector coordinate)

physicalCoordinateProjectorsCommute :
  ∀ left right vector coordinate →
  Projector.physicalCoordinateProject left
    (Projector.physicalCoordinateProject right vector) coordinate
  ≡ Projector.physicalCoordinateProject right
      (Projector.physicalCoordinateProject left vector) coordinate
physicalCoordinateProjectorsCommute left right vector coordinate =
  trans
    (symmetryLeft coordinate)
    (trans
      (maskSwap coordinate)
      (physicalCoordinateProjectCompositionExact right left vector coordinate))
  where
  symmetryLeft : ∀ coordinate →
    Projector.physicalCoordinateProject left
      (Projector.physicalCoordinateProject right vector) coordinate
    ≡ Projector.physicalCoordinateProject
        (intersectMask left right) vector coordinate
  symmetryLeft coordinate =
    relationSymmetric
      (physicalCoordinateProjectCompositionExact
        left right vector coordinate)

  relationSymmetric : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  relationSymmetric refl = refl

  maskSwap : ∀ coordinate →
    Projector.physicalCoordinateProject
      (intersectMask left right) vector coordinate
    ≡ Projector.physicalCoordinateProject
      (intersectMask right left) vector coordinate
  maskSwap coordinate
    rewrite intersectMaskCommutative left right coordinate = refl

triplePhysicalConstraintMask :
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalCoordinateMask
triplePhysicalConstraintMask gauge tangent boundary =
  intersectMask gauge (intersectMask tangent boundary)

triplePhysicalConstraintProject :
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalCoordinateMask →
  Projector.PhysicalVector → Projector.PhysicalVector
triplePhysicalConstraintProject gauge tangent boundary =
  Projector.physicalCoordinateProject
    (triplePhysicalConstraintMask gauge tangent boundary)

triplePhysicalConstraintProjectExact :
  ∀ gauge tangent boundary vector coordinate →
  triplePhysicalConstraintProject
    gauge tangent boundary vector coordinate
  ≡ Projector.physicalCoordinateProject gauge
      (Projector.physicalCoordinateProject tangent
        (Projector.physicalCoordinateProject boundary vector))
      coordinate
triplePhysicalConstraintProjectExact
    gauge tangent boundary vector coordinate =
  trans
    (physicalCoordinateProjectCompositionExact
      gauge (intersectMask tangent boundary) vector coordinate)
    (congOuter
      (physicalCoordinateProjectCompositionExact
        tangent boundary vector coordinate))
  where
  congOuter :
    Projector.physicalCoordinateProject
      (intersectMask tangent boundary) vector coordinate
    ≡ Projector.physicalCoordinateProject tangent
        (Projector.physicalCoordinateProject boundary vector) coordinate →
    Projector.physicalCoordinateProject gauge
      (Projector.physicalCoordinateProject
        (intersectMask tangent boundary) vector) coordinate
    ≡ Projector.physicalCoordinateProject gauge
      (Projector.physicalCoordinateProject tangent
        (Projector.physicalCoordinateProject boundary vector)) coordinate
  congOuter refl = refl

triplePhysicalConstraintProjectorIdempotent :
  ∀ gauge tangent boundary vector coordinate →
  triplePhysicalConstraintProject gauge tangent boundary
    (triplePhysicalConstraintProject gauge tangent boundary vector)
    coordinate
  ≡ triplePhysicalConstraintProject gauge tangent boundary vector coordinate
triplePhysicalConstraintProjectorIdempotent gauge tangent boundary =
  Projector.physicalConstraintProjectorIdempotent
    (triplePhysicalConstraintMask gauge tangent boundary)

triplePhysicalConstraintProjectorSelfAdjoint :
  ∀ gauge tangent boundary left right →
  Physical.physicalCoordinateDot left
    (triplePhysicalConstraintProject gauge tangent boundary right)
  ≡ Physical.physicalCoordinateDot
      (triplePhysicalConstraintProject gauge tangent boundary left) right
triplePhysicalConstraintProjectorSelfAdjoint gauge tangent boundary =
  Projector.physicalConstraintProjectorSelfAdjoint
    (triplePhysicalConstraintMask gauge tangent boundary)

record TripleConstraintImage
    (gauge tangent boundary : Projector.PhysicalCoordinateMask)
    (vector : Projector.PhysicalVector) : Set where
  field
    gaugeImage : Projector.PhysicalConstraintProjectorImage gauge vector
    tangentImage : Projector.PhysicalConstraintProjectorImage tangent vector
    boundaryImage : Projector.PhysicalConstraintProjectorImage boundary vector

open TripleConstraintImage public

tripleImageGivesIntersectionImage :
  ∀ {gauge tangent boundary vector} →
  TripleConstraintImage gauge tangent boundary vector →
  Projector.PhysicalConstraintProjectorImage
    (triplePhysicalConstraintMask gauge tangent boundary) vector
tripleImageGivesIntersectionImage {gauge} {tangent} {boundary} {vector} image =
  Projector.physicalConstraintProjectorImageCharacterizationBackward
    (triplePhysicalConstraintMask gauge tangent boundary)
    vector
    fixed
  where
  fixed : ∀ coordinate →
    triplePhysicalConstraintProject gauge tangent boundary vector coordinate
    ≡ vector coordinate
  fixed coordinate
    with gauge coordinate | tangent coordinate | boundary coordinate
  ... | true | true | true = refl
  ... | false | tangentSelected | boundarySelected =
    trans refl
      (symmetry
        (Projector.outsideMaskZero
          (gaugeImage image) coordinate refl))
  ... | true | false | boundarySelected =
    trans refl
      (symmetry
        (Projector.outsideMaskZero
          (tangentImage image) coordinate refl))
  ... | true | true | false =
    trans refl
      (symmetry
        (Projector.outsideMaskZero
          (boundaryImage image) coordinate refl))

  symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  symmetry refl = refl

physicalProjectorCompositionLevel : ProofLevel
physicalProjectorCompositionLevel = machineChecked

tripleConstraintProjectorLevel : ProofLevel
tripleConstraintProjectorLevel = machineChecked
