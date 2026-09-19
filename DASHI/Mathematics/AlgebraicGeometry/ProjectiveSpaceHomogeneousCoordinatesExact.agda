module DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)

record ComplexFieldPresentation : Set₁ where
  field
    Complex : Set
    zero one : Complex
    add multiply : Complex → Complex → Complex
    negate : Complex → Complex
    nonzero : Complex → Set
    inverse : (z : Complex) → nonzero z → Complex

open ComplexFieldPresentation public

record HomogeneousVector
    (field : ComplexFieldPresentation)
    (dimension : Nat) : Set where
  field
    coordinates : List (Complex field)
    coordinateCount : Nat
    coordinateCountExact : coordinateCount ≡ suc dimension
    notAllZero : Set

open HomogeneousVector public

record ProjectiveRescaling
    {field : ComplexFieldPresentation}
    {dimension : Nat}
    (left right : HomogeneousVector field dimension) : Set where
  field
    scalar : Complex field
    scalarNonzero : nonzero field scalar
    coordinatewiseRescaling : Set

open ProjectiveRescaling public

record LiteralComplexProjectiveSpace
    (field : ComplexFieldPresentation)
    (dimension : Nat) : Set₁ where
  field
    Point : Set
    classOf : HomogeneousVector field dimension → Point
    sameClassIffRescaling :
      (left right : HomogeneousVector field dimension) →
      classOf left ≡ classOf right →
      ProjectiveRescaling left right
    rescalingGivesSameClass :
      (left right : HomogeneousVector field dimension) →
      ProjectiveRescaling left right →
      classOf left ≡ classOf right

open LiteralComplexProjectiveSpace public

record CoordinateLinearSubspace
    {field : ComplexFieldPresentation}
    {dimension : Nat}
    (space : LiteralComplexProjectiveSpace field dimension)
    (codimension : Nat) : Set₁ where
  field
    contains : Point space → Set
    homogeneousCoordinateVanishingMeaning : Set
    algebraicSubvarietyWitness : Set

open CoordinateLinearSubspace public

record ProjectiveSpaceGeometryComparisonBoundary : Set where
  constructor projective-space-geometry-comparison-boundary
  field
    homogeneousCoordinatePresentationPaid : Bool
    coordinateLinearSubspacePresentationPaid : Bool
    quotientConstructionPaid : Bool
    smoothProjectiveVarietyIdentificationPaid : Bool
    singularDeRhamComparisonPaid : Bool
    hyperplaneCycleClassPowerIdentityPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveSpaceGeometryComparisonBoundary :
  ProjectiveSpaceGeometryComparisonBoundary
canonicalProjectiveSpaceGeometryComparisonBoundary =
  projective-space-geometry-comparison-boundary
    true true false false false false false
