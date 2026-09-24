module DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact where

------------------------------------------------------------------------
-- EXACT HOMOGENEOUS COORDINATES
--
-- Unlike the first presentation cut, nonzero-ness and rescaling are proof
-- relevant: a homogeneous vector carries an actual nonzero-coordinate witness,
-- and projective rescaling carries literal coordinate-list equality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

record ComplexFieldPresentation : Set₁ where
  field
    Complex : Set
    zero one : Complex
    add multiply : Complex → Complex → Complex
    negate : Complex → Complex
    nonzero : Complex → Set
    inverse : (z : Complex) → nonzero z → Complex

open ComplexFieldPresentation public

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

scaleCoordinates :
  (field : ComplexFieldPresentation) →
  Complex field →
  List (Complex field) →
  List (Complex field)
scaleCoordinates field scalar =
  mapList (multiply field scalar)

data ContainsNonzero
    (field : ComplexFieldPresentation) :
    List (Complex field) → Set where
  hereNonzero :
    ∀ {z zs} →
    nonzero field z →
    ContainsNonzero field (z ∷ zs)

  thereNonzero :
    ∀ {z zs} →
    ContainsNonzero field zs →
    ContainsNonzero field (z ∷ zs)

record HomogeneousVector
    (field : ComplexFieldPresentation)
    (dimension : Nat) : Set where
  field
    coordinates : List (Complex field)
    coordinateCountExact :
      listLength coordinates ≡ suc dimension
    notAllZero :
      ContainsNonzero field coordinates

open HomogeneousVector public

record ProjectiveMultiplicativeLaws
    (field : ComplexFieldPresentation) : Set₁ where
  field
    oneNonzero :
      nonzero field (one field)

    multiplyNonzero :
      ∀ {x y} →
      nonzero field x →
      nonzero field y →
      nonzero field (multiply field x y)

    inverseNonzero :
      ∀ {x} (xNonzero : nonzero field x) →
      nonzero field (inverse field x xNonzero)

    multiplyOneLeft :
      ∀ x →
      multiply field (one field) x ≡ x

    multiplyAssociative :
      ∀ x y z →
      multiply field x (multiply field y z)
      ≡ multiply field (multiply field x y) z

    inverseLeft :
      ∀ x (xNonzero : nonzero field x) →
      multiply field
        (inverse field x xNonzero)
        x
      ≡ one field

open ProjectiveMultiplicativeLaws public

scaleOneCoordinates :
  ∀ {field} →
  ProjectiveMultiplicativeLaws field →
  (xs : List (Complex field)) →
  scaleCoordinates field (one field) xs ≡ xs
scaleOneCoordinates laws [] = refl
scaleOneCoordinates {field} laws (x ∷ xs) =
  cong₂ _∷_
    (multiplyOneLeft laws x)
    (scaleOneCoordinates laws xs)
  where
    cong₂ :
      ∀ {A B C : Set}
        (f : A → B → C)
        {a a' : A} {b b' : B} →
      a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

scaleComposition :
  ∀ {field} →
  ProjectiveMultiplicativeLaws field →
  (outer inner : Complex field) →
  (xs : List (Complex field)) →
  scaleCoordinates field outer
    (scaleCoordinates field inner xs)
  ≡ scaleCoordinates field
      (multiply field outer inner)
      xs
scaleComposition laws outer inner [] = refl
scaleComposition {field} laws outer inner (x ∷ xs) =
  cong₂ _∷_
    (multiplyAssociative laws outer inner x)
    (scaleComposition laws outer inner xs)
  where
    cong₂ :
      ∀ {A B C : Set}
        (f : A → B → C)
        {a a' : A} {b b' : B} →
      a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

scaleInverseCoordinates :
  ∀ {field} →
  (laws : ProjectiveMultiplicativeLaws field) →
  (scalar : Complex field) →
  (scalarNonzero : nonzero field scalar) →
  (xs : List (Complex field)) →
  scaleCoordinates field
    (inverse field scalar scalarNonzero)
    (scaleCoordinates field scalar xs)
  ≡ xs
scaleInverseCoordinates laws scalar scalarNonzero [] = refl
scaleInverseCoordinates {field} laws scalar scalarNonzero (x ∷ xs) =
  cong₂ _∷_ headEquality
    (scaleInverseCoordinates laws scalar scalarNonzero xs)
  where
    headEquality :
      multiply field
        (inverse field scalar scalarNonzero)
        (multiply field scalar x)
      ≡ x
    headEquality =
      trans
        (multiplyAssociative laws
          (inverse field scalar scalarNonzero)
          scalar
          x)
        (trans
          (cong
            (λ coefficient → multiply field coefficient x)
            (inverseLeft laws scalar scalarNonzero))
          (multiplyOneLeft laws x))

    cong₂ :
      ∀ {A B C : Set}
        (f : A → B → C)
        {a a' : A} {b b' : B} →
      a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

record ProjectiveRescaling
    {field : ComplexFieldPresentation}
    {dimension : Nat}
    (left right : HomogeneousVector field dimension) : Set where
  field
    scalar : Complex field
    scalarNonzero : nonzero field scalar
    coordinatewiseRescaling :
      coordinates right
      ≡ scaleCoordinates field scalar (coordinates left)

open ProjectiveRescaling public

rescalingReflexive :
  ∀ {field dimension} →
  (laws : ProjectiveMultiplicativeLaws field) →
  (vector : HomogeneousVector field dimension) →
  ProjectiveRescaling vector vector
rescalingReflexive {field} laws vector = record
  { scalar = one field
  ; scalarNonzero = oneNonzero laws
  ; coordinatewiseRescaling =
      sym (scaleOneCoordinates laws (coordinates vector))
  }

rescalingSymmetric :
  ∀ {field dimension} →
  (laws : ProjectiveMultiplicativeLaws field) →
  {left right : HomogeneousVector field dimension} →
  ProjectiveRescaling left right →
  ProjectiveRescaling right left
rescalingSymmetric {field} laws {left} {right} rescaling = record
  { scalar =
      inverse field
        (scalar rescaling)
        (scalarNonzero rescaling)
  ; scalarNonzero =
      inverseNonzero laws (scalarNonzero rescaling)
  ; coordinatewiseRescaling =
      sym
        (trans
          (cong
            (scaleCoordinates field
              (inverse field
                (scalar rescaling)
                (scalarNonzero rescaling)))
            (coordinatewiseRescaling rescaling))
          (scaleInverseCoordinates
            laws
            (scalar rescaling)
            (scalarNonzero rescaling)
            (coordinates left)))
  }

rescalingTransitive :
  ∀ {field dimension} →
  (laws : ProjectiveMultiplicativeLaws field) →
  {first second third : HomogeneousVector field dimension} →
  ProjectiveRescaling first second →
  ProjectiveRescaling second third →
  ProjectiveRescaling first third
rescalingTransitive {field} laws {first} firstSecond secondThird = record
  { scalar =
      multiply field
        (scalar secondThird)
        (scalar firstSecond)
  ; scalarNonzero =
      multiplyNonzero laws
        (scalarNonzero secondThird)
        (scalarNonzero firstSecond)
  ; coordinatewiseRescaling =
      trans
        (coordinatewiseRescaling secondThird)
        (trans
          (cong
            (scaleCoordinates field (scalar secondThird))
            (coordinatewiseRescaling firstSecond))
          (scaleComposition laws
            (scalar secondThird)
            (scalar firstSecond)
            (coordinates first)))
  }

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
    nonzeroCoordinateWitnessPaid : Bool
    literalRescalingEqualityPaid : Bool
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
    true true true true false false false false false
