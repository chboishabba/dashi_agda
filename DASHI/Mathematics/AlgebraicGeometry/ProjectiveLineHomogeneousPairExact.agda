module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact where

------------------------------------------------------------------------
-- CP^1 HOMOGENEOUS COORDINATES AS LITERAL NONZERO PAIRS
--
-- The generic CP^n presentation stores coordinates as an exact-length list.
-- At n=1, eliminate that list bureaucracy completely: homogeneous vectors are
-- exactly pairs (z0,z1) with a proof that at least one coordinate is nonzero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Product using (_×_)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP

record HomogeneousPair
    (field : CP.ComplexFieldPresentation) : Set where
  constructor homogeneous-pair
  field
    first second : CP.Complex field
    notBothZero :
      CP.ContainsNonzero field (first ∷ second ∷ [])

open HomogeneousPair public

homogeneousLineToPair :
  ∀ {field} →
  CP.HomogeneousVector field (suc zero) →
  HomogeneousPair field
homogeneousLineToPair vector
    with CP.coordinates vector
       | CP.coordinateCountExact vector
       | CP.notAllZero vector
... | [] | () | nonzero
... | first ∷ [] | () | nonzero
... | first ∷ second ∷ [] | refl | nonzero =
  homogeneous-pair first second nonzero
... | first ∷ second ∷ third ∷ rest | () | nonzero

pairToHomogeneousLine :
  ∀ {field} →
  HomogeneousPair field →
  CP.HomogeneousVector field (suc zero)
pairToHomogeneousLine pair = record
  { CP.coordinates =
      first pair ∷ second pair ∷ []
  ; CP.coordinateCountExact =
      refl
  ; CP.notAllZero =
      notBothZero pair
  }

pairRoundTrip :
  ∀ {field}
    (pair : HomogeneousPair field) →
  homogeneousLineToPair (pairToHomogeneousLine pair)
  ≡ pair
pairRoundTrip (homogeneous-pair first second nonzero) = refl

homogeneousLineCoordinatesRoundTrip :
  ∀ {field}
    (vector : CP.HomogeneousVector field (suc zero)) →
  CP.coordinates
    (pairToHomogeneousLine (homogeneousLineToPair vector))
  ≡ CP.coordinates vector
homogeneousLineCoordinatesRoundTrip vector
    with CP.coordinates vector
       | CP.coordinateCountExact vector
       | CP.notAllZero vector
... | [] | () | nonzero
... | first ∷ [] | () | nonzero
... | first ∷ second ∷ [] | refl | nonzero = refl
... | first ∷ second ∷ third ∷ rest | () | nonzero

scalePair :
  ∀ {field} →
  CP.Complex field →
  HomogeneousPair field →
  CP.Complex field →
  CP.Complex field →
  Set
scalePair {field} scalar pair scaledFirst scaledSecond =
  scaledFirst ≡ CP.multiply field scalar (first pair)
  ×
  scaledSecond ≡ CP.multiply field scalar (second pair)

record ProjectiveLineHomogeneousPairBoundary : Set where
  constructor projective-line-homogeneous-pair-boundary
  field
    exactLengthTwoEliminationPaid : Bool
    homogeneousPairCarrierPaid : Bool
    pairToVectorPaid : Bool
    vectorToPairPaid : Bool
    homogeneousVectorPairEquivalencePaid : Bool
    projectiveLineQuotientInhabited : Bool
    quotientEliminatorPaid : Bool
    pointDivisorCycleClassPaid : Bool
    literalP1HodgeWeldPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveLineHomogeneousPairBoundary :
  ProjectiveLineHomogeneousPairBoundary
canonicalProjectiveLineHomogeneousPairBoundary =
  projective-line-homogeneous-pair-boundary
    true true true true true false false false false false
