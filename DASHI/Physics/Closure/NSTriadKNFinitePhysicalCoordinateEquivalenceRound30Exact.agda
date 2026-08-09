module DASHI.Physics.Closure.NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- DASHI CONTRIBUTION
--
-- State the exact finite-coordinate bridge required between the repository's
-- dependent physical Fourier carrier and the literal degree-two coordinate
-- equations.  Encoding and decoding are genuine inverses, and the complete
-- vector field commutes with them coordinate by coordinate.  Consequently the
-- Round-29 rational polynomial Lipschitz theorem can be transported only after
-- this same-object bridge is supplied; a separately chosen polynomial system
-- cannot be used as a surrogate for the physical Galerkin field.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinLocalLipschitzRound28Exact as Coordinate
import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinVectorLipschitzRound29Exact as Vector

record FinitePhysicalCoordinateEquivalence
    {stateLevel : Level}
    (PhysicalState : Set stateLevel) : Set (lsuc stateLevel) where
  field
    encode : PhysicalState → Polynomial.Assignment
    decode : Polynomial.Assignment → PhysicalState

    decodeEncode : ∀ state → decode (encode state) ≡ state
    encodeDecode : ∀ coordinates variable →
      encode (decode coordinates) variable ≡ coordinates variable

open FinitePhysicalCoordinateEquivalence public

record LiteralCoordinatesRepresentPhysicalVectorField
    {stateLevel : Level}
    {PhysicalState : Set stateLevel}
    (equivalence : FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (coordinateField : Vector.LiteralFiniteGalerkinVectorField) :
    Set (lsuc stateLevel) where
  field
    equationFor :
      Polynomial.CoordinateVariable →
      Polynomial.LiteralGalerkinCoordinateEquation

    equationEnumerated : ∀ variable →
      equationFor variable ∈ Vector.coordinateEquations coordinateField

    physicalFieldEncodedExactly : ∀ state variable →
      encode equivalence (physicalVectorField state) variable
      ≡ Polynomial.coordinateRightHandSide
          (equationFor variable) (encode equivalence state)

open LiteralCoordinatesRepresentPhysicalVectorField public

-- Local list membership, intentionally tied to the exact finite equation list.
data _∈_ {A : Set} (value : A) : List A → Set where
  here : ∀ {head tail} → value ≡ head → value ∈ (head ∷ tail)
  there : ∀ {head tail} → value ∈ tail → value ∈ (head ∷ tail)

physicalCoordinateRightHandSideDifference :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : FinitePhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField} →
  (representation : LiteralCoordinatesRepresentPhysicalVectorField
    equivalence physicalVectorField coordinateField) →
  (state reference : PhysicalState) variable →
  encode equivalence (physicalVectorField state) variable
    - encode equivalence (physicalVectorField reference) variable
  ≡ Polynomial.differenceAtoms
      (Polynomial.rightHandSideAtoms
        (equationFor representation variable))
      (encode equivalence state)
      (encode equivalence reference)
physicalCoordinateRightHandSideDifference
    {equivalence = equivalence}
    {physicalVectorField = physicalVectorField}
    representation state reference variable =
  trans
    (cong₂ _-_
      (physicalFieldEncodedExactly representation state variable)
      (physicalFieldEncodedExactly representation reference variable))
    (Polynomial.coordinateRightHandSideDifference
      (equationFor representation variable)
      (encode equivalence state)
      (encode equivalence reference))

record PhysicalCoordinateBall
    {stateLevel}
    {PhysicalState : Set stateLevel}
    (equivalence : FinitePhysicalCoordinateEquivalence PhysicalState)
    (radius : ℚ)
    (state : PhysicalState) : Set stateLevel where
  field
    encodedBound : Coordinate.AssignmentBound radius (encode equivalence state)

open PhysicalCoordinateBall public

record PhysicalCoordinateDifferenceBall
    {stateLevel}
    {PhysicalState : Set stateLevel}
    (equivalence : FinitePhysicalCoordinateEquivalence PhysicalState)
    (delta : ℚ)
    (state reference : PhysicalState) : Set stateLevel where
  field
    encodedDifferenceBound :
      Coordinate.AssignmentDifferenceBound delta
        (encode equivalence state) (encode equivalence reference)

open PhysicalCoordinateDifferenceBall public

transportCompleteFiniteVectorLipschitz :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : FinitePhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField} →
  LiteralCoordinatesRepresentPhysicalVectorField
    equivalence physicalVectorField coordinateField →
  (radius delta : ℚ) →
  0ℚ ≤ radius →
  0ℚ ≤ delta →
  (state reference : PhysicalState) →
  PhysicalCoordinateBall equivalence radius state →
  PhysicalCoordinateBall equivalence radius reference →
  PhysicalCoordinateDifferenceBall equivalence delta state reference →
  Vector.finiteVectorDifferenceL1
    (Vector.coordinateEquations coordinateField)
    (encode equivalence state) (encode equivalence reference)
  ≤ Vector.finiteVectorLipschitzWeight radius
      (Vector.coordinateEquations coordinateField) * delta
transportCompleteFiniteVectorLipschitz
    representation radius delta radiusNN deltaNN state reference
    stateBound referenceBound differenceBound =
  Vector.literalFiniteVectorFieldLocalLipschitz
    _ radius delta radiusNN deltaNN
    (encode _ state) (encode _ reference)
    (encodedBound stateBound)
    (encodedBound referenceBound)
    (encodedDifferenceBound differenceBound)

finitePhysicalCoordinateEquivalenceClosed : Bool
finitePhysicalCoordinateEquivalenceClosed = true

physicalPolynomialSameObjectBridgeClosed : Bool
physicalPolynomialSameObjectBridgeClosed = false

finitePhysicalCoordinateEquivalenceClosedIsTrue :
  finitePhysicalCoordinateEquivalenceClosed ≡ true
finitePhysicalCoordinateEquivalenceClosedIsTrue = refl

physicalPolynomialSameObjectBridgeClosedIsFalse :
  physicalPolynomialSameObjectBridgeClosed ≡ false
physicalPolynomialSameObjectBridgeClosedIsFalse = refl
