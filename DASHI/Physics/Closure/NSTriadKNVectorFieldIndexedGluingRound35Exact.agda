module DASHI.Physics.Closure.NSTriadKNVectorFieldIndexedGluingRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- DOI: 10.1007/978-3-642-61667-9.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the Round-30 same-object coordinate bridge from point transport to
-- dynamics transport.  The coordinate vector field is defined from the exact
-- enumerated Galerkin equation chosen by the representation.  The existing
-- `physicalFieldEncodedExactly` theorem is therefore one face of a commuting
-- square.
--
-- Function extensionality is intentionally not assumed.  The reverse face is
-- proved coordinate by coordinate using encode/decode round-trip exactness:
-- decoding the coordinate RHS and re-encoding it agrees at every coordinate
-- with the encoded physical RHS.  Thus the complete vector field, not merely
-- state points, is glued across the seam.
--
-- This theorem is immediately inhabited by every Round-30 literal coordinate
-- representation.  The remaining F2 producer is to construct the analogous
-- equivalence and square on the Round-34 Bishop-real coordinate carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinVectorLipschitzRound29Exact as Vector
import DASHI.Physics.Closure.NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact as Old

coordinateVectorField :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : Old.FinitePhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField} →
  Old.LiteralCoordinatesRepresentPhysicalVectorField
    equivalence physicalVectorField coordinateField →
  Polynomial.Assignment → Polynomial.Assignment
coordinateVectorField representation coordinates variable =
  Polynomial.coordinateRightHandSide
    (Old.equationFor representation variable)
    coordinates

record VectorFieldIndexedGluing
    {stateLevel : Level}
    {PhysicalState : Set stateLevel}
    (equivalence : Old.FinitePhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (coordinateField : Vector.LiteralFiniteGalerkinVectorField) :
    Set (lsuc stateLevel) where
  field
    representation :
      Old.LiteralCoordinatesRepresentPhysicalVectorField
        equivalence physicalVectorField coordinateField

    forwardSquare : ∀ state variable →
      Old.encode equivalence (physicalVectorField state) variable
      ≡ coordinateVectorField representation
          (Old.encode equivalence state) variable

    reverseSquareInCoordinates : ∀ state variable →
      Old.encode equivalence
        (Old.decode equivalence
          (coordinateVectorField representation
            (Old.encode equivalence state)))
        variable
      ≡ Old.encode equivalence (physicalVectorField state) variable

open VectorFieldIndexedGluing public

reverseSquareFromForward :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : Old.FinitePhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField}
    (representation :
      Old.LiteralCoordinatesRepresentPhysicalVectorField
        equivalence physicalVectorField coordinateField) →
  ∀ state variable →
  Old.encode equivalence
    (Old.decode equivalence
      (coordinateVectorField representation
        (Old.encode equivalence state)))
    variable
  ≡ Old.encode equivalence (physicalVectorField state) variable
reverseSquareFromForward {equivalence = equivalence}
    representation state variable =
  trans
    (Old.encodeDecode equivalence
      (coordinateVectorField representation
        (Old.encode equivalence state))
      variable)
    (sym
      (Old.physicalFieldEncodedExactly
        representation state variable))

canonicalVectorFieldIndexedGluing :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : Old.FinitePhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField} →
  (representation :
    Old.LiteralCoordinatesRepresentPhysicalVectorField
      equivalence physicalVectorField coordinateField) →
  VectorFieldIndexedGluing equivalence physicalVectorField coordinateField
canonicalVectorFieldIndexedGluing representation = record
  { representation = representation
  ; forwardSquare =
      Old.physicalFieldEncodedExactly representation
  ; reverseSquareInCoordinates =
      reverseSquareFromForward representation
  }

forwardThenReverseSquare :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : Old.FinitePhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField}
    (gluing :
      VectorFieldIndexedGluing
        equivalence physicalVectorField coordinateField) →
  ∀ state variable →
  coordinateVectorField (representation gluing)
      (Old.encode equivalence state) variable
  ≡ Old.encode equivalence
      (Old.decode equivalence
        (coordinateVectorField (representation gluing)
          (Old.encode equivalence state)))
      variable
forwardThenReverseSquare {equivalence = equivalence}
    gluing state variable =
  sym
    (Old.encodeDecode equivalence
      (coordinateVectorField (representation gluing)
        (Old.encode equivalence state))
      variable)

vectorFieldIndexedGluingClosed : Bool
vectorFieldIndexedGluingClosed = true

physicalBishopVectorFieldIndexedGluingConstructed : Bool
physicalBishopVectorFieldIndexedGluingConstructed = false

vectorFieldIndexedGluingClosedIsTrue :
  vectorFieldIndexedGluingClosed ≡ true
vectorFieldIndexedGluingClosedIsTrue = refl

physicalBishopVectorFieldIndexedGluingConstructedIsFalse :
  physicalBishopVectorFieldIndexedGluingConstructed ≡ false
physicalBishopVectorFieldIndexedGluingConstructedIsFalse = refl
