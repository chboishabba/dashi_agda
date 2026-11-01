module DASHI.Physics.Closure.NSTriadKNBishopSetoidCoordinateGluingRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Author: Zachary Murray.
-- Title: "Constructive Analysis in the Agda Proof Assistant".
-- Persistent identifier: 10.48550/arXiv.2205.08354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- The old Round-30 coordinate equivalence has codomain
--
--   CoordinateVariable -> Q.
--
-- That syntax is useful for exact rational Galerkin coefficients but it cannot
-- be the trajectory carrier for the complete-real Picard lane.  Round 34 gave
-- the same polynomial syntax a semantics in Murray--Bishop reals, whose native
-- equality is the constructive real setoid relation `_≃_` rather than Agda's
-- intensional propositional equality.
--
-- This module therefore defines the correct F2 seam: a physical-state setoid
-- equivalent to the Bishop-real assignment setoid, together with an exact
-- pointwise representation of the literal Galerkin vector field.  From the
-- forward encoding theorem and the two setoid round trips we prove the reverse
-- vector-field square as well.  Thus later Picard transport can work on the
-- complete-real carrier without pretending that rational assignments are
-- complete or quotienting Bishop equality by an unsafe axiom.
--
-- The actual Fourier-state <-> Bishop-assignment codec remains a physical
-- producer.  This file closes the type-correct gluing theorem it must inhabit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinVectorLipschitzRound29Exact as Vector
import DASHI.Physics.Closure.NSTriadKNFinitePhysicalCoordinateEquivalenceRound30Exact as OldCoordinates
import DASHI.Physics.Closure.NSTriadKNMurrayBishopGalerkinCoordinateSemanticsRound34Exact as Bishop

BishopAssignmentsEquivalent : Bishop.BishopAssignment → Bishop.BishopAssignment → Set
BishopAssignmentsEquivalent left right =
  ∀ variable → BishopReal._≃_ (left variable) (right variable)

bishopAssignmentsEquivalentRefl :
  ∀ assignment → BishopAssignmentsEquivalent assignment assignment
bishopAssignmentsEquivalentRefl assignment variable =
  BishopProperties.≃-refl

bishopAssignmentsEquivalentSym :
  ∀ {left right} →
  BishopAssignmentsEquivalent left right →
  BishopAssignmentsEquivalent right left
bishopAssignmentsEquivalentSym equivalent variable =
  BishopProperties.≃-sym (equivalent variable)

bishopAssignmentsEquivalentTrans :
  ∀ {left middle right} →
  BishopAssignmentsEquivalent left middle →
  BishopAssignmentsEquivalent middle right →
  BishopAssignmentsEquivalent left right
bishopAssignmentsEquivalentTrans first second variable =
  BishopProperties.≃-trans (first variable) (second variable)

record BishopPhysicalCoordinateEquivalence
    {stateLevel : Level}
    (PhysicalState : Set stateLevel) : Set (lsuc stateLevel) where
  field
    _≈State_ : PhysicalState → PhysicalState → Set stateLevel

    stateRefl : ∀ state → state ≈State state
    stateSym : ∀ {left right} → left ≈State right → right ≈State left
    stateTrans : ∀ {left middle right} →
      left ≈State middle → middle ≈State right → left ≈State right

    encode : PhysicalState → Bishop.BishopAssignment
    decode : Bishop.BishopAssignment → PhysicalState

    decodeEncode : ∀ state → decode (encode state) ≈State state
    encodeDecode : ∀ coordinates →
      BishopAssignmentsEquivalent (encode (decode coordinates)) coordinates

    encodeReflectsState : ∀ {left right} →
      BishopAssignmentsEquivalent (encode left) (encode right) →
      left ≈State right

open BishopPhysicalCoordinateEquivalence public

record BishopLiteralCoordinatesRepresentPhysicalVectorField
    {stateLevel : Level}
    {PhysicalState : Set stateLevel}
    (equivalence : BishopPhysicalCoordinateEquivalence PhysicalState)
    (physicalVectorField : PhysicalState → PhysicalState)
    (coordinateField : Vector.LiteralFiniteGalerkinVectorField) :
    Set (lsuc stateLevel) where
  field
    equationFor :
      Polynomial.CoordinateVariable →
      Polynomial.LiteralGalerkinCoordinateEquation

    equationEnumerated : ∀ variable →
      OldCoordinates._∈_
        (equationFor variable)
        (Vector.coordinateEquations coordinateField)

    physicalFieldEncodedExactly : ∀ state variable →
      BishopReal._≃_
        (encode equivalence (physicalVectorField state) variable)
        (Bishop.bishopCoordinateRightHandSide
          (equationFor variable) (encode equivalence state))

open BishopLiteralCoordinatesRepresentPhysicalVectorField public

bishopCoordinateVectorField :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : BishopPhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField} →
  BishopLiteralCoordinatesRepresentPhysicalVectorField
    equivalence physicalVectorField coordinateField →
  Bishop.BishopAssignment → Bishop.BishopAssignment
bishopCoordinateVectorField representation coordinates variable =
  Bishop.bishopCoordinateRightHandSide
    (equationFor representation variable) coordinates

bishopForwardVectorFieldSquare :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : BishopPhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField}
    (representation : BishopLiteralCoordinatesRepresentPhysicalVectorField
      equivalence physicalVectorField coordinateField) →
  ∀ state →
  BishopAssignmentsEquivalent
    (encode equivalence (physicalVectorField state))
    (bishopCoordinateVectorField representation (encode equivalence state))
bishopForwardVectorFieldSquare representation state variable =
  physicalFieldEncodedExactly representation state variable

bishopReverseVectorFieldSquare :
  ∀ {stateLevel}
    {PhysicalState : Set stateLevel}
    {equivalence : BishopPhysicalCoordinateEquivalence PhysicalState}
    {physicalVectorField : PhysicalState → PhysicalState}
    {coordinateField : Vector.LiteralFiniteGalerkinVectorField}
    (representation : BishopLiteralCoordinatesRepresentPhysicalVectorField
      equivalence physicalVectorField coordinateField) →
  ∀ coordinates →
  _≈State_ equivalence
    (physicalVectorField (decode equivalence coordinates))
    (decode equivalence
      (bishopCoordinateVectorField representation coordinates))
bishopReverseVectorFieldSquare {equivalence = equivalence}
    representation coordinates =
  encodeReflectsState equivalence λ variable →
    BishopProperties.≃-trans
      (physicalFieldEncodedExactly representation
        (decode equivalence coordinates) variable)
      (BishopProperties.≃-sym
        (encodeDecode equivalence
          (bishopCoordinateVectorField representation coordinates)
          variable))

bishopSetoidCoordinateGluingClosed : Bool
bishopSetoidCoordinateGluingClosed = true

physicalBishopStateCoordinateEquivalenceConstructed : Bool
physicalBishopStateCoordinateEquivalenceConstructed = false

bishopSetoidCoordinateGluingClosedIsTrue :
  bishopSetoidCoordinateGluingClosed ≡ true
bishopSetoidCoordinateGluingClosedIsTrue = refl

physicalBishopStateCoordinateEquivalenceConstructedIsFalse :
  physicalBishopStateCoordinateEquivalenceConstructed ≡ false
physicalBishopStateCoordinateEquivalenceConstructedIsFalse = refl
