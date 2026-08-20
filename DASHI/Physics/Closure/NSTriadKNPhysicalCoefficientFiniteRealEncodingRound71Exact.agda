module DASHI.Physics.Closure.NSTriadKNPhysicalCoefficientFiniteRealEncodingRound71Exact where

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
-- ROUND 71 / PHYSICAL -> FINITE-REAL ENCODING
--
-- Continue the finite real coordinate repair by extracting, from every literal
-- physical TransverseModeCoefficient, exactly its six scalar components:
--
--   x.re, x.im, y.re, y.im, z.re, z.im.
--
-- The values live in the SAME Carrier F as the physical Complex3 coefficient.
-- The erased slot list is proved exactly equal to slotsForMode at each cell and
-- to slotsForModes of the literal coefficient-mode list after finite folding.
--
-- This constructs the physical -> finite-real encoding half of the ODE bridge
-- without rationalizing the state.  The reverse direction is deliberately not
-- fabricated: arbitrary six-tuples need transversality evidence before they can
-- become TransverseModeCoefficient values.  The eventual Picard carrier should
-- therefore either use a transverse finite subspace directly or prove that the
-- canonical vector field preserves the transverse constraints and transport a
-- Euclidean trajectory into it.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNFiniteRealCanonicalCoordinateCarrierRound71Exact as Finite

append : ∀ {a} {A : Set a} → List A → List A → List A
append [] right = right
append (x ∷ xs) right = x ∷ append xs right

coefficientModes :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) → List Z3.FourierMode
coefficientModes [] = []
coefficientModes (coefficient ∷ rest) =
  Phase.coefficientMode coefficient ∷ coefficientModes rest

entriesForCoefficient :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Phase.TransverseModeCoefficient F E → List (Finite.RealSlotValue F)
entriesForCoefficient {F = F} coefficient =
  let
    mode = Phase.coefficientMode coefficient
    vector = Phase.coefficientValue coefficient
    xv = C3.x vector
    yv = C3.y vector
    zv = C3.z vector
  in
    Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.xAxis Polynomial.realPart)
      (C3.real xv)
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.xAxis Polynomial.imaginaryPart)
      (C3.imaginary xv)
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.yAxis Polynomial.realPart)
      (C3.real yv)
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.yAxis Polynomial.imaginaryPart)
      (C3.imaginary yv)
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.zAxis Polynomial.realPart)
      (C3.real zv)
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.zAxis Polynomial.imaginaryPart)
      (C3.imaginary zv)
  ∷ []

entriesForCoefficientEraseExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficient : Phase.TransverseModeCoefficient F E) →
  Finite.eraseSlots (entriesForCoefficient coefficient)
  ≡ Finite.slotsForMode (Phase.coefficientMode coefficient)
entriesForCoefficientEraseExact coefficient = refl

entriesForCoefficients :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) →
  List (Finite.RealSlotValue F)
entriesForCoefficients [] = []
entriesForCoefficients (coefficient ∷ rest) =
  append (entriesForCoefficient coefficient) (entriesForCoefficients rest)

eraseSlotsAppend :
  ∀ {r} {F : C3.RealField r}
    (left right : List (Finite.RealSlotValue F)) →
  Finite.eraseSlots (append left right)
  ≡ Finite.append (Finite.eraseSlots left) (Finite.eraseSlots right)
eraseSlotsAppend [] right = refl
eraseSlotsAppend (entry ∷ rest) right
  rewrite eraseSlotsAppend rest right = refl

entriesForCoefficientsEraseExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
  Finite.eraseSlots (entriesForCoefficients coefficients)
  ≡ Finite.slotsForModes (coefficientModes coefficients)
entriesForCoefficientsEraseExact [] = refl
entriesForCoefficientsEraseExact (coefficient ∷ rest) =
  trans
    (eraseSlotsAppend
      (entriesForCoefficient coefficient)
      (entriesForCoefficients rest))
    (cong₂ Finite.append
      (entriesForCoefficientEraseExact coefficient)
      (entriesForCoefficientsEraseExact rest))

finiteRealStateFromPhysicalCoefficients :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
  Finite.FiniteRealCoordinateState F
    (Finite.slotsForModes (coefficientModes coefficients))
finiteRealStateFromPhysicalCoefficients coefficients =
  Finite.finite-real-coordinate-state
    (entriesForCoefficients coefficients)
    (entriesForCoefficientsEraseExact coefficients)

round71PhysicalCoefficientFiniteRealEncodingConstructed : Bool
round71PhysicalCoefficientFiniteRealEncodingConstructed = true

round71EncodingUsesSamePhysicalRealField : Bool
round71EncodingUsesSamePhysicalRealField = true

round71ArbitraryRealSlotsDecodeToTransverseCoefficient : Bool
round71ArbitraryRealSlotsDecodeToTransverseCoefficient = false

round71PhysicalCoefficientFiniteRealEncodingConstructedIsTrue :
  round71PhysicalCoefficientFiniteRealEncodingConstructed ≡ true
round71PhysicalCoefficientFiniteRealEncodingConstructedIsTrue = refl

round71ArbitraryRealSlotsDecodeToTransverseCoefficientIsFalse :
  round71ArbitraryRealSlotsDecodeToTransverseCoefficient ≡ false
round71ArbitraryRealSlotsDecodeToTransverseCoefficientIsFalse = refl
