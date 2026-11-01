module DASHI.Physics.Closure.NSTriadKNFiniteRealCanonicalCoordinateCarrierRound71Exact where

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
-- ROUND 71 / FINITE REAL COORDINATE CARRIER REPAIR
--
-- The older Round26/30 Picard lane uses
--
--     Assignment = CoordinateVariable -> Q.
--
-- That type is not the finite cutoff phase space: CoordinateVariable ranges
-- over every Fourier mode, axis and real/imaginary part.  It is also Q-valued,
-- whereas the literal physical Fourier carrier is parameterized by the chosen
-- algebraic real field F.
--
-- This file repairs the carrier layer without claiming the still-missing ODE
-- theorem.  For every canonical cutoff reality-orbit list, enumerate exactly
-- six coordinate slots per retained Fourier mode (three axes x two complex
-- parts), and store exactly one Carrier F value in the same literal order.
--
-- The resulting state is genuinely finite by construction and uses the same
-- real field as the physical Complex3 coefficients.  What remains is the hard
-- SAME-OBJECT theorem identifying the canonical physical Galerkin RHS with a
-- locally-Lipschitz vector field on THIS finite real carrier, followed by a real
-- Picard-Lindelof authority/continuation theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (x ∷ xs) right = x ∷ append xs right

slotsForMode : Z3.FourierMode → List Polynomial.CoordinateVariable
slotsForMode mode =
    Polynomial.coordinate-variable mode Polynomial.xAxis Polynomial.realPart
  ∷ Polynomial.coordinate-variable mode Polynomial.xAxis Polynomial.imaginaryPart
  ∷ Polynomial.coordinate-variable mode Polynomial.yAxis Polynomial.realPart
  ∷ Polynomial.coordinate-variable mode Polynomial.yAxis Polynomial.imaginaryPart
  ∷ Polynomial.coordinate-variable mode Polynomial.zAxis Polynomial.realPart
  ∷ Polynomial.coordinate-variable mode Polynomial.zAxis Polynomial.imaginaryPart
  ∷ []

slotsForModes : List Z3.FourierMode → List Polynomial.CoordinateVariable
slotsForModes [] = []
slotsForModes (mode ∷ rest) =
  append (slotsForMode mode) (slotsForModes rest)

length : ∀ {A : Set} → List A → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

lengthAppend : ∀ {A : Set} (left right : List A) →
  length (append left right) ≡ length left + length right
lengthAppend [] right = refl
lengthAppend (x ∷ xs) right
  rewrite lengthAppend xs right = refl

six : Nat
six = suc (suc (suc (suc (suc (suc zero)))))

sixTimes : Nat → Nat
sixTimes zero = zero
sixTimes (suc n) = six + sixTimes n

slotsForModeLengthSix : ∀ mode → length (slotsForMode mode) ≡ six
slotsForModeLengthSix mode = refl

slotsForModesLengthExact : ∀ modes →
  length (slotsForModes modes) ≡ sixTimes (length modes)
slotsForModesLengthExact [] = refl
slotsForModesLengthExact (mode ∷ rest)
  rewrite lengthAppend (slotsForMode mode) (slotsForModes rest)
        | slotsForModeLengthSix mode
        | slotsForModesLengthExact rest = refl

canonicalCutoffSlots : Nat → List Polynomial.CoordinateVariable
canonicalCutoffSlots cutoff =
  slotsForModes (Orbit.canonicalCutoffOrbitModes cutoff)

canonicalCutoffSlotCountExact : ∀ cutoff →
  length (canonicalCutoffSlots cutoff)
  ≡ sixTimes (length (Orbit.canonicalCutoffOrbitModes cutoff))
canonicalCutoffSlotCountExact cutoff =
  slotsForModesLengthExact (Orbit.canonicalCutoffOrbitModes cutoff)

record RealSlotValue {r : Level} (F : C3.RealField r) : Set r where
  constructor real-slot-value
  field
    slot : Polynomial.CoordinateVariable
    value : C3.Carrier F

open RealSlotValue public

eraseSlots :
  ∀ {r} {F : C3.RealField r} →
  List (RealSlotValue F) → List Polynomial.CoordinateVariable
eraseSlots [] = []
eraseSlots (entry ∷ rest) = slot entry ∷ eraseSlots rest

record FiniteRealCoordinateState
    {r : Level}
    (F : C3.RealField r)
    (slots : List Polynomial.CoordinateVariable) : Set r where
  constructor finite-real-coordinate-state
  field
    entries : List (RealSlotValue F)
    exactSlotOrder : eraseSlots entries ≡ slots

open FiniteRealCoordinateState public

zeroEntries :
  ∀ {r} (F : C3.RealField r) →
  (slots : List Polynomial.CoordinateVariable) →
  List (RealSlotValue F)
zeroEntries F [] = []
zeroEntries F (slot ∷ rest) =
  real-slot-value slot (C3.zero F) ∷ zeroEntries F rest

eraseZeroEntriesExact :
  ∀ {r} (F : C3.RealField r) slots →
  eraseSlots (zeroEntries F slots) ≡ slots
eraseZeroEntriesExact F [] = refl
eraseZeroEntriesExact F (slot ∷ rest)
  rewrite eraseZeroEntriesExact F rest = refl

zeroFiniteRealCoordinateState :
  ∀ {r} (F : C3.RealField r) slots →
  FiniteRealCoordinateState F slots
zeroFiniteRealCoordinateState F slots =
  finite-real-coordinate-state
    (zeroEntries F slots)
    (eraseZeroEntriesExact F slots)

CanonicalCutoffRealCoordinateState :
  ∀ {r} (F : C3.RealField r) → Nat → Set r
CanonicalCutoffRealCoordinateState F cutoff =
  FiniteRealCoordinateState F (canonicalCutoffSlots cutoff)

round71FiniteRealCanonicalCoordinateCarrierConstructed : Bool
round71FiniteRealCanonicalCoordinateCarrierConstructed = true

round71FiniteCarrierUsesPhysicalRealField : Bool
round71FiniteCarrierUsesPhysicalRealField = true

round71CanonicalPhysicalRHSActsOnFiniteRealCarrier : Bool
round71CanonicalPhysicalRHSActsOnFiniteRealCarrier = false

round71RealPicardLindelofTrajectoryConstructed : Bool
round71RealPicardLindelofTrajectoryConstructed = false

round71FiniteRealCanonicalCoordinateCarrierConstructedIsTrue :
  round71FiniteRealCanonicalCoordinateCarrierConstructed ≡ true
round71FiniteRealCanonicalCoordinateCarrierConstructedIsTrue = refl

round71CanonicalPhysicalRHSActsOnFiniteRealCarrierIsFalse :
  round71CanonicalPhysicalRHSActsOnFiniteRealCarrier ≡ false
round71CanonicalPhysicalRHSActsOnFiniteRealCarrierIsFalse = refl

round71RealPicardLindelofTrajectoryConstructedIsFalse :
  round71RealPicardLindelofTrajectoryConstructed ≡ false
round71RealPicardLindelofTrajectoryConstructedIsFalse = refl
