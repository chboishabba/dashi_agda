{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNFixedCanonicalFiniteRealCodecRound851Exact where

------------------------------------------------------------------------
-- R851 / ROUND71 CANONICAL REALITY STATE -> FINITE REAL COORDINATE CODEC
--
-- Round71 already stores one Complex3 F value for every canonical positive
-- reality-orbit representative.  The repaired finite-real carrier stores
-- exactly six Carrier F slots per representative.  This owner connects those
-- two literal representations with no ambient complex phase space and no new
-- dynamics.
--
-- For one stored Fourier value
--
--   (x_re,x_im,y_re,y_im,z_re,z_im)
--
-- is emitted in exactly Finite.slotsForMode order.  Therefore every canonical
-- Round71 state has a canonical finite-real encoding, and the Round71 vector
-- field has a finite-real output simply by encoding its literal RHS state.
--
-- Reality remains structural: negative modes are still reconstructed by the
-- existing Round71 lookup and are NOT duplicated into the coordinate carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNFiniteRealCanonicalCoordinateCarrierRound71Exact as Finite
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed

------------------------------------------------------------------------
-- Six literal real coordinates of one Complex3 value.
------------------------------------------------------------------------

encodeModeValue :
  ∀ {r : Level} {F : C3.RealField r} →
  Fixed.CanonicalModeValue F →
  List (Finite.RealSlotValue F)
encodeModeValue {F = F} entry =
  let
    mode = Fixed.mode entry
    value = Fixed.value entry
  in
    Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.xAxis Polynomial.realPart)
      (C3.real (C3.x value))
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.xAxis Polynomial.imaginaryPart)
      (C3.imaginary (C3.x value))
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.yAxis Polynomial.realPart)
      (C3.real (C3.y value))
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.yAxis Polynomial.imaginaryPart)
      (C3.imaginary (C3.y value))
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.zAxis Polynomial.realPart)
      (C3.real (C3.z value))
  ∷ Finite.real-slot-value
      (Polynomial.coordinate-variable mode Polynomial.zAxis Polynomial.imaginaryPart)
      (C3.imaginary (C3.z value))
  ∷ []

encodeModeValueSlots :
  ∀ {r : Level} {F : C3.RealField r}
    (entry : Fixed.CanonicalModeValue F) →
  Finite.eraseSlots (encodeModeValue entry)
  ≡ Finite.slotsForMode (Fixed.mode entry)
encodeModeValueSlots entry = refl

encodeValues :
  ∀ {r : Level} {F : C3.RealField r} →
  List (Fixed.CanonicalModeValue F) →
  List (Finite.RealSlotValue F)
encodeValues [] = []
encodeValues (entry ∷ rest) =
  Finite.append (encodeModeValue entry) (encodeValues rest)

eraseAppend :
  ∀ {r : Level} {F : C3.RealField r}
    (left right : List (Finite.RealSlotValue F)) →
  Finite.eraseSlots (Finite.append left right)
  ≡ Finite.append (Finite.eraseSlots left) (Finite.eraseSlots right)
eraseAppend [] right = refl
eraseAppend (entry ∷ rest) right
  rewrite eraseAppend rest right = refl

encodeValuesSlots :
  ∀ {r : Level} {F : C3.RealField r}
    (entries : List (Fixed.CanonicalModeValue F)) →
  Finite.eraseSlots (encodeValues entries)
  ≡ Finite.slotsForModes (Fixed.modeList entries)
encodeValuesSlots [] = refl
encodeValuesSlots (entry ∷ rest)
  rewrite eraseAppend (encodeModeValue entry) (encodeValues rest)
        | encodeModeValueSlots entry
        | encodeValuesSlots rest = refl

------------------------------------------------------------------------
-- Canonical Round71 state encoding.
------------------------------------------------------------------------

encodeState :
  ∀ {r : Level} {F : C3.RealField r} {N} →
  Fixed.CanonicalRealityState F N →
  Finite.CanonicalCutoffRealCoordinateState F N
encodeState {F = F} {N = N} state =
  Finite.finite-real-coordinate-state
    (encodeValues (Fixed.positiveValues state))
    exact
  where
  exact :
    Finite.eraseSlots (encodeValues (Fixed.positiveValues state))
    ≡ Finite.canonicalCutoffSlots N
  exact =
    trans
      (encodeValuesSlots (Fixed.positiveValues state))
      (cong Finite.slotsForModes (Fixed.positiveModesExact state))

------------------------------------------------------------------------
-- The finite-real Round71 RHS is not a new field: it is the encoding of the
-- already literal Round71 vector field.
------------------------------------------------------------------------

encodedRound71RHS :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E) →
  Fixed.CanonicalRealityState F (Fixed.cutoff geometry) →
  Finite.CanonicalCutoffRealCoordinateState F (Fixed.cutoff geometry)
encodedRound71RHS geometry state =
  encodeState (Fixed.fixedCanonicalRealityVectorField geometry state)

encodedRound71RHSEntriesExact :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry)) →
  Finite.entries (encodedRound71RHS geometry state)
  ≡
  encodeValues
    (Fixed.positiveValues
      (Fixed.fixedCanonicalRealityVectorField geometry state))
encodedRound71RHSEntriesExact geometry state = refl

round851CanonicalRound71StateFiniteRealEncoded : Bool
round851CanonicalRound71StateFiniteRealEncoded = true

round851RealityDuplicatedInCoordinates : Bool
round851RealityDuplicatedInCoordinates = false

round851LiteralRound71RHSFiniteRealEncoded : Bool
round851LiteralRound71RHSFiniteRealEncoded = true

round851CoordinatePolynomialSameObjectClosed : Bool
round851CoordinatePolynomialSameObjectClosed = false

round851RealPicardApplied : Bool
round851RealPicardApplied = false

round851ClayPromotion : Bool
round851ClayPromotion = false

round851CanonicalRound71StateFiniteRealEncodedIsTrue :
  round851CanonicalRound71StateFiniteRealEncoded ≡ true
round851CanonicalRound71StateFiniteRealEncodedIsTrue = refl
