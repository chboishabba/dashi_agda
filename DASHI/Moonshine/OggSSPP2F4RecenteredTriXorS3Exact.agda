module DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact where

------------------------------------------------------------------------
-- RECENTER THE EXISTING TRI-XOR C3^2 BEFORE ELLIPTIC RECOGNITION
--
-- The established PhaseQuotient9 group has identity (low,low).
-- The signed elliptic-origin chart instead uses (mid,mid).
-- Transport the original group law along the literal cyclic translation
--   low -> mid -> high -> low,
-- so (mid,mid) really is an identity and signed inversion really is -I.
--
-- The C3 shear (a,b) -> (a+b,b) and Frobenius-type reflection
-- (a,b) -> (a,-b) are then honest additive automorphisms of this
-- recentered group. This is a DASHI *target representation*, not a theorem
-- that the arithmetic elliptic addition law already intertwines.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Base369 as Base
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Legacy
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

advance : Base.TriTruth → Base.TriTruth
advance Base.tri-low = Base.tri-mid
advance Base.tri-mid = Base.tri-high
advance Base.tri-high = Base.tri-low

retreat : Base.TriTruth → Base.TriTruth
retreat Base.tri-low = Base.tri-high
retreat Base.tri-mid = Base.tri-low
retreat Base.tri-high = Base.tri-mid

advanceRetreat : (t : Base.TriTruth) → advance (retreat t) ≡ t
advanceRetreat Base.tri-low = refl
advanceRetreat Base.tri-mid = refl
advanceRetreat Base.tri-high = refl

retreatAdvance : (t : Base.TriTruth) → retreat (advance t) ≡ t
retreatAdvance Base.tri-low = refl
retreatAdvance Base.tri-mid = refl
retreatAdvance Base.tri-high = refl

centerAdd : Base.TriTruth → Base.TriTruth → Base.TriTruth
centerAdd a b = advance (Base.triXor (retreat a) (retreat b))

centerNeg : Base.TriTruth → Base.TriTruth
centerNeg Base.tri-low = Base.tri-high
centerNeg Base.tri-mid = Base.tri-mid
centerNeg Base.tri-high = Base.tri-low

centerUnitLeft : (a : Base.TriTruth) →
  centerAdd Base.tri-mid a ≡ a
centerUnitLeft Base.tri-low = refl
centerUnitLeft Base.tri-mid = refl
centerUnitLeft Base.tri-high = refl

centerUnitRight : (a : Base.TriTruth) →
  centerAdd a Base.tri-mid ≡ a
centerUnitRight Base.tri-low = refl
centerUnitRight Base.tri-mid = refl
centerUnitRight Base.tri-high = refl

centerInverseRight : (a : Base.TriTruth) →
  centerAdd a (centerNeg a) ≡ Base.tri-mid
centerInverseRight Base.tri-low = refl
centerInverseRight Base.tri-mid = refl
centerInverseRight Base.tri-high = refl

centerInverseLeft : (a : Base.TriTruth) →
  centerAdd (centerNeg a) a ≡ Base.tri-mid
centerInverseLeft Base.tri-low = refl
centerInverseLeft Base.tri-mid = refl
centerInverseLeft Base.tri-high = refl

centerCommutative : (a b : Base.TriTruth) →
  centerAdd a b ≡ centerAdd b a
centerCommutative Base.tri-low Base.tri-low = refl
centerCommutative Base.tri-low Base.tri-mid = refl
centerCommutative Base.tri-low Base.tri-high = refl
centerCommutative Base.tri-mid Base.tri-low = refl
centerCommutative Base.tri-mid Base.tri-mid = refl
centerCommutative Base.tri-mid Base.tri-high = refl
centerCommutative Base.tri-high Base.tri-low = refl
centerCommutative Base.tri-high Base.tri-mid = refl
centerCommutative Base.tri-high Base.tri-high = refl

centerAssociative : (a b c : Base.TriTruth) →
  centerAdd a (centerAdd b c) ≡ centerAdd (centerAdd a b) c
centerAssociative Base.tri-low Base.tri-low Base.tri-low = refl
centerAssociative Base.tri-low Base.tri-low Base.tri-mid = refl
centerAssociative Base.tri-low Base.tri-low Base.tri-high = refl
centerAssociative Base.tri-low Base.tri-mid Base.tri-low = refl
centerAssociative Base.tri-low Base.tri-mid Base.tri-mid = refl
centerAssociative Base.tri-low Base.tri-mid Base.tri-high = refl
centerAssociative Base.tri-low Base.tri-high Base.tri-low = refl
centerAssociative Base.tri-low Base.tri-high Base.tri-mid = refl
centerAssociative Base.tri-low Base.tri-high Base.tri-high = refl
centerAssociative Base.tri-mid Base.tri-low Base.tri-low = refl
centerAssociative Base.tri-mid Base.tri-low Base.tri-mid = refl
centerAssociative Base.tri-mid Base.tri-low Base.tri-high = refl
centerAssociative Base.tri-mid Base.tri-mid Base.tri-low = refl
centerAssociative Base.tri-mid Base.tri-mid Base.tri-mid = refl
centerAssociative Base.tri-mid Base.tri-mid Base.tri-high = refl
centerAssociative Base.tri-mid Base.tri-high Base.tri-low = refl
centerAssociative Base.tri-mid Base.tri-high Base.tri-mid = refl
centerAssociative Base.tri-mid Base.tri-high Base.tri-high = refl
centerAssociative Base.tri-high Base.tri-low Base.tri-low = refl
centerAssociative Base.tri-high Base.tri-low Base.tri-mid = refl
centerAssociative Base.tri-high Base.tri-low Base.tri-high = refl
centerAssociative Base.tri-high Base.tri-mid Base.tri-low = refl
centerAssociative Base.tri-high Base.tri-mid Base.tri-mid = refl
centerAssociative Base.tri-high Base.tri-mid Base.tri-high = refl
centerAssociative Base.tri-high Base.tri-high Base.tri-low = refl
centerAssociative Base.tri-high Base.tri-high Base.tri-mid = refl
centerAssociative Base.tri-high Base.tri-high Base.tri-high = refl

CenteredNine : Set
CenteredNine = Phase.PhaseQuotient9

centerZero : CenteredNine
centerZero = Base.tri-mid , Base.tri-mid

centerPlus : CenteredNine → CenteredNine → CenteredNine
centerPlus (a , b) (c , d) = centerAdd a c , centerAdd b d

centerMinus : CenteredNine → CenteredNine
centerMinus (a , b) = centerNeg a , centerNeg b

toOriginal : CenteredNine → Phase.PhaseQuotient9
toOriginal (a , b) = retreat a , retreat b

fromOriginal : Phase.PhaseQuotient9 → CenteredNine
fromOriginal (a , b) = advance a , advance b

originalCenteredRoundTrip :
  (p : CenteredNine) → fromOriginal (toOriginal p) ≡ p
originalCenteredRoundTrip (Base.tri-low , Base.tri-low) = refl
originalCenteredRoundTrip (Base.tri-low , Base.tri-mid) = refl
originalCenteredRoundTrip (Base.tri-low , Base.tri-high) = refl
originalCenteredRoundTrip (Base.tri-mid , Base.tri-low) = refl
originalCenteredRoundTrip (Base.tri-mid , Base.tri-mid) = refl
originalCenteredRoundTrip (Base.tri-mid , Base.tri-high) = refl
originalCenteredRoundTrip (Base.tri-high , Base.tri-low) = refl
originalCenteredRoundTrip (Base.tri-high , Base.tri-mid) = refl
originalCenteredRoundTrip (Base.tri-high , Base.tri-high) = refl

centeredOriginalRoundTrip :
  (p : Phase.PhaseQuotient9) → toOriginal (fromOriginal p) ≡ p
centeredOriginalRoundTrip (Base.tri-low , Base.tri-low) = refl
centeredOriginalRoundTrip (Base.tri-low , Base.tri-mid) = refl
centeredOriginalRoundTrip (Base.tri-low , Base.tri-high) = refl
centeredOriginalRoundTrip (Base.tri-mid , Base.tri-low) = refl
centeredOriginalRoundTrip (Base.tri-mid , Base.tri-mid) = refl
centeredOriginalRoundTrip (Base.tri-mid , Base.tri-high) = refl
centeredOriginalRoundTrip (Base.tri-high , Base.tri-low) = refl
centeredOriginalRoundTrip (Base.tri-high , Base.tri-mid) = refl
centeredOriginalRoundTrip (Base.tri-high , Base.tri-high) = refl

legacyGroupTransport :
  (p q : CenteredNine) →
  toOriginal (centerPlus p q) ≡ Legacy.q9Add (toOriginal p) (toOriginal q)
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
legacyGroupTransport (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-high) = refl

centerZeroMapsToOriginalZero :
  toOriginal centerZero ≡ Legacy.q9Zero
centerZeroMapsToOriginalZero = refl

centeredSignedInversionPreservesIdentity :
  centerMinus centerZero ≡ centerZero
centeredSignedInversionPreservesIdentity = refl

frobPlane : CenteredNine → CenteredNine
frobPlane (a , b) = a , centerNeg b

shearPlane : CenteredNine → CenteredNine
shearPlane (a , b) = centerAdd a b , b

frobSquared : (p : CenteredNine) →
  frobPlane (frobPlane p) ≡ p
frobSquared (Base.tri-low , Base.tri-low) = refl
frobSquared (Base.tri-low , Base.tri-mid) = refl
frobSquared (Base.tri-low , Base.tri-high) = refl
frobSquared (Base.tri-mid , Base.tri-low) = refl
frobSquared (Base.tri-mid , Base.tri-mid) = refl
frobSquared (Base.tri-mid , Base.tri-high) = refl
frobSquared (Base.tri-high , Base.tri-low) = refl
frobSquared (Base.tri-high , Base.tri-mid) = refl
frobSquared (Base.tri-high , Base.tri-high) = refl

shearCubed : (p : CenteredNine) →
  shearPlane (shearPlane (shearPlane p)) ≡ p
shearCubed (Base.tri-low , Base.tri-low) = refl
shearCubed (Base.tri-low , Base.tri-mid) = refl
shearCubed (Base.tri-low , Base.tri-high) = refl
shearCubed (Base.tri-mid , Base.tri-low) = refl
shearCubed (Base.tri-mid , Base.tri-mid) = refl
shearCubed (Base.tri-mid , Base.tri-high) = refl
shearCubed (Base.tri-high , Base.tri-low) = refl
shearCubed (Base.tri-high , Base.tri-mid) = refl
shearCubed (Base.tri-high , Base.tri-high) = refl

frobConjugatesShear :
  (p : CenteredNine) →
  frobPlane (shearPlane (frobPlane p))
    ≡ shearPlane (shearPlane p)
frobConjugatesShear (Base.tri-low , Base.tri-low) = refl
frobConjugatesShear (Base.tri-low , Base.tri-mid) = refl
frobConjugatesShear (Base.tri-low , Base.tri-high) = refl
frobConjugatesShear (Base.tri-mid , Base.tri-low) = refl
frobConjugatesShear (Base.tri-mid , Base.tri-mid) = refl
frobConjugatesShear (Base.tri-mid , Base.tri-high) = refl
frobConjugatesShear (Base.tri-high , Base.tri-low) = refl
frobConjugatesShear (Base.tri-high , Base.tri-mid) = refl
frobConjugatesShear (Base.tri-high , Base.tri-high) = refl

frobAdditive :
  (p q : CenteredNine) →
  frobPlane (centerPlus p q)
    ≡ centerPlus (frobPlane p) (frobPlane q)
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
frobAdditive (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-high) = refl

shearAdditive :
  (p q : CenteredNine) →
  shearPlane (centerPlus p q)
    ≡ centerPlus (shearPlane p) (shearPlane q)
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
shearAdditive (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-high) = refl

frobFixesFirstAxis :
  (a : Base.TriTruth) →
  frobPlane (a , Base.tri-mid) ≡ (a , Base.tri-mid)
frobFixesFirstAxis Base.tri-low = refl
frobFixesFirstAxis Base.tri-mid = refl
frobFixesFirstAxis Base.tri-high = refl

shearFixesFirstAxis :
  (a : Base.TriTruth) →
  shearPlane (a , Base.tri-mid) ≡ (a , Base.tri-mid)
shearFixesFirstAxis Base.tri-low = refl
shearFixesFirstAxis Base.tri-mid = refl
shearFixesFirstAxis Base.tri-high = refl

frobFixedImpliesSecondZero :
  (p : CenteredNine) →
  frobPlane p ≡ p →
  proj₂ p ≡ Base.tri-mid
frobFixedImpliesSecondZero (Base.tri-low , Base.tri-low) ()
frobFixedImpliesSecondZero (Base.tri-low , Base.tri-mid) _ = refl
frobFixedImpliesSecondZero (Base.tri-low , Base.tri-high) ()
frobFixedImpliesSecondZero (Base.tri-mid , Base.tri-low) ()
frobFixedImpliesSecondZero (Base.tri-mid , Base.tri-mid) _ = refl
frobFixedImpliesSecondZero (Base.tri-mid , Base.tri-high) ()
frobFixedImpliesSecondZero (Base.tri-high , Base.tri-low) ()
frobFixedImpliesSecondZero (Base.tri-high , Base.tri-mid) _ = refl
frobFixedImpliesSecondZero (Base.tri-high , Base.tri-high) ()

shearFixedImpliesSecondZero :
  (p : CenteredNine) →
  shearPlane p ≡ p →
  proj₂ p ≡ Base.tri-mid
shearFixedImpliesSecondZero (Base.tri-low , Base.tri-low) ()
shearFixedImpliesSecondZero (Base.tri-low , Base.tri-mid) _ = refl
shearFixedImpliesSecondZero (Base.tri-low , Base.tri-high) ()
shearFixedImpliesSecondZero (Base.tri-mid , Base.tri-low) ()
shearFixedImpliesSecondZero (Base.tri-mid , Base.tri-mid) _ = refl
shearFixedImpliesSecondZero (Base.tri-mid , Base.tri-high) ()
shearFixedImpliesSecondZero (Base.tri-high , Base.tri-low) ()
shearFixedImpliesSecondZero (Base.tri-high , Base.tri-mid) _ = refl
shearFixedImpliesSecondZero (Base.tri-high , Base.tri-high) ()

inversionFixedOnlyCenter :
  (p : CenteredNine) →
  centerMinus p ≡ p →
  p ≡ centerZero
inversionFixedOnlyCenter (Base.tri-low , Base.tri-low) ()
inversionFixedOnlyCenter (Base.tri-low , Base.tri-mid) ()
inversionFixedOnlyCenter (Base.tri-low , Base.tri-high) ()
inversionFixedOnlyCenter (Base.tri-mid , Base.tri-low) ()
inversionFixedOnlyCenter (Base.tri-mid , Base.tri-mid) _ = refl
inversionFixedOnlyCenter (Base.tri-mid , Base.tri-high) ()
inversionFixedOnlyCenter (Base.tri-high , Base.tri-low) ()
inversionFixedOnlyCenter (Base.tri-high , Base.tri-mid) ()
inversionFixedOnlyCenter (Base.tri-high , Base.tri-high) ()

-- No construction in this owner turns arithmetic-coordinate maps into
-- homomorphisms of the independently selected Mathlib elliptic group.
record RecenteredTriXorS3Boundary : Set where
  constructor recentered-trixor-s3-boundary
  field
    actualLegacyTriXorOperationTransported : Bool
    centreNowGroupIdentity : Bool
    signedInversionNowAdditiveInverse : Bool
    frobeniusReflectionAdditive : Bool
    shearAdditive : Bool
    frobeniusOrderTwo : Bool
    shearOrderThree : Bool
    shearReflectionS3Relation : Bool
    fixedLocusProfilesDistinguishable : Bool
    actualEllipticAdditionIntertwinerConstructed : Bool

canonicalRecenteredTriXorS3Boundary : RecenteredTriXorS3Boundary
canonicalRecenteredTriXorS3Boundary =
  recentered-trixor-s3-boundary
    true true true true true true true true true false
