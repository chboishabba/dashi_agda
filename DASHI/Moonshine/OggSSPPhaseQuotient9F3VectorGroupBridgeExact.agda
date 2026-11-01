module DASHI.Moonshine.OggSSPPhaseQuotient9F3VectorGroupBridgeExact where

------------------------------------------------------------------------
-- EXACT ORIGINAL PHASE-QUOTIENT-9 -> F3^2 GROUP LAW
--
-- Repo-native nine-phase group has zero (tri-low,tri-low), not the
-- visually middle/middle zero of the separate signed ternary sheet.
-- This bridge respects the ORIGINAL triXor addition before any recentering.
--
-- Group-level isomorphism to F3^2; NOT yet identification with E(F4),
-- its genuine Weil pairing, Monster 3B, or a VOA representation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Foundations.PhaseQuotientNonaryGroupSeparationExact as Nine
import DASHI.Moonshine.OggSSPEllipticNineWeilHeisenbergFiniteActionExact as Finite

toF3 : Base.TriTruth → Finite.F3
toF3 Base.tri-low = Finite.z
toF3 Base.tri-mid = Finite.p
toF3 Base.tri-high = Finite.m

fromF3 : Finite.F3 → Base.TriTruth
fromF3 Finite.z = Base.tri-low
fromF3 Finite.p = Base.tri-mid
fromF3 Finite.m = Base.tri-high

toF3FromF3 : (x : Finite.F3) → toF3 (fromF3 x) ≡ x
toF3FromF3 Finite.z = refl
toF3FromF3 Finite.p = refl
toF3FromF3 Finite.m = refl

fromF3ToF3 : (x : Base.TriTruth) → fromF3 (toF3 x) ≡ x
fromF3ToF3 Base.tri-low = refl
fromF3ToF3 Base.tri-mid = refl
fromF3ToF3 Base.tri-high = refl

phaseToVector : Phase.PhaseQuotient9 → Finite.V
phaseToVector (a , b) = toF3 a , toF3 b

vectorToPhase : Finite.V → Phase.PhaseQuotient9
vectorToPhase (a , b) = fromF3 a , fromF3 b

phaseVectorRoundTrip :
  (v : Phase.PhaseQuotient9) → vectorToPhase (phaseToVector v) ≡ v
phaseVectorRoundTrip (Base.tri-low , Base.tri-low) = refl
phaseVectorRoundTrip (Base.tri-low , Base.tri-mid) = refl
phaseVectorRoundTrip (Base.tri-low , Base.tri-high) = refl
phaseVectorRoundTrip (Base.tri-mid , Base.tri-low) = refl
phaseVectorRoundTrip (Base.tri-mid , Base.tri-mid) = refl
phaseVectorRoundTrip (Base.tri-mid , Base.tri-high) = refl
phaseVectorRoundTrip (Base.tri-high , Base.tri-low) = refl
phaseVectorRoundTrip (Base.tri-high , Base.tri-mid) = refl
phaseVectorRoundTrip (Base.tri-high , Base.tri-high) = refl

vectorPhaseRoundTrip :
  (v : Finite.V) → phaseToVector (vectorToPhase v) ≡ v
vectorPhaseRoundTrip (Finite.z , Finite.z) = refl
vectorPhaseRoundTrip (Finite.z , Finite.p) = refl
vectorPhaseRoundTrip (Finite.z , Finite.m) = refl
vectorPhaseRoundTrip (Finite.p , Finite.z) = refl
vectorPhaseRoundTrip (Finite.p , Finite.p) = refl
vectorPhaseRoundTrip (Finite.p , Finite.m) = refl
vectorPhaseRoundTrip (Finite.m , Finite.z) = refl
vectorPhaseRoundTrip (Finite.m , Finite.p) = refl
vectorPhaseRoundTrip (Finite.m , Finite.m) = refl

phaseIdentityGoesToZero :
  phaseToVector Nine.q9Zero ≡ (Finite.z , Finite.z)
phaseIdentityGoesToZero = refl

phaseAdditionPreserved :
  (v w : Phase.PhaseQuotient9) →
  phaseToVector (Nine.q9Add v w)
  ≡ Finite.vadd (phaseToVector v) (phaseToVector w)
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-low , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-mid , Base.tri-high) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-low) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-mid) (Base.tri-high , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-low , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-mid , Base.tri-high) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-low) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-mid) = refl
phaseAdditionPreserved (Base.tri-high , Base.tri-high) (Base.tri-high , Base.tri-high) = refl

------------------------------------------------------------------------
-- Transport the independently checked symplectic/anti-symplectic actions
-- onto the ORIGINAL phase group, not via cyclic NonaryTruth arithmetic.
------------------------------------------------------------------------

phaseShear : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
phaseShear v = vectorToPhase (Finite.shear (phaseToVector v))

phaseReflect : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
phaseReflect v = vectorToPhase (Finite.reflect (phaseToVector v))

phaseInvert : Phase.PhaseQuotient9 → Phase.PhaseQuotient9
phaseInvert v = vectorToPhase (Finite.inversion (phaseToVector v))

phaseAlternatingForm :
  Phase.PhaseQuotient9 → Phase.PhaseQuotient9 → Finite.F3
phaseAlternatingForm v w =
  Finite.omega (phaseToVector v) (phaseToVector w)

data ActualEllipticGroupRecognitionPaid : Set where
data ActualWeilPairingRecognitionPaid : Set where
data VOASelectedThreeBIntertwinerPaid : Set where

record PhaseNineF3VectorBoundary : Set where
  field
    originalTriXorGroupPreserved : Bool
    originalLowLowIdentityPreserved : Bool
    cyclicNonaryTruthMisidentifiedAsVectorGroup : Bool
    originalPhaseCarriesSymplecticActions : Bool
    ellipticAdditionRecognitionPaid : Bool
    actualWeilPairingRecognitionPaid : Bool
    selectedVOAIntertwinerPaid : Bool

open import Agda.Builtin.Bool using (Bool; true; false)

canonicalPhaseNineF3VectorBoundary : PhaseNineF3VectorBoundary
canonicalPhaseNineF3VectorBoundary =
  record
    { originalTriXorGroupPreserved = true
    ; originalLowLowIdentityPreserved = true
    ; cyclicNonaryTruthMisidentifiedAsVectorGroup = false
    ; originalPhaseCarriesSymplecticActions = true
    ; ellipticAdditionRecognitionPaid = false
    ; actualWeilPairingRecognitionPaid = false
    ; selectedVOAIntertwinerPaid = false
    }
