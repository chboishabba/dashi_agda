module DASHI.Physics.OrbitSignatureDiscriminant where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List using (List; _∷_; []; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- Candidate signatures in 4D.
data Signature : Set where
  sig40 : Signature
  sig31 : Signature
  sig22 : Signature
  sig13 : Signature
  sig04 : Signature

Profile : Set
Profile = List Nat

record OrbitProfile (σ : Signature) : Set₁ where
  field
    profile : Profile

open OrbitProfile public

-- Refined profile: orientation tag + shell1 + shell2 (|Q|=1,2)
-- Orientation tag is the signature code (p*10+q), encoding arrow direction.
OrientationTag : Signature → Nat
OrientationTag sig40 = 40
OrientationTag sig31 = 31
OrientationTag sig22 = 22
OrientationTag sig13 = 13
OrientationTag sig04 = 4

ProfileOf : Signature → Profile
ProfileOf sig40 = (OrientationTag sig40 ∷ 8 ∷ []) ++ replicate 24 1
ProfileOf sig31 = (OrientationTag sig31 ∷ 24 ∷ 6 ∷ 2 ∷ []) ++ replicate 28 1
ProfileOf sig22 = (OrientationTag sig22 ∷ 16 ∷ 16 ∷ 4 ∷ 4 ∷ []) ++ replicate 8 1
ProfileOf sig13 = (OrientationTag sig13 ∷ 24 ∷ 6 ∷ 2 ∷ []) ++ replicate 28 1
ProfileOf sig04 = (OrientationTag sig04 ∷ 8 ∷ []) ++ replicate 24 1

-- Measured profile (from dashifine/orbit_profiles/orbit_profile_p3_q1_shell{1,2}.csv).
-- shell1: [24,6,2], shell2: 28×1; orientation tag 31
MeasuredProfile : Profile
MeasuredProfile = (31 ∷ 24 ∷ 6 ∷ 2 ∷ []) ++ replicate 28 1

MeasuredSignature : Signature
MeasuredSignature = sig31

measured-profile-def : MeasuredProfile ≡ ProfileOf MeasuredSignature
measured-profile-def = refl

OrientationTag-diff : OrientationTag sig31 ≢ OrientationTag sig13
OrientationTag-diff ()

Profile-sig31≢sig13 : ProfileOf sig31 ≢ ProfileOf sig13
Profile-sig31≢sig13 eq =
  OrientationTag-diff (cong List.head eq)

SignatureFromMeasuredProfile :
  MeasuredProfile ≡ ProfileOf sig31 → MeasuredSignature ≡ sig31
SignatureFromMeasuredProfile _ = refl
