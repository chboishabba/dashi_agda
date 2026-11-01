module DASHI.Physics.OrbitSignatureDiscriminant where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Data.Empty using (⊥; ⊥-elim)
open import DASHI.Physics.OrbitProfileData as OPD

-- Candidate signatures in 4D.
data Signature : Set where
  sig40 : Signature
  sig31 : Signature
  sig22 : Signature
  sig13 : Signature
  sig04 : Signature

Profile : Set
Profile = List Nat

append3 : Profile → Profile → Profile → Profile
append3 a b c = (a ++ b) ++ c

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
ProfileOf sig40 = append3 (OrientationTag sig40 ∷ []) (OPD.shell1_p4_q0) (OPD.shell2_p4_q0)
ProfileOf sig31 = append3 (OrientationTag sig31 ∷ []) (OPD.shell1_p3_q1) (OPD.shell2_p3_q1)
ProfileOf sig22 = append3 (OrientationTag sig22 ∷ []) (OPD.shell1_p2_q2) (OPD.shell2_p2_q2)
ProfileOf sig13 = append3 (OrientationTag sig13 ∷ []) (OPD.shell1_p1_q3) (OPD.shell2_p1_q3)
ProfileOf sig04 = append3 (OrientationTag sig04 ∷ []) (OPD.shell1_p0_q4) (OPD.shell2_p0_q4)

-- Measured profile (from dashifine/orbit_profiles/orbit_profile_p3_q1_shell{1,2}.csv).
-- shell1: [24,6,2], shell2: 28×1; orientation tag 31
MeasuredProfile : Profile
MeasuredProfile = append3 (31 ∷ []) (OPD.shell1_p3_q1) (OPD.shell2_p3_q1)

MeasuredSignature : Signature
MeasuredSignature = sig31

measured-profile-def : MeasuredProfile ≡ ProfileOf MeasuredSignature
measured-profile-def = refl

OrientationTag-diff : OrientationTag sig31 ≢ OrientationTag sig13
OrientationTag-diff ()

OrientationTag-neq31-sig40 : 31 ≢ OrientationTag sig40
OrientationTag-neq31-sig40 ()

OrientationTag-neq31-sig22 : 31 ≢ OrientationTag sig22
OrientationTag-neq31-sig22 ()

OrientationTag-neq31-sig13 : 31 ≢ OrientationTag sig13
OrientationTag-neq31-sig13 ()

OrientationTag-neq31-sig04 : 31 ≢ OrientationTag sig04
OrientationTag-neq31-sig04 ()

headProfile :
  Profile → Nat
headProfile [] = 0
headProfile (x ∷ _) = x

headMeasured : headProfile MeasuredProfile ≡ 31
headMeasured = refl

headProfileOf : ∀ s → headProfile (ProfileOf s) ≡ OrientationTag s
headProfileOf sig40 = refl
headProfileOf sig31 = refl
headProfileOf sig22 = refl
headProfileOf sig13 = refl
headProfileOf sig04 = refl

Profile-sig31≢sig13 : ProfileOf sig31 ≢ ProfileOf sig13
Profile-sig31≢sig13 eq =
  OrientationTag-diff (cong headProfile eq)

SignatureFromMeasuredProfile :
  MeasuredProfile ≡ ProfileOf sig31 → MeasuredSignature ≡ sig31
SignatureFromMeasuredProfile _ = refl

SignatureFromMeasuredProfileUnique :
  ∀ s → MeasuredProfile ≡ ProfileOf s → s ≡ sig31
SignatureFromMeasuredProfileUnique sig31 _ = refl
SignatureFromMeasuredProfileUnique sig40 eq =
  ⊥-elim (OrientationTag-neq31-sig40 h)
  where
    h : 31 ≡ OrientationTag sig40
    h = trans (sym headMeasured)
          (trans (cong headProfile eq) (headProfileOf sig40))
SignatureFromMeasuredProfileUnique sig22 eq =
  ⊥-elim (OrientationTag-neq31-sig22 h)
  where
    h : 31 ≡ OrientationTag sig22
    h = trans (sym headMeasured)
          (trans (cong headProfile eq) (headProfileOf sig22))
SignatureFromMeasuredProfileUnique sig13 eq =
  ⊥-elim (OrientationTag-neq31-sig13 h)
  where
    h : 31 ≡ OrientationTag sig13
    h = trans (sym headMeasured)
          (trans (cong headProfile eq) (headProfileOf sig13))
SignatureFromMeasuredProfileUnique sig04 eq =
  ⊥-elim (OrientationTag-neq31-sig04 h)
  where
    h : 31 ≡ OrientationTag sig04
    h = trans (sym headMeasured)
          (trans (cong headProfile eq) (headProfileOf sig04))
open import DASHI.Physics.OrbitProfileData as OPD
