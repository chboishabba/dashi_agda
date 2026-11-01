module DASHI.Geometry.SignatureExclusionFromOrbitProfile where

open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.SignatureUniqueness31 as SU using (SignatureLaw; sig31)
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

signatureLawFromProfileEq :
  ∀ (profile : List Nat) →
  profile ≡ OSD.ProfileOf OSD.sig31 →
  SignatureLaw
signatureLawFromProfileEq profile eq = record { forced = sig31 }

signatureFromProfileEq :
  ∀ (profile : List Nat) →
  profile ≡ OSD.ProfileOf OSD.sig31 →
  CTI.Signature
signatureFromProfileEq profile eq = CTI.sig31
