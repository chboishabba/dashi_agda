module DASHI.Physics.OrbitSignatureDiscriminant where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

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

postulate
  -- Orbit profile computed from the discrete shell for a signature.
  ProfileOf : Signature → Profile

  -- Injectivity of the profile map on the candidate set.
  OrbitProfileInjective :
    ∀ σ σ' → ProfileOf σ ≡ ProfileOf σ' → σ ≡ σ'

  -- Measured profile (e.g., imported from external scan).
  MeasuredProfile : Profile
  MeasuredSignature : Signature
  measured-profile-def : MeasuredProfile ≡ ProfileOf MeasuredSignature

SignatureFromMeasuredProfile :
  MeasuredProfile ≡ ProfileOf sig31 → MeasuredSignature ≡ sig31
SignatureFromMeasuredProfile h =
  OrbitProfileInjective MeasuredSignature sig31
    (trans (sym measured-profile-def) h)
