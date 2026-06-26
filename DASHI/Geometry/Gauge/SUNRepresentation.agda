module DASHI.Geometry.Gauge.SUNRepresentation where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives

data SUNRepKind : Set where
  fundamental     : SUNRepKind
  antiFundamental : SUNRepKind
  adjoint         : SUNRepKind
  tensorYoung     : Nat → SUNRepKind
  singlet         : SUNRepKind

data SUNRepresentationObligation : Set where
  needsConcreteRepSpace      : SUNRepresentationObligation
  needsCharacterTheoryBridge : SUNRepresentationObligation
  needsTensorProductControl  : SUNRepresentationObligation

canonicalSUNRepresentationObligations : List SUNRepresentationObligation
canonicalSUNRepresentationObligations =
  needsConcreteRepSpace
  ∷ needsCharacterTheoryBridge
  ∷ needsTensorProductControl
  ∷ []

record SUNRepresentation (N : Nat) : Set₁ where
  field
    repKind : SUNRepKind
    actionRespectsMult : Bool
    actionRespMultIsTrue : actionRespectsMult ≡ true
    openObligations : List SUNRepresentationObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalSUNRepresentationObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

fundamentalRepresentation : (N : Nat) → SUNRepresentation N
fundamentalRepresentation N = record
  { repKind = fundamental
  ; actionRespectsMult = true
  ; actionRespMultIsTrue = refl
  ; openObligations = canonicalSUNRepresentationObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }

adjointRepresentation : (N : Nat) → SUNRepresentation N
adjointRepresentation N = record
  { repKind = adjoint
  ; actionRespectsMult = true
  ; actionRespMultIsTrue = refl
  ; openObligations = canonicalSUNRepresentationObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
