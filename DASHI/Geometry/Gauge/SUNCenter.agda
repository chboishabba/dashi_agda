module DASHI.Geometry.Gauge.SUNCenter where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives

data CyclicGroupN (N : Nat) : Set where
  cyclic : Nat → CyclicGroupN N

data SUNCenterObligation : Set where
  needsConcretePhaseEmbedding : SUNCenterObligation
  needsWilsonLoopSensitivity  : SUNCenterObligation
  needsTHooftSectorRoute      : SUNCenterObligation

canonicalSUNCenterObligations : List SUNCenterObligation
canonicalSUNCenterObligations =
  needsConcretePhaseEmbedding
  ∷ needsWilsonLoopSensitivity
  ∷ needsTHooftSectorRoute
  ∷ []

record SUNCenter (N : Nat) : Set₁ where
  field
    centreCarrier : CyclicGroupN N
    centreOrder : Nat
    centreOrderIsN : centreOrder ≡ N
    actsByGlobalPhase : Bool
    actsByGlobalPhaseIsTrue : actsByGlobalPhase ≡ true
    openObligations : List SUNCenterObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalSUNCenterObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalSUNCenter : (N : Nat) → SUNCenter N
canonicalSUNCenter N = record
  { centreCarrier = cyclic 0
  ; centreOrder = N
  ; centreOrderIsN = refl
  ; actsByGlobalPhase = true
  ; actsByGlobalPhaseIsTrue = refl
  ; openObligations = canonicalSUNCenterObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
