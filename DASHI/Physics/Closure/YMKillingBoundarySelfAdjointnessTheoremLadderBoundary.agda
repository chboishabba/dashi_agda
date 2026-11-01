module DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremLadderBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

ym1Reference : String
ym1Reference =
  "DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremBoundary"

dominationReference : String
dominationReference =
  "DASHI.Physics.Closure.YMBochnerWeitzenbockHamiltonianDominationBoundary"

spectralMarginReference : String
spectralMarginReference =
  "DASHI.Physics.Closure.YMSpectralMarginFromHolonomyDominationBoundary"

osTransferReference : String
osTransferReference =
  "DASHI.Physics.Closure.YMBruhatTitsToOSLatticeTransferBoundary"

data YMTheoremLadderRung : Set where
  ym1SelfAdjointnessRung : YMTheoremLadderRung
  quotientHamiltonianRung : YMTheoremLadderRung
  dominationRung : YMTheoremLadderRung
  spectralMarginRung : YMTheoremLadderRung
  osTransferRung : YMTheoremLadderRung
  continuumAuthorityRung : YMTheoremLadderRung

canonicalYMTheoremLadderRungs : List YMTheoremLadderRung
canonicalYMTheoremLadderRungs =
  ym1SelfAdjointnessRung
  ∷ quotientHamiltonianRung
  ∷ dominationRung
  ∷ spectralMarginRung
  ∷ osTransferRung
  ∷ continuumAuthorityRung
  ∷ []

ymTheoremLadderRungCount : Nat
ymTheoremLadderRungCount =
  listLength canonicalYMTheoremLadderRungs

ymTheoremLadderRungCountIs6 : ymTheoremLadderRungCount ≡ 6
ymTheoremLadderRungCountIs6 = refl

data YMTheoremLadderBlocker : Set where
  blocker-ym1-unproved : YMTheoremLadderBlocker
  blocker-domination-unproved : YMTheoremLadderBlocker
  blocker-spectral-margin-unproved : YMTheoremLadderBlocker
  blocker-os-transfer-unproved : YMTheoremLadderBlocker
  blocker-ym-clay-unproved : YMTheoremLadderBlocker
  blocker-terminal-promotion-forbidden : YMTheoremLadderBlocker

canonicalYMTheoremLadderBlockers : List YMTheoremLadderBlocker
canonicalYMTheoremLadderBlockers =
  blocker-ym1-unproved
  ∷ blocker-domination-unproved
  ∷ blocker-spectral-margin-unproved
  ∷ blocker-os-transfer-unproved
  ∷ blocker-ym-clay-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

ymTheoremLadderBlockerCount : Nat
ymTheoremLadderBlockerCount =
  listLength canonicalYMTheoremLadderBlockers

ymTheoremLadderBlockerCountIs6 : ymTheoremLadderBlockerCount ≡ 6
ymTheoremLadderBlockerCountIs6 = refl

YMTheoremLadderPromoted : Bool
YMTheoremLadderPromoted = false

YMTheoremLadderPromotedIsFalse : YMTheoremLadderPromoted ≡ false
YMTheoremLadderPromotedIsFalse = refl

YMClayPromotedFromTheoremLadder : Bool
YMClayPromotedFromTheoremLadder = false

YMClayPromotedFromTheoremLadderIsFalse :
  YMClayPromotedFromTheoremLadder ≡ false
YMClayPromotedFromTheoremLadderIsFalse = refl

record YMKillingBoundarySelfAdjointnessTheoremLadderBoundary : Set where
  field
    ladderRungs : List YMTheoremLadderRung
    ladderRungsAreCanonical :
      ladderRungs ≡ canonicalYMTheoremLadderRungs
    blockers : List YMTheoremLadderBlocker
    blockersAreCanonical :
      blockers ≡ canonicalYMTheoremLadderBlockers
    rungCountIs6 :
      ymTheoremLadderRungCount ≡ 6
    blockerCountIs6 :
      ymTheoremLadderBlockerCount ≡ 6
    ladderStillFalse :
      YMTheoremLadderPromoted ≡ false
    ymClayStillFalse :
      YMClayPromotedFromTheoremLadder ≡ false

canonicalYMKillingBoundarySelfAdjointnessTheoremLadderBoundary :
  YMKillingBoundarySelfAdjointnessTheoremLadderBoundary
canonicalYMKillingBoundarySelfAdjointnessTheoremLadderBoundary =
  record
    { ladderRungs = canonicalYMTheoremLadderRungs
    ; ladderRungsAreCanonical = refl
    ; blockers = canonicalYMTheoremLadderBlockers
    ; blockersAreCanonical = refl
    ; rungCountIs6 = refl
    ; blockerCountIs6 = refl
    ; ladderStillFalse = refl
    ; ymClayStillFalse = refl
    }
