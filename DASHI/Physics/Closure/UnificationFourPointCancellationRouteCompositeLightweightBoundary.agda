module DASHI.Physics.Closure.UnificationFourPointCancellationRouteCompositeLightweightBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data UFourPointRouteClause : Set where
  hcFourPointInputImported : UFourPointRouteClause
  moduloNullLinearityRouteImported : UFourPointRouteClause
  plusMinusOneFourPointSpecializationRecorded : UFourPointRouteClause
  badFamilyExclusionRetained : UFourPointRouteClause
  parallelogramSocketRecorded : UFourPointRouteClause
  jvnConsumerStillBlocked : UFourPointRouteClause

canonicalUFourPointRouteClauses : List UFourPointRouteClause
canonicalUFourPointRouteClauses =
  hcFourPointInputImported
  ∷ moduloNullLinearityRouteImported
  ∷ plusMinusOneFourPointSpecializationRecorded
  ∷ badFamilyExclusionRetained
  ∷ parallelogramSocketRecorded
  ∷ jvnConsumerStillBlocked
  ∷ []

uFourPointRouteClauseCount : Nat
uFourPointRouteClauseCount = listLength canonicalUFourPointRouteClauses

uFourPointRouteClauseCountIs6 : uFourPointRouteClauseCount ≡ 6
uFourPointRouteClauseCountIs6 = refl

data UFourPointRouteBlocker : Set where
  blocker-fourPointCancellationTheoremStillOpen : UFourPointRouteBlocker
  blocker-parallelogramStillOpen : UFourPointRouteBlocker
  blocker-jordanVonNeumannStillOpen : UFourPointRouteBlocker
  blocker-terminalPromotionForbidden : UFourPointRouteBlocker

canonicalUFourPointRouteBlockers : List UFourPointRouteBlocker
canonicalUFourPointRouteBlockers =
  blocker-fourPointCancellationTheoremStillOpen
  ∷ blocker-parallelogramStillOpen
  ∷ blocker-jordanVonNeumannStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationFourPointCancellationRouteCompositeRecorded : Bool
UnificationFourPointCancellationRouteCompositeRecorded = true

UnificationFourPointCancellationRouteCompositeProved : Bool
UnificationFourPointCancellationRouteCompositeProved = false

record UnificationFourPointCancellationRouteCompositeLightweightBoundary : Set where
  field
    clauses : List UFourPointRouteClause
    clausesCanonical : clauses ≡ canonicalUFourPointRouteClauses
    blockers : List UFourPointRouteBlocker
    blockersCanonical : blockers ≡ canonicalUFourPointRouteBlockers
    clauseCountIs6 : uFourPointRouteClauseCount ≡ 6
    provedStillFalse :
      UnificationFourPointCancellationRouteCompositeProved ≡ false

canonicalUnificationFourPointCancellationRouteCompositeLightweightBoundary :
  UnificationFourPointCancellationRouteCompositeLightweightBoundary
canonicalUnificationFourPointCancellationRouteCompositeLightweightBoundary =
  record
    { clauses = canonicalUFourPointRouteClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUFourPointRouteBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

UnificationFourPointCancellationRouteCompositeRecordedIsTrue :
  UnificationFourPointCancellationRouteCompositeRecorded ≡ true
UnificationFourPointCancellationRouteCompositeRecordedIsTrue = refl
