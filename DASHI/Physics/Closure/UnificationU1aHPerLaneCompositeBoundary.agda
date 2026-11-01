module DASHI.Physics.Closure.UnificationU1aHPerLaneCompositeBoundary where

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

data UnificationU1aHPerLaneClause : Set where
  nsLaneImported : UnificationU1aHPerLaneClause
  ymLaneImported : UnificationU1aHPerLaneClause
  globalLaneImported : UnificationU1aHPerLaneClause
  discriminantRouteFed : UnificationU1aHPerLaneClause
  hcRouteFed : UnificationU1aHPerLaneClause
  jvnConsumerRouteFed : UnificationU1aHPerLaneClause

canonicalUnificationU1aHPerLaneClauses : List UnificationU1aHPerLaneClause
canonicalUnificationU1aHPerLaneClauses =
  nsLaneImported
  ∷ ymLaneImported
  ∷ globalLaneImported
  ∷ discriminantRouteFed
  ∷ hcRouteFed
  ∷ jvnConsumerRouteFed
  ∷ []

unificationU1aHPerLaneClauseCount : Nat
unificationU1aHPerLaneClauseCount =
  listLength canonicalUnificationU1aHPerLaneClauses

unificationU1aHPerLaneClauseCountIs6 :
  unificationU1aHPerLaneClauseCount ≡ 6
unificationU1aHPerLaneClauseCountIs6 = refl

data UnificationU1aHPerLaneBlocker : Set where
  blocker-nsWriteupAuthorityStillOpen : UnificationU1aHPerLaneBlocker
  blocker-ymNonlinearAuthorityStillOpen : UnificationU1aHPerLaneBlocker
  blocker-signatureCliffordAuthorityStillOpen : UnificationU1aHPerLaneBlocker
  blocker-terminalPromotionForbidden : UnificationU1aHPerLaneBlocker

canonicalUnificationU1aHPerLaneBlockers : List UnificationU1aHPerLaneBlocker
canonicalUnificationU1aHPerLaneBlockers =
  blocker-nsWriteupAuthorityStillOpen
  ∷ blocker-ymNonlinearAuthorityStillOpen
  ∷ blocker-signatureCliffordAuthorityStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationU1aHPerLaneCompositeRecorded : Bool
UnificationU1aHPerLaneCompositeRecorded = true

UnificationU1aHPerLaneCompositeProved : Bool
UnificationU1aHPerLaneCompositeProved = false

record UnificationU1aHPerLaneCompositeBoundary : Set where
  field
    clauses : List UnificationU1aHPerLaneClause
    clausesCanonical : clauses ≡ canonicalUnificationU1aHPerLaneClauses
    blockers : List UnificationU1aHPerLaneBlocker
    blockersCanonical : blockers ≡ canonicalUnificationU1aHPerLaneBlockers
    clauseCountIs6 : unificationU1aHPerLaneClauseCount ≡ 6
    theoremStillFalse : UnificationU1aHPerLaneCompositeProved ≡ false

canonicalUnificationU1aHPerLaneCompositeBoundary :
  UnificationU1aHPerLaneCompositeBoundary
canonicalUnificationU1aHPerLaneCompositeBoundary =
  record
    { clauses = canonicalUnificationU1aHPerLaneClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUnificationU1aHPerLaneBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; theoremStillFalse = refl
    }

UnificationU1aHPerLaneCompositeRecordedIsTrue :
  UnificationU1aHPerLaneCompositeRecorded ≡ true
UnificationU1aHPerLaneCompositeRecordedIsTrue = refl
