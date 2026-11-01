module DASHI.Physics.Closure.UnificationSignatureCliffordConsumerSocketBoundary where

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

data UnificationSignatureCliffordClause : Set where
  jvnSocketImported : UnificationSignatureCliffordClause
  cliffordSignatureTableImported : UnificationSignatureCliffordClause
  diracConsumerRowRecorded : UnificationSignatureCliffordClause
  majoranaConsumerRowRecorded : UnificationSignatureCliffordClause
  euclideanConsumerRowRecorded : UnificationSignatureCliffordClause
  terminalPromotionStillBlocked : UnificationSignatureCliffordClause

canonicalUnificationSignatureCliffordClauses :
  List UnificationSignatureCliffordClause
canonicalUnificationSignatureCliffordClauses =
  jvnSocketImported
  ∷ cliffordSignatureTableImported
  ∷ diracConsumerRowRecorded
  ∷ majoranaConsumerRowRecorded
  ∷ euclideanConsumerRowRecorded
  ∷ terminalPromotionStillBlocked
  ∷ []

unificationSignatureCliffordClauseCount : Nat
unificationSignatureCliffordClauseCount =
  listLength canonicalUnificationSignatureCliffordClauses

unificationSignatureCliffordClauseCountIs6 :
  unificationSignatureCliffordClauseCount ≡ 6
unificationSignatureCliffordClauseCountIs6 = refl

data UnificationSignatureCliffordBlocker : Set where
  blocker-signatureAuthorityStillOpen : UnificationSignatureCliffordBlocker
  blocker-cliffordAuthorityStillOpen : UnificationSignatureCliffordBlocker
  blocker-physicsAdapterStillOpen : UnificationSignatureCliffordBlocker
  blocker-terminalPromotionForbidden : UnificationSignatureCliffordBlocker

canonicalUnificationSignatureCliffordBlockers :
  List UnificationSignatureCliffordBlocker
canonicalUnificationSignatureCliffordBlockers =
  blocker-signatureAuthorityStillOpen
  ∷ blocker-cliffordAuthorityStillOpen
  ∷ blocker-physicsAdapterStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationSignatureCliffordConsumerSocketRecorded : Bool
UnificationSignatureCliffordConsumerSocketRecorded = true

UnificationSignatureCliffordConsumerSocketProved : Bool
UnificationSignatureCliffordConsumerSocketProved = false

record UnificationSignatureCliffordConsumerSocketBoundary : Set where
  field
    clauses : List UnificationSignatureCliffordClause
    clausesCanonical : clauses ≡ canonicalUnificationSignatureCliffordClauses
    blockers : List UnificationSignatureCliffordBlocker
    blockersCanonical : blockers ≡ canonicalUnificationSignatureCliffordBlockers
    clauseCountIs6 : unificationSignatureCliffordClauseCount ≡ 6
    theoremStillFalse :
      UnificationSignatureCliffordConsumerSocketProved ≡ false

canonicalUnificationSignatureCliffordConsumerSocketBoundary :
  UnificationSignatureCliffordConsumerSocketBoundary
canonicalUnificationSignatureCliffordConsumerSocketBoundary =
  record
    { clauses = canonicalUnificationSignatureCliffordClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUnificationSignatureCliffordBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; theoremStillFalse = refl
    }

UnificationSignatureCliffordConsumerSocketRecordedIsTrue :
  UnificationSignatureCliffordConsumerSocketRecorded ≡ true
UnificationSignatureCliffordConsumerSocketRecordedIsTrue = refl
