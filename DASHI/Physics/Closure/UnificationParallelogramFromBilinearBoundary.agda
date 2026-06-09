module DASHI.Physics.Closure.UnificationParallelogramFromBilinearBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
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

parallelogramText : String
parallelogramText =
  "G(s1+s2)+G(s1-s2)-2G(s1)-2G(s2)=0"

data UParallelogramClause : Set where
  discriminantCrossTermConsumed : UParallelogramClause
  nullClassSubspaceConsumed : UParallelogramClause
  bilinearPolarizationExpansionRecorded : UParallelogramClause
  crossTermsCancelBetweenPlusMinusRecorded : UParallelogramClause
  parallelogramLawRecorded : UParallelogramClause
  jordanVonNeumannRouteFed : UParallelogramClause
  signatureCliffordRemainLaterConsumers : UParallelogramClause

canonicalUParallelogramClauses : List UParallelogramClause
canonicalUParallelogramClauses =
  discriminantCrossTermConsumed
  ∷ nullClassSubspaceConsumed
  ∷ bilinearPolarizationExpansionRecorded
  ∷ crossTermsCancelBetweenPlusMinusRecorded
  ∷ parallelogramLawRecorded
  ∷ jordanVonNeumannRouteFed
  ∷ signatureCliffordRemainLaterConsumers
  ∷ []

uParallelogramClauseCount : Nat
uParallelogramClauseCount = listLength canonicalUParallelogramClauses

uParallelogramClauseCountIs7 : uParallelogramClauseCount ≡ 7
uParallelogramClauseCountIs7 = refl

data UParallelogramBlocker : Set where
  blocker-discriminantCrossTermTheoremStillOpen : UParallelogramBlocker
  blocker-nullClassSubspaceTheoremStillOpen : UParallelogramBlocker
  blocker-parallelogramTheoremStillOpen : UParallelogramBlocker
  blocker-jordanVonNeumannStillOpen : UParallelogramBlocker
  blocker-terminalPromotionForbidden : UParallelogramBlocker

canonicalUParallelogramBlockers : List UParallelogramBlocker
canonicalUParallelogramBlockers =
  blocker-discriminantCrossTermTheoremStillOpen
  ∷ blocker-nullClassSubspaceTheoremStillOpen
  ∷ blocker-parallelogramTheoremStillOpen
  ∷ blocker-jordanVonNeumannStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationParallelogramFromBilinearRecorded : Bool
UnificationParallelogramFromBilinearRecorded = true

UnificationParallelogramFromBilinearProved : Bool
UnificationParallelogramFromBilinearProved = false

record UnificationParallelogramFromBilinearBoundary : Set where
  field
    clauses : List UParallelogramClause
    clausesCanonical : clauses ≡ canonicalUParallelogramClauses
    blockers : List UParallelogramBlocker
    blockersCanonical : blockers ≡ canonicalUParallelogramBlockers
    clauseCountIs7 : uParallelogramClauseCount ≡ 7
    theoremStillFalse :
      UnificationParallelogramFromBilinearProved ≡ false

canonicalUnificationParallelogramFromBilinearBoundary :
  UnificationParallelogramFromBilinearBoundary
canonicalUnificationParallelogramFromBilinearBoundary =
  record
    { clauses = canonicalUParallelogramClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUParallelogramBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

UnificationParallelogramFromBilinearRecordedIsTrue :
  UnificationParallelogramFromBilinearRecorded ≡ true
UnificationParallelogramFromBilinearRecordedIsTrue = refl
