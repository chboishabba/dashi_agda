module DASHI.Physics.Closure.UnificationHCToModuloNullLinearityCompositeLightweightBoundary where

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

hcReference : String
hcReference =
  "DASHI.Physics.Closure.UnificationHierarchyConsistencyKillsFourPointDefectBoundary"

childReference : String
childReference =
  "DASHI.Physics.Closure.UnificationCrossTermChildCompositeLightweightBoundary"

transportReference : String
transportReference =
  "DASHI.Physics.Closure.UnificationNullTransportModuloNullConsumerLightweightBoundary"

data UHCModuloClause : Set where
  h1ScalingRouteImported : UHCModuloClause
  crossTermNullChildImported : UHCModuloClause
  nullTransportConsumerImported : UHCModuloClause
  representativeIndependenceRouted : UHCModuloClause
  moduloNullLinearitySocketRecorded : UHCModuloClause
  heavyConsumerReplacementRecorded : UHCModuloClause

canonicalUHCModuloClauses : List UHCModuloClause
canonicalUHCModuloClauses =
  h1ScalingRouteImported
  ∷ crossTermNullChildImported
  ∷ nullTransportConsumerImported
  ∷ representativeIndependenceRouted
  ∷ moduloNullLinearitySocketRecorded
  ∷ heavyConsumerReplacementRecorded
  ∷ []

uHCModuloClauseCount : Nat
uHCModuloClauseCount = listLength canonicalUHCModuloClauses

uHCModuloClauseCountIs6 : uHCModuloClauseCount ≡ 6
uHCModuloClauseCountIs6 = refl

data UHCModuloBlocker : Set where
  blocker-hcTheoremStillOpen : UHCModuloBlocker
  blocker-moduloNullLinearityStillOpen : UHCModuloBlocker
  blocker-fourPointStillOpen : UHCModuloBlocker
  blocker-terminalPromotionForbidden : UHCModuloBlocker

canonicalUHCModuloBlockers : List UHCModuloBlocker
canonicalUHCModuloBlockers =
  blocker-hcTheoremStillOpen
  ∷ blocker-moduloNullLinearityStillOpen
  ∷ blocker-fourPointStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationHCToModuloNullLinearityCompositeRecorded : Bool
UnificationHCToModuloNullLinearityCompositeRecorded = true

UnificationHCToModuloNullLinearityCompositeProved : Bool
UnificationHCToModuloNullLinearityCompositeProved = false

record UnificationHCToModuloNullLinearityCompositeLightweightBoundary : Set where
  field
    clauses : List UHCModuloClause
    clausesCanonical : clauses ≡ canonicalUHCModuloClauses
    blockers : List UHCModuloBlocker
    blockersCanonical : blockers ≡ canonicalUHCModuloBlockers
    clauseCountIs6 : uHCModuloClauseCount ≡ 6
    provedStillFalse :
      UnificationHCToModuloNullLinearityCompositeProved ≡ false

canonicalUnificationHCToModuloNullLinearityCompositeLightweightBoundary :
  UnificationHCToModuloNullLinearityCompositeLightweightBoundary
canonicalUnificationHCToModuloNullLinearityCompositeLightweightBoundary =
  record
    { clauses = canonicalUHCModuloClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUHCModuloBlockers
    ; blockersCanonical = refl
    ; clauseCountIs6 = refl
    ; provedStillFalse = refl
    }

UnificationHCToModuloNullLinearityCompositeRecordedIsTrue :
  UnificationHCToModuloNullLinearityCompositeRecorded ≡ true
UnificationHCToModuloNullLinearityCompositeRecordedIsTrue = refl
