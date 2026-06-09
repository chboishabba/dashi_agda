module DASHI.Physics.Closure.UnificationHCToFourPointInputCompositeLightweightBoundary where

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

hcModuloReference : String
hcModuloReference =
  "DASHI.Physics.Closure.UnificationHCToModuloNullLinearityCompositeLightweightBoundary"

fourPointPipelineReference : String
fourPointPipelineReference =
  "scripts/unification_cross_term_to_four_point_pipeline_harness.py"

data UHCFourPointClause : Set where
  hcToModuloNullImported : UHCFourPointClause
  plusMinusOneSpecializationRecorded : UHCFourPointClause
  fourPointResidualInputReady : UHCFourPointClause
  badFamilySeparationRetained : UHCFourPointClause
  parallelogramConsumerStillBlocked : UHCFourPointClause

canonicalUHCFourPointClauses : List UHCFourPointClause
canonicalUHCFourPointClauses =
  hcToModuloNullImported
  ∷ plusMinusOneSpecializationRecorded
  ∷ fourPointResidualInputReady
  ∷ badFamilySeparationRetained
  ∷ parallelogramConsumerStillBlocked
  ∷ []

uHCFourPointClauseCount : Nat
uHCFourPointClauseCount = listLength canonicalUHCFourPointClauses

uHCFourPointClauseCountIs5 : uHCFourPointClauseCount ≡ 5
uHCFourPointClauseCountIs5 = refl

data UHCFourPointBlocker : Set where
  blocker-fourPointTheoremStillOpen : UHCFourPointBlocker
  blocker-parallelogramStillOpen : UHCFourPointBlocker
  blocker-jordanVonNeumannStillOpen : UHCFourPointBlocker
  blocker-terminalPromotionForbidden : UHCFourPointBlocker

canonicalUHCFourPointBlockers : List UHCFourPointBlocker
canonicalUHCFourPointBlockers =
  blocker-fourPointTheoremStillOpen
  ∷ blocker-parallelogramStillOpen
  ∷ blocker-jordanVonNeumannStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ []

UnificationHCToFourPointInputCompositeRecorded : Bool
UnificationHCToFourPointInputCompositeRecorded = true

UnificationHCToFourPointInputCompositeProved : Bool
UnificationHCToFourPointInputCompositeProved = false

record UnificationHCToFourPointInputCompositeLightweightBoundary : Set where
  field
    clauses : List UHCFourPointClause
    clausesCanonical : clauses ≡ canonicalUHCFourPointClauses
    blockers : List UHCFourPointBlocker
    blockersCanonical : blockers ≡ canonicalUHCFourPointBlockers
    clauseCountIs5 : uHCFourPointClauseCount ≡ 5
    provedStillFalse : UnificationHCToFourPointInputCompositeProved ≡ false

canonicalUnificationHCToFourPointInputCompositeLightweightBoundary :
  UnificationHCToFourPointInputCompositeLightweightBoundary
canonicalUnificationHCToFourPointInputCompositeLightweightBoundary =
  record
    { clauses = canonicalUHCFourPointClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUHCFourPointBlockers
    ; blockersCanonical = refl
    ; clauseCountIs5 = refl
    ; provedStillFalse = refl
    }

UnificationHCToFourPointInputCompositeRecordedIsTrue :
  UnificationHCToFourPointInputCompositeRecorded ≡ true
UnificationHCToFourPointInputCompositeRecordedIsTrue = refl
