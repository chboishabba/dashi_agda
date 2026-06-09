module DASHI.Physics.Closure.YMContinuumMassGapFinalAssemblyBoundary where

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

finalAssemblyFormulaText : String
finalAssemblyFormulaText =
  "Delta_phys = gamma_infty * Lambda_YM * C_G > 0"

data YMFinalAssemblyClause : Set where
  finiteGapLimitInputRecorded : YMFinalAssemblyClause
  rgInvariantScaleInputRecorded : YMFinalAssemblyClause
  stepScalingGlobalBoundConsumed : YMFinalAssemblyClause
  btToEuclideanTransferInputRecorded : YMFinalAssemblyClause
  osWightmanSocketInputRecorded : YMFinalAssemblyClause
  finalMassGapFormulaRecorded : YMFinalAssemblyClause
  reflectionPositivityBoundaryStillNamed : YMFinalAssemblyClause

canonicalYMFinalAssemblyClauses : List YMFinalAssemblyClause
canonicalYMFinalAssemblyClauses =
  finiteGapLimitInputRecorded
  ∷ rgInvariantScaleInputRecorded
  ∷ stepScalingGlobalBoundConsumed
  ∷ btToEuclideanTransferInputRecorded
  ∷ osWightmanSocketInputRecorded
  ∷ finalMassGapFormulaRecorded
  ∷ reflectionPositivityBoundaryStillNamed
  ∷ []

ymFinalAssemblyClauseCount : Nat
ymFinalAssemblyClauseCount = listLength canonicalYMFinalAssemblyClauses

ymFinalAssemblyClauseCountIs7 : ymFinalAssemblyClauseCount ≡ 7
ymFinalAssemblyClauseCountIs7 = refl

data YMFinalAssemblyBlocker : Set where
  blocker-reflectionPositivityBoundaryStillOpen : YMFinalAssemblyBlocker
  blocker-osWightmanAuthorityStillOpen : YMFinalAssemblyBlocker
  blocker-finalContinuumAssemblyProofStillOpen : YMFinalAssemblyBlocker
  blocker-ymClayPromotionForbidden : YMFinalAssemblyBlocker

canonicalYMFinalAssemblyBlockers : List YMFinalAssemblyBlocker
canonicalYMFinalAssemblyBlockers =
  blocker-reflectionPositivityBoundaryStillOpen
  ∷ blocker-osWightmanAuthorityStillOpen
  ∷ blocker-finalContinuumAssemblyProofStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMContinuumMassGapFinalAssemblyRecorded : Bool
YMContinuumMassGapFinalAssemblyRecorded = true

YMContinuumMassGapFinalAssemblyProved : Bool
YMContinuumMassGapFinalAssemblyProved = false

record YMContinuumMassGapFinalAssemblyBoundary : Set where
  field
    clauses : List YMFinalAssemblyClause
    clausesCanonical : clauses ≡ canonicalYMFinalAssemblyClauses
    blockers : List YMFinalAssemblyBlocker
    blockersCanonical : blockers ≡ canonicalYMFinalAssemblyBlockers
    clauseCountIs7 : ymFinalAssemblyClauseCount ≡ 7
    theoremStillFalse :
      YMContinuumMassGapFinalAssemblyProved ≡ false

canonicalYMContinuumMassGapFinalAssemblyBoundary :
  YMContinuumMassGapFinalAssemblyBoundary
canonicalYMContinuumMassGapFinalAssemblyBoundary =
  record
    { clauses = canonicalYMFinalAssemblyClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMFinalAssemblyBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMContinuumMassGapFinalAssemblyRecordedIsTrue :
  YMContinuumMassGapFinalAssemblyRecorded ≡ true
YMContinuumMassGapFinalAssemblyRecordedIsTrue = refl
