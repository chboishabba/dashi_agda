module DASHI.Physics.Closure.YMReflectionPositivityFullTheoremAssemblyBoundary where

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

data YMReflectionPositivityAssemblyClause : Set where
  tauThetaCommutativityImported : YMReflectionPositivityAssemblyClause
  actionSplitImported : YMReflectionPositivityAssemblyClause
  transferMatrixHermitianImported : YMReflectionPositivityAssemblyClause
  osAxiomImported : YMReflectionPositivityAssemblyClause
  boundaryConventionParentFed : YMReflectionPositivityAssemblyClause
  osWightmanRouteUnlockedOnlyAfterRP : YMReflectionPositivityAssemblyClause
  clayPromotionStillBlocked : YMReflectionPositivityAssemblyClause

canonicalYMReflectionPositivityAssemblyClauses :
  List YMReflectionPositivityAssemblyClause
canonicalYMReflectionPositivityAssemblyClauses =
  tauThetaCommutativityImported
  ∷ actionSplitImported
  ∷ transferMatrixHermitianImported
  ∷ osAxiomImported
  ∷ boundaryConventionParentFed
  ∷ osWightmanRouteUnlockedOnlyAfterRP
  ∷ clayPromotionStillBlocked
  ∷ []

ymReflectionPositivityAssemblyClauseCount : Nat
ymReflectionPositivityAssemblyClauseCount =
  listLength canonicalYMReflectionPositivityAssemblyClauses

ymReflectionPositivityAssemblyClauseCountIs7 :
  ymReflectionPositivityAssemblyClauseCount ≡ 7
ymReflectionPositivityAssemblyClauseCountIs7 = refl

data YMReflectionPositivityAssemblyBlocker : Set where
  blocker-rpTheoremAuthorityStillOpen : YMReflectionPositivityAssemblyBlocker
  blocker-osWightmanAuthorityStillOpen : YMReflectionPositivityAssemblyBlocker
  blocker-finalMassGapAuthorityStillOpen : YMReflectionPositivityAssemblyBlocker
  blocker-ymClayPromotionForbidden : YMReflectionPositivityAssemblyBlocker

canonicalYMReflectionPositivityAssemblyBlockers :
  List YMReflectionPositivityAssemblyBlocker
canonicalYMReflectionPositivityAssemblyBlockers =
  blocker-rpTheoremAuthorityStillOpen
  ∷ blocker-osWightmanAuthorityStillOpen
  ∷ blocker-finalMassGapAuthorityStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ []

YMReflectionPositivityFullTheoremAssemblyRecorded : Bool
YMReflectionPositivityFullTheoremAssemblyRecorded = true

YMReflectionPositivityFullTheoremAssemblyProved : Bool
YMReflectionPositivityFullTheoremAssemblyProved = false

record YMReflectionPositivityFullTheoremAssemblyBoundary : Set where
  field
    clauses : List YMReflectionPositivityAssemblyClause
    clausesCanonical : clauses ≡ canonicalYMReflectionPositivityAssemblyClauses
    blockers : List YMReflectionPositivityAssemblyBlocker
    blockersCanonical : blockers ≡ canonicalYMReflectionPositivityAssemblyBlockers
    clauseCountIs7 : ymReflectionPositivityAssemblyClauseCount ≡ 7
    theoremStillFalse : YMReflectionPositivityFullTheoremAssemblyProved ≡ false

canonicalYMReflectionPositivityFullTheoremAssemblyBoundary :
  YMReflectionPositivityFullTheoremAssemblyBoundary
canonicalYMReflectionPositivityFullTheoremAssemblyBoundary =
  record
    { clauses = canonicalYMReflectionPositivityAssemblyClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMReflectionPositivityAssemblyBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; theoremStillFalse = refl
    }

YMReflectionPositivityFullTheoremAssemblyRecordedIsTrue :
  YMReflectionPositivityFullTheoremAssemblyRecorded ≡ true
YMReflectionPositivityFullTheoremAssemblyRecordedIsTrue = refl
