module DASHI.Physics.Closure.YMStandardLanguagePaperAssemblyBoundary where

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

data YMStandardLanguagePaperAssemblyClause : Set where
  gaugeLanguageTheoremAssemblyRecorded :
    YMStandardLanguagePaperAssemblyClause
  osWightmanCitationPackagingRecorded :
    YMStandardLanguagePaperAssemblyClause
  continuumMassGapStatementPackagingRecorded :
    YMStandardLanguagePaperAssemblyClause
  authorityAndReviewBlockersRecorded :
    YMStandardLanguagePaperAssemblyClause
  localMathematicsAlreadyPresent :
    YMStandardLanguagePaperAssemblyClause
  ymClayPromotionStillFalseRecorded :
    YMStandardLanguagePaperAssemblyClause
  terminalPromotionStillFalseRecorded :
    YMStandardLanguagePaperAssemblyClause

canonicalYMStandardLanguagePaperAssemblyClauses :
  List YMStandardLanguagePaperAssemblyClause
canonicalYMStandardLanguagePaperAssemblyClauses =
  gaugeLanguageTheoremAssemblyRecorded
  ∷ osWightmanCitationPackagingRecorded
  ∷ continuumMassGapStatementPackagingRecorded
  ∷ authorityAndReviewBlockersRecorded
  ∷ localMathematicsAlreadyPresent
  ∷ ymClayPromotionStillFalseRecorded
  ∷ terminalPromotionStillFalseRecorded
  ∷ []

ymStandardLanguagePaperAssemblyClauseCount : Nat
ymStandardLanguagePaperAssemblyClauseCount =
  listLength canonicalYMStandardLanguagePaperAssemblyClauses

ymStandardLanguagePaperAssemblyClauseCountIs7 :
  ymStandardLanguagePaperAssemblyClauseCount ≡ 7
ymStandardLanguagePaperAssemblyClauseCountIs7 = refl

data YMStandardLanguagePaperAssemblyBlocker : Set where
  blocker-gaugeLanguagePaperAssemblyStillOpen :
    YMStandardLanguagePaperAssemblyBlocker
  blocker-osWightmanCitationPackagingStillOpen :
    YMStandardLanguagePaperAssemblyBlocker
  blocker-continuumMassGapStatementPackagingStillOpen :
    YMStandardLanguagePaperAssemblyBlocker
  blocker-authorityReviewStillOpen :
    YMStandardLanguagePaperAssemblyBlocker
  blocker-ymClayPromotionForbidden :
    YMStandardLanguagePaperAssemblyBlocker
  blocker-terminalPromotionForbidden :
    YMStandardLanguagePaperAssemblyBlocker

canonicalYMStandardLanguagePaperAssemblyBlockers :
  List YMStandardLanguagePaperAssemblyBlocker
canonicalYMStandardLanguagePaperAssemblyBlockers =
  blocker-gaugeLanguagePaperAssemblyStillOpen
  ∷ blocker-osWightmanCitationPackagingStillOpen
  ∷ blocker-continuumMassGapStatementPackagingStillOpen
  ∷ blocker-authorityReviewStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ blocker-terminalPromotionForbidden
  ∷ []

ymStandardLanguagePaperAssemblyBlockerCount : Nat
ymStandardLanguagePaperAssemblyBlockerCount =
  listLength canonicalYMStandardLanguagePaperAssemblyBlockers

ymStandardLanguagePaperAssemblyBlockerCountIs6 :
  ymStandardLanguagePaperAssemblyBlockerCount ≡ 6
ymStandardLanguagePaperAssemblyBlockerCountIs6 = refl

YMStandardLanguagePaperAssemblyRecorded : Bool
YMStandardLanguagePaperAssemblyRecorded = true

YMStandardLanguagePaperAssemblyReady : Bool
YMStandardLanguagePaperAssemblyReady = false

YMStandardLanguagePaperPublished : Bool
YMStandardLanguagePaperPublished = false

YMClayPromotionFromStandardLanguagePaperAssembly : Bool
YMClayPromotionFromStandardLanguagePaperAssembly = false

TerminalPromotionFromStandardLanguagePaperAssembly : Bool
TerminalPromotionFromStandardLanguagePaperAssembly = false

record YMStandardLanguagePaperAssemblyBoundary : Set where
  field
    clauses : List YMStandardLanguagePaperAssemblyClause
    clausesCanonical : clauses ≡ canonicalYMStandardLanguagePaperAssemblyClauses
    blockers : List YMStandardLanguagePaperAssemblyBlocker
    blockersCanonical : blockers ≡ canonicalYMStandardLanguagePaperAssemblyBlockers
    clauseCountIs7 : ymStandardLanguagePaperAssemblyClauseCount ≡ 7
    blockerCountIs6 : ymStandardLanguagePaperAssemblyBlockerCount ≡ 6
    assemblyReadyStillFalse : YMStandardLanguagePaperAssemblyReady ≡ false
    paperPublishedStillFalse : YMStandardLanguagePaperPublished ≡ false
    ymClayPromotionStillFalse :
      YMClayPromotionFromStandardLanguagePaperAssembly ≡ false
    terminalPromotionStillFalse :
      TerminalPromotionFromStandardLanguagePaperAssembly ≡ false

canonicalYMStandardLanguagePaperAssemblyBoundary :
  YMStandardLanguagePaperAssemblyBoundary
canonicalYMStandardLanguagePaperAssemblyBoundary =
  record
    { clauses = canonicalYMStandardLanguagePaperAssemblyClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMStandardLanguagePaperAssemblyBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; blockerCountIs6 = refl
    ; assemblyReadyStillFalse = refl
    ; paperPublishedStillFalse = refl
    ; ymClayPromotionStillFalse = refl
    ; terminalPromotionStillFalse = refl
    }

YMStandardLanguagePaperAssemblyRecordedIsTrue :
  YMStandardLanguagePaperAssemblyRecorded ≡ true
YMStandardLanguagePaperAssemblyRecordedIsTrue = refl
