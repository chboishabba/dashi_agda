module DASHI.Physics.Closure.YMPaperSubmissionPacketBoundary where

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

data YMPaperSubmissionPacketClause : Set where
  paperNarrativeAssembledRecorded :
    YMPaperSubmissionPacketClause
  citationPacketRecorded :
    YMPaperSubmissionPacketClause
  theoremAndClaimScopeStatementRecorded :
    YMPaperSubmissionPacketClause
  reviewerFacingAuthorityBlockersRecorded :
    YMPaperSubmissionPacketClause
  submissionStillFalseRecorded :
    YMPaperSubmissionPacketClause
  clayPromotionStillFalseRecorded :
    YMPaperSubmissionPacketClause
  terminalPromotionStillFalseRecorded :
    YMPaperSubmissionPacketClause

canonicalYMPaperSubmissionPacketClauses :
  List YMPaperSubmissionPacketClause
canonicalYMPaperSubmissionPacketClauses =
  paperNarrativeAssembledRecorded
  ∷ citationPacketRecorded
  ∷ theoremAndClaimScopeStatementRecorded
  ∷ reviewerFacingAuthorityBlockersRecorded
  ∷ submissionStillFalseRecorded
  ∷ clayPromotionStillFalseRecorded
  ∷ terminalPromotionStillFalseRecorded
  ∷ []

ymPaperSubmissionPacketClauseCount : Nat
ymPaperSubmissionPacketClauseCount =
  listLength canonicalYMPaperSubmissionPacketClauses

ymPaperSubmissionPacketClauseCountIs7 :
  ymPaperSubmissionPacketClauseCount ≡ 7
ymPaperSubmissionPacketClauseCountIs7 = refl

data YMPaperSubmissionPacketBlocker : Set where
  blocker-paperNarrativePacketStillOpen :
    YMPaperSubmissionPacketBlocker
  blocker-citationPacketStillOpen :
    YMPaperSubmissionPacketBlocker
  blocker-theoremAndClaimScopeStatementStillOpen :
    YMPaperSubmissionPacketBlocker
  blocker-reviewerFacingAuthorityPacketStillOpen :
    YMPaperSubmissionPacketBlocker
  blocker-ymClayPromotionForbidden :
    YMPaperSubmissionPacketBlocker
  blocker-terminalPromotionForbidden :
    YMPaperSubmissionPacketBlocker

canonicalYMPaperSubmissionPacketBlockers :
  List YMPaperSubmissionPacketBlocker
canonicalYMPaperSubmissionPacketBlockers =
  blocker-paperNarrativePacketStillOpen
  ∷ blocker-citationPacketStillOpen
  ∷ blocker-theoremAndClaimScopeStatementStillOpen
  ∷ blocker-reviewerFacingAuthorityPacketStillOpen
  ∷ blocker-ymClayPromotionForbidden
  ∷ blocker-terminalPromotionForbidden
  ∷ []

ymPaperSubmissionPacketBlockerCount : Nat
ymPaperSubmissionPacketBlockerCount =
  listLength canonicalYMPaperSubmissionPacketBlockers

ymPaperSubmissionPacketBlockerCountIs6 :
  ymPaperSubmissionPacketBlockerCount ≡ 6
ymPaperSubmissionPacketBlockerCountIs6 = refl

YMPaperSubmissionPacketRecorded : Bool
YMPaperSubmissionPacketRecorded = true

YMPaperSubmissionPacketReady : Bool
YMPaperSubmissionPacketReady = false

YMPaperSubmitted : Bool
YMPaperSubmitted = false

YMClayPromotionFromSubmissionPacket : Bool
YMClayPromotionFromSubmissionPacket = false

TerminalPromotionFromSubmissionPacket : Bool
TerminalPromotionFromSubmissionPacket = false

record YMPaperSubmissionPacketBoundary : Set where
  field
    clauses : List YMPaperSubmissionPacketClause
    clausesCanonical : clauses ≡ canonicalYMPaperSubmissionPacketClauses
    blockers : List YMPaperSubmissionPacketBlocker
    blockersCanonical : blockers ≡ canonicalYMPaperSubmissionPacketBlockers
    clauseCountIs7 : ymPaperSubmissionPacketClauseCount ≡ 7
    blockerCountIs6 : ymPaperSubmissionPacketBlockerCount ≡ 6
    packetReadyStillFalse : YMPaperSubmissionPacketReady ≡ false
    paperSubmittedStillFalse : YMPaperSubmitted ≡ false
    ymClayPromotionStillFalse :
      YMClayPromotionFromSubmissionPacket ≡ false
    terminalPromotionStillFalse :
      TerminalPromotionFromSubmissionPacket ≡ false

canonicalYMPaperSubmissionPacketBoundary :
  YMPaperSubmissionPacketBoundary
canonicalYMPaperSubmissionPacketBoundary =
  record
    { clauses = canonicalYMPaperSubmissionPacketClauses
    ; clausesCanonical = refl
    ; blockers = canonicalYMPaperSubmissionPacketBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; blockerCountIs6 = refl
    ; packetReadyStillFalse = refl
    ; paperSubmittedStillFalse = refl
    ; ymClayPromotionStillFalse = refl
    ; terminalPromotionStillFalse = refl
    }

YMPaperSubmissionPacketRecordedIsTrue :
  YMPaperSubmissionPacketRecorded ≡ true
YMPaperSubmissionPacketRecordedIsTrue = refl
