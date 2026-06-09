module DASHI.Physics.Closure.UnificationAuthorityReviewPacketBoundary where

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

data UnificationAuthorityReviewPacketClause : Set where
  laneJustificationSummaryRecorded :
    UnificationAuthorityReviewPacketClause
  quotientRepresentativeLegitimacySummaryRecorded :
    UnificationAuthorityReviewPacketClause
  signatureCliffordConsumerSummaryRecorded :
    UnificationAuthorityReviewPacketClause
  reviewerFacingAuthorityBlockersRecorded :
    UnificationAuthorityReviewPacketClause
  reviewPacketStillFalseRecorded :
    UnificationAuthorityReviewPacketClause
  terminalPromotionStillFalseRecorded :
    UnificationAuthorityReviewPacketClause
  localMathematicsAlreadyPresentRecorded :
    UnificationAuthorityReviewPacketClause

canonicalUnificationAuthorityReviewPacketClauses :
  List UnificationAuthorityReviewPacketClause
canonicalUnificationAuthorityReviewPacketClauses =
  laneJustificationSummaryRecorded
  ∷ quotientRepresentativeLegitimacySummaryRecorded
  ∷ signatureCliffordConsumerSummaryRecorded
  ∷ reviewerFacingAuthorityBlockersRecorded
  ∷ reviewPacketStillFalseRecorded
  ∷ terminalPromotionStillFalseRecorded
  ∷ localMathematicsAlreadyPresentRecorded
  ∷ []

unificationAuthorityReviewPacketClauseCount : Nat
unificationAuthorityReviewPacketClauseCount =
  listLength canonicalUnificationAuthorityReviewPacketClauses

unificationAuthorityReviewPacketClauseCountIs7 :
  unificationAuthorityReviewPacketClauseCount ≡ 7
unificationAuthorityReviewPacketClauseCountIs7 = refl

data UnificationAuthorityReviewPacketBlocker : Set where
  blocker-laneJustificationSummaryStillOpen :
    UnificationAuthorityReviewPacketBlocker
  blocker-quotientRepresentativeLegitimacySummaryStillOpen :
    UnificationAuthorityReviewPacketBlocker
  blocker-signatureCliffordConsumerSummaryStillOpen :
    UnificationAuthorityReviewPacketBlocker
  blocker-reviewerFacingAuthorityPacketStillOpen :
    UnificationAuthorityReviewPacketBlocker
  blocker-reviewAcceptanceStillOpen :
    UnificationAuthorityReviewPacketBlocker
  blocker-terminalPromotionForbidden :
    UnificationAuthorityReviewPacketBlocker
  blocker-unificationAuthorityClosureStillOpen :
    UnificationAuthorityReviewPacketBlocker

canonicalUnificationAuthorityReviewPacketBlockers :
  List UnificationAuthorityReviewPacketBlocker
canonicalUnificationAuthorityReviewPacketBlockers =
  blocker-laneJustificationSummaryStillOpen
  ∷ blocker-quotientRepresentativeLegitimacySummaryStillOpen
  ∷ blocker-signatureCliffordConsumerSummaryStillOpen
  ∷ blocker-reviewerFacingAuthorityPacketStillOpen
  ∷ blocker-reviewAcceptanceStillOpen
  ∷ blocker-terminalPromotionForbidden
  ∷ blocker-unificationAuthorityClosureStillOpen
  ∷ []

unificationAuthorityReviewPacketBlockerCount : Nat
unificationAuthorityReviewPacketBlockerCount =
  listLength canonicalUnificationAuthorityReviewPacketBlockers

unificationAuthorityReviewPacketBlockerCountIs7 :
  unificationAuthorityReviewPacketBlockerCount ≡ 7
unificationAuthorityReviewPacketBlockerCountIs7 = refl

UnificationAuthorityReviewPacketRecorded : Bool
UnificationAuthorityReviewPacketRecorded = true

UnificationAuthorityReviewPacketReady : Bool
UnificationAuthorityReviewPacketReady = false

TerminalPromotionFromUnificationAuthorityReviewPacket : Bool
TerminalPromotionFromUnificationAuthorityReviewPacket = false

record UnificationAuthorityReviewPacketBoundary : Set where
  field
    clauses : List UnificationAuthorityReviewPacketClause
    clausesCanonical :
      clauses ≡ canonicalUnificationAuthorityReviewPacketClauses
    blockers : List UnificationAuthorityReviewPacketBlocker
    blockersCanonical :
      blockers ≡ canonicalUnificationAuthorityReviewPacketBlockers
    clauseCountIs7 :
      unificationAuthorityReviewPacketClauseCount ≡ 7
    blockerCountIs7 :
      unificationAuthorityReviewPacketBlockerCount ≡ 7
    packetRecordedTrue :
      UnificationAuthorityReviewPacketRecorded ≡ true
    packetReadyStillFalse :
      UnificationAuthorityReviewPacketReady ≡ false
    terminalPromotionStillFalse :
      TerminalPromotionFromUnificationAuthorityReviewPacket ≡ false

canonicalUnificationAuthorityReviewPacketBoundary :
  UnificationAuthorityReviewPacketBoundary
canonicalUnificationAuthorityReviewPacketBoundary =
  record
    { clauses = canonicalUnificationAuthorityReviewPacketClauses
    ; clausesCanonical = refl
    ; blockers = canonicalUnificationAuthorityReviewPacketBlockers
    ; blockersCanonical = refl
    ; clauseCountIs7 = refl
    ; blockerCountIs7 = refl
    ; packetRecordedTrue = refl
    ; packetReadyStillFalse = refl
    ; terminalPromotionStillFalse = refl
    }

UnificationAuthorityReviewPacketRecordedIsTrue :
  UnificationAuthorityReviewPacketRecorded ≡ true
UnificationAuthorityReviewPacketRecordedIsTrue = refl
