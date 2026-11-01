module DASHI.Physics.Closure.UnificationCrossTermNullityLightweightBoundary where

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

------------------------------------------------------------------------
-- Lightweight U-1a cross-term nullity theorem receipt.

nullClassBoundaryReference : String
nullClassBoundaryReference =
  "DASHI.Physics.Closure.UnificationGluingCrossTermNullClassBoundary"

transportBoundaryReference : String
transportBoundaryReference =
  "DASHI.Physics.Closure.UnificationNullToQuotientEqualityTransportBoundary"

moduloNullBoundaryReference : String
moduloNullBoundaryReference =
  "DASHI.Physics.Closure.UnificationGluingModuloNullLinearityCompositeBoundary"

fourPointBoundaryReference : String
fourPointBoundaryReference =
  "DASHI.Physics.Closure.UnificationFourPointCancellationFromCrossTermNullityBoundary"

data U1aCrossTermClause : Set where
  chooseAdmissibleDefectQuotientCarrier : U1aCrossTermClause
  chooseGluingOperatorOnRepresentatives : U1aCrossTermClause
  defineCrossTermResidual : U1aCrossTermClause
  proveResidualLiesInNullClass : U1aCrossTermClause
  proveRepresentativeInvarianceOfNullClaim : U1aCrossTermClause
  transportNullClaimToQuotientEquality : U1aCrossTermClause
  feedModuloNullGluingLinearity : U1aCrossTermClause
  feedFourPointCancellationRoute : U1aCrossTermClause

canonicalU1aCrossTermClauses : List U1aCrossTermClause
canonicalU1aCrossTermClauses =
  chooseAdmissibleDefectQuotientCarrier
  ∷ chooseGluingOperatorOnRepresentatives
  ∷ defineCrossTermResidual
  ∷ proveResidualLiesInNullClass
  ∷ proveRepresentativeInvarianceOfNullClaim
  ∷ transportNullClaimToQuotientEquality
  ∷ feedModuloNullGluingLinearity
  ∷ feedFourPointCancellationRoute
  ∷ []

u1aCrossTermClauseCount : Nat
u1aCrossTermClauseCount =
  listLength canonicalU1aCrossTermClauses

u1aCrossTermClauseCountIs8 : u1aCrossTermClauseCount ≡ 8
u1aCrossTermClauseCountIs8 = refl

data U1aDownstreamConsumer : Set where
  consumer-nullToQuotientEquality : U1aDownstreamConsumer
  consumer-moduloNullGluingLinearity : U1aDownstreamConsumer
  consumer-fourPointCancellation : U1aDownstreamConsumer
  consumer-parallelogramIdentity : U1aDownstreamConsumer
  consumer-quadraticEmergence : U1aDownstreamConsumer

canonicalU1aDownstreamConsumers : List U1aDownstreamConsumer
canonicalU1aDownstreamConsumers =
  consumer-nullToQuotientEquality
  ∷ consumer-moduloNullGluingLinearity
  ∷ consumer-fourPointCancellation
  ∷ consumer-parallelogramIdentity
  ∷ consumer-quadraticEmergence
  ∷ []

u1aDownstreamConsumerCount : Nat
u1aDownstreamConsumerCount =
  listLength canonicalU1aDownstreamConsumers

u1aDownstreamConsumerCountIs5 : u1aDownstreamConsumerCount ≡ 5
u1aDownstreamConsumerCountIs5 = refl

data U1aBlocker : Set where
  blocker-crossTermNullity-unproved : U1aBlocker
  blocker-moduloNullLinearity-unproved : U1aBlocker
  blocker-fourPoint-unproved : U1aBlocker
  blocker-parallelogram-unproved : U1aBlocker
  blocker-quadraticEmergence-unproved : U1aBlocker
  blocker-terminal-promotion-forbidden : U1aBlocker

canonicalU1aBlockers : List U1aBlocker
canonicalU1aBlockers =
  blocker-crossTermNullity-unproved
  ∷ blocker-moduloNullLinearity-unproved
  ∷ blocker-fourPoint-unproved
  ∷ blocker-parallelogram-unproved
  ∷ blocker-quadraticEmergence-unproved
  ∷ blocker-terminal-promotion-forbidden
  ∷ []

u1aBlockerCount : Nat
u1aBlockerCount =
  listLength canonicalU1aBlockers

u1aBlockerCountIs6 : u1aBlockerCount ≡ 6
u1aBlockerCountIs6 = refl

UnificationCrossTermNullityTheoremProvedLightweight : Bool
UnificationCrossTermNullityTheoremProvedLightweight = false

UnificationCrossTermNullityTheoremProvedLightweightIsFalse :
  UnificationCrossTermNullityTheoremProvedLightweight ≡ false
UnificationCrossTermNullityTheoremProvedLightweightIsFalse = refl

UnificationFourPointPromotedFromU1a : Bool
UnificationFourPointPromotedFromU1a = false

UnificationFourPointPromotedFromU1aIsFalse :
  UnificationFourPointPromotedFromU1a ≡ false
UnificationFourPointPromotedFromU1aIsFalse = refl

TerminalPromotionFromU1a : Bool
TerminalPromotionFromU1a = false

TerminalPromotionFromU1aIsFalse :
  TerminalPromotionFromU1a ≡ false
TerminalPromotionFromU1aIsFalse = refl

record UnificationCrossTermNullityLightweightBoundary : Set where
  field
    theoremClauses : List U1aCrossTermClause
    theoremClausesAreCanonical :
      theoremClauses ≡ canonicalU1aCrossTermClauses
    downstreamConsumers :
      List U1aDownstreamConsumer
    downstreamConsumersAreCanonical :
      downstreamConsumers ≡ canonicalU1aDownstreamConsumers
    blockers : List U1aBlocker
    blockersAreCanonical :
      blockers ≡ canonicalU1aBlockers
    theoremClauseCountIs8 :
      u1aCrossTermClauseCount ≡ 8
    consumerCountIs5 :
      u1aDownstreamConsumerCount ≡ 5
    blockerCountIs6 :
      u1aBlockerCount ≡ 6
    u1aStillFalse :
      UnificationCrossTermNullityTheoremProvedLightweight ≡ false
    fourPointStillFalse :
      UnificationFourPointPromotedFromU1a ≡ false
    terminalStillFalse :
      TerminalPromotionFromU1a ≡ false

canonicalUnificationCrossTermNullityLightweightBoundary :
  UnificationCrossTermNullityLightweightBoundary
canonicalUnificationCrossTermNullityLightweightBoundary =
  record
    { theoremClauses = canonicalU1aCrossTermClauses
    ; theoremClausesAreCanonical = refl
    ; downstreamConsumers = canonicalU1aDownstreamConsumers
    ; downstreamConsumersAreCanonical = refl
    ; blockers = canonicalU1aBlockers
    ; blockersAreCanonical = refl
    ; theoremClauseCountIs8 = refl
    ; consumerCountIs5 = refl
    ; blockerCountIs6 = refl
    ; u1aStillFalse = refl
    ; fourPointStillFalse = refl
    ; terminalStillFalse = refl
    }

UnificationCrossTermNullityLightweightBoundaryRecorded : Bool
UnificationCrossTermNullityLightweightBoundaryRecorded = true

UnificationCrossTermNullityLightweightBoundaryRecordedIsTrue :
  UnificationCrossTermNullityLightweightBoundaryRecorded ≡ true
UnificationCrossTermNullityLightweightBoundaryRecordedIsTrue = refl
