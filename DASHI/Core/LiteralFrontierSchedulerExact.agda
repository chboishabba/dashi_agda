module DASHI.Core.LiteralFrontierSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Cross
import DASHI.Core.RecursiveParetoFrontierLiftingExact as Recursive

------------------------------------------------------------------------
-- LITERAL FRONTIER SCHEDULER
--
-- The generic adaptive machinery becomes operational only when it is applied
-- to the repository's literal outstanding obligations.  Every candidate move
-- is therefore given an explicit disposition:
--
--   close     : an independently adequate formal closure capability exists;
--   redirect  : the move reduces/recharts the live frontier but does not close;
--   reject    : the move is blocked by a no-go, mismatch, stale dependency,
--               authority defect, or consumer irrelevance.
--
-- The scheduler deliberately does not infer programme progress from a selected
-- move.  Programme promotion remains owned by ExactConsumerReceipt.
------------------------------------------------------------------------

data LiteralDisposition : Set where
  closeLeaf
  redirectFrontier
  rejectMove
  : LiteralDisposition

data RejectionReason : Set where
  knownNoGo
  carrierMismatch
  scopeMismatch
  consumerMismatch
  staleOrAlreadyOwned
  authorityInsufficient
  residualIrrelevant
  : RejectionReason

record LiteralFrontierMove : Set where
  constructor literalFrontierMove
  field
    producer : Cross.RefinementProducerKind
    liveLeafReference : String
    moveReference : String
    residualReference : String
    consumerReference : String
    sameObjectReference : String
    authorityReference : String
    paretoReference : String

open LiteralFrontierMove public

record ClosedLiteralMove (move : LiteralFrontierMove) : Set where
  constructor closedLiteralMove
  field
    theoremAuthority : ProofSearch.TheoremAuthority
    closedLeafCapability : ProofSearch.ClosedLeafCapability theoremAuthority
    exactConsumerReceipt : ProofSearch.ExactConsumerReceipt
    closureReference : String

open ClosedLiteralMove public

record RedirectedLiteralMove (move : LiteralFrontierMove) : Set where
  constructor redirectedLiteralMove
  field
    frontierReducedOrRecharted : Bool
    frontierReducedOrRechartedIsTrue : frontierReducedOrRecharted ≡ true
    nextResidualReference : String
    retainedEvidenceReference : String
    redirectReference : String

open RedirectedLiteralMove public

record RejectedLiteralMove (move : LiteralFrontierMove) : Set where
  constructor rejectedLiteralMove
  field
    reason : RejectionReason
    rejectionReference : String
    retainedForAudit : Bool
    retainedForAuditIsTrue : retainedForAudit ≡ true

open RejectedLiteralMove public

data LiteralMoveOutcome (move : LiteralFrontierMove) : Set where
  closed : ClosedLiteralMove move → LiteralMoveOutcome move
  redirected : RedirectedLiteralMove move → LiteralMoveOutcome move
  rejected : RejectedLiteralMove move → LiteralMoveOutcome move

programmeProgressFromClosed :
  {move : LiteralFrontierMove} →
  ClosedLiteralMove move → ProofSearch.ProgrammeProgress
programmeProgressFromClosed closure =
  ProofSearch.promote (exactConsumerReceipt closure)

record LiteralFrontierPortfolio : Set₁ where
  constructor literalFrontierPortfolio
  field
    Move : Set
    literalMove : Move → LiteralFrontierMove
    outcome : (move : Move) → LiteralMoveOutcome (literalMove move)
    liveConsumerReference : String
    portfolioCompletenessReference : String
    residualRelevantOnly : Bool
    residualRelevantOnlyIsTrue : residualRelevantOnly ≡ true

open LiteralFrontierPortfolio public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LiteralFrontierSchedulerBoundary : Set where
  constructor literalFrontierSchedulerBoundary
  field
    everyInterestingMoveClosesLeaf : Bool
    everyInterestingMoveClosesLeafIsFalse : everyInterestingMoveClosesLeaf ≡ false
    redirectEqualsFormalClosure : Bool
    redirectEqualsFormalClosureIsFalse : redirectEqualsFormalClosure ≡ false
    rejectedMoveShouldBeDeletedFromHistory : Bool
    rejectedMoveShouldBeDeletedFromHistoryIsFalse : rejectedMoveShouldBeDeletedFromHistory ≡ false
    formalClosureRequiresExactConsumerReceipt : Bool
    formalClosureRequiresExactConsumerReceiptIsTrue : formalClosureRequiresExactConsumerReceipt ≡ true
    literalPortfolioMayContainCloseRedirectAndRejectTogether : Bool
    literalPortfolioMayContainCloseRedirectAndRejectTogetherIsTrue :
      literalPortfolioMayContainCloseRedirectAndRejectTogether ≡ true
    tetrationalCapacityRequiresLiteralPortfolioToMaterialiseEverything : Bool
    tetrationalCapacityRequiresLiteralPortfolioToMaterialiseEverythingIsFalse :
      tetrationalCapacityRequiresLiteralPortfolioToMaterialiseEverything ≡ false

canonicalLiteralFrontierSchedulerBoundary : LiteralFrontierSchedulerBoundary
canonicalLiteralFrontierSchedulerBoundary =
  literalFrontierSchedulerBoundary false refl false refl false refl true refl true refl false refl

existingCrossBoundary : Cross.ProofSearchExperimentalParetoBoundary
existingCrossBoundary = Cross.canonicalProofSearchExperimentalParetoBoundary

existingRecursiveBoundary : Recursive.RecursiveParetoFrontierBoundary
existingRecursiveBoundary = Recursive.canonicalRecursiveParetoFrontierBoundary
