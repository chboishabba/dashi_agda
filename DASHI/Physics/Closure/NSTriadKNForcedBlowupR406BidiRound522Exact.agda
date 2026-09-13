module DASHI.Physics.Closure.NSTriadKNForcedBlowupR406BidiRound522Exact where

------------------------------------------------------------------------
-- ROUND522 / BIDIRECTIONAL FORCED-BLOWUP <-> R406 ADVERSARIAL WIRING
--
-- This is the narrow BIDI requested by the live NS proof search.  It does not
-- create a parallel planner.  It takes R521's source-bounded external comparator
-- and wires it in both directions against the existing R406/signed-forcing
-- consumer:
--
--   external -> internal:
--     smooth-forced blowup mechanism
--       -> instantiate its forcing on the literal DASHI carrier
--       -> ask whether the exact signed critical forcing budget is inhabited
--       -> test the candidate R406 estimate or expose the separating hypothesis.
--
--   internal -> external:
--     exact DASHI forcing hypotheses / candidate estimate
--       -> classify whether the external construction is inside or outside the
--          theorem's quantified class
--       -> only then use the external result as a falsification/comparison test.
--
-- Neither direction promotes Buckmaster's reported unseen forced-NS claim to a
-- theorem.  Neither direction pays leaf A merely by performing the comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNClayResidualIntrospectionRound509Exact as R509
import DASHI.Physics.Closure.NSTriadKNSmoothForcedBlowupAdversarialBoundaryRound521Exact as R521

------------------------------------------------------------------------
-- BIDI direction and exact live consumer.
------------------------------------------------------------------------

data BidiDirection522 : Set where
  externalToInternal522 : BidiDirection522
  internalToExternal522 : BidiDirection522

data BidiConsumer522 : Set where
  literalR406SignedCrossConsumer522 : BidiConsumer522
  signedCriticalForcingConsumer522 : BidiConsumer522

data BidiCoordinate522 : Set where
  externalForcingLiteralCarrierIdentity522 : BidiCoordinate522
  externalForcingSignedBudgetMembership522 : BidiCoordinate522
  candidateEstimateQuantifierScope522 : BidiCoordinate522
  separatingForcingHypothesis522 : BidiCoordinate522

data BidiProducer522 : Set where
  literalExternalForcingInstantiation522 : BidiProducer522
  signedBudgetMembershipCheck522 : BidiProducer522
  theoremQuantifierAudit522 : BidiProducer522
  explicitHypothesisExtraction522 : BidiProducer522

record BoundBidiDemand522 : Set where
  constructor bound-bidi-demand-522
  field
    direction : BidiDirection522
    consumer : BidiConsumer522
    coordinate : BidiCoordinate522
    producer : BidiProducer522

open BoundBidiDemand522 public

------------------------------------------------------------------------
-- External -> internal route.
------------------------------------------------------------------------

externalToInternalFirst522 : BoundBidiDemand522
externalToInternalFirst522 =
  bound-bidi-demand-522
    externalToInternal522
    signedCriticalForcingConsumer522
    externalForcingLiteralCarrierIdentity522
    literalExternalForcingInstantiation522

externalToInternalAfterInstantiation522 : BoundBidiDemand522
externalToInternalAfterInstantiation522 =
  bound-bidi-demand-522
    externalToInternal522
    signedCriticalForcingConsumer522
    externalForcingSignedBudgetMembership522
    signedBudgetMembershipCheck522

externalToInternalIfBudgetFails522 : BoundBidiDemand522
externalToInternalIfBudgetFails522 =
  bound-bidi-demand-522
    externalToInternal522
    signedCriticalForcingConsumer522
    separatingForcingHypothesis522
    explicitHypothesisExtraction522

externalToInternalIfBudgetHolds522 : BoundBidiDemand522
externalToInternalIfBudgetHolds522 =
  bound-bidi-demand-522
    externalToInternal522
    literalR406SignedCrossConsumer522
    candidateEstimateQuantifierScope522
    theoremQuantifierAudit522

------------------------------------------------------------------------
-- Internal -> external route.
--
-- The live theorem candidate must say what forcing class it actually controls.
-- Only after that scope is explicit can an external construction be classified
-- as an in-class falsification test or an out-of-class separator.
------------------------------------------------------------------------

internalToExternalFirst522 : BoundBidiDemand522
internalToExternalFirst522 =
  bound-bidi-demand-522
    internalToExternal522
    literalR406SignedCrossConsumer522
    candidateEstimateQuantifierScope522
    theoremQuantifierAudit522

internalToExternalAfterScope522 : BoundBidiDemand522
internalToExternalAfterScope522 =
  bound-bidi-demand-522
    internalToExternal522
    signedCriticalForcingConsumer522
    externalForcingSignedBudgetMembership522
    signedBudgetMembershipCheck522

------------------------------------------------------------------------
-- Collision exposed by introspection.
--
-- A coarse observer that records only "smooth forcing" cannot decide the
-- downstream signed-budget consumer.  The missing coordinate is precisely
-- signed-budget membership on the same literal forcing carrier.
------------------------------------------------------------------------

data SmoothOnlyObservation522 : Set where
  observedSmooth522 : SmoothOnlyObservation522

data SignedBudgetAnswer522 : Set where
  budgetInClass522 : SignedBudgetAnswer522
  budgetOutOfClass522 : SignedBudgetAnswer522

record SmoothForcingWorld522 : Set where
  constructor smooth-forcing-world-522
  field
    smoothObservation : SmoothOnlyObservation522
    signedBudgetAnswer : SignedBudgetAnswer522

open SmoothForcingWorld522 public

worldBudgetIn522 : SmoothForcingWorld522
worldBudgetIn522 = smooth-forcing-world-522 observedSmooth522 budgetInClass522

worldBudgetOut522 : SmoothForcingWorld522
worldBudgetOut522 = smooth-forcing-world-522 observedSmooth522 budgetOutOfClass522

coarseObserve522 : SmoothForcingWorld522 → SmoothOnlyObservation522
coarseObserve522 = smoothObservation

coarseObserverCollision522 :
  coarseObserve522 worldBudgetIn522 ≡ coarseObserve522 worldBudgetOut522
coarseObserverCollision522 = refl

refinedObserve522 : SmoothForcingWorld522 → SignedBudgetAnswer522
refinedObserve522 = signedBudgetAnswer

data BudgetAnswersEqual522 : SignedBudgetAnswer522 → SignedBudgetAnswer522 → Set where
  sameBudgetAnswer522 :
    {x : SignedBudgetAnswer522} → BudgetAnswersEqual522 x x

refinedObserverSeparatesCollision522 :
  BudgetAnswersEqual522
    (refinedObserve522 worldBudgetIn522)
    (refinedObserve522 worldBudgetOut522)
  → ⊥
refinedObserverSeparatesCollision522 ()

------------------------------------------------------------------------
-- Exact relation to current live residuals.
------------------------------------------------------------------------

round522CurrentGlobalResidualStillLeafA :
  R509.residual R509.currentNSIntrospectiveState509
  ≡ R509.signedCrossUniformBoundResidual
round522CurrentGlobalResidualStillLeafA = refl

round522ExternalComparatorCurrentDemand :
  R521.currentAdversarialDemand521
  ≡ R521.instantiateExternalForcingOnLiteralCarrier521
round522ExternalComparatorCurrentDemand =
  R521.currentAdversarialDemandIsLiteralInstantiation521

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BidiComparisonPaysLeafAPermission522 : Set where
data SmoothnessDeterminesBudgetMembershipPermission522 : Set where
data ReportedUnseenClaimBecomesTheoremPermission522 : Set where

bidiComparisonDoesNotPayLeafA522 : BidiComparisonPaysLeafAPermission522 → ⊥
bidiComparisonDoesNotPayLeafA522 ()

smoothnessDoesNotDetermineBudgetMembership522 :
  SmoothnessDeterminesBudgetMembershipPermission522 → ⊥
smoothnessDoesNotDetermineBudgetMembership522 ()

reportedUnseenClaimDoesNotBecomeTheorem522 :
  ReportedUnseenClaimBecomesTheoremPermission522 → ⊥
reportedUnseenClaimDoesNotBecomeTheorem522 ()

------------------------------------------------------------------------
-- Status ledger.
------------------------------------------------------------------------

round522BidiWiringImplemented : Bool
round522BidiWiringImplemented = true

round522CoarseSmoothObserverAdequate : Bool
round522CoarseSmoothObserverAdequate = false

round522MissingCoordinateIsSignedBudgetMembership : Bool
round522MissingCoordinateIsSignedBudgetMembership = true

round522ExternalResultAutomaticallyRefutesR406 : Bool
round522ExternalResultAutomaticallyRefutesR406 = false

round522ExternalResultAutomaticallyProvesR406 : Bool
round522ExternalResultAutomaticallyProvesR406 = false

round522ClayPromotion : Bool
round522ClayPromotion = false

round522BidiWiringImplementedIsTrue :
  round522BidiWiringImplemented ≡ true
round522BidiWiringImplementedIsTrue = refl

round522CoarseSmoothObserverAdequateIsFalse :
  round522CoarseSmoothObserverAdequate ≡ false
round522CoarseSmoothObserverAdequateIsFalse = refl

round522MissingCoordinateIsSignedBudgetMembershipIsTrue :
  round522MissingCoordinateIsSignedBudgetMembership ≡ true
round522MissingCoordinateIsSignedBudgetMembershipIsTrue = refl

round522ExternalResultAutomaticallyRefutesR406IsFalse :
  round522ExternalResultAutomaticallyRefutesR406 ≡ false
round522ExternalResultAutomaticallyRefutesR406IsFalse = refl

round522ExternalResultAutomaticallyProvesR406IsFalse :
  round522ExternalResultAutomaticallyProvesR406 ≡ false
round522ExternalResultAutomaticallyProvesR406IsFalse = refl

round522ClayPromotionIsFalse : round522ClayPromotion ≡ false
round522ClayPromotionIsFalse = refl
