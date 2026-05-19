module Ontology.Brain.BrainGovernanceProviso where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.BlockerKillConditions using
  (KillCondition; w1KillCondition; w2KillCondition; w3KillCondition;
   w4KillCondition; w5KillCondition; w6KillCondition)

------------------------------------------------------------------------
-- Brain-lane governance proviso.
--
-- The Brain lane remains non-promoting.  It can only enter a lateral
-- support-review queue after a direct physics lane has a typed exhaustion
-- receipt and no retarget availability.  This module does not construct or
-- alter any W1-W6 kill receipt.

data BrainGovernanceRole : Set where
  nonPromotingAdjacentLane :
    BrainGovernanceRole

data LateralSupportReviewStatus : Set where
  notEligible :
    LateralSupportReviewStatus
  eligibleAfterTypedExhaustionWithoutRetarget :
    LateralSupportReviewStatus

record DirectLaneExhaustionProviso : Setω where
  field
    directLaneKillCondition :
      KillCondition

    typedExhaustionReceiptPresent :
      Bool

    retargetAvailable :
      Bool

record BrainGovernanceProviso : Setω where
  field
    role :
      BrainGovernanceRole

    w1Kill :
      KillCondition

    w2Kill :
      KillCondition

    w3Kill :
      KillCondition

    w4Kill :
      KillCondition

    w5Kill :
      KillCondition

    w6Kill :
      KillCondition

    promotesBrainLane :
      Bool

    promotesPhysicsLane :
      Bool

    claimsBiologicalRecovery :
      Bool

    claimsMultiscalePersistence :
      Bool

    claimsUnification :
      Bool

    defaultReviewStatus :
      LateralSupportReviewStatus

    conditionalReviewProviso :
      DirectLaneExhaustionProviso →
      LateralSupportReviewStatus

    provisoBoundary :
      List String

brainLateralReviewAfterExhaustion :
  DirectLaneExhaustionProviso →
  LateralSupportReviewStatus
brainLateralReviewAfterExhaustion proviso
  with DirectLaneExhaustionProviso.typedExhaustionReceiptPresent proviso
     | DirectLaneExhaustionProviso.retargetAvailable proviso
... | true  | false =
  eligibleAfterTypedExhaustionWithoutRetarget
... | _     | _     =
  notEligible

brainGovernanceProviso : BrainGovernanceProviso
brainGovernanceProviso =
  record
    { role = nonPromotingAdjacentLane
    ; w1Kill = w1KillCondition
    ; w2Kill = w2KillCondition
    ; w3Kill = w3KillCondition
    ; w4Kill = w4KillCondition
    ; w5Kill = w5KillCondition
    ; w6Kill = w6KillCondition
    ; promotesBrainLane = false
    ; promotesPhysicsLane = false
    ; claimsBiologicalRecovery = false
    ; claimsMultiscalePersistence = false
    ; claimsUnification = false
    ; defaultReviewStatus = notEligible
    ; conditionalReviewProviso = brainLateralReviewAfterExhaustion
    ; provisoBoundary =
        "Brain lane remains non-promoting governance support only"
        ∷ "W1-W6 physics lanes remain assigned to their typed kill conditions"
        ∷ "Brain lane does not construct or replace any physics promotion receipt"
        ∷ "Lateral support review requires typed exhaustion in a direct lane"
        ∷ "Lateral support review also requires no retarget availability"
        ∷ "No biological recovery, multiscale persistence, physics promotion, or unification is claimed"
        ∷ []
    }

brainProvisoDoesNotPromoteBrain :
  BrainGovernanceProviso.promotesBrainLane brainGovernanceProviso ≡ false
brainProvisoDoesNotPromoteBrain = refl

brainProvisoDoesNotPromotePhysics :
  BrainGovernanceProviso.promotesPhysicsLane brainGovernanceProviso ≡ false
brainProvisoDoesNotPromotePhysics = refl

brainProvisoDefaultReviewNotEligible :
  BrainGovernanceProviso.defaultReviewStatus brainGovernanceProviso
  ≡
  notEligible
brainProvisoDefaultReviewNotEligible = refl
