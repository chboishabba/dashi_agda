module DASHI.Core.ActionFibreClosureStoppingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ACTION-FIBRE CLOSURE STOPPING
--
-- A consumer may stop before unique hidden-world identity when every currently
-- live hypothesis induces the same independently authorised consumer action.
------------------------------------------------------------------------

record ActionFibreProblem : Set₁ where
  constructor actionFibreProblem
  field
    Hypothesis : Set
    Action : Set
    Live : Hypothesis → Set
    actionFor : Hypothesis → Action
    Authorised : Action → Set
    consumerReference : String

open ActionFibreProblem public

record ActionFibreClosed (P : ActionFibreProblem) : Set₁ where
  constructor actionFibreClosed
  field
    representative : Hypothesis P
    representativeLive : Live P representative
    representativeAuthorised : Authorised P (actionFor P representative)
    allLiveAgree :
      (h : Hypothesis P) →
      Live P h →
      actionFor P h ≡ actionFor P representative
    closureReference : String

open ActionFibreClosed public

record StopForConsumer (P : ActionFibreProblem) : Set₁ where
  constructor stopForConsumer
  field
    closure : ActionFibreClosed P
    stoppingReference : String

open StopForConsumer public

actionFibreClosureStops :
  (P : ActionFibreProblem) → ActionFibreClosed P → StopForConsumer P
actionFibreClosureStops P closed =
  stopForConsumer closed
    "All currently live hypotheses induce the same authorised consumer action; unique world identity is not required for this consumer."

------------------------------------------------------------------------
-- Exact finite witness: two distinct live worlds, one authorised action.
------------------------------------------------------------------------

data World : Set where world₁ world₂ : World
data Decision : Set where monitor : Decision

toyLive : World → Set
toyLive world₁ = ⊤
toyLive world₂ = ⊤

toyAction : World → Decision
toyAction world₁ = monitor
toyAction world₂ = monitor

data ToyAuthorised : Decision → Set where monitorAuthorised : ToyAuthorised monitor

toyProblem : ActionFibreProblem
toyProblem = actionFibreProblem World Decision toyLive toyAction ToyAuthorised
  "bounded operational consumer"

toyClosed : ActionFibreClosed toyProblem
toyClosed = actionFibreClosed world₁ tt monitorAuthorised agree
  "world1 and world2 remain distinct but both induce the authorised monitor action"
  where
    agree : (h : World) → toyLive h → toyAction h ≡ toyAction world₁
    agree world₁ _ = refl
    agree world₂ _ = refl

toyStop : StopForConsumer toyProblem
toyStop = actionFibreClosureStops toyProblem toyClosed

worldsRemainDistinct : world₁ ≡ world₂ → ⊥
worldsRemainDistinct ()

record ActionFibreClosureBoundary : Set where
  constructor actionFibreClosureBoundary
  field
    stoppingRequiresUniqueWorldIdentity : Bool
    stoppingRequiresUniqueWorldIdentityIsFalse : stoppingRequiresUniqueWorldIdentity ≡ false
    actionAgreementWithoutAuthorityIsEnough : Bool
    actionAgreementWithoutAuthorityIsEnoughIsFalse : actionAgreementWithoutAuthorityIsEnough ≡ false
    multipleLiveWorldsMayStillPermitStopping : Bool
    multipleLiveWorldsMayStillPermitStoppingIsTrue : multipleLiveWorldsMayStillPermitStopping ≡ true
    closureIsConsumerRelative : Bool
    closureIsConsumerRelativeIsTrue : closureIsConsumerRelative ≡ true

canonicalActionFibreClosureBoundary : ActionFibreClosureBoundary
canonicalActionFibreClosureBoundary =
  actionFibreClosureBoundary false refl false refl true refl true refl
