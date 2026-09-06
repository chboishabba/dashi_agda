module DASHI.Core.ResidualActionInterventionDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Model
import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.SequentialRobustActionabilityPlannerExact as RobustPlan

------------------------------------------------------------------------
-- RESIDUAL ACTION <-> INTERVENTIONAL DISCRIMINATOR
--
-- A perturb-and-measure action may be useful because it separates two live
-- worlds, not merely because it changes the endpoint.  Conversely a robust,
-- independently authorised action can sometimes close the declared consumer
-- before the latent mechanism is uniquely identified.
------------------------------------------------------------------------

record PerturbationDiscriminatorReceipt : Set₁ where
  constructor perturbationDiscriminatorReceipt
  field
    residual : Model.ModelResidual
    actionKind : Action.ResidualActionKind
    World Existing : Set
    existingObservation : World → Existing
    collision : Discriminator.CurrentObserverCollision existingObservation
    perturbAndMeasureBundle : Discriminator.ExperimentBundle World
    separatesAfterPerturbation :
      Discriminator.BundleSeparates
        perturbAndMeasureBundle
        (Discriminator.left collision)
        (Discriminator.right collision)
    perturbationAdmissionReference : String
    sameObjectReference : String
    postPerturbationObservationReference : String

open PerturbationDiscriminatorReceipt public

record ConsumerEarlyStopReceipt : Set₁ where
  constructor consumerEarlyStopReceipt
  field
    Hypothesis Intervention Outcome : Set
    system :
      DASHI.Core.RobustInterventionAcrossHypothesesExact.HypothesisInterventionSystem
        Hypothesis Intervention Outcome
    Authority : Intervention → Set
    live : Hypothesis → Set
    plan : RobustPlan.SequentialActionabilityPlan system Authority live
    stoppingReference : String
    consumerReference : String

open ConsumerEarlyStopReceipt public

record ResidualInterventionDiscriminatorBoundary : Set where
  constructor residualInterventionDiscriminatorBoundary
  field
    endpointChangeAloneMakesPerturbationDiscriminating : Bool
    endpointChangeAloneMakesPerturbationDiscriminatingIsFalse :
      endpointChangeAloneMakesPerturbationDiscriminating ≡ false
    perturbationCanBeUsefulBySeparatingCollidingWorlds : Bool
    perturbationCanBeUsefulBySeparatingCollidingWorldsIsTrue :
      perturbationCanBeUsefulBySeparatingCollidingWorlds ≡ true
    robustAuthorisedActionMayCloseConsumerBeforeModelIdentity : Bool
    robustAuthorisedActionMayCloseConsumerBeforeModelIdentityIsTrue :
      robustAuthorisedActionMayCloseConsumerBeforeModelIdentity ≡ true
    discriminatingPowerDoesNotCreatePerturbationAuthority : Bool
    discriminatingPowerDoesNotCreatePerturbationAuthorityIsTrue :
      discriminatingPowerDoesNotCreatePerturbationAuthority ≡ true

canonicalResidualInterventionDiscriminatorBoundary :
  ResidualInterventionDiscriminatorBoundary
canonicalResidualInterventionDiscriminatorBoundary =
  residualInterventionDiscriminatorBoundary false refl true refl true refl true refl
