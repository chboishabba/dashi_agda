module DASHI.Core.BoundAcquisitionDemandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- GENERIC EXACT-LIVE BOUND ACQUISITION DEMAND
--
-- A scheduler may identify a selected requirement and may also describe a
-- plausible acquisition route.  Progress-sensitive code needs the stronger
-- statement that the concrete acquisition attacks the residual and producer
-- selected for that exact requirement.
------------------------------------------------------------------------

record AcquisitionAlignment
    (Requirement Residual Producer Acquisition : Set) : Set₁ where
  constructor acquisition-alignment
  field
    residualForRequirement : Requirement → Residual
    producerForRequirement : Requirement → Producer
    acquisitionResidual : Acquisition → Residual
    acquisitionProducer : Acquisition → Producer

open AcquisitionAlignment public

record BoundAcquisitionDemand
    {Requirement Residual Producer Acquisition : Set}
    (alignment : AcquisitionAlignment Requirement Residual Producer Acquisition)
    (selected : Requirement)
    (liveResidual : Residual) : Set₁ where
  constructor bound-acquisition-demand
  field
    acquisition : Acquisition
    residualMatchesSelectedRequirement :
      liveResidual ≡ residualForRequirement alignment selected
    acquisitionResidualMatchesLiveResidual :
      acquisitionResidual alignment acquisition ≡ liveResidual
    acquisitionProducerMatchesSelectedRequirement :
      acquisitionProducer alignment acquisition ≡ producerForRequirement alignment selected

open BoundAcquisitionDemand public

acquisitionPaysSelectedResidual :
  ∀ {Requirement Residual Producer Acquisition}
    {alignment : AcquisitionAlignment Requirement Residual Producer Acquisition}
    {selected : Requirement}
    {liveResidual : Residual} →
  (demand : BoundAcquisitionDemand alignment selected liveResidual) →
  acquisitionResidual alignment (acquisition demand) ≡
  residualForRequirement alignment selected
acquisitionPaysSelectedResidual demand =
  trans
    (acquisitionResidualMatchesLiveResidual demand)
    (residualMatchesSelectedRequirement demand)

acquisitionUsesSelectedProducer :
  ∀ {Requirement Residual Producer Acquisition}
    {alignment : AcquisitionAlignment Requirement Residual Producer Acquisition}
    {selected : Requirement}
    {liveResidual : Residual} →
  (demand : BoundAcquisitionDemand alignment selected liveResidual) →
  acquisitionProducer alignment (acquisition demand) ≡
  producerForRequirement alignment selected
acquisitionUsesSelectedProducer = acquisitionProducerMatchesSelectedRequirement

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BoundDemandAutomaticallyPaysRequirement : Set where
data SameProducerIdentifiesResidual : Set where
data BoundDemandAutomaticallyClosesConsumer : Set where

bindingDoesNotPayRequirement : BoundDemandAutomaticallyPaysRequirement → ⊥
bindingDoesNotPayRequirement ()

producerIdentityDoesNotIdentifyResidual : SameProducerIdentifiesResidual → ⊥
producerIdentityDoesNotIdentifyResidual ()

bindingDoesNotCloseConsumer : BoundDemandAutomaticallyClosesConsumer → ⊥
bindingDoesNotCloseConsumer ()
