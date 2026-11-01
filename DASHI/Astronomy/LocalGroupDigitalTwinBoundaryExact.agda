module DASHI.Astronomy.LocalGroupDigitalTwinBoundaryExact where

open import DASHI.Core.Prelude
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Boundary from a source-bound present-state reconstruction to a validated
-- time-indexed Local Group digital twin.
------------------------------------------------------------------------

twinAnd : Bool → Bool → Bool
twinAnd true b = b
twinAnd false _ = false

data TwinObligation : Set where
  stateVector : TwinObligation
  evolutionLaw : TwinObligation
  potentialModel : TwinObligation
  massUncertainty : TwinObligation
  interactionModel : TwinObligation
  observationUpdate : TwinObligation
  dataAssimilation : TwinObligation
  predictiveValidation : TwinObligation

data PaymentState : Set where
  unpaidPayment : PaymentState
  attributedClaimPayment : PaymentState
  sourceBoundPayment : PaymentState
  independentlyVerifiedPayment : PaymentState

record TwinBoundary : Set where
  constructor twinBoundary
  field
    presentState : PaymentState
    timeEvolution : PaymentState
    gravitationalPotential : PaymentState
    galaxyMassUncertainty : PaymentState
    satelliteInteractions : PaymentState
    observationalUpdating : PaymentState
    assimilation : PaymentState
    predictionValidation : PaymentState

open TwinBoundary public

firstLightBoundary : TwinBoundary
firstLightBoundary =
  twinBoundary
    sourceBoundPayment
    unpaidPayment
    unpaidPayment
    unpaidPayment
    attributedClaimPayment
    unpaidPayment
    unpaidPayment
    unpaidPayment

record TwinPromotionReceipt : Set where
  constructor twinPromotionReceipt
  field
    boundary : TwinBoundary
    evolutionPaid : Bool
    potentialPaid : Bool
    uncertaintyPaid : Bool
    interactionsPaid : Bool
    updatePaid : Bool
    assimilationPaid : Bool
    validationPaid : Bool

open TwinPromotionReceipt public

validatedTwin : TwinPromotionReceipt → Bool
validatedTwin r =
  twinAnd (evolutionPaid r)
  (twinAnd (potentialPaid r)
  (twinAnd (uncertaintyPaid r)
  (twinAnd (interactionsPaid r)
  (twinAnd (updatePaid r)
  (twinAnd (assimilationPaid r)
           (validationPaid r))))))

firstLightRenderingPaysValidatedTwin : Bool
firstLightRenderingPaysValidatedTwin = false

firstLightRenderingPaysValidatedTwinIsFalse :
  firstLightRenderingPaysValidatedTwin ≡ false
firstLightRenderingPaysValidatedTwinIsFalse = refl

frameBenchmarkPaysEvolutionLaw : Bool
frameBenchmarkPaysEvolutionLaw = false

frameBenchmarkPaysEvolutionLawIsFalse :
  frameBenchmarkPaysEvolutionLaw ≡ false
frameBenchmarkPaysEvolutionLawIsFalse = refl

sagittariusTimeDependenceMotivatesDynamicLane : Bool
sagittariusTimeDependenceMotivatesDynamicLane = true

sagittariusTimeDependenceMotivatesDynamicLaneIsTrue :
  sagittariusTimeDependenceMotivatesDynamicLane ≡ true
sagittariusTimeDependenceMotivatesDynamicLaneIsTrue = refl

------------------------------------------------------------------------
-- Explicit next evidence demands rather than a new planner.
------------------------------------------------------------------------

record TwinEvidenceDemand : Set where
  constructor twinEvidenceDemand
  field
    obligation : TwinObligation
    demand : String
    whyNeeded : String

nextTwinDemands : List TwinEvidenceDemand
nextTwinDemands =
  twinEvidenceDemand evolutionLaw
    "acquire the exact time-evolution equations/integrator used by the Virtual Observatory"
    "a static phase-space state does not determine X_(t+dt)"
  ∷ twinEvidenceDemand potentialModel
    "bind the Milky Way/M31/LMC gravitational-potential assumptions to exact source or implementation receipts"
    "frame agreement does not validate force law or potential"
  ∷ twinEvidenceDemand massUncertainty
    "retain mass priors/posteriors and their source provenance for MW, M31, LMC, M33 and relevant satellites"
    "dynamical trajectories depend materially on uncertain masses"
  ∷ twinEvidenceDemand interactionModel
    "acquire the exact interaction treatment for LMC/Sagittarius/M31/M33 and satellite systems"
    "Vasiliev et al. supplies a concrete warning against static-Milky-Way dynamics"
  ∷ twinEvidenceDemand observationUpdate
    "define how new catalogue rows update the same source-bound state object"
    "a Virtual Observatory should distinguish state revision from rendering"
  ∷ twinEvidenceDemand dataAssimilation
    "define an observation-to-model assimilation receipt"
    "new measurements must not silently overwrite model state"
  ∷ twinEvidenceDemand predictiveValidation
    "hold out source-bound observables and compare predictions against them"
    "reproduction of construction inputs is not predictive validation"
  ∷ []
