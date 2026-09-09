module DASHI.Cognition.PNF.SensibLawCullenConsumerCollisionMissingCoordinateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.ConsumerCollisionMissingCoordinateExact as Collision

------------------------------------------------------------------------
-- CULLEN INTROSPECTIVE REGRESSION
--
-- This module formalises only the representation lesson exposed by the source
-- audit.  It does not restate the judicial holding.
--
-- The coarse legacy observation retained only:
--
--   "police-function context"
--
-- and thereby collapsed two fine worlds:
--
--   police function + no invoked statutory power
--   police function + invoked statutory power.
--
-- The legacy bundled premise consumer distinguishes those worlds.  Therefore
-- police-function context alone cannot determine whether that bundled premise
-- is paid.  `StatutoryPowerStatus` is an explicit separating coordinate for
-- this collision.
------------------------------------------------------------------------

data CullenFineWorld : Set where
  policeFunctionWithoutInvokedStatutoryPower : CullenFineWorld
  policeFunctionWithInvokedStatutoryPower : CullenFineWorld

data PoliceFunctionObservation : Set where
  policeFunctionContextObserved : PoliceFunctionObservation

data LegacyBundledPremiseDecision : Set where
  legacyBundledPremiseUnpaid : LegacyBundledPremiseDecision
  legacyBundledPremisePaid : LegacyBundledPremiseDecision

data StatutoryPowerStatus : Set where
  statutoryPowerNotInvoked : StatutoryPowerStatus
  statutoryPowerInvoked : StatutoryPowerStatus

observePoliceFunctionContext : CullenFineWorld → PoliceFunctionObservation
observePoliceFunctionContext _ = policeFunctionContextObserved

legacyBundledPremiseConsumer :
  CullenFineWorld → LegacyBundledPremiseDecision
legacyBundledPremiseConsumer policeFunctionWithoutInvokedStatutoryPower =
  legacyBundledPremiseUnpaid
legacyBundledPremiseConsumer policeFunctionWithInvokedStatutoryPower =
  legacyBundledPremisePaid

inspectStatutoryPower : CullenFineWorld → StatutoryPowerStatus
inspectStatutoryPower policeFunctionWithoutInvokedStatutoryPower =
  statutoryPowerNotInvoked
inspectStatutoryPower policeFunctionWithInvokedStatutoryPower =
  statutoryPowerInvoked

------------------------------------------------------------------------
-- Literal collision:
-- same coarse observation, different consumer result.
------------------------------------------------------------------------

cullenLegacyCollisionWitness :
  Compression.CompressionFailureWitness
    observePoliceFunctionContext legacyBundledPremiseConsumer
cullenLegacyCollisionWitness =
  Compression.compressionFailureWitness
    policeFunctionWithoutInvokedStatutoryPower
    policeFunctionWithInvokedStatutoryPower
    refl
    (λ ())

cullenLegacyConsumerCollision :
  Collision.ConsumerCollision
    observePoliceFunctionContext legacyBundledPremiseConsumer
cullenLegacyConsumerCollision =
  Collision.consumerCollision
    cullenLegacyCollisionWitness
    "Police-function context is observationally identical across the two fine worlds, while the legacy bundled-premise consumer differs."

policeFunctionContextCannotDetermineLegacyBundledPremise :
  NonFactor.FactorsThrough
    observePoliceFunctionContext legacyBundledPremiseConsumer → ⊥
policeFunctionContextCannotDetermineLegacyBundledPremise =
  Collision.coarseObservationCannotDetermineConsumer
    cullenLegacyConsumerCollision

------------------------------------------------------------------------
-- The added coordinate repairs THIS collision.
--
-- This is representation adequacy only.  It does not say that invoked statutory
-- power is a necessary premise of Cullen duty.  In fact, the source audit is
-- precisely why the old bundled rule must be reconstructed instead of reused.
------------------------------------------------------------------------

consumeRefinedCullenObservation :
  Collision.CoarsePlusCoordinate
    PoliceFunctionObservation StatutoryPowerStatus →
  LegacyBundledPremiseDecision
consumeRefinedCullenObservation
  (Collision.coarsePlusCoordinate _ statutoryPowerNotInvoked) =
  legacyBundledPremiseUnpaid
consumeRefinedCullenObservation
  (Collision.coarsePlusCoordinate _ statutoryPowerInvoked) =
  legacyBundledPremisePaid

cullenCoordinateRepair :
  Collision.ConsumerAdequateRefinement
    (Collision.addCoordinate observePoliceFunctionContext inspectStatutoryPower)
    legacyBundledPremiseConsumer
cullenCoordinateRepair =
  Collision.consumerAdequateRefinement
    consumeRefinedCullenObservation
    (λ
      { policeFunctionWithoutInvokedStatutoryPower → refl
      ; policeFunctionWithInvokedStatutoryPower → refl
      })
    "Adding StatutoryPowerStatus separates the collision and makes the legacy bundled-premise decision factor through the refined carrier."

statutoryPowerCoordinateActuallySeparates :
  inspectStatutoryPower policeFunctionWithoutInvokedStatutoryPower
    ≡ inspectStatutoryPower policeFunctionWithInvokedStatutoryPower → ⊥
statutoryPowerCoordinateActuallySeparates = λ ()

------------------------------------------------------------------------
-- The generic theorem re-derives that every adequate one-coordinate repair
-- must distinguish these witnesses.  For this concrete candidate coordinate,
-- assuming equality is impossible.
------------------------------------------------------------------------

cullenRepairCannotCollapseStatutoryPowerStatus :
  inspectStatutoryPower
      (Compression.leftFine cullenLegacyCollisionWitness)
    ≡ inspectStatutoryPower
      (Compression.rightFine cullenLegacyCollisionWitness) →
  ⊥
cullenRepairCannotCollapseStatutoryPowerStatus =
  Collision.coordinateRepairMustDistinguishCollision
    cullenLegacyConsumerCollision
    cullenCoordinateRepair

------------------------------------------------------------------------
-- Important non-promotions.
------------------------------------------------------------------------

data StatutoryPowerStatusIsNecessaryForCullenDuty : Set where

data CoordinateRepairReinstatesLegacyDutyRule : Set where

data RepresentationAdequacyIsJudicialAuthority : Set where

statutoryPowerCoordinateDoesNotBecomeDutyElement :
  StatutoryPowerStatusIsNecessaryForCullenDuty → ⊥
statutoryPowerCoordinateDoesNotBecomeDutyElement ()

repairDoesNotReinstateLegacyRule :
  CoordinateRepairReinstatesLegacyDutyRule → ⊥
repairDoesNotReinstateLegacyRule ()

representationTheoremIsNotAuthority :
  RepresentationAdequacyIsJudicialAuthority → ⊥
representationTheoremIsNotAuthority ()

------------------------------------------------------------------------
-- Introspective reading exported to the legal runtime.
------------------------------------------------------------------------

firstMissingCoordinateReading : String
firstMissingCoordinateReading =
  "When two source states are identical under the current upstream observation but a downstream legal consumer distinguishes them, the retained carrier is too coarse. Any valid repair must expose a typed coordinate that separates the colliding witnesses; source authority determines which candidate coordinate is admissible."
