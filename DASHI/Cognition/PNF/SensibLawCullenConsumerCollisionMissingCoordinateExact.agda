module DASHI.Cognition.PNF.SensibLawCullenConsumerCollisionMissingCoordinateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis

------------------------------------------------------------------------
-- CULLEN INTROSPECTIVE REGRESSION
--
-- Thin legal instantiation of the repository's canonical consumer-indexed
-- residual-refinement theorem.
--
-- Representation lesson only:
--
--   police-function context
--
-- was too coarse to stand in for the older bundled
-- "statutory police functions/powers" premise.  The source audit distinguishes
-- police-function context from whether statutory power was actually invoked.
--
-- This module does NOT restate Cullen's holding and does NOT promote
-- StatutoryPowerStatus into a necessary duty element.
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
-- Canonical collision:
-- same upstream observation + different consumer result.
------------------------------------------------------------------------

cullenLegacyConsumerCollision :
  Consumer.ConsumerRelevantCollision
    observePoliceFunctionContext legacyBundledPremiseConsumer
cullenLegacyConsumerCollision =
  Consumer.consumer-relevant-collision
    policeFunctionWithoutInvokedStatutoryPower
    policeFunctionWithInvokedStatutoryPower
    refl
    (λ ())

policeFunctionContextCannotDetermineLegacyBundledPremise :
  Consumer.ConsumerSufficient
    observePoliceFunctionContext legacyBundledPremiseConsumer → ⊥
policeFunctionContextCannotDetermineLegacyBundledPremise =
  Consumer.coarseCollisionBlocksSufficiency cullenLegacyConsumerCollision

------------------------------------------------------------------------
-- Candidate typed residual.
--
-- The joint observer (police-function context, statutory-power status) is
-- sufficient for THIS old bundled-premise consumer.  That is a representation
-- theorem, not a duty theorem.
------------------------------------------------------------------------

jointCullenObserver :
  CullenFineWorld → PoliceFunctionObservation × StatutoryPowerStatus
jointCullenObserver =
  Observer.pairObserver observePoliceFunctionContext inspectStatutoryPower

jointCullenObserverSufficient :
  Consumer.ConsumerSufficient jointCullenObserver legacyBundledPremiseConsumer
jointCullenObserverSufficient
  policeFunctionWithoutInvokedStatutoryPower
  policeFunctionWithoutInvokedStatutoryPower
  same = refl
jointCullenObserverSufficient
  policeFunctionWithInvokedStatutoryPower
  policeFunctionWithInvokedStatutoryPower
  same = refl
jointCullenObserverSufficient
  policeFunctionWithoutInvokedStatutoryPower
  policeFunctionWithInvokedStatutoryPower
  ()
jointCullenObserverSufficient
  policeFunctionWithInvokedStatutoryPower
  policeFunctionWithoutInvokedStatutoryPower
  ()

cullenStatutoryPowerResidualRepair :
  Consumer.ResidualRepair
    observePoliceFunctionContext
    inspectStatutoryPower
    legacyBundledPremiseConsumer
cullenStatutoryPowerResidualRepair =
  Consumer.residual-repair jointCullenObserverSufficient

------------------------------------------------------------------------
-- The reusable invariant instantiated literally:
-- every sufficient repair must distinguish this collision.
------------------------------------------------------------------------

statutoryPowerResidualMustSeparateCullenCollision :
  inspectStatutoryPower (Consumer.left cullenLegacyConsumerCollision)
    ≡ inspectStatutoryPower (Consumer.right cullenLegacyConsumerCollision) → ⊥
statutoryPowerResidualMustSeparateCullenCollision =
  Consumer.residualMustSeparateRelevantCollision
    cullenLegacyConsumerCollision
    cullenStatutoryPowerResidualRepair

cullenRepairIsStrictRefinement :
  Observer.StrictRefinement
    observePoliceFunctionContext
    jointCullenObserver
cullenRepairIsStrictRefinement =
  Consumer.consumerRelevantResidualGivesStrictRefinement
    cullenLegacyConsumerCollision
    cullenStatutoryPowerResidualRepair

------------------------------------------------------------------------
-- Existing discriminator synthesis consumes the same collision.
--
-- This is deliberately not a second planner: the source-inspection coordinate
-- is exposed as the repository's canonical ExperimentBundle / language
-- extension carrier.
------------------------------------------------------------------------

statutoryPowerInspectionBundle : Synthesis.ExperimentBundle CullenFineWorld
statutoryPowerInspectionBundle =
  Synthesis.experimentBundle
    StatutoryPowerStatus
    inspectStatutoryPower
    1
    "inspect whether statutory power was invoked on the source-correct route"
    "source/judicial-reasons calibration required before legal promotion"

statutoryPowerInspectionSeparatesCollision :
  Synthesis.BundleSeparates
    statutoryPowerInspectionBundle
    (Consumer.left cullenLegacyConsumerCollision)
    (Consumer.right cullenLegacyConsumerCollision)
statutoryPowerInspectionSeparatesCollision =
  Synthesis.bundleSeparates statutoryPowerResidualMustSeparateCullenCollision

cullenCoarseObserverCollision :
  Synthesis.CurrentObserverCollision observePoliceFunctionContext
cullenCoarseObserverCollision =
  Synthesis.currentObserverCollision
    (Consumer.left cullenLegacyConsumerCollision)
    (Consumer.right cullenLegacyConsumerCollision)
    (Consumer.sameSurface cullenLegacyConsumerCollision)

cullenStatutoryPowerLanguageExtension :
  Synthesis.DiscriminatingLanguageExtension observePoliceFunctionContext
cullenStatutoryPowerLanguageExtension =
  Synthesis.discriminatingLanguageExtension
    cullenCoarseObserverCollision
    statutoryPowerInspectionBundle
    statutoryPowerInspectionSeparatesCollision

------------------------------------------------------------------------
-- Consumer-indexing regression.
--
-- After the premise split, a different internal consumer asks only whether the
-- OLD bundled rule is reusable unchanged.  Its answer is the same in both fine
-- worlds: reconstruct the source-correct route.  Therefore statutory-power
-- status is not automatically required for every consumer merely because it
-- was necessary for the legacy bundled-premise PAYMENT consumer.
------------------------------------------------------------------------

data LegacyRuleReuseAudit : Set where
  reconstructSourceCorrectRoute : LegacyRuleReuseAudit

legacyRuleReuseAuditConsumer : CullenFineWorld → LegacyRuleReuseAudit
legacyRuleReuseAuditConsumer _ = reconstructSourceCorrectRoute

policeFunctionObservationSufficientForRuleReuseAudit :
  Consumer.ConsumerSufficient
    observePoliceFunctionContext legacyRuleReuseAuditConsumer
policeFunctionObservationSufficientForRuleReuseAudit left right same = refl

------------------------------------------------------------------------
-- Non-promotions.
------------------------------------------------------------------------

data StatutoryPowerStatusIsNecessaryForCullenDuty : Set where

data ResidualRepairReinstatesLegacyDutyRule : Set where

data RepresentationAdequacyIsJudicialAuthority : Set where

data AnySeparatingResidualIsSourceAdmissible : Set where

data ResidualNeededByOneConsumerIsNeededByEveryConsumer : Set where

statutoryPowerCoordinateDoesNotBecomeDutyElement :
  StatutoryPowerStatusIsNecessaryForCullenDuty → ⊥
statutoryPowerCoordinateDoesNotBecomeDutyElement ()

repairDoesNotReinstateLegacyRule :
  ResidualRepairReinstatesLegacyDutyRule → ⊥
repairDoesNotReinstateLegacyRule ()

representationTheoremIsNotAuthority :
  RepresentationAdequacyIsJudicialAuthority → ⊥
representationTheoremIsNotAuthority ()

separationAloneDoesNotProveSourceAdmissibility :
  AnySeparatingResidualIsSourceAdmissible → ⊥
separationAloneDoesNotProveSourceAdmissibility ()

oneConsumerDoesNotUniversaliseResidual :
  ResidualNeededByOneConsumerIsNeededByEveryConsumer → ⊥
oneConsumerDoesNotUniversaliseResidual ()

------------------------------------------------------------------------
-- Runtime reading.
------------------------------------------------------------------------

firstMissingCoordinateReading : String
firstMissingCoordinateReading =
  "If the current observer collapses two source states that a downstream legal consumer distinguishes, the observer is insufficient. Every consumer-sufficient residual repair must split that exact collision. The collision constrains acquisition; source/authority review decides which separating coordinate is admissible, and necessity remains indexed to the declared consumer."
