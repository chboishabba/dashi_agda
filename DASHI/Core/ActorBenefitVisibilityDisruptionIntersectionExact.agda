module DASHI.Core.ActorBenefitVisibilityDisruptionIntersectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DisruptionBenefitHypothesisExact as Benefit
import DASHI.Core.CommonSelectorVisibilityHyperfabricExact as Visibility
import DASHI.Core.RequiredAxisSupportSquareExact as Support

------------------------------------------------------------------------
-- ACTOR BENEFIT x VISIBILITY x DISRUPTION-EFFECT INTERSECTION
--
-- Evidence-gathering only.  This module distinguishes:
--   * an actor benefits from disruption of a capability;
--   * an actor/system can identify or observe a person;
--   * loss of that person actually disrupts the capability;
--   * case-specific operational/forensic evidence.
--
-- No coordinate compensates for a missing coordinate.
------------------------------------------------------------------------

data ActorCaseAxis : Set where
  benefitAxis
  visibilityAxis
  disruptionEffectAxis
  threatPerceptionAxis
  opportunityOrAccessAxis
  operationalEvidenceAxis
  : ActorCaseAxis

record ActorCapabilityHypothesis : Set where
  constructor actor-capability-hypothesis
  field
    actorLabel : String
    personLabel : String
    capabilityLabel : String
    beneficiary : Benefit.DisruptionBeneficiaryHypothesis
    visibilityClass : Visibility.SelectorClass
    hypothesisReference : String

open ActorCapabilityHypothesis public

record ActorCaseEvidenceState : Set where
  constructor actor-case-evidence-state
  field
    hypothesis : ActorCapabilityHypothesis
    evidenceAt : ActorCaseAxis → Support.SupportSquare
    evidenceReference : ActorCaseAxis → String

open ActorCaseEvidenceState public

AllActorCaseAxesRequired : ActorCaseAxis → Set
AllActorCaseAxesRequired _ = ⊤

actorEvidenceFamily : ActorCaseEvidenceState → Support.AxisEvidenceFamily ActorCaseAxis
actorEvidenceFamily state =
  Support.axisEvidenceFamily (evidenceAt state) AllActorCaseAxesRequired

record CaseSpecificActorIntersection (state : ActorCaseEvidenceState) : Set₁ where
  constructor case-specific-actor-intersection
  field
    requiredAxesResolved : Support.RequiredAxesResolved (actorEvidenceFamily state)
    sameObjectReference : String

open CaseSpecificActorIntersection public

missingAxisBlocksCaseSpecificIntersection :
  ∀ {state : ActorCaseEvidenceState} →
  Support.MissingRequiredAxis (actorEvidenceFamily state) →
  CaseSpecificActorIntersection state → ⊥
missingAxisBlocksCaseSpecificIntersection missing intersection =
  Support.missingRequiredAxisBlocksResolution
    missing
    (requiredAxesResolved intersection)

------------------------------------------------------------------------
-- Coarser research stages.  These are useful even when actor attribution is
-- nowhere near resolved.
------------------------------------------------------------------------

record BenefitEstablished (state : ActorCaseEvidenceState) : Set where
  constructor benefit-established
  field
    benefitReceipt : Support.ResolvedPositive (evidenceAt state benefitAxis)

record VisibilityEstablished (state : ActorCaseEvidenceState) : Set where
  constructor visibility-established
  field
    visibilityReceipt : Support.ResolvedPositive (evidenceAt state visibilityAxis)

record ActualDisruptionEstablished (state : ActorCaseEvidenceState) : Set where
  constructor actual-disruption-established
  field
    disruptionReceipt : Support.ResolvedPositive (evidenceAt state disruptionEffectAxis)

------------------------------------------------------------------------
-- Boundary receipts.
------------------------------------------------------------------------

record ActorIntersectionBoundary : Set where
  constructor actor-intersection-boundary
  field
    benefitPlusVisibilityAutomaticallyEstablishesPerpetration : Bool
    benefitPlusVisibilityAutomaticallyEstablishesPerpetrationIsFalse :
      benefitPlusVisibilityAutomaticallyEstablishesPerpetration ≡ false

    historicalSabotagePrecedentCanFillOperationalEvidenceAxis : Bool
    historicalSabotagePrecedentCanFillOperationalEvidenceAxisIsFalse :
      historicalSabotagePrecedentCanFillOperationalEvidenceAxis ≡ false

    actualProgrammeDelayAutomaticallyIdentifiesWhoCausedLoss : Bool
    actualProgrammeDelayAutomaticallyIdentifiesWhoCausedLossIsFalse :
      actualProgrammeDelayAutomaticallyIdentifiesWhoCausedLoss ≡ false

    missingOneRequiredAxisMayBeCompensatedByStrongEvidenceElsewhere : Bool
    missingOneRequiredAxisMayBeCompensatedByStrongEvidenceElsewhereIsFalse :
      missingOneRequiredAxisMayBeCompensatedByStrongEvidenceElsewhere ≡ false

    publicVisibilityCanStillBeRelevantToActorDiscovery : Bool
    publicVisibilityCanStillBeRelevantToActorDiscoveryIsTrue :
      publicVisibilityCanStillBeRelevantToActorDiscovery ≡ true

canonicalActorIntersectionBoundary : ActorIntersectionBoundary
canonicalActorIntersectionBoundary = actor-intersection-boundary
  false refl
  false refl
  false refl
  false refl
  true refl
