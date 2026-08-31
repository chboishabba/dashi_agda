module DASHI.Analysis.RiemannAristotlePoleNearTranslationModulationBidiMeetingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Analysis.RiemannAristotlePoleNearTranslationModulationIntertwinerExact as HT
import DASHI.Analysis.RiemannAristotlePoleNearWindowRestrictionResidualExact as HW

------------------------------------------------------------------------
-- EARLY BIDI MEETING
--
-- Previously the direct phase-statistic and explicit-formula routes first met
-- at the final SignedFiniteNearEvaluationSurface.  The Monster translation /
-- modulation xpollination reveals an earlier common producer: H_T.
--
-- This owner prevents the two routes from supplying independently chosen
-- centring/modulation conventions.
------------------------------------------------------------------------

record EarlyPoleNearBidiMeeting : Set₁ where
  constructor early-pole-near-bidi-meeting
  field
    H_T : HT.TargetTranslationModulationIntertwiner

    directConsumer : HT.DirectPhaseConsumer H_T
    explicitFormulaConsumer : HT.ExplicitFormulaModulationConsumer H_T

    -- The explicit-formula branch additionally carries the restriction leaf.
    H_W : HW.PoleNearWindowRestriction H_T
    windowAuthority : HW.WindowRestrictionAuthority H_T H_W

    -- Both views certify that the same target-centred modulation convention is
    -- being consumed.  No equality between unrelated proof objects is assumed;
    -- sharing H_T by dependency is the authority.
    sameHTFeedsBothRoutes : Set
    meetingReference : Agda.Builtin.String.String

open EarlyPoleNearBidiMeeting public

record EarlyBidiMeetingBoundary : Set where
  constructor early-bidi-meeting-boundary
  field
    routesFirstMeetOnlyAtFinalEvaluation : Bool
    routesFirstMeetOnlyAtFinalEvaluationIsFalse :
      routesFirstMeetOnlyAtFinalEvaluation ≡ false

    routesShareTranslationModulationPrerequisite : Bool
    routesShareTranslationModulationPrerequisiteIsTrue :
      routesShareTranslationModulationPrerequisite ≡ true

    explicitFormulaRouteAlsoNeedsRestrictionResidual : Bool
    explicitFormulaRouteAlsoNeedsRestrictionResidualIsTrue :
      explicitFormulaRouteAlsoNeedsRestrictionResidual ≡ true

    monsterCarrierIdentifiedWithRHCarrier : Bool
    monsterCarrierIdentifiedWithRHCarrierIsFalse :
      monsterCarrierIdentifiedWithRHCarrier ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalEarlyBidiMeetingBoundary : EarlyBidiMeetingBoundary
canonicalEarlyBidiMeetingBoundary =
  early-bidi-meeting-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
