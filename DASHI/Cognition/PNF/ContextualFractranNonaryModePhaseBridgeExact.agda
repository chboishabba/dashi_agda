module DASHI.Cognition.PNF.ContextualFractranNonaryModePhaseBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- The exact nonary quotient is one fixed identity mode plus four inverse
-- phase pairs.  This file exposes its phase as SSPTrit without identifying the
-- nine-state carrier with C9 or with a semantic predicate space.
------------------------------------------------------------------------

modePhaseTrit : Five.ModePhaseQuotient9 → Trit.SSPTrit
modePhaseTrit Five.identityMode = Trit.sspZero
modePhaseTrit Five.A2negative = Trit.sspNegOne
modePhaseTrit Five.A2positive = Trit.sspPosOne
modePhaseTrit Five.B1negative = Trit.sspNegOne
modePhaseTrit Five.B1positive = Trit.sspPosOne
modePhaseTrit Five.B2negative = Trit.sspNegOne
modePhaseTrit Five.B2positive = Trit.sspPosOne
modePhaseTrit Five.Enegative = Trit.sspNegOne
modePhaseTrit Five.Epositive = Trit.sspPosOne

invertModePhase : Five.ModePhaseQuotient9 → Five.ModePhaseQuotient9
invertModePhase Five.identityMode = Five.identityMode
invertModePhase Five.A2negative = Five.A2positive
invertModePhase Five.A2positive = Five.A2negative
invertModePhase Five.B1negative = Five.B1positive
invertModePhase Five.B1positive = Five.B1negative
invertModePhase Five.B2negative = Five.B2positive
invertModePhase Five.B2positive = Five.B2negative
invertModePhase Five.Enegative = Five.Epositive
invertModePhase Five.Epositive = Five.Enegative

invertModePhaseInvolutive :
  (state : Five.ModePhaseQuotient9) →
  invertModePhase (invertModePhase state) ≡ state
invertModePhaseInvolutive Five.identityMode = refl
invertModePhaseInvolutive Five.A2negative = refl
invertModePhaseInvolutive Five.A2positive = refl
invertModePhaseInvolutive Five.B1negative = refl
invertModePhaseInvolutive Five.B1positive = refl
invertModePhaseInvolutive Five.B2negative = refl
invertModePhaseInvolutive Five.B2positive = refl
invertModePhaseInvolutive Five.Enegative = refl
invertModePhaseInvolutive Five.Epositive = refl

modePhaseObservationIntertwines :
  (state : Five.ModePhaseQuotient9) →
  modePhaseTrit (invertModePhase state)
  ≡ Context.negateTrit (modePhaseTrit state)
modePhaseObservationIntertwines Five.identityMode = refl
modePhaseObservationIntertwines Five.A2negative = refl
modePhaseObservationIntertwines Five.A2positive = refl
modePhaseObservationIntertwines Five.B1negative = refl
modePhaseObservationIntertwines Five.B1positive = refl
modePhaseObservationIntertwines Five.B2negative = refl
modePhaseObservationIntertwines Five.B2positive = refl
modePhaseObservationIntertwines Five.Enegative = refl
modePhaseObservationIntertwines Five.Epositive = refl

identityModeIsFold : modePhaseTrit Five.identityMode ≡ Trit.sspZero
identityModeIsFold = refl

record ContextualNonaryPhaseBoundary : Set where
  constructor contextualNonaryPhaseBoundary
  field
    nonaryHasOneFixedPlusFourInversePairs : Bool
    identityModeCarriesBinaryOrientationAfterQuotient : Bool
    modePhaseObservationIsSSPPolarity : Bool
    nonaryQuotientIsAutomaticallyC9SemanticPhase : Bool

canonicalContextualNonaryPhaseBoundary : ContextualNonaryPhaseBoundary
canonicalContextualNonaryPhaseBoundary =
  contextualNonaryPhaseBoundary true false true false
