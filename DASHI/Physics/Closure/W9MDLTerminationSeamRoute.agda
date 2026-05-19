module DASHI.Physics.Closure.W9MDLTerminationSeamRoute where

-- W9 MDL termination seam route.
--
-- This module records the strongest non-pressure route currently supported by
-- local receipts: normalizeAdd reaches its canonical carry-resolved state in
-- one step, the observable sum is preserved, and the carry-depth/budget scalar
-- is already packaged as a CancellationPressureLyapunovBridge.  The route is
-- accepted by the main W9 kill route through the kill-matrix constructor that
-- consumes this MDL termination seam.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Arithmetic.CancellationPressureCore as Core
import DASHI.Arithmetic.CancellationPressureLyapunovBridge as Bridge
import DASHI.Arithmetic.CancellationPressureMDL as CP-MDL
import DASHI.Arithmetic.NormalizeAdd as NA
import DASHI.Arithmetic.NormalizeAddState as NAS
import DASHI.Arithmetic.NormalizeAddSumPreservation as Sum
import DASHI.MDL.MDLLyapunov as MDL
import DASHI.Physics.Closure.BlockerKillConditionsBase as KillBase
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation as W9f
import DASHI.Physics.Closure.W9LyapunovAdapterReceipt as W9a
import DASHI.Physics.Closure.W9WeightedSupportRetargetConsumerReceipt as W9r

normalizeAdd-idempotent :
  ∀ s →
  NA.normalizeAdd (NA.normalizeAdd s)
  ≡
  NA.normalizeAdd s
normalizeAdd-idempotent _ = refl

data MDLTerminationSeamScope : Set where
  normalizeAddOneStepCarryResolution :
    MDLTerminationSeamScope

data MDLTerminationSeamBoundary : Set where
  nonPressureRoute :
    MDLTerminationSeamBoundary
  nonQcoreRoute :
    MDLTerminationSeamBoundary
  noAdmissibleQuadraticPromotion :
    MDLTerminationSeamBoundary
  noCancellationPressureCompatibilityPromotion :
    MDLTerminationSeamBoundary
  currentKillMatrixConstructorAccepted :
    MDLTerminationSeamBoundary

record MDLTerminationSeamWitness : Setω where
  field
    State :
      Set

    step :
      State → State

    terminal :
      State → Set

    pressureCore :
      Core.CancellationPressureCore

    mdlFunctional :
      MDL.MDLFunctional State

    mdlBridge :
      CP-MDL.CancellationPressureMDL pressureCore

    lyapunovBridge :
      Bridge.CancellationPressureLyapunovBridge pressureCore

    sumPreservationReceipt :
      Sum.NormalizeAddSumPreservationReceipt

    retargetConsumerReceipt :
      W9r.WeightedSupportRetargetConsumerReceipt

    stepReachesTerminal :
      ∀ s →
      terminal (step s)

    stepIdempotentAtTerminal :
      ∀ s →
      step (step s) ≡ step s

    scope :
      MDLTerminationSeamScope

    boundary :
      List MDLTerminationSeamBoundary

    noPressureEqualityClaim :
      List String

canonicalMDLTerminationSeamWitness :
  MDLTerminationSeamWitness
canonicalMDLTerminationSeamWitness =
  record
    { State =
        NAS.NormalizeAddState
    ; step =
        NA.normalizeAdd
    ; terminal =
        NAS.normalizeAddCanonical
    ; pressureCore =
        W9a.carryDepthBudgetPressureCore
    ; mdlFunctional =
        W9a.carryDepthBudgetMDLFunctional
    ; mdlBridge =
        W9a.carryDepthBudgetCancellationPressureMDL
    ; lyapunovBridge =
        W9a.carryDepthBudgetLyapunovBridge
    ; sumPreservationReceipt =
        Sum.canonicalNormalizeAddSumPreservationReceipt
    ; retargetConsumerReceipt =
        W9r.canonicalWeightedSupportRetargetConsumerReceipt
    ; stepReachesTerminal =
        NA.normalizeAdd-canonical
    ; stepIdempotentAtTerminal =
        normalizeAdd-idempotent
    ; scope =
        normalizeAddOneStepCarryResolution
    ; boundary =
        nonPressureRoute
        ∷ nonQcoreRoute
        ∷ noAdmissibleQuadraticPromotion
        ∷ noCancellationPressureCompatibilityPromotion
        ∷ currentKillMatrixConstructorAccepted
        ∷ []
    ; noPressureEqualityClaim =
        "This witness uses NormalizeAddState termination and MDL Lyapunov descent"
        ∷ "It does not provide ExistingCancellationPressureCompatibilityObligation.pressureWitness"
        ∷ "It does not provide WeightedValuationReplacementObligation.cancellationPressureIdentifiesWeightedQuadraticEnergy"
        ∷ "It does not construct CancellationPressureCompatibility or W9KillReceipt"
        ∷ []
    }

record W9MDLTerminationSeamKillRouteConsumer
  (witness : MDLTerminationSeamWitness) : Setω where
  field
    consumesWitnessScope :
      MDLTerminationSeamWitness.scope witness
      ≡
      normalizeAddOneStepCarryResolution

    consumesRetargetAcceptance :
      W9f.CancellationPressureRetargetConsumerAcceptanceReceipt
        W9r.weightedSupportRetargetConsumer
        W9.canonicalPairPressureRetargetReceipt

    consumesWitnessRetargetAcceptance :
      W9f.CancellationPressureRetargetConsumerAcceptanceReceipt
        (W9r.WeightedSupportRetargetConsumerReceipt.consumer
          (MDLTerminationSeamWitness.retargetConsumerReceipt witness))
        W9.canonicalPairPressureRetargetReceipt

    consumesWitnessRetargetScope :
      W9r.WeightedSupportRetargetConsumerReceipt.receiptScope
        (MDLTerminationSeamWitness.retargetConsumerReceipt witness)
      ≡
      W9r.retargetConsumerAcceptedOnly

    preservesRetargetNonPromotion :
      W9.PressureCompatibleTargetWithQcoreBoundaryReceipt.nonPromotionBoundary
        W9.canonicalPairPressureRetargetReceipt
      ≡
      W9.retargetMustNotClaimCanonicalQcore

    preservesCurrentW9BlockedState :
      KillBase.W9MDLTerminationSeamAcceptedRouteRequest.preservesCurrentBlockedState
        KillBase.canonicalW9MDLTerminationSeamAcceptedRouteRequest
      ≡
      KillBase.blocked

    consumerBoundary :
      List MDLTerminationSeamBoundary

canonicalW9MDLTerminationSeamKillRouteConsumer :
  W9MDLTerminationSeamKillRouteConsumer
    canonicalMDLTerminationSeamWitness
canonicalW9MDLTerminationSeamKillRouteConsumer =
  record
    { consumesWitnessScope =
        refl
    ; consumesRetargetAcceptance =
        W9r.weightedSupportRetargetAcceptanceReceipt
    ; consumesWitnessRetargetAcceptance =
        W9r.WeightedSupportRetargetConsumerReceipt.acceptance
          (MDLTerminationSeamWitness.retargetConsumerReceipt
            canonicalMDLTerminationSeamWitness)
    ; consumesWitnessRetargetScope =
        refl
    ; preservesRetargetNonPromotion =
        refl
    ; preservesCurrentW9BlockedState =
        refl
    ; consumerBoundary =
        nonPressureRoute
        ∷ nonQcoreRoute
        ∷ noCancellationPressureCompatibilityPromotion
        ∷ currentKillMatrixConstructorAccepted
        ∷ []
    }

data W9MDLTerminationSeamRouteStatus : Set where
  witnessConstructedAcceptedByMainW9KillRoute :
    W9MDLTerminationSeamRouteStatus

record W9MDLTerminationSeamRouteChangeRequest : Setω where
  field
    routeStatus :
      W9MDLTerminationSeamRouteStatus

    killMatrixRouteChangeRequest :
      KillBase.W9MDLTerminationSeamAcceptedRouteRequest

    witness :
      MDLTerminationSeamWitness

    nonPressureConsumer :
      W9MDLTerminationSeamKillRouteConsumer witness

    currentKillMatrixState :
      KillBase.KillState

    currentKillMatrixStateIsBlocked :
      currentKillMatrixState ≡ KillBase.blocked

    currentAcceptedW9KillRouteConstructors :
      List String

    missingConstructorName :
      String

    exactAcceptedTheoremConsumerRouteChange :
      String

    requiredConstructorShape :
      String

    preservedBoundaries :
      List MDLTerminationSeamBoundary

    noClosureClaim :
      List String

canonicalW9MDLTerminationSeamRouteChangeRequest :
  W9MDLTerminationSeamRouteChangeRequest
canonicalW9MDLTerminationSeamRouteChangeRequest =
  record
    { routeStatus =
        witnessConstructedAcceptedByMainW9KillRoute
    ; killMatrixRouteChangeRequest =
        KillBase.canonicalW9MDLTerminationSeamAcceptedRouteRequest
    ; witness =
        canonicalMDLTerminationSeamWitness
    ; nonPressureConsumer =
        canonicalW9MDLTerminationSeamKillRouteConsumer
    ; currentKillMatrixState =
        KillBase.blocked
    ; currentKillMatrixStateIsBlocked =
        refl
    ; currentAcceptedW9KillRouteConstructors =
        "existingPressureWitnessRoute : ExistingCancellationPressureCompatibilityObligation theorem dim≡15 -> W9KillRouteReceipt theorem dim≡15"
        ∷ "weightedReplacementRoute : WeightedValuationReplacementObligation theorem dim≡15 -> W9KillRouteReceipt theorem dim≡15"
        ∷ "mdlTerminationSeamRoute : W9MDLTerminationSeamKillRouteConsumer canonicalMDLTerminationSeamWitness -> W9KillRouteReceipt theorem dim≡15"
        ∷ []
    ; missingConstructorName =
        "none"
    ; exactAcceptedTheoremConsumerRouteChange =
        "Installed mdlTerminationSeamRoute in BlockerKillConditions.W9KillRouteReceipt; it explicitly accepts the non-pressure MDLTerminationSeamWitness while preserving the non-Qcore retarget boundary."
    ; requiredConstructorShape =
        "mdlTerminationSeamRoute : W9MDLTerminationSeamKillRouteConsumer canonicalMDLTerminationSeamWitness -> W9KillRouteReceipt theorem dim≡15"
    ; preservedBoundaries =
        nonPressureRoute
        ∷ nonQcoreRoute
        ∷ noAdmissibleQuadraticPromotion
        ∷ noCancellationPressureCompatibilityPromotion
        ∷ []
    ; noClosureClaim =
        "The MDL termination seam witness is constructed and consumed locally"
        ∷ "The main W9 kill matrix now consumes it through mdlTerminationSeamRoute"
        ∷ "No W9KillReceipt is constructed by this module, avoiding an import cycle back to the kill matrix"
        ∷ "No pressure equality or weighted cancellation-to-quadratic identification is fabricated"
        ∷ []
    }

currentW9MDLTerminationSeamStatus :
  W9MDLTerminationSeamRouteStatus
currentW9MDLTerminationSeamStatus =
  W9MDLTerminationSeamRouteChangeRequest.routeStatus
    canonicalW9MDLTerminationSeamRouteChangeRequest
