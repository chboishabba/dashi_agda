module DASHI.Physics.Closure.BlockerKillConditionsBase where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Neutral blocker-kill vocabulary.
--
-- This module is intentionally free of lane receipt imports.  Downstream
-- seam-route diagnostics can depend on these request/state types without
-- importing the full kill matrix or creating a theorem-consumer cycle.

data KillState : Set where
  blocked :
    KillState
  unblocked :
    KillState

data BlockerLane : Set where
  W1MdlCr :
    BlockerLane
  W2NaturalP2Convergence :
    BlockerLane
  W3Empirical :
    BlockerLane
  W4Chemistry :
    BlockerLane
  W5GRQFT :
    BlockerLane
  W6ITIRPNF :
    BlockerLane
  W8Origin :
    BlockerLane
  W9Cancellation :
    BlockerLane

data NoBypassLaw : Set where
  noProsePromotion :
    NoBypassLaw
  noLocalSurrogatePromotion :
    NoBypassLaw
  noConstructorlessTokenBypass :
    NoBypassLaw
  noCarrierMergeByAssumption :
    NoBypassLaw
  noEmpiricalByInspection :
    NoBypassLaw
  noPhysicalCalibrationByNatSurrogate :
    NoBypassLaw
  noRuntimeReceiptByInspection :
    NoBypassLaw
  noPressureWitnessByNaming :
    NoBypassLaw

record KillCondition : Set where
  field
    lane :
      BlockerLane

    currentState :
      KillState

    noBypassLaw :
      List NoBypassLaw

data W9KillRouteChangeStatus : Set where
  acceptedRouteChangeNeeded :
    W9KillRouteChangeStatus
  acceptedRouteChangeInstalled :
    W9KillRouteChangeStatus

record W9MDLTerminationSeamAcceptedRouteRequest : Set where
  field
    routeChangeStatus :
      W9KillRouteChangeStatus

    currentAcceptedW9KillRouteConstructors :
      List String

    missingConstructorName :
      String

    expectedConsumerModule :
      String

    requiredConstructorShape :
      String

    importCycleBoundary :
      String

    preservesCurrentBlockedState :
      KillState

    preservesCurrentBlockedState≡blocked :
      preservesCurrentBlockedState ≡ blocked

    preservedNoBypassLaw :
      List NoBypassLaw

    noClosureClaim :
      List String

canonicalW9MDLTerminationSeamAcceptedRouteRequest :
  W9MDLTerminationSeamAcceptedRouteRequest
canonicalW9MDLTerminationSeamAcceptedRouteRequest =
  record
    { routeChangeStatus =
        acceptedRouteChangeInstalled
    ; currentAcceptedW9KillRouteConstructors =
        "existingPressureWitnessRoute : ExistingCancellationPressureCompatibilityObligation theorem dim≡15 -> W9KillRouteReceipt theorem dim≡15"
        ∷ "weightedReplacementRoute : WeightedValuationReplacementObligation theorem dim≡15 -> W9KillRouteReceipt theorem dim≡15"
        ∷ "mdlTerminationSeamRoute : W9MDLTerminationSeamKillRouteConsumer canonicalMDLTerminationSeamWitness -> W9KillRouteReceipt theorem dim≡15"
        ∷ []
    ; missingConstructorName =
        "none"
    ; expectedConsumerModule =
        "DASHI.Physics.Closure.W9MDLTerminationSeamRoute"
    ; requiredConstructorShape =
        "installed: mdlTerminationSeamRoute : W9MDLTerminationSeamKillRouteConsumer canonicalMDLTerminationSeamWitness -> W9KillRouteReceipt theorem dim≡15"
    ; importCycleBoundary =
        "BlockerKillConditionsBase carries only neutral status/request vocabulary; BlockerKillConditions imports W9MDLTerminationSeamRoute after the seam module was split to depend only on this base, avoiding a theorem-consumer cycle."
    ; preservesCurrentBlockedState =
        blocked
    ; preservesCurrentBlockedState≡blocked =
        refl
    ; preservedNoBypassLaw =
        noPressureWitnessByNaming
        ∷ noProsePromotion
        ∷ []
    ; noClosureClaim =
        "The accepted route does not add a pressure-equality witness"
        ∷ "This request does not assert that the weighted replacement route is satisfied"
        ∷ "The kill-condition row remains marked blocked until governance promotes the lane state"
        ∷ []
    }
