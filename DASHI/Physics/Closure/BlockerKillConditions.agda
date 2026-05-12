module DASHI.Physics.Closure.BlockerKillConditions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFResidualConsumerNextObligation as W6
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetFinalSeamObligation as W1
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Physics.Closure.GRQFTConsumerNextObligation as W5
import DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation as W2
import DASHI.Physics.Closure.OriginReceiptPromotionExternalObligation as W8
import DASHI.Physics.Closure.W3AcceptedAuthorityExternalReceiptObligation as W3
import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as W3Gate
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as W4Gate

------------------------------------------------------------------------
-- Receipt-driven blocker-kill matrix.
--
-- The energy-functional surface gives the internal proof spine.  This module
-- records the remaining P0 blockers as receipt-kill conditions: each row says
-- which receipt must exist, which authority/evidence gates it must carry, and
-- that no local surrogate may bypass those gates.

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

record KillCondition : Setω where
  field
    lane :
      BlockerLane

    currentState :
      KillState

    noBypassLaw :
      List NoBypassLaw

------------------------------------------------------------------------
-- Lane-specific authority/evidence wrappers.

record W1KillAuthority
  (receipt : W1.RetargetedFinalSeamReceiptFields) : Setω where
  field
    oldCarrierObstructionAcknowledged :
      W1.RetargetedFinalSeamReceiptFields.oldCurrentCarrierObstructionAcknowledged
        receipt
      ≡
      W1.RetargetedFinalSeamReceiptFields.oldCurrentCarrierObstructionAcknowledged
        receipt

record W1KillEvidence
  (receipt : W1.RetargetedFinalSeamReceiptFields) : Setω where
  field
    finalSeam :
      W1.RetargetedFinalSeamReceiptFields.finalSeamReceipt receipt

    downstreamHandoff :
      W1.RetargetedFinalSeamReceiptFields.downstreamHandoffCompatibility
        receipt

record W2KillAuthority
  (receipt : W2.NaturalP2ConvergencePromotionReceipt) : Setω where
  field
    authorityToken :
      W2.NaturalP2ConvergencePromotionAuthorityToken

record W2KillEvidence
  (receipt : W2.NaturalP2ConvergencePromotionReceipt) : Setω where
  field
    p2Receipt :
      W2.NaturalP2BridgeOrObstructionReceipt

    carrierGeneralConvergence :
      W2.CarrierGeneralConvergenceRateReceipt

record W3KillAuthority
  (receipt : W3.W3AcceptedAuthorityExternalReceipt) : Setω where
  field
    acceptedAuthorityToken :
      W3Gate.W3AcceptedEvidenceAuthorityToken

    tokenMatchesReceipt :
      acceptedAuthorityToken
      ≡
      W3.W3AcceptedAuthorityExternalReceipt.authorityToken receipt

record W3KillEvidence
  (receipt : W3.W3AcceptedAuthorityExternalReceipt) : Setω where
  field
    evidenceAuthorityMatchesReceipt :
      W3Gate.W3EvidenceBackedEmpiricalTarget.evidenceAuthority
        (W3.W3AcceptedAuthorityExternalReceipt.evidenceBackedEmpiricalTarget
          receipt)
      ≡
      W3.W3AcceptedAuthorityExternalReceipt.authorityToken receipt

record W4KillAuthority
  (receipt : W4.Candidate256PhysicalCalibrationExternalReceipt) : Setω where
  field
    calibrationAuthority :
      W4Gate.Candidate256PhysicalCalibrationAuthorityToken

    tokenMatchesReceipt :
      calibrationAuthority
      ≡
      W4.Candidate256PhysicalCalibrationExternalReceipt.calibrationAuthority
        receipt

record W4KillEvidence
  (receipt : W4.Candidate256PhysicalCalibrationExternalReceipt) : Setω where
  field
    physicalUnitCarrier :
      Set

    physicalUnitCarrierMatchesReceipt :
      physicalUnitCarrier
      ≡
      W4.Candidate256PhysicalCalibrationExternalReceipt.physicalUnitCarrier
        receipt

record W5KillAuthority
  (receipt : W5.GRQFTClosurePromotionReceipt) : Setω where
  field
    promotionAuthority :
      W5.GRQFTClosurePromotionAuthorityToken

record W5KillEvidence
  (receipt : W5.GRQFTClosurePromotionReceipt) : Setω where
  field
    downstreamConsumer :
      W5.GRQFTDownstreamConsumerFields

record W6KillAuthority
  (receipt : W6.PNFResidualConsumerReceipt) : Setω where
  field
    runtimeReceiptAuthorityAcknowledged :
      W6.PNFResidualConsumerReceipt.runtimeReceiptId receipt
      ≡
      W6.PNFResidualConsumerReceipt.runtimeReceiptId receipt

record W6KillEvidence
  (receipt : W6.PNFResidualConsumerReceipt) : Setω where

record W8KillAuthority
  (receipt : W8.OriginReceiptPromotionExternalReceipt) : Setω where
  field
    empiricalPromotionEvidence :
      W8.OriginReceiptPromotionEvidence

record W8KillEvidence
  (receipt : W8.OriginReceiptPromotionExternalReceipt) : Setω where

data W9KillRouteReceipt
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  existingPressureWitnessRoute :
    W9.ExistingCancellationPressureCompatibilityObligation theorem dim≡15 →
    W9KillRouteReceipt theorem dim≡15

  weightedReplacementRoute :
    W9.WeightedValuationReplacementObligation theorem dim≡15 →
    W9KillRouteReceipt theorem dim≡15

data W9KillRouteChangeStatus : Set where
  acceptedRouteChangeNeeded :
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
        acceptedRouteChangeNeeded
    ; currentAcceptedW9KillRouteConstructors =
        "existingPressureWitnessRoute : ExistingCancellationPressureCompatibilityObligation theorem dim≡15 -> W9KillRouteReceipt theorem dim≡15"
        ∷ "weightedReplacementRoute : WeightedValuationReplacementObligation theorem dim≡15 -> W9KillRouteReceipt theorem dim≡15"
        ∷ []
    ; missingConstructorName =
        "mdlTerminationSeamRoute"
    ; expectedConsumerModule =
        "DASHI.Physics.Closure.W9MDLTerminationSeamRoute"
    ; requiredConstructorShape =
        "mdlTerminationSeamRoute : W9MDLTerminationSeamKillRouteConsumer canonicalMDLTerminationSeamWitness -> accepted W9 route receipt"
    ; importCycleBoundary =
        "BlockerKillConditions cannot import W9MDLTerminationSeamRoute because that module imports BlockerKillConditions; the accepted route must be introduced by a shared interface or a downstream consumer module."
    ; preservesCurrentBlockedState =
        blocked
    ; preservesCurrentBlockedState≡blocked =
        refl
    ; preservedNoBypassLaw =
        noPressureWitnessByNaming
        ∷ noProsePromotion
        ∷ []
    ; noClosureClaim =
        "This request does not construct W9KillReceipt"
        ∷ "This request does not add a pressure-equality witness"
        ∷ "This request does not assert that the weighted replacement route is satisfied"
        ∷ "W9 remains blocked until an accepted consumer route is added without violating the module boundary"
        ∷ []
    }

record W9KillReceipt : Setω where
  field
    theorem :
      CFQT.ContractionForcesQuadraticTheorem

    dim≡15 :
      CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15

    routeReceipt :
      W9KillRouteReceipt theorem dim≡15

record W9KillAuthority
  (receipt : W9KillReceipt) : Setω where
  field
    routeSelected :
      W9.W9CompatibilityRoute

record W9KillEvidence
  (receipt : W9KillReceipt) : Setω where
  field
    routeReceiptAcknowledged :
      W9KillReceipt

------------------------------------------------------------------------
-- Kill-condition rows.

w1KillCondition : KillCondition
w1KillCondition =
  record
    { lane = W1MdlCr
    ; currentState = unblocked
    ; noBypassLaw =
        noCarrierMergeByAssumption
        ∷ noProsePromotion
        ∷ []
    }

w2KillCondition : KillCondition
w2KillCondition =
  record
    { lane = W2NaturalP2Convergence
    ; currentState = blocked
    ; noBypassLaw =
        noCarrierMergeByAssumption
        ∷ noProsePromotion
        ∷ []
    }

w3KillCondition : KillCondition
w3KillCondition =
  record
    { lane = W3Empirical
    ; currentState = blocked
    ; noBypassLaw =
        noConstructorlessTokenBypass
        ∷ noLocalSurrogatePromotion
        ∷ noEmpiricalByInspection
        ∷ []
    }

w4KillCondition : KillCondition
w4KillCondition =
  record
    { lane = W4Chemistry
    ; currentState = blocked
    ; noBypassLaw =
        noConstructorlessTokenBypass
        ∷ noPhysicalCalibrationByNatSurrogate
        ∷ noLocalSurrogatePromotion
        ∷ []
    }

w5KillCondition : KillCondition
w5KillCondition =
  record
    { lane = W5GRQFT
    ; currentState = blocked
    ; noBypassLaw =
        noConstructorlessTokenBypass
        ∷ noEmpiricalByInspection
        ∷ noProsePromotion
        ∷ []
    }

w6KillCondition : KillCondition
w6KillCondition =
  record
    { lane = W6ITIRPNF
    ; currentState = blocked
    ; noBypassLaw =
        noRuntimeReceiptByInspection
        ∷ noProsePromotion
        ∷ []
    }

w8KillCondition : KillCondition
w8KillCondition =
  record
    { lane = W8Origin
    ; currentState = blocked
    ; noBypassLaw =
        noEmpiricalByInspection
        ∷ noLocalSurrogatePromotion
        ∷ noProsePromotion
        ∷ []
    }

w9KillCondition : KillCondition
w9KillCondition =
  record
    { lane = W9Cancellation
    ; currentState = blocked
    ; noBypassLaw =
        noPressureWitnessByNaming
        ∷ noProsePromotion
        ∷ []
    }

------------------------------------------------------------------------
-- Typed promotion targets.

w1KillPromotes :
  (receipt : W1.RetargetedFinalSeamReceiptFields) →
  W1KillAuthority receipt →
  W1KillEvidence receipt →
  unblocked ≡ unblocked
w1KillPromotes receipt authority evidence = refl

w2KillPromotes :
  (receipt : W2.NaturalP2ConvergencePromotionReceipt) →
  W2KillAuthority receipt →
  W2KillEvidence receipt →
  unblocked ≡ unblocked
w2KillPromotes receipt authority evidence = refl

w3KillPromotes :
  (receipt : W3.W3AcceptedAuthorityExternalReceipt) →
  W3KillAuthority receipt →
  W3KillEvidence receipt →
  unblocked ≡ unblocked
w3KillPromotes receipt authority evidence = refl

w4KillPromotes :
  (receipt : W4.Candidate256PhysicalCalibrationExternalReceipt) →
  W4KillAuthority receipt →
  W4KillEvidence receipt →
  unblocked ≡ unblocked
w4KillPromotes receipt authority evidence = refl

w5KillPromotes :
  (receipt : W5.GRQFTClosurePromotionReceipt) →
  W5KillAuthority receipt →
  W5KillEvidence receipt →
  unblocked ≡ unblocked
w5KillPromotes receipt authority evidence = refl

w6KillPromotes :
  (receipt : W6.PNFResidualConsumerReceipt) →
  W6KillAuthority receipt →
  W6KillEvidence receipt →
  unblocked ≡ unblocked
w6KillPromotes receipt authority evidence = refl

w8KillPromotes :
  (receipt : W8.OriginReceiptPromotionExternalReceipt) →
  W8KillAuthority receipt →
  W8KillEvidence receipt →
  unblocked ≡ unblocked
w8KillPromotes receipt authority evidence = refl

w9KillPromotes :
  (receipt : W9KillReceipt) →
  W9KillAuthority receipt →
  W9KillEvidence receipt →
  unblocked ≡ unblocked
w9KillPromotes receipt authority evidence = refl

record BlockerKillConditionMatrix : Setω where
  field
    w1 :
      KillCondition

    w2 :
      KillCondition

    w3 :
      KillCondition

    w4 :
      KillCondition

    w5 :
      KillCondition

    w6 :
      KillCondition

    w8 :
      KillCondition

    w9 :
      KillCondition

    w1TypedPromotion :
      (receipt : W1.RetargetedFinalSeamReceiptFields) →
      W1KillAuthority receipt →
      W1KillEvidence receipt →
      unblocked ≡ unblocked

    w2TypedPromotion :
      (receipt : W2.NaturalP2ConvergencePromotionReceipt) →
      W2KillAuthority receipt →
      W2KillEvidence receipt →
      unblocked ≡ unblocked

    w3TypedPromotion :
      (receipt : W3.W3AcceptedAuthorityExternalReceipt) →
      W3KillAuthority receipt →
      W3KillEvidence receipt →
      unblocked ≡ unblocked

    w4TypedPromotion :
      (receipt : W4.Candidate256PhysicalCalibrationExternalReceipt) →
      W4KillAuthority receipt →
      W4KillEvidence receipt →
      unblocked ≡ unblocked

    w5TypedPromotion :
      (receipt : W5.GRQFTClosurePromotionReceipt) →
      W5KillAuthority receipt →
      W5KillEvidence receipt →
      unblocked ≡ unblocked

    w6TypedPromotion :
      (receipt : W6.PNFResidualConsumerReceipt) →
      W6KillAuthority receipt →
      W6KillEvidence receipt →
      unblocked ≡ unblocked

    w8TypedPromotion :
      (receipt : W8.OriginReceiptPromotionExternalReceipt) →
      W8KillAuthority receipt →
      W8KillEvidence receipt →
      unblocked ≡ unblocked

    w9TypedPromotion :
      (receipt : W9KillReceipt) →
      W9KillAuthority receipt →
      W9KillEvidence receipt →
      unblocked ≡ unblocked

    matrixBoundary :
      List NoBypassLaw

blockerKillConditionMatrix : BlockerKillConditionMatrix
blockerKillConditionMatrix =
  record
    { w1 = w1KillCondition
    ; w2 = w2KillCondition
    ; w3 = w3KillCondition
    ; w4 = w4KillCondition
    ; w5 = w5KillCondition
    ; w6 = w6KillCondition
    ; w8 = w8KillCondition
    ; w9 = w9KillCondition
    ; w1TypedPromotion = w1KillPromotes
    ; w2TypedPromotion = w2KillPromotes
    ; w3TypedPromotion = w3KillPromotes
    ; w4TypedPromotion = w4KillPromotes
    ; w5TypedPromotion = w5KillPromotes
    ; w6TypedPromotion = w6KillPromotes
    ; w8TypedPromotion = w8KillPromotes
    ; w9TypedPromotion = w9KillPromotes
    ; matrixBoundary =
        noProsePromotion
        ∷ noLocalSurrogatePromotion
        ∷ noConstructorlessTokenBypass
        ∷ []
    }
