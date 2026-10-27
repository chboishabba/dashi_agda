module DASHI.Unified.Physics where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Physics.Closure.ClayNSProofRoadmapReceipt as NSRoadmap
import DASHI.Physics.Closure.ClayYMProofRoadmapReceipt as YMRoadmap
import DASHI.Physics.Closure.YMClayPromotionBoundary as YMBoundary
import DASHI.Physics.Closure.NSABCDMaxCut20261002Exact as NSMaxCut
import DASHI.Unified.InvariantSpine as Spine
import DASHI.Unified.NSABCDTOENonPromotionBridgeExact as NSABCDTOE
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact as NSTOE
import DASHI.Unified.NavierStokesR650DecisionTOEConvergenceExact as NSDecisionTOE

navierStokesObject : Spine.UnifiedObjectInvariant
navierStokesObject =
  Spine.unifiedObjectInvariant
    "navier-stokes-approach-parent"
    Unified.physicsLane
    "Navier-Stokes carrier and roadmap observations"
    "flow/PDE carrier -> approach lane -> blocked external theorem promotion"
    Unified.flowCarrier
    (Spine.defaultRoleVector "navier-stokes-approach-parent")
    Residual.partial
    Asserted.approachingClosedProof
    Spine.blockedInvariant
    (Spine.blockedJProjection "Navier-Stokes has no inhabited modular-j proof bridge")
    (Spine.blockedFormalProjectionBundle "Navier-Stokes projections are present as blocked non-promoting parent carriers")

yangMillsObject : Spine.UnifiedObjectInvariant
yangMillsObject =
  Spine.unifiedObjectInvariant
    "yang-mills-approach-parent"
    Unified.physicsLane
    "Yang-Mills carrier, RG, OS/Wightman, and Clay-boundary observations"
    "gauge/QFT carrier -> approach lane -> blocked external theorem promotion"
    Unified.gaugeCarrier
    (Spine.defaultRoleVector "yang-mills-approach-parent")
    Residual.partial
    Asserted.approachingClosedProof
    Spine.blockedInvariant
    (Spine.blockedJProjection "Yang-Mills has no inhabited modular-j proof bridge")
    (Spine.blockedFormalProjectionBundle "Yang-Mills projections are present as blocked non-promoting parent carriers")

canonicalPhysicsObjects : List Spine.UnifiedObjectInvariant
canonicalPhysicsObjects =
  navierStokesObject ∷ yangMillsObject ∷ []

navierStokesJPromotionBlocked :
  Spine.objectExternalJPromotion navierStokesObject ≡ false
navierStokesJPromotionBlocked =
  refl

yangMillsJPromotionBlocked :
  Spine.objectExternalJPromotion yangMillsObject ≡ false
yangMillsJPromotionBlocked =
  refl

navierStokesPostureIsApproaching :
  Spine.proofPosture navierStokesObject ≡ Asserted.approachingClosedProof
navierStokesPostureIsApproaching =
  refl

yangMillsPostureIsApproaching :
  Spine.proofPosture yangMillsObject ≡ Asserted.approachingClosedProof
yangMillsPostureIsApproaching =
  refl


------------------------------------------------------------------------
-- Exact NS max-cut TOE attachment.
------------------------------------------------------------------------

navierStokesABCDTOEConvergenceReceipt :
  NSABCDTOE.NSABCDTOEConvergenceReceipt
navierStokesABCDTOEConvergenceReceipt =
  NSABCDTOE.canonicalNSABCDTOEConvergenceReceipt

navierStokesClayPromotionRemainsFalse :
  NSMaxCut.clayPromotion ≡ false
navierStokesClayPromotionRemainsFalse =
  NSABCDTOE.nsClayPromotionRemainsFalse


navierStokesR650CombinedSelfExternalRecombined :
  NSTOE.NSR650.round650SelfExternalRecombineToSingleGlobalCommutator ≡ true
navierStokesR650CombinedSelfExternalRecombined =
  NSTOE.toeNSR650CombinedSelfExternalRecombined

navierStokesR650CombinedPaymentRemainsOpen :
  NSTOE.NSR650.round650CombinedSelfExternalCutoffUniformPaymentClosed ≡ false
navierStokesR650CombinedPaymentRemainsOpen =
  NSTOE.toeNSR650CombinedCutoffUniformPaymentRemainsOpen

navierStokesR650ClayPromotionRemainsFalse :
  NSTOE.NSR650.round650ClayPromotion ≡ false
navierStokesR650ClayPromotionRemainsFalse =
  NSTOE.toeNSR650ClayPromotionRemainsFalse
