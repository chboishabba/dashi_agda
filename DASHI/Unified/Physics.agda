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
import DASHI.Unified.InvariantSpine as Spine
import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as YMTOE
open import DASHI.Physics.YangMills.CompactLieProofLevel

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
-- Reuse the canonical Yang-Mills TOE convergence boundary.
------------------------------------------------------------------------

yangMillsTOEClayPromotionBlocked :
  YMTOE.toeClayYangMillsPromoted ≡ false
yangMillsTOEClayPromotionBlocked =
  YMTOE.toeClayYangMillsPromotedIsFalse

yangMillsTOECriticalFamilyCountIsSeven :
  YMTOE.toeCriticalFamilyCount ≡ 7
yangMillsTOECriticalFamilyCountIsSeven =
  YMTOE.toeCriticalFamilyCountIsSeven

yangMillsTOEIrreducibleFamilyCountIsFourteen :
  YMTOE.toeIrreducibleSourceFamilyCount ≡ 14
yangMillsTOEIrreducibleFamilyCountIsFourteen =
  YMTOE.toeIrreducibleSourceFamilyCountIsFourteen


yangMillsTOEPublishedRGDoesNotPromoteContinuum :
  YMTOE.toeFlat4DContinuumTransferProvedHere ≡ false
yangMillsTOEPublishedRGDoesNotPromoteContinuum =
  YMTOE.toePublishedRGDoesNotPromoteContinuum

yangMillsTOEContinuumMassGapBlocked :
  YMTOE.toeContinuumMassGapPromoted ≡ false
yangMillsTOEContinuumMassGapBlocked =
  YMTOE.toeContinuumMassGapPromotedIsFalse

------------------------------------------------------------------------
-- Antigravity S4 / P3G normalized TOE surface.
------------------------------------------------------------------------

yangMillsTOEAntigravityS4CompilerLevel :
  ProofLevel
yangMillsTOEAntigravityS4CompilerLevel =
  YMTOE.toeAntigravityS4PhysicalMinCutCompilerLevel

yangMillsTOEAntigravityP3GCompilerLevel :
  ProofLevel
yangMillsTOEAntigravityP3GCompilerLevel =
  YMTOE.toeAntigravityP3GPhysicalProducerCompilerLevel

yangMillsTOEAntigravityInitialSharedCouplingLevel :
  ProofLevel
yangMillsTOEAntigravityInitialSharedCouplingLevel =
  YMTOE.toeAntigravityP3GInitialSharedCouplingLevel

yangMillsTOEAntigravityLocalRemainderLevel :
  ProofLevel
yangMillsTOEAntigravityLocalRemainderLevel =
  YMTOE.toeAntigravityP3GLocalRemainderLevel
