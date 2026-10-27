module DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact where

open import DASHI.Core.Prelude

import Base369
import DASHI.Core.SymmetryResolvedFibreExact as TOE
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.SSPHyperfibreSymmetryTowerExact as Tower
import DASHI.Biology.SSPIndexedWeaveHyperfabricExact as Weave
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SU2
import DASHI.Physics.Closure.SSP369PolarResidualQuotient as Polar
import DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel as Address
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Physics.Closure.NSTriadKNStage3Ternary369Ledger as NS369
import DASHI.Physics.Closure.NSCross369OrientationBridgeExact as NSCross
import DASHI.Physics.Closure.NSTriadKN369HighHighGramBridgeReceipt as NSGram
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.IncompressibleEulerGalerkinCoreExact as EulerCompat
import DASHI.Physics.Closure.AlpogeBuckmasterSmoothForcedEulerBlowupBoundaryExact as ABEuler
import DASHI.Foundations.Base369MobiusTransport as Mobius

------------------------------------------------------------------------
-- 1. Native SSP ternary orientation is already a lawful algebra/action.
--
-- This is the theorem-bearing replacement for treating a later Boolean
-- support shadow as the algebraic authority of SSP.
------------------------------------------------------------------------

sspOrientationAction : TOE.LawfulAction SSP.FibreOrientation Tower.LaneState
sspOrientationAction = record
  { identity = SSP.mediatedOrientation
  ; compose = Weave.composeOrientation
  ; act = Weave.transportOrientation
  ; composeIdLeft = Weave.composeOrientationIdLeft
  ; composeIdRight = Weave.composeOrientationIdRight
  ; composeAssoc = Weave.composeOrientationAssoc
  ; actIdentity = λ state → refl
  ; actComposition = Weave.transportOrientationComposition
  }

sspNativeCompositionPreserved :
  (q p : SSP.FibreOrientation) →
  (state : Tower.LaneState) →
  TOE.act sspOrientationAction (TOE.compose sspOrientationAction q p) state
  ≡
  TOE.act sspOrientationAction q (TOE.act sspOrientationAction p state)
sspNativeCompositionPreserved = TOE.actComposition sspOrientationAction

------------------------------------------------------------------------
-- 2. The finite SU(2)/SO(3)-motivated 6 -> 3 two-sheet adapter is an exact
-- symmetry-resolved fibre.  The central sheet flip acts nontrivially upstairs
-- and trivially on the projected axis, while polarity is retained as the
-- reopening residual.
------------------------------------------------------------------------

composeLiftPolarity :
  Mobius.OrientationPolarity →
  Mobius.OrientationPolarity →
  Mobius.OrientationPolarity
composeLiftPolarity Mobius.positive polarity = polarity
composeLiftPolarity Mobius.negative Mobius.positive = Mobius.negative
composeLiftPolarity Mobius.negative Mobius.negative = Mobius.positive

composeLiftPolarityIdLeft :
  (p : Mobius.OrientationPolarity) →
  composeLiftPolarity Mobius.positive p ≡ p
composeLiftPolarityIdLeft Mobius.positive = refl
composeLiftPolarityIdLeft Mobius.negative = refl

composeLiftPolarityIdRight :
  (p : Mobius.OrientationPolarity) →
  composeLiftPolarity p Mobius.positive ≡ p
composeLiftPolarityIdRight Mobius.positive = refl
composeLiftPolarityIdRight Mobius.negative = refl

composeLiftPolarityAssoc :
  (r q p : Mobius.OrientationPolarity) →
  composeLiftPolarity (composeLiftPolarity r q) p
  ≡ composeLiftPolarity r (composeLiftPolarity q p)
composeLiftPolarityAssoc Mobius.positive Mobius.positive Mobius.positive = refl
composeLiftPolarityAssoc Mobius.positive Mobius.positive Mobius.negative = refl
composeLiftPolarityAssoc Mobius.positive Mobius.negative Mobius.positive = refl
composeLiftPolarityAssoc Mobius.positive Mobius.negative Mobius.negative = refl
composeLiftPolarityAssoc Mobius.negative Mobius.positive Mobius.positive = refl
composeLiftPolarityAssoc Mobius.negative Mobius.positive Mobius.negative = refl
composeLiftPolarityAssoc Mobius.negative Mobius.negative Mobius.positive = refl
composeLiftPolarityAssoc Mobius.negative Mobius.negative Mobius.negative = refl

liftAction : Mobius.OrientationPolarity → SU2.AxisLift → SU2.AxisLift
liftAction Mobius.positive lifted = lifted
liftAction Mobius.negative lifted = SU2.flipAxisLift lifted

liftActionComposition :
  (q p : Mobius.OrientationPolarity) →
  (lifted : SU2.AxisLift) →
  liftAction (composeLiftPolarity q p) lifted
  ≡ liftAction q (liftAction p lifted)
liftActionComposition Mobius.positive Mobius.positive lifted = refl
liftActionComposition Mobius.positive Mobius.negative lifted = refl
liftActionComposition Mobius.negative Mobius.positive lifted = refl
liftActionComposition Mobius.negative Mobius.negative lifted =
  SU2.flipAxisLiftInvolutive lifted

axisAction : Mobius.OrientationPolarity → SU2.SU2Axis → SU2.SU2Axis
axisAction polarity axis = axis

axisActionComposition :
  (q p : Mobius.OrientationPolarity) →
  (axis : SU2.SU2Axis) →
  axisAction (composeLiftPolarity q p) axis
  ≡ axisAction q (axisAction p axis)
axisActionComposition q p axis = refl

liftLawfulAction : TOE.LawfulAction Mobius.OrientationPolarity SU2.AxisLift
liftLawfulAction = record
  { identity = Mobius.positive
  ; compose = composeLiftPolarity
  ; act = liftAction
  ; composeIdLeft = composeLiftPolarityIdLeft
  ; composeIdRight = composeLiftPolarityIdRight
  ; composeAssoc = composeLiftPolarityAssoc
  ; actIdentity = λ lifted → refl
  ; actComposition = liftActionComposition
  }

axisLawfulAction : TOE.LawfulAction Mobius.OrientationPolarity SU2.SU2Axis
axisLawfulAction = record
  { identity = Mobius.positive
  ; compose = composeLiftPolarity
  ; act = axisAction
  ; composeIdLeft = composeLiftPolarityIdLeft
  ; composeIdRight = composeLiftPolarityIdRight
  ; composeAssoc = composeLiftPolarityAssoc
  ; actIdentity = λ axis → refl
  ; actComposition = axisActionComposition
  }

axisProjectionEquivariant :
  (polarity : Mobius.OrientationPolarity) →
  (lifted : SU2.AxisLift) →
  SU2.projectAxisLift (liftAction polarity lifted)
  ≡ axisAction polarity (SU2.projectAxisLift lifted)
axisProjectionEquivariant Mobius.positive lifted = refl
axisProjectionEquivariant Mobius.negative lifted =
  SU2.projectAxisLiftFlipInvariant lifted

axisObserver :
  TOE.EquivariantObserver
    Mobius.OrientationPolarity SU2.AxisLift SU2.SU2Axis
    liftLawfulAction axisLawfulAction
axisObserver = record
  { observe = SU2.projectAxisLift
  ; observeEquivariant = axisProjectionEquivariant
  }

axisResidualObserver :
  TOE.ReopenableObserver SU2.AxisLift SU2.SU2Axis SU2.LiftPolarity
axisResidualObserver = record
  { project = SU2.projectAxisLift
  ; retainResidual = proj₂
  ; reopen = λ axis polarity → axis , polarity
  ; reopenExact = λ lifted → refl
  }

axisLiftSymmetryResolvedFibre :
  TOE.SymmetryResolvedFibre
    Mobius.OrientationPolarity SU2.AxisLift SU2.SU2Axis SU2.LiftPolarity
axisLiftSymmetryResolvedFibre = record
  { richAction = liftLawfulAction
  ; surfaceAction = axisLawfulAction
  ; observer = axisObserver
  ; residualObserver = axisResidualObserver
  ; sameProjection = λ lifted → refl
  }

axisPlusPolarityRecoversLift :
  (lifted : SU2.AxisLift) →
  TOE.reopen (TOE.residualObserver axisLiftSymmetryResolvedFibre)
    (TOE.observe (TOE.observer axisLiftSymmetryResolvedFibre) lifted)
    (TOE.retainResidual (TOE.residualObserver axisLiftSymmetryResolvedFibre) lifted)
  ≡ lifted
axisPlusPolarityRecoversLift = TOE.reopenAfterObservation axisLiftSymmetryResolvedFibre

------------------------------------------------------------------------
-- 3. The existing SSP 9 -> 6 polar surface already carries the zero-branch
-- phase residual internally.  Therefore it is an exact reopenable observer;
-- the external residual parameter is Unit because the surface is already
-- residual-bearing.
------------------------------------------------------------------------

sspPolarReopenableObserver :
  TOE.ReopenableObserver Wheel.FullPhaseCell Address.PolarProjectionResult ⊤
sspPolarReopenableObserver = record
  { project = Address.polarProject
  ; retainResidual = λ cell → tt
  ; reopen = λ surface receipt → Polar.reopenPolarResult surface
  ; reopenExact = Polar.reopenPolarProjectExact
  }

sspPolarProjectionIsLosslessWithResidual :
  (cell : Wheel.FullPhaseCell) →
  TOE.reopen sspPolarReopenableObserver
    (TOE.project sspPolarReopenableObserver cell)
    (TOE.retainResidual sspPolarReopenableObserver cell)
  ≡ cell
sspPolarProjectionIsLosslessWithResidual =
  TOE.reopenExact sspPolarReopenableObserver

------------------------------------------------------------------------
-- 4. NS independently supplies a genuine 3 x 3 interpretation of the nine
-- labels: signed analytic disposition x proof maturity.  This does not assert
-- that Base369's cyclic nonaryXor is the product operation.
------------------------------------------------------------------------

nsNonaryProductDecodeEncode :
  (x : NS369.Stage3NonaryCoordinate) →
  NS369.decodeNonary (NS369.encodeNonary x) ≡ x
nsNonaryProductDecodeEncode = NS369.nonaryDecodeEncode

nsNonaryProductEncodeDecode :
  (x : Base369.NonaryTruth) →
  NS369.encodeNonary (NS369.decodeNonary x) ≡ x
nsNonaryProductEncodeDecode = NS369.nonaryEncodeDecode

------------------------------------------------------------------------
-- TOE-level regression surface.
------------------------------------------------------------------------

record TOESymmetryResolved369Bridge : Set₁ where
  constructor bridge
  field
    sspNativeAction : TOE.LawfulAction SSP.FibreOrientation Tower.LaneState

    su2AxisLiftResolved :
      TOE.SymmetryResolvedFibre
        Mobius.OrientationPolarity SU2.AxisLift SU2.SU2Axis SU2.LiftPolarity

    sspPolarResidualResolved :
      TOE.ReopenableObserver Wheel.FullPhaseCell Address.PolarProjectionResult ⊤

    nativeSSPCompositionIsPreserved :
      (q p : SSP.FibreOrientation) →
      (state : Tower.LaneState) →
      TOE.act sspNativeAction (TOE.compose sspNativeAction q p) state
      ≡ TOE.act sspNativeAction q (TOE.act sspNativeAction p state)

    sixToThreeReopensWithPolarity :
      (lifted : SU2.AxisLift) →
      TOE.reopen (TOE.residualObserver su2AxisLiftResolved)
        (TOE.observe (TOE.observer su2AxisLiftResolved) lifted)
        (TOE.retainResidual (TOE.residualObserver su2AxisLiftResolved) lifted)
      ≡ lifted

    nineToPolarSurfaceReopensExactly :
      (cell : Wheel.FullPhaseCell) →
      TOE.reopen sspPolarResidualResolved
        (TOE.project sspPolarResidualResolved cell)
        (TOE.retainResidual sspPolarResidualResolved cell)
      ≡ cell

canonicalTOESymmetryResolved369Bridge : TOESymmetryResolved369Bridge
canonicalTOESymmetryResolved369Bridge = bridge
  sspOrientationAction
  axisLiftSymmetryResolvedFibre
  sspPolarReopenableObserver
  sspNativeCompositionPreserved
  axisPlusPolarityRecoversLift
  sspPolarProjectionIsLosslessWithResidual

------------------------------------------------------------------------
-- 5. Reuse original NS 369 proof boundaries.
--
-- The complex three-axis cross product is an oriented-coordinate
-- observation. It is not the cyclic C3 group or a Clay proof.
-- The high-high Gram receipt records the still-open Rayleigh margin.
-- This bridge preserves BOTH facts without changing either owner.
------------------------------------------------------------------------

toeNS369CrossRetainsBeltramiSuppression :
  NSCross.nsBeltramiCrossSuppressionReused ≡ true
toeNS369CrossRetainsBeltramiSuppression =
  NSCross.nsBeltramiCrossSuppressionReusedIsTrue

toeNS369CrossRetainsLerayCancellation :
  NSCross.nsOutputTransverseLerayCancellationReused ≡ true
toeNS369CrossRetainsLerayCancellation =
  NSCross.nsOutputTransverseLerayCancellationReusedIsTrue

toeNS369GramReceiptIsFailClosed :
  NSGram.failClosed NSGram.canonicalNSTriadKN369HighHighGramBridgeReceipt
  ≡ true
toeNS369GramReceiptIsFailClosed =
  NSGram.failClosedIsTrue NSGram.canonicalNSTriadKN369HighHighGramBridgeReceipt

toeNS369GramTheoremNotPromoted :
  NSGram.theoremPromoted NSGram.canonicalNSTriadKN369HighHighGramBridgeReceipt
  ≡ false
toeNS369GramTheoremNotPromoted =
  NSGram.theoremPromotedIsFalse NSGram.canonicalNSTriadKN369HighHighGramBridgeReceipt

toeNS369ClayNotPromoted :
  NSGram.clayPromoted NSGram.canonicalNSTriadKN369HighHighGramBridgeReceipt
  ≡ false
toeNS369ClayNotPromoted =
  NSGram.clayPromotedIsFalse NSGram.canonicalNSTriadKN369HighHighGramBridgeReceipt

toeNS369ComplexThreeNotCyclicC3 :
  NSCross.nsComplex3CarrierPromotedToCyclicC3 ≡ false
toeNS369ComplexThreeNotCyclicC3 = refl


------------------------------------------------------------------------
-- 6. Reuse the historical Euler/Galerkin carrier and external blowup boundary.
--
-- Preconditions:
--   * Galerkin.projectedNonlinearity is the existing physical Fourier owner.
--   * EulerCompat is only a zero-origin compatibility adapter.
--   * ABEuler is an external-result boundary with explicit non-promotion.
--
-- Invariants:
--   * this TOE edge does not reassign Euler/Galerkin priority;
--   * an external Lean proof is not a DASHI proof term;
--   * an external smooth-forced Euler blowup theorem does not pay the
--     unforced Navier--Stokes signed R406 / direct-companion leaf.
--
-- Postcondition:
--   the focused TOE import graph reaches the canonical Galerkin owner and the
--   exact external non-promotion theorems without a second PDE ontology.
------------------------------------------------------------------------

toeHistoricalProjectedGalerkinSumAlreadyConstructed :
  Galerkin.literalProjectedGalerkinSumConstructed ≡ true
toeHistoricalProjectedGalerkinSumAlreadyConstructed =
  Galerkin.literalProjectedGalerkinSumConstructedIsTrue

toeEulerCompatibilityAdapterDoesNotOriginateCarrier :
  EulerCompat.thisAdapterOriginatesEulerGalerkinCarrier ≡ false
toeEulerCompatibilityAdapterDoesNotOriginateCarrier = refl

toeEulerCompatibilityAdapterGetsNoOriginPriority :
  EulerCompat.thisAdapterGetsEulerOriginPriorityCredit ≡ false
toeEulerCompatibilityAdapterGetsNoOriginPriority =
  EulerCompat.thisAdapterGetsEulerOriginPriorityCreditIsFalse

toeAlpogeBuckmasterAdapterGetsNoEulerOriginPriority :
  ABEuler.thisAdapterReceivesEulerOriginPriorityCredit ≡ false
toeAlpogeBuckmasterAdapterGetsNoEulerOriginPriority =
  ABEuler.thisAdapterReceivesEulerOriginPriorityCreditIsFalse

toeExternalEulerLeanProofNotTranscribed :
  ABEuler.externalLeanProofTranscribedIntoDASHIHere ≡ false
toeExternalEulerLeanProofNotTranscribed =
  ABEuler.externalLeanProofTranscribedIntoDASHIHereIsFalse

toeExternalEulerConstructionNotReproduced :
  ABEuler.externalConstructionMechanismReproducedHere ≡ false
toeExternalEulerConstructionNotReproduced =
  ABEuler.externalConstructionMechanismReproducedHereIsFalse

toeForcedEulerBlowupDoesNotPayUnforcedNSLeaf :
  ABEuler.forcedEulerBlowupPaysUnforcedNSLeafA ≡ false
toeForcedEulerBlowupDoesNotPayUnforcedNSLeaf =
  ABEuler.forcedEulerBlowupPaysUnforcedNSLeafAIsFalse
