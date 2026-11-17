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
import DASHI.Physics.Closure.NSTriadKNPeriodicTwoInequalityMaxCutRound650Exact as NSR650
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
-- 5. Live periodic Navier--Stokes max-cut normalized onto the TOE graph.
--
-- ZKP O/R/C/S/L/P/G/F.
--
-- O: Expose the current R650 periodic-B frontier from the existing TOE owner.
-- R: Reuse R650 and R722. Do not create a second Navier--Stokes ontology.
-- C: Export only exact carrier and routing facts.
-- S: Keep finite algebra, analytic payment, and Clay promotion distinct.
-- L: This bridge owns only the normalized TOE import edge.
-- P: TOE consumers see one combined global commutator analytic object.
-- G: Original PDE authors and original DASHI theorem owners retain credit.
-- F: Open analytic payment and Clay promotion remain fail-closed.
--
-- Preconditions.
--   * R700/R701 already expose the literal complete nested orbit.
--   * R722 already recombines self and external terms.
--
-- Invariants.
--   * Separate self cancellation is not a required analytic leaf.
--   * Separate external payment is not a required analytic leaf.
--   * A representation compiler is not a cutoff-uniform PDE estimate.
--
-- Postconditions.
--   * The focused TOE graph reaches the live periodic-B max-cut.
--   * Clay promotion remains false.
------------------------------------------------------------------------

toeNSR650LiteralNestedOrbitExpansionClosed :
  NSR650.round650LiteralNestedFourHelicityOrbitExpansionClosed ≡ true
toeNSR650LiteralNestedOrbitExpansionClosed = refl

toeNSR650CombinedSelfExternalRecombined :
  NSR650.round650SelfExternalRecombineToSingleGlobalCommutator ≡ true
toeNSR650CombinedSelfExternalRecombined = refl

toeNSR650SeparateSelfPaymentNotRequired :
  NSR650.round650SeparateSelfCancellationRequiredAfterRecombination ≡ false
toeNSR650SeparateSelfPaymentNotRequired = refl

toeNSR650SeparateExternalPaymentNotRequired :
  NSR650.round650SeparateExternalPaymentRequiredAfterRecombination ≡ false
toeNSR650SeparateExternalPaymentNotRequired = refl

toeNSR650RemainingObjectIsCombinedGlobalCommutator :
  NSR650.round650RemainingAnalyticObjectIsCombinedGlobalCommutator ≡ true
toeNSR650RemainingObjectIsCombinedGlobalCommutator = refl

toeNSR650CombinedCutoffUniformPaymentRemainsOpen :
  NSR650.round650CombinedSelfExternalCutoffUniformPaymentClosed ≡ false
toeNSR650CombinedCutoffUniformPaymentRemainsOpen = refl

toeNSR650ClayPromotionRemainsFalse :
  NSR650.round650ClayPromotion ≡ false
toeNSR650ClayPromotionRemainsFalse =
  NSR650.round650ClayPromotionIsFalse
