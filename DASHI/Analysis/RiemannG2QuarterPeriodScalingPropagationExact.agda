module DASHI.Analysis.RiemannG2QuarterPeriodScalingPropagationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth
import DASHI.Analysis.RiemannG2NarrowWindowNoCancellationReturnExact as Narrow
import DASHI.Analysis.RiemannAristotleExplicitCutoffCarrierLeanReturnExact as Far
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma

------------------------------------------------------------------------
-- QUARTER-PERIOD SCALING PROPAGATION
--
-- The checked-Lean narrow-window theorem forces J*Lambda > pi/2 before the
-- literal near scalar can even enter a sign-oscillatory regime.  This module
-- assumes the repository's ordinary scaling/order/asymptotic machinery and
-- isolates only the same-object receipts needed to propagate the chosen J(t)
-- through the already-owned consumers.
--
-- A key positive fact is already owned by the explicit-cutoff return:
--
--   farShellBound A |t| J
--     = 18 A log(|t|+4)/J + 72 A/sqrt(J)
--
-- for every cutoff J, together with farShellBound -> 0 as J -> infinity.
-- Thus growth of J is not intrinsically hostile to the far-shell channel.
-- The still-unclosed deterministic Gamma payment must remain separate.
------------------------------------------------------------------------

data ScalingRegime : Set where
  inverseWidthScaling
  quarterPeriodCrossingScaling
  downstreamCompatibleScaling
  : ScalingRegime

record LiteralHighOrdinateWidthLaw : Set₁ where
  field
    Scalar : Set
    targetHeight supportRadius : Scalar
    inverseWidthReference : String

    -- Same-object theorem on the actual constructed taper width.
    highOrdinateInverseWidthLaw : Set
    exactSupportRadiusIsLiteralLambda : Set
    exactTargetHeightIsLiteralTarget : Set

open LiteralHighOrdinateWidthLaw public

record MinimalQuarterPeriodCutoff
    (W : LiteralHighOrdinateWidthLaw) : Set₁ where
  field
    Cutoff : Set
    cutoffAt : Scalar W -> Cutoff
    chosenCutoff : Cutoff

    sameLiteralTargetUsed : Set
    sameLiteralWidthUsed : Set

    quarterPeriodCrossing : Set
    minimalityAmongAdmissibleCutoffs : Set
    cutoffGrowthReference : String

open MinimalQuarterPeriodCutoff public

record SameCutoffFarPropagation
    (W : LiteralHighOrdinateWidthLaw)
    (J : MinimalQuarterPeriodCutoff W) : Set₁ where
  field
    finiteNearCarrierAtChosenCutoff : Set
    literalDoffNearFarSplitAtChosenCutoff : Set
    farShellFormulaAtChosenCutoff : Set
    farShellBudgetFitsRequestedFarAllowance : Set
    exactChosenCutoffUsedEverywhere : Set
    farReference : String

open SameCutoffFarPropagation public

record SameCutoffGammaClusterPropagation
    (W : LiteralHighOrdinateWidthLaw)
    (J : MinimalQuarterPeriodCutoff W) : Set₁ where
  field
    literalGammaBudgetAtChosenCutoff : Set
    gammaBudgetUsesSameLiteralTaper : Set
    clusterMarginAtChosenCutoff : Set
    gammaPlusFarFitsClusterMargin : Set
    explicitFormulaWindowAtChosenCutoff : Set
    exactChosenCutoffUsedEverywhere : Set
    propagationReference : String

open SameCutoffGammaClusterPropagation public

record QuarterPeriodScalingAdmission
    (W : LiteralHighOrdinateWidthLaw) : Set₁ where
  constructor quarter-period-scaling-admission
  field
    cutoff : MinimalQuarterPeriodCutoff W
    farPropagation : SameCutoffFarPropagation W cutoff
    gammaClusterPropagation : SameCutoffGammaClusterPropagation W cutoff

open QuarterPeriodScalingAdmission public

assembleQuarterPeriodScalingAdmission :
  (W : LiteralHighOrdinateWidthLaw) ->
  (J : MinimalQuarterPeriodCutoff W) ->
  SameCutoffFarPropagation W J ->
  SameCutoffGammaClusterPropagation W J ->
  QuarterPeriodScalingAdmission W
assembleQuarterPeriodScalingAdmission W J far gammaCluster =
  quarter-period-scaling-admission J far gammaCluster

------------------------------------------------------------------------
-- Existing theorem receipts that materially simplify the propagation audit.
------------------------------------------------------------------------

farShellFormulaOwnedAtEveryCutoff :
  Far.explicitEveryCutoffBoundOwned
    Far.canonicalExplicitCutoffCarrierLeanReturn ≡ true
farShellFormulaOwnedAtEveryCutoff =
  Far.explicitEveryCutoffBoundOwnedIsTrue
    Far.canonicalExplicitCutoffCarrierLeanReturn

farShellTendsToZeroAsCutoffGrows :
  Far.farShellTendsToZeroOwned
    Far.canonicalExplicitCutoffCarrierLeanReturn ≡ true
farShellTendsToZeroAsCutoffGrows =
  Far.farShellTendsToZeroOwnedIsTrue
    Far.canonicalExplicitCutoffCarrierLeanReturn

arbitraryAccuracyFarCutoffOwned :
  Far.arbitraryAccuracyCutoffOwned
    Far.canonicalExplicitCutoffCarrierLeanReturn ≡ true
arbitraryAccuracyFarCutoffOwned =
  Far.arbitraryAccuracyCutoffOwnedIsTrue
    Far.canonicalExplicitCutoffCarrierLeanReturn

literalGammaBudgetStillOpen :
  Gamma.literalPoleQuotientGammaBudgetClosed
    Gamma.canonicalPoleQuotientGammaBudgetBoundary ≡ false
literalGammaBudgetStillOpen =
  Gamma.literalPoleQuotientGammaBudgetClosedIsFalse
    Gamma.canonicalPoleQuotientGammaBudgetBoundary

quarterPeriodCrossingNecessary :
  Narrow.survivingRouteRequiresQuarterPeriodCrossing
    Narrow.canonicalNarrowWindowNoCancellationReturn ≡ true
quarterPeriodCrossingNecessary =
  Narrow.survivingRouteRequiresQuarterPeriodCrossingIsTrue
    Narrow.canonicalNarrowWindowNoCancellationReturn

------------------------------------------------------------------------
-- Search disposition.
--
-- The far-shell formula is monotone-favourable in the only structural sense we
-- need here: the repository already owns convergence to zero as J grows.  So a
-- quarter-period cutoff of order inverse width does not by itself create a far
-- obstruction.  The next possible incompatibility is whether the SAME chosen J
-- and taper can satisfy the literal Gamma + cluster consumer.
------------------------------------------------------------------------

data PropagationDisposition : Set where
  farChannelStructurallyCompatibleWithCutoffGrowth
  gammaClusterSameObjectPaymentOpen
  fullOscillatoryAdmissionClosed
  : PropagationDisposition

currentFarDisposition : PropagationDisposition
currentFarDisposition = farChannelStructurallyCompatibleWithCutoffGrowth

currentGammaClusterDisposition : PropagationDisposition
currentGammaClusterDisposition = gammaClusterSameObjectPaymentOpen

record QuarterPeriodScalingBoundary : Set where
  constructor quarter-period-scaling-boundary
  field
    inverseWidthLawAlreadyImpliedByNarrowNoGo : Bool
    inverseWidthLawAlreadyImpliedByNarrowNoGoIsFalse :
      inverseWidthLawAlreadyImpliedByNarrowNoGo ≡ false

    quarterPeriodCrossingRequired : Bool
    quarterPeriodCrossingRequiredIsTrue :
      quarterPeriodCrossingRequired ≡ true

    farShellBoundAvailableAtEveryChosenCutoff : Bool
    farShellBoundAvailableAtEveryChosenCutoffIsTrue :
      farShellBoundAvailableAtEveryChosenCutoff ≡ true

    farShellDecayAsCutoffGrowsAlreadyOwned : Bool
    farShellDecayAsCutoffGrowsAlreadyOwnedIsTrue :
      farShellDecayAsCutoffGrowsAlreadyOwned ≡ true

    cutoffGrowthCreatesAutomaticFarShellNoGo : Bool
    cutoffGrowthCreatesAutomaticFarShellNoGoIsFalse :
      cutoffGrowthCreatesAutomaticFarShellNoGo ≡ false

    literalGammaClusterCompatibilityClosed : Bool
    literalGammaClusterCompatibilityClosedIsFalse :
      literalGammaClusterCompatibilityClosed ≡ false

    highestAlphaReading : String

canonicalQuarterPeriodScalingBoundary : QuarterPeriodScalingBoundary
canonicalQuarterPeriodScalingBoundary =
  quarter-period-scaling-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Assume ordinary scaling machinery is available and derive the literal Lambda(t) law on the actual taper. Choose the minimal same-object J(t) crossing pi/2. The explicit far-shell lane is not the likely obstruction: Lean already owns an every-cutoff formula and farShellBound -> 0 as J grows. The live compatibility payment is to bind that same enlarged J(t) to the literal deterministic Gamma response and surviving cluster margin. If Gamma+far cannot fit the cluster margin at the crossing scale, the present G2 architecture acquires a genuine large-window incompatibility no-go; otherwise the oscillatory scalar donor search reopens."
