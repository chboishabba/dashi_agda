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
-- literal near scalar can enter a sign-oscillatory regime. The cutoff J belongs
-- to the Off near/far producer only. The final Gamma response and cluster margin
-- are functions of the same literal taper and have no J argument.
--
-- A key positive fact is already owned by the explicit-cutoff return:
--
--   farShellBound A |t| J
--     = 18 A log(|t|+4)/J + 72 A/sqrt(J)
--
-- for every cutoff J, together with farShellBound -> 0 as J -> infinity.
-- Thus growth of J is not intrinsically hostile to the far-shell channel.
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

------------------------------------------------------------------------
-- Corrected deterministic complement package: taper-only, not cutoff-indexed.
------------------------------------------------------------------------

record SameTaperGammaClusterPropagation
    (W : LiteralHighOrdinateWidthLaw) : Set₁ where
  field
    literalGammaBudgetOnSameTaper : Set
    gammaBudgetUsesSameLiteralTaper : Set
    clusterMarginOnSameTaper : Set
    gammaAllowanceCompatibleWithClusterMargin : Set
    propagationReference : String

open SameTaperGammaClusterPropagation public

-- Compatibility alias for historical consumers. The J parameter is deliberately
-- ignored: keeping the old name must not reintroduce Gamma(J) or cluster(J).
SameCutoffGammaClusterPropagation :
  (W : LiteralHighOrdinateWidthLaw) ->
  MinimalQuarterPeriodCutoff W -> Set₁
SameCutoffGammaClusterPropagation W J = SameTaperGammaClusterPropagation W

record QuarterPeriodScalingAdmission
    (W : LiteralHighOrdinateWidthLaw) : Set₁ where
  constructor quarter-period-scaling-admission
  field
    cutoff : MinimalQuarterPeriodCutoff W
    farPropagation : SameCutoffFarPropagation W cutoff
    gammaClusterPropagation : SameTaperGammaClusterPropagation W

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
    "Choose one same-object quarter-period crossing cutoff J for the signed Off near/far producer. The explicit far-shell lane is structurally compatible with cutoff growth because an every-cutoff bound and convergence to zero are already owned. Do not propagate J into Gamma or cluster: their final APIs are taper-only. The remaining deterministic complement payment is same-taper Gamma/cluster allowance compatibility, while the live J-dependent mathematics is the signed finite-near Off estimate at that common cutoff."

------------------------------------------------------------------------
-- Explicit coordinate correction pins.
------------------------------------------------------------------------

gammaPropagationCarriesCutoffCoordinate : Bool
gammaPropagationCarriesCutoffCoordinate = false

gammaPropagationCarriesCutoffCoordinateIsFalse :
  gammaPropagationCarriesCutoffCoordinate ≡ false
gammaPropagationCarriesCutoffCoordinateIsFalse = refl

clusterPropagationCarriesCutoffCoordinate : Bool
clusterPropagationCarriesCutoffCoordinate = false

clusterPropagationCarriesCutoffCoordinateIsFalse :
  clusterPropagationCarriesCutoffCoordinate ≡ false
clusterPropagationCarriesCutoffCoordinateIsFalse = refl
