module DASHI.Physics.Closure.NSTriadKNBlockerToLocalizedBKMCompatibility where

------------------------------------------------------------------------
-- PURPOSE
-- Separate the now-constructed finite compatibility bridge from the remaining
-- physical and continuation identifications.
--
-- Constructed:
--   * exact periodic hard-shell LP/Bony interaction interface;
--   * cutoff-indexed forced-tail weight geometry;
--   * exact finite residue/operator/gap authority;
--   * forced-tail majorant control of Luo's explicit-cutoff quantity.
--
-- Still open:
--   * equality of the finite classified interactions with the physical
--     Navier--Stokes nonlinear residuals;
--   * equality of the canonical finite Schur operator with the physical PDE
--     pair-incidence operator;
--   * equality of the Nat-valued localized quantity with the terminal-window
--     integral;
--   * the analytic limsup and continuation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement as ForcedTail
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNLittlewoodPaleyInfrastructureInventory as LP
import DASHI.Physics.Closure.NSTriadKNLocalizedBKMSourceAndTargetAudit as Sources
import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryCutoffIndexedExact as Depth
import DASHI.Physics.Closure.NSTriadKNResidueScaleOperatorGapExact as ResidueGap
import DASHI.Physics.Closure.NSTriadKNLuoExplicitCutoffLocalizedCriterionExact as Luo

------------------------------------------------------------------------
-- Semantic classification of the existing blocker outputs.
------------------------------------------------------------------------

data ExistingBlockerSemanticKind : Set where
  weightedSchurRestrictedRow
  weakStrongQuadraticGapCompatibility
  localizedGradientCutoffMajorant
  localizedVorticityProjection
  timeDependentDissipationThreshold : ExistingBlockerSemanticKind

forcedTailBlockerSemanticKind : ExistingBlockerSemanticKind
forcedTailBlockerSemanticKind = weightedSchurRestrictedRow

residueScaleBlockerSemanticKind : ExistingBlockerSemanticKind
residueScaleBlockerSemanticKind = weakStrongQuadraticGapCompatibility

luoBridgeOutputSemanticKind : ExistingBlockerSemanticKind
luoBridgeOutputSemanticKind = localizedGradientCutoffMajorant

------------------------------------------------------------------------
-- Constructed exact finite bridge.
------------------------------------------------------------------------

record ExactFiniteBlockersToLuoBridge : Set₁ where
  constructor bridge
  field
    periodicLPBonyInterfaceConstructed :
      LP.exactPeriodicLPBonyPDEInterfaceConstructed ≡ true

    cutoffIndexedDepthGeometry :
      Depth.CutoffIndexedProfileDepthGeometry

    residueOperatorGapAuthority :
      ResidueGap.ExactResidueScaleOperatorGapAuthority

    forcedTailMajorantControlsLuoQuantity :
      Luo.forcedTailOutputControlsLuoCutoffQuantity ≡ true

open ExactFiniteBlockersToLuoBridge public

exactFiniteBlockersToLuoBridge : ExactFiniteBlockersToLuoBridge
exactFiniteBlockersToLuoBridge =
  bridge
    LP.exactPeriodicLPBonyPDEInterfaceConstructedIsTrue
    Depth.canonicalCutoffIndexedProfileDepthGeometry
    ResidueGap.exactResidueScaleOperatorGapAuthority
    Luo.forcedTailOutputControlsLuoCutoffQuantityIsTrue

------------------------------------------------------------------------
-- Physical adapter 1: weighted-Schur forced-tail control to an LP gradient
-- or vorticity estimate.  The finite majorant algebra is now closed; only the
-- literal physical identification fields remain.
------------------------------------------------------------------------

record ForcedTailToLocalizedVorticityBridge : Set₁ where
  field
    adversarialRestrictedRow :
      ForcedTail.ForcedTailToAdversarialRestrictedRowN1

    transitionRestrictedRow :
      ForcedTail.ForcedTailToTransitionRestrictedRowN1

    cutoffIndexIdentifiedWithDyadicShellScale : Set
    finiteBonyPiecesEqualPhysicalNonlinearPieces : Set
    restrictedWeightedRowsControlShellGradientOrVorticity : Set
    pointwiseShellControlTransportsToTimeIntegral : Set
    constantsUniformInGalerkinCutoff : Set

open ForcedTailToLocalizedVorticityBridge public

------------------------------------------------------------------------
-- Physical adapter 2: residue/gap compatibility to a solution-dependent Q(t).
-- This remains a useful alternative to the explicit-cutoff Luo route.
------------------------------------------------------------------------

record ResidueScaleToDissipationWavenumberBridge : Set₁ where
  field
    residueScaleCompatibility :
      QGap.ResidueScaleCompatibility

    periodicProjectorInterface :
      LP.PeriodicLittlewoodPaleyProjectorInterface

    dissipationRange :
      Sources.DissipationWavenumberInterface

    bernsteinViscosityThresholdVerified : Set
    highModesAbsorbedAboveThreshold : Set
    lowModeCriterionControlledByResidueScale : Set

open ResidueScaleToDissipationWavenumberBridge public

------------------------------------------------------------------------
-- Complete physical localized-continuation adapter.
------------------------------------------------------------------------

record BlockersToLocalizedBKMBridge : Set₁ where
  field
    finiteBridge : ExactFiniteBlockersToLuoBridge

    forcedTailToVorticity :
      ForcedTailToLocalizedVorticityBridge

    continuationAuthority :
      Sources.BKMContinuationAuthority

    solutionClassMatchesDASHIPeriodicNavierStokes : Set
    bridgeContainsNoUntrackedPostulates : Set

open BlockersToLocalizedBKMBridge public

blockersToContinuationAuthority :
  BlockersToLocalizedBKMBridge →
  Sources.BKMContinuationAuthority
blockersToContinuationAuthority completeBridge =
  continuationAuthority completeBridge

------------------------------------------------------------------------
-- Honest route status.
------------------------------------------------------------------------

exactFiniteBlockersToLuoBridgeConstructed : Bool
exactFiniteBlockersToLuoBridgeConstructed = true

finiteBonyPiecesEqualPhysicalNonlinearPieces : Bool
finiteBonyPiecesEqualPhysicalNonlinearPieces = false

forcedTailResidualsIdentifiedWithBonyPieces : Bool
forcedTailResidualsIdentifiedWithBonyPieces = false

forcedTailToLocalizedVorticityBridgeClosed : Bool
forcedTailToLocalizedVorticityBridgeClosed = false

residueScaleToDissipationWavenumberBridgeClosed : Bool
residueScaleToDissipationWavenumberBridgeClosed = false

blockersToLocalizedBKMBridgeClosed : Bool
blockersToLocalizedBKMBridgeClosed = false

exactFiniteBlockersToLuoBridgeConstructedIsTrue :
  exactFiniteBlockersToLuoBridgeConstructed ≡ true
exactFiniteBlockersToLuoBridgeConstructedIsTrue = refl

finiteBonyPiecesEqualPhysicalNonlinearPiecesIsFalse :
  finiteBonyPiecesEqualPhysicalNonlinearPieces ≡ false
finiteBonyPiecesEqualPhysicalNonlinearPiecesIsFalse = refl

forcedTailResidualsIdentifiedWithBonyPiecesIsFalse :
  forcedTailResidualsIdentifiedWithBonyPieces ≡ false
forcedTailResidualsIdentifiedWithBonyPiecesIsFalse = refl

forcedTailToLocalizedVorticityBridgeClosedIsFalse :
  forcedTailToLocalizedVorticityBridgeClosed ≡ false
forcedTailToLocalizedVorticityBridgeClosedIsFalse = refl

residueScaleToDissipationWavenumberBridgeClosedIsFalse :
  residueScaleToDissipationWavenumberBridgeClosed ≡ false
residueScaleToDissipationWavenumberBridgeClosedIsFalse = refl

blockersToLocalizedBKMBridgeClosedIsFalse :
  blockersToLocalizedBKMBridgeClosed ≡ false
blockersToLocalizedBKMBridgeClosedIsFalse = refl

semanticMismatchAuditClosed : Bool
semanticMismatchAuditClosed = true

semanticMismatchAuditClosedIsTrue :
  semanticMismatchAuditClosed ≡ true
semanticMismatchAuditClosedIsTrue = refl
