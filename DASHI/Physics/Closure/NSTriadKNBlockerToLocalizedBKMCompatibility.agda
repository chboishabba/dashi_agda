module DASHI.Physics.Closure.NSTriadKNBlockerToLocalizedBKMCompatibility where

------------------------------------------------------------------------
-- PURPOSE
-- State the exact semantic adapters still required between the two live
-- Stage-3 blockers and any frequency-localized continuation criterion.
--
-- The forced-tail records are weighted-Schur restricted-row witnesses.
-- ResidueScaleCompatibility is a weak/strong quadratic-form and gap-
-- absorption witness.  Neither type is definitionally a Littlewood--Paley
-- vorticity norm or a time-dependent dissipation wavenumber.  This module
-- therefore refuses the unsound shortcut of treating either blocker as an
-- already-proved localized BKM estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement as ForcedTail
import DASHI.Physics.Closure.NSTriadKNQGapTransfer as QGap
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileBounds as PairBounds
import DASHI.Physics.Closure.NSTriadKNLittlewoodPaleyInfrastructureInventory as LP
import DASHI.Physics.Closure.NSTriadKNLocalizedBKMSourceAndTargetAudit as Sources

------------------------------------------------------------------------
-- Semantic classification of the existing blocker outputs.
------------------------------------------------------------------------

data ExistingBlockerSemanticKind : Set where
  weightedSchurRestrictedRow
  weakStrongQuadraticGapCompatibility
  localizedVorticityProjection
  timeDependentDissipationThreshold : ExistingBlockerSemanticKind

forcedTailBlockerSemanticKind : ExistingBlockerSemanticKind
forcedTailBlockerSemanticKind = weightedSchurRestrictedRow

residueScaleBlockerSemanticKind : ExistingBlockerSemanticKind
residueScaleBlockerSemanticKind = weakStrongQuadraticGapCompatibility

------------------------------------------------------------------------
-- Adapter 1: weighted-Schur forced-tail control to an LP vorticity estimate.
------------------------------------------------------------------------

record ForcedTailToLocalizedVorticityBridge : Set₁ where
  field
    adversarialRestrictedRow :
      ForcedTail.ForcedTailToAdversarialRestrictedRowN1

    transitionRestrictedRow :
      ForcedTail.ForcedTailToTransitionRestrictedRowN1

    cutoffIndexIdentifiedWithDyadicShellScale : Set

    restrictedWeightedRowsControlShellVorticity : Set

    pointwiseShellControlTransportsToTimeIntegral : Set

    constantsUniformInGalerkinCutoff : Set

open ForcedTailToLocalizedVorticityBridge public

------------------------------------------------------------------------
-- Adapter 2: residue/gap compatibility to a solution-dependent Q(t).
------------------------------------------------------------------------

record ResidueScaleToDissipationWavenumberBridge : Set₁ where
  field
    residueScaleCompatibility :
      QGap.ResidueScaleCompatibility

    periodicProjectorInterface :
      LP.PeriodicLittlewoodPaleyProjectorInterface

    dissipationWavenumberConstructed : Set

    bernsteinViscosityThresholdVerified : Set

    highModesAbsorbedAboveThreshold : Set

    lowModeCriterionControlledByResidueScale : Set

open ResidueScaleToDissipationWavenumberBridge public

------------------------------------------------------------------------
-- Complete localized-continuation adapter.
------------------------------------------------------------------------

record BlockersToLocalizedBKMBridge : Set₁ where
  field
    forcedTailToVorticity :
      ForcedTailToLocalizedVorticityBridge

    residueScaleToDissipationRange :
      ResidueScaleToDissipationWavenumberBridge

    continuationAuthority :
      Sources.BKMContinuationAuthority

    solutionClassMatchesDASHIPeriodicNavierStokes : Set

    bridgeContainsNoUntrackedPostulates : Set

open BlockersToLocalizedBKMBridge public

blockersToContinuationAuthority :
  BlockersToLocalizedBKMBridge →
  Sources.BKMContinuationAuthority
blockersToContinuationAuthority bridge =
  continuationAuthority bridge

------------------------------------------------------------------------
-- Honest route status.
------------------------------------------------------------------------

forcedTailToLocalizedVorticityBridgeClosed : Bool
forcedTailToLocalizedVorticityBridgeClosed = false

residueScaleToDissipationWavenumberBridgeClosed : Bool
residueScaleToDissipationWavenumberBridgeClosed = false

blockersToLocalizedBKMBridgeClosed : Bool
blockersToLocalizedBKMBridgeClosed = false

forcedTailToLocalizedVorticityBridgeClosedIsFalse :
  forcedTailToLocalizedVorticityBridgeClosed ≡ false
forcedTailToLocalizedVorticityBridgeClosedIsFalse = refl

residueScaleToDissipationWavenumberBridgeClosedIsFalse :
  residueScaleToDissipationWavenumberBridgeClosed ≡ false
residueScaleToDissipationWavenumberBridgeClosedIsFalse = refl

blockersToLocalizedBKMBridgeClosedIsFalse :
  blockersToLocalizedBKMBridgeClosed ≡ false
blockersToLocalizedBKMBridgeClosedIsFalse = refl

currentPairIncidenceBKMExclusionStillFalse :
  PairBounds.canonicalBKMExclusionProved ≡ false
currentPairIncidenceBKMExclusionStillFalse = refl

semanticMismatchAuditClosed : Bool
semanticMismatchAuditClosed = true

semanticMismatchAuditClosedIsTrue :
  semanticMismatchAuditClosed ≡ true
semanticMismatchAuditClosedIsTrue = refl
