{-# OPTIONS --safe #-}
module DASHI.Unified.SingularBasinCoarseRGTOEExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Dynamics.SingularBasinReductionExact as Reduction
import DASHI.Physics.Dynamics.SingularBasinFiniteWitnessExact as Finite
import DASHI.Physics.Dynamics.SingularBasinCompressionBridgeExact as Compression
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as Resolution
import DASHI.Physics.Dynamics.SingularBasinResolutionWitnessExact as ResolutionWitness
import DASHI.Physics.Dynamics.SingularBasinValidatedNumericsArtifactExact as Validated
import DASHI.Physics.Dynamics.YanchukStableManifoldCrossingTargetExact as Yanchuk

------------------------------------------------------------------------
-- TOE normalization for singular-basin / coarse-RG non-preservation.
--
-- S. Yanchuk, S. Wieczorek, H. Jardón-Kojakhmetov, and H. Alkhayuon retain
-- source attribution for the 2026 singular-basin result and public model.
-- Existing DASHI modules remain the theorem owners.
-- This module only normalizes those results into the TOE import graph.
------------------------------------------------------------------------

finiteReduction :
  Reduction.BasinReduction Finite.FullState Finite.ReducedState
finiteReduction =
  Finite.finiteReduction

finiteReductionNotBasinPreserving :
  ¬ Reduction.BasinPreserving finiteReduction
finiteReductionNotBasinPreserving =
  Finite.finite-reduction-not-basin-preserving

finiteFullBasinDoesNotFactorThroughReduction :
  ¬ Reduction.PredicateFactorisation Finite.project Finite.FullInBasin
finiteFullBasinDoesNotFactorThroughReduction =
  Finite.finite-full-basin-does-not-factor-through-reduction

selectedResolutionNotRobust :
  ¬ Resolution.RobustAt
      ResolutionWitness.finiteResolutionGeometry
      Finite.FullInBasin
      ResolutionWitness.selectedResolution
      Finite.funnelState
selectedResolutionNotRobust =
  ResolutionWitness.funnel-state-not-robust-at-selected-resolution

selectedProjectionNotResolutionAdequate :
  ¬ Resolution.ResolutionAdequateForPredicate
      ResolutionWitness.finiteResolutionGeometry
      Finite.project
      Finite.FullInBasin
      ResolutionWitness.selectedResolution
selectedProjectionNotResolutionAdequate =
  ResolutionWitness.selected-projection-not-resolution-adequate

selectedResolutionAlsoRefutesGlobalFactorisation :
  ¬ Reduction.PredicateFactorisation Finite.project Finite.FullInBasin
selectedResolutionAlsoRefutesGlobalFactorisation =
  ResolutionWitness.selected-resolution-witness-also-refutes-global-factorisation

singularBasinValidationStatus :
  Validated.SingularBasinValidationStatus
singularBasinValidationStatus =
  Validated.canonicalSingularBasinValidationStatus

intervalODECheckerStillMissing :
  Validated.intervalODECheckerPresent singularBasinValidationStatus ≡ false
intervalODECheckerStillMissing =
  Validated.intervalODECheckerPresentIsFalse singularBasinValidationStatus

checkerSoundToBasinCertificateStillMissing :
  Validated.checkerSoundToBasinCertificatePresent singularBasinValidationStatus
  ≡ false
checkerSoundToBasinCertificateStillMissing =
  Validated.checkerSoundToBasinCertificatePresentIsFalse singularBasinValidationStatus

analyticGlobalWidthLawStillMissing :
  Validated.analyticGlobalWidthLawPresent singularBasinValidationStatus ≡ false
analyticGlobalWidthLawStillMissing =
  Validated.analyticGlobalWidthLawPresentIsFalse singularBasinValidationStatus

yanchukStableManifoldValidationBoundary :
  Yanchuk.YanchukStableManifoldValidationBoundary
yanchukStableManifoldValidationBoundary =
  Yanchuk.canonicalYanchukStableManifoldValidationBoundary

intervalStableManifoldTubeStillMissing :
  Yanchuk.intervalStableManifoldTubeCertified
    yanchukStableManifoldValidationBoundary
  ≡ false
intervalStableManifoldTubeStillMissing =
  Yanchuk.intervalStableManifoldTubeCertifiedIsFalse
    yanchukStableManifoldValidationBoundary

basinSeparationTheoremStillMissing :
  Yanchuk.basinSeparationTheoremCertified
    yanchukStableManifoldValidationBoundary
  ≡ false
basinSeparationTheoremStillMissing =
  Yanchuk.basinSeparationTheoremCertifiedIsFalse
    yanchukStableManifoldValidationBoundary

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F process frame.
------------------------------------------------------------------------

record SingularBasinTOEZKPFrame : Set where
  constructor singular-basin-toe-zkp-frame
  field
    O-objective : String
    R-reuse : String
    C-construction : String
    S-safety : String
    L-lane : String
    P-preconditions : String
    G-governance : String
    F-postconditions : String
    esdMutationAllowed : Bool
    numericalReceiptCreatesAnalyticTheorem : Bool
    coarseProjectionCreatesExactBasinClassifier : Bool

open SingularBasinTOEZKPFrame public

canonicalSingularBasinTOEZKPFrame :
  SingularBasinTOEZKPFrame
canonicalSingularBasinTOEZKPFrame =
  singular-basin-toe-zkp-frame
    "attach existing singular-basin and coarse-projection obstruction theorems to the DASHI TOE"
    "reuse finite reduction, compression, resolution, validated-numerics, and Yanchuk stable-manifold owners"
    "one normalized facade plus root aliases and focused validation"
    "same reduced state with different basin membership blocks exact factorisation; numerical receipts stay below analytic promotion"
    "one disjoint dynamics/coarse-RG TOE normalization lane"
    "canonical owners already exist; attribution stays with source and theorem owners; ESD surfaces stay read-only"
    "fail closed; use repository referee and kernel checks; standards named in the parent TOE are process lenses only"
    "TOE roots expose exact non-preservation, non-factorisation, resolution failure, and the remaining validated-manifold proof wall"
    false
    false
    false

singularBasinTOEUsesExistingOwners : Bool
singularBasinTOEUsesExistingOwners = true

singularBasinTOEUsesExistingOwnersIsTrue :
  singularBasinTOEUsesExistingOwners ≡ true
singularBasinTOEUsesExistingOwnersIsTrue = refl

singularBasinTOENumericalPromotionRemainsFalse :
  numericalReceiptCreatesAnalyticTheorem canonicalSingularBasinTOEZKPFrame
  ≡ false
singularBasinTOENumericalPromotionRemainsFalse = refl

singularBasinTOECoarseExactnessNotAssumed :
  coarseProjectionCreatesExactBasinClassifier canonicalSingularBasinTOEZKPFrame
  ≡ false
singularBasinTOECoarseExactnessNotAssumed = refl
