{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND491:
-- CORRECTED WILSON TWO-INSERTION PRODUCER FOR THE EXISTING R274 COMPILER.
--
-- R274's downstream theorem is good:
--
--   connected covariance <= rooted connecting shell
--     -> 1/4 * (1/2)^distance.
--
-- Its historical source-facing prose called the selected observables "literal
-- CMP116 J insertions".  R486/R490 show that this is not source-faithful for
-- Wilson loops: Balaban's printed J is a bond-valued complexified Lie field,
-- and CMP122 explicitly leaves loop-observable expectation analysis as future
-- work.
--
-- This owner keeps the quantitative theorem but corrects the producer type.
-- The live theorem is simply the finite Wilson two-insertion connected-shell
-- estimate on the SAME RG state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanWilsonExpectationSourceBoundaryRound490Exact as R490

record WilsonTwoInsertionConnectedShell
    (Scale Volume Root State Observable : Set) : Set₁ where
  field
    shellData : Shell.TraversalShellData Scale Volume Root

    stateAtScale : Nat → State
    scaleOf : State → Scale
    volumeOf : State → Volume

    physicalDistance : Observable → Observable → Nat
    connectingRoot : State → Observable → Observable → Root

    connectedCovarianceMagnitude :
      State → Observable → Observable → ℚ

    -- WEXT in its exact quantitative form.
    wilsonConnectedCovarianceBelowConnectingShell :
      ∀ state left right →
      connectedCovarianceMagnitude state left right
      ≤
      Shell.rootedShell shellData
        (scaleOf state)
        (volumeOf state)
        (connectingRoot state left right)
        (physicalDistance left right)

    -- Existing finite-graph support fact required by the R274 semantics.
    connectingClusterMeetsBothWilsonSupports :
      ∀ state left right → Set

open WilsonTwoInsertionConnectedShell public

asR274TwoSourceConnectedRootedShellData :
  ∀ {Scale Volume Root State Observable} →
  WilsonTwoInsertionConnectedShell
    Scale Volume Root State Observable →
  R274.TwoSourceConnectedRootedShellData
    Scale Volume Root State Observable
asR274TwoSourceConnectedRootedShellData dataSet = record
  { R274.TwoSourceConnectedRootedShellData.shellData =
      shellData dataSet
  ; R274.TwoSourceConnectedRootedShellData.stateAtScale =
      stateAtScale dataSet
  ; R274.TwoSourceConnectedRootedShellData.scaleOf =
      scaleOf dataSet
  ; R274.TwoSourceConnectedRootedShellData.volumeOf =
      volumeOf dataSet
  ; R274.TwoSourceConnectedRootedShellData.physicalDistance =
      physicalDistance dataSet
  ; R274.TwoSourceConnectedRootedShellData.connectingRoot =
      connectingRoot dataSet
  ; R274.TwoSourceConnectedRootedShellData.connectedCovarianceMagnitude =
      connectedCovarianceMagnitude dataSet
  ; R274.TwoSourceConnectedRootedShellData.connectedCovarianceBelowConnectingShell =
      wilsonConnectedCovarianceBelowConnectingShell dataSet
  ; R274.TwoSourceConnectedRootedShellData.connectingClusterMeetsBothSupports =
      connectingClusterMeetsBothWilsonSupports dataSet
  }

wilsonCorrelationDecayTrajectory :
  ∀ {Scale Volume Root State Observable} →
  WilsonTwoInsertionConnectedShell
    Scale Volume Root State Observable →
  DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact.QuantitativeCorrelationDecayTrajectory
wilsonCorrelationDecayTrajectory dataSet =
  R274.asCorrelationDecayTrajectory
    (asR274TwoSourceConnectedRootedShellData dataSet)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round491R274CompilerReuseLevel : ProofLevel
round491R274CompilerReuseLevel =
  R274.round274RootedShellToConnectedCorrelationCompilerLevel

round491ConnectingClusterGeometryLevel : ProofLevel
round491ConnectingClusterGeometryLevel =
  R274.round274ConnectingClusterDiameterDominatesSupportDistanceLevel

-- This is now the single quantitative Wilson-correlation theorem required by
-- the source-native/polymer route.  R488/R489 describe its local analytic
-- insertion prerequisites; R490 records that Bałaban did not publish this
-- loop-observable extension.
round491WilsonTwoInsertionConnectedShellLevel : ProofLevel
round491WilsonTwoInsertionConnectedShellLevel = conditional

round491SourceBoundaryLevel : ProofLevel
round491SourceBoundaryLevel =
  R490.round490SourceBoundaryCompilerLevel

observableEqualsPrintedBalabanJRequired : Bool
observableEqualsPrintedBalabanJRequired = false

observableEqualsPrintedBalabanJRequiredIsFalse :
  observableEqualsPrintedBalabanJRequired ≡ false
observableEqualsPrintedBalabanJRequiredIsFalse = refl

freshDownstreamGeometricDecayCompilerRequired : Bool
freshDownstreamGeometricDecayCompilerRequired = false

freshDownstreamGeometricDecayCompilerRequiredIsFalse :
  freshDownstreamGeometricDecayCompilerRequired ≡ false
freshDownstreamGeometricDecayCompilerRequiredIsFalse = refl
