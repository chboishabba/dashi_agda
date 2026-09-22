{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBSourceCorrectRound492Exact where

------------------------------------------------------------------------
-- ROUND492 / SOURCE-CORRECT CANONICAL B OVERLAY
--
-- Keep BalabanClayCanonicalBCurrentExact as the historical/provenance rollup,
-- but correct the preferred physical producer for Wilson correlations.
--
-- Source archaeology:
--
-- * CMP109/CMP116 printed J is a bond-valued complexified Lie-algebra field.
-- * The R403 observable-indexed SourceDirection carrier is generic normalized
--   source calculus, not a same-object proof that TestObservable = printed J.
-- * CMP119 (3.44)--(3.47) proves normalized expectation localization for the
--   bond/point insertions treated there.
-- * CMP122 explicitly names expectation values of physical observables such as
--   loop variables / averaged loop variables as future applications requiring
--   further analysis.
--
-- Therefore the preferred B theorem for the selected Wilson pair is R491:
--
--   |Cov(W_L,W_R)| <= rootedShell(d(W_L,W_R)).
--
-- R274 already compiles that exact theorem to
--
--   |Cov(W_L,W_R)| <= (1/4) * (1/2)^d.
--
-- No printed-J norm calibration or observable=printed-J identification is
-- required by this corrected producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayCanonicalBCurrentExact as Historical
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact as R491
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.BalabanHalfRateTransferCoordinateMassGapRound316Exact as R316

------------------------------------------------------------------------
-- Preferred quantitative producer.
------------------------------------------------------------------------

bWilsonTwoInsertionConnectedShellLevel : ProofLevel
bWilsonTwoInsertionConnectedShellLevel =
  R491.round491WilsonTwoInsertionConnectedShellLevel

bConnectedShellToGeometricDecayCompilerLevel : ProofLevel
bConnectedShellToGeometricDecayCompilerLevel =
  R491.round491R274CompilerReuseLevel

bConnectingClusterGeometryLevel : ProofLevel
bConnectingClusterGeometryLevel =
  R491.round491ConnectingClusterGeometryLevel

bFiniteWilsonBoundedTestCompilerLevel : ProofLevel
bFiniteWilsonBoundedTestCompilerLevel =
  R315.round315BoundedTestCompilerLevel

bStandardClusteringToMassGapTransferLevel : ProofLevel
bStandardClusteringToMassGapTransferLevel =
  R316.round316HalfRateClusteringSpectrumTransferLevel

-- Same-object physical attachment that still survives after R491: the
-- reconstructed Hamiltonian/energy coordinate must be the one whose half-rate
-- Euclidean decay is being consumed by the standard spectral theorem.
bSameHamiltonianTransferCoordinateLevel : ProofLevel
bSameHamiltonianTransferCoordinateLevel =
  R316.round316PhysicalTransferCoordinateLevel

bSameHamiltonianTransferCoordinateStillPhysical : Bool
bSameHamiltonianTransferCoordinateStillPhysical = true

bSameHamiltonianTransferCoordinateStillPhysicalIsTrue :
  bSameHamiltonianTransferCoordinateStillPhysical ≡ true
bSameHamiltonianTransferCoordinateStillPhysicalIsTrue = refl

------------------------------------------------------------------------
-- Corrected source boundary.
------------------------------------------------------------------------

bCMP119122WilsonLoopLocalizationPublished : Bool
bCMP119122WilsonLoopLocalizationPublished = false

bCMP119122WilsonLoopLocalizationPublishedIsFalse :
  bCMP119122WilsonLoopLocalizationPublished ≡ false
bCMP119122WilsonLoopLocalizationPublishedIsFalse = refl

bWilsonLoopExpectationExtensionStillRequired : Bool
bWilsonLoopExpectationExtensionStillRequired = true

bWilsonLoopExpectationExtensionStillRequiredIsTrue :
  bWilsonLoopExpectationExtensionStillRequired ≡ true
bWilsonLoopExpectationExtensionStillRequiredIsTrue = refl

bObservableEqualsPrintedBalabanJRequired : Bool
bObservableEqualsPrintedBalabanJRequired =
  R491.observableEqualsPrintedBalabanJRequired

bObservableEqualsPrintedBalabanJRequiredIsFalse :
  bObservableEqualsPrintedBalabanJRequired ≡ false
bObservableEqualsPrintedBalabanJRequiredIsFalse =
  R491.observableEqualsPrintedBalabanJRequiredIsFalse

bPrintedJNormCalibrationRequiredForWilsonRoute : Bool
bPrintedJNormCalibrationRequiredForWilsonRoute = false

bPrintedJNormCalibrationRequiredForWilsonRouteIsFalse :
  bPrintedJNormCalibrationRequiredForWilsonRoute ≡ false
bPrintedJNormCalibrationRequiredForWilsonRouteIsFalse = refl

------------------------------------------------------------------------
-- Legacy/provenance status.
------------------------------------------------------------------------

historicalSelectedJRollupRetainedForAudit : Bool
historicalSelectedJRollupRetainedForAudit = true

historicalSelectedJRollupRetainedForAuditIsTrue :
  historicalSelectedJRollupRetainedForAudit ≡ true
historicalSelectedJRollupRetainedForAuditIsTrue = refl

historicalSelectedJRollupMandatoryForPreferredWilsonRoute : Bool
historicalSelectedJRollupMandatoryForPreferredWilsonRoute = false

historicalSelectedJRollupMandatoryForPreferredWilsonRouteIsFalse :
  historicalSelectedJRollupMandatoryForPreferredWilsonRoute ≡ false
historicalSelectedJRollupMandatoryForPreferredWilsonRouteIsFalse = refl

------------------------------------------------------------------------
-- Board/compiler accounting.
------------------------------------------------------------------------

round492SourceCorrectOverlayCompilerLevel : ProofLevel
round492SourceCorrectOverlayCompilerLevel = machineChecked

round492LiveBAnalyticPaymentLevel : ProofLevel
round492LiveBAnalyticPaymentLevel =
  R491.round491WilsonTwoInsertionConnectedShellLevel

freshDownstreamDecayCompilerRequired : Bool
freshDownstreamDecayCompilerRequired = false

freshDownstreamDecayCompilerRequiredIsFalse :
  freshDownstreamDecayCompilerRequired ≡ false
freshDownstreamDecayCompilerRequiredIsFalse = refl
