{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanCanonicalBOSIndexedCompletionRound333Exact as R333
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact as R330
import DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact as R332
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.BalabanOSIndexedTransferCoordinateRound331Exact as R331
import DASHI.Physics.YangMills.BalabanHalfRateTransferCoordinateMassGapRound316Exact as R316

------------------------------------------------------------------------
-- DIRECT SOURCE -> CONTINUUM OS MASS-GAP FRONTIER
--
-- The bounded-form route
--
--   dense L2 transfer defect -> uniform finite gap -> P_a/E_a Mosco recovery
--
-- is a valid strong route, but it is not the least-privilege terminal consumer.
--
-- R304/R316/R330-R333 already provide a direct source/OS route:
--
--   exact finite T5 two-J shell
--     + OS-indexed Euclidean time/support semantics
--     + Wilson-cylinder presentation
--     + one-sided sequential order closure
--     + transfer coordinate OF the reconstructed OS Hamiltonian
--       -> continuum pair clustering
--       -> physical mass-gap certificate.
--
-- Thus the dense-L2 envelope normalization, Delta*a_k finite-gap calibration,
-- and P_a/E_a Mosco recovery are route-specific strong payments, not globally
-- mandatory prerequisites for the terminal physical spectral gap.
------------------------------------------------------------------------

record DirectSourceOSMassGapInputs
    {Measure TestObservable PhysicalObservable Loop Translation Rotation : Set}
    {Observable Point Scalar : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (finite : R296.ExactT5JMagnitudePresentation dataSet extension)
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ)
    (reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system)
    (Energy : Set) : Set₁ where
  field
    application :
      R333.CanonicalBOSIndexedApplication
        {PhysicalObservable = PhysicalObservable}
        {Loop = Loop}
        dataSet extension finite assembly reconstruction Energy

    completion :
      R333.CanonicalBOSIndexedCompletion application

open DirectSourceOSMassGapInputs public

directSourceOSBuildsPhysicalMassGap :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set} →
  DirectSourceOSMassGapInputs
    {PhysicalObservable = PhysicalObservable}
    {Loop = Loop}
    dataSet extension finite assembly reconstruction Energy →
  OS.PhysicalMassGapCertificate (OS.Hamiltonian reconstruction) Energy
directSourceOSBuildsPhysicalMassGap inputs =
  R333.compileCanonicalBOSIndexedCompletion (completion inputs)

------------------------------------------------------------------------
-- Exact route classification.
------------------------------------------------------------------------

denseL2NormalizationMandatoryForDirectSourceRoute : Bool
denseL2NormalizationMandatoryForDirectSourceRoute = false

denseL2NormalizationMandatoryForDirectSourceRouteIsFalse :
  denseL2NormalizationMandatoryForDirectSourceRoute ≡ false
denseL2NormalizationMandatoryForDirectSourceRouteIsFalse = refl

finiteTrajectoryGapCalibrationMandatoryForDirectSourceRoute : Bool
finiteTrajectoryGapCalibrationMandatoryForDirectSourceRoute = false

finiteTrajectoryGapCalibrationMandatoryForDirectSourceRouteIsFalse :
  finiteTrajectoryGapCalibrationMandatoryForDirectSourceRoute ≡ false
finiteTrajectoryGapCalibrationMandatoryForDirectSourceRouteIsFalse = refl

paEaMoscoRecoveryMandatoryForDirectSourceRoute : Bool
paEaMoscoRecoveryMandatoryForDirectSourceRoute = false

paEaMoscoRecoveryMandatoryForDirectSourceRouteIsFalse :
  paEaMoscoRecoveryMandatoryForDirectSourceRoute ≡ false
paEaMoscoRecoveryMandatoryForDirectSourceRouteIsFalse = refl

continuumMeasureCarrierStillRequired : Bool
continuumMeasureCarrierStillRequired = true

continuumMeasureCarrierStillRequiredIsTrue :
  continuumMeasureCarrierStillRequired ≡ true
continuumMeasureCarrierStillRequiredIsTrue = refl

osReconstructionStillRequired : Bool
osReconstructionStillRequired = true

osReconstructionStillRequiredIsTrue :
  osReconstructionStillRequired ≡ true
osReconstructionStillRequiredIsTrue = refl

mandatoryFreshBAnalyticInequalityCountIsZero : Bool
mandatoryFreshBAnalyticInequalityCountIsZero =
  R330.Round330Boundary.mandatoryFreshBYMAnalyticInequalityCountIsZero
    R330.canonicalRound330Boundary

directSourceApplicationCompilerLevel : ProofLevel
directSourceApplicationCompilerLevel = R333.round333ApplicationCompilerLevel

h2aPhysicalTimeSupportMeaningLevel : ProofLevel
h2aPhysicalTimeSupportMeaningLevel = R332.round332SupportDistanceMeaningLevel

h2bPhysicalWilsonPresentationLevel : ProofLevel
h2bPhysicalWilsonPresentationLevel = R315.round315SelectedWilsonPresentationLevel

h3TransferCoordinateOfOSHamiltonianLevel : ProofLevel
h3TransferCoordinateOfOSHamiltonianLevel =
  R331.round331PhysicalTransferCoordinateOfOSHamiltonianLevel

spectralTransferAuthorityLevel : ProofLevel
spectralTransferAuthorityLevel =
  R316.round316HalfRateClusteringSpectrumTransferLevel

physicalDirectSourceOSRouteLevel : ProofLevel
physicalDirectSourceOSRouteLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
