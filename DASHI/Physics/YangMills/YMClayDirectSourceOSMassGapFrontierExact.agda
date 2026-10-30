{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact as R313
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanCanonicalBOSIndexedCompletionRound333Exact as R333
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound330Exact as R330
import DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact as R332
import DASHI.Physics.YangMills.BalabanPairwiseWilsonBoundedTestsRound315Exact as R315
import DASHI.Physics.YangMills.BalabanOSIndexedTransferCoordinateRound331Exact as R331
import DASHI.Physics.YangMills.BalabanHalfRateTransferCoordinateMassGapRound316Exact as R316
import DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact as H1

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
-- H1 -> R295 -> R313 -> R296 -> R333: direct Route-S min-cut.
--
-- Do not pay a second finite-magnitude/source-localization lemma after the
-- canonical R320 physical selected-J payment. R313 already derives literal
-- absolute two-J localization from R295 when the scalar magnitude is rational
-- absolute value. Both are the SAME physical T5 family.
--
-- Source attribution: Tadeusz Bałaban, CMP 116 (1988),
-- DOI 10.1007/BF01239022. DASHI owns only the compiler composition.
------------------------------------------------------------------------

routeSH1BuildsFiniteMagnitude :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension) →
  H1.RouteSH1DirectSelectedPayment base →
  (magnitudeIsAbsolute :
    ∀ value → R278.magnitude extension value ≡ ∣ value ∣) →
  R296.ExactT5JMagnitudePresentation dataSet extension
routeSH1BuildsFiniteMagnitude base payment magnitudeIsAbsolute =
  R313.exactT5JMagnitudeFromR295
    (H1.h1BuildsLocalizedR295 base payment) magnitudeIsAbsolute

-- Exact same-source invariant: the upgraded R296 does not select a second
-- independent finite T5 source family.
routeSH1FiniteKeepsSelectedSource :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (payment : H1.RouteSH1DirectSelectedPayment base)
    (magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ∣ value ∣) →
  R296.source (routeSH1BuildsFiniteMagnitude base payment magnitudeIsAbsolute)
    ≡ H1.h1BuildsLocalizedR295 base payment
routeSH1FiniteKeepsSelectedSource base payment magnitudeIsAbsolute = refl

-- The existing R333 physical application and completion are STILL actual
-- theorem-bearing inputs. This composition is a typed physical implication,
-- not a manufactured continuum Schwinger family or mass-gap witness.
routeSH1BuildsPhysicalMassGap :
  ∀ {Measure TestObservable PhysicalObservable Loop Translation Rotation}
    {Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (payment : H1.RouteSH1DirectSelectedPayment base)
    (magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ∣ value ∣)
    {assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {Energy : Set} →
  DirectSourceOSMassGapInputs
    {PhysicalObservable = PhysicalObservable} {Loop = Loop}
    dataSet extension
    (routeSH1BuildsFiniteMagnitude base payment magnitudeIsAbsolute)
    assembly reconstruction Energy →
  OS.PhysicalMassGapCertificate (OS.Hamiltonian reconstruction) Energy
routeSH1BuildsPhysicalMassGap base payment magnitudeIsAbsolute inputs =
  directSourceOSBuildsPhysicalMassGap inputs

routeSH1ReusesR313MagnitudeCompiler : Bool
routeSH1ReusesR313MagnitudeCompiler =
  R313.r296AbsoluteLocalizationIndependentAfterR295MagnitudeBound

routeSH1ReusesR313MagnitudeCompilerIsFalse :
  routeSH1ReusesR313MagnitudeCompiler ≡ false
routeSH1ReusesR313MagnitudeCompilerIsFalse =
  R313.r296AbsoluteLocalizationIndependentAfterR295MagnitudeBoundIsFalse

routeSH1ToDirectOSCompilerLevel : ProofLevel
-- Source-written typed compiler; exact-head Agda kernel receipt not observed.
routeSH1ToDirectOSCompilerLevel = conditional

routeSH1SelectedPhysicalPaymentLevel : ProofLevel
routeSH1SelectedPhysicalPaymentLevel = H1.routeSH1PhysicalLevel

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


canonicalH1HasOneTheoremBearingField : Bool
canonicalH1HasOneTheoremBearingField =
  H1.canonicalH1HasOneTheoremBearingField

canonicalH1HasOneTheoremBearingFieldIsTrue :
  canonicalH1HasOneTheoremBearingField ≡ true
canonicalH1HasOneTheoremBearingFieldIsTrue =
  H1.canonicalH1HasOneTheoremBearingFieldIsTrue

historicalPublishedLocalizationWrapperMandatory : Bool
historicalPublishedLocalizationWrapperMandatory =
  H1.publishedLocalizationWrapperMandatoryForCanonicalH1

historicalPublishedLocalizationWrapperMandatoryIsFalse :
  historicalPublishedLocalizationWrapperMandatory ≡ false
historicalPublishedLocalizationWrapperMandatoryIsFalse =
  H1.publishedLocalizationWrapperMandatoryForCanonicalH1IsFalse

h1IndependentDirectShellRequired : Bool
h1IndependentDirectShellRequired =
  H1.independentDirectT5ShellMandatoryAfterH1

h1IndependentDirectShellRequiredIsFalse :
  h1IndependentDirectShellRequired ≡ false
h1IndependentDirectShellRequiredIsFalse =
  H1.independentDirectT5ShellMandatoryAfterH1IsFalse

h1PhysicalDirectSelectedDecayLevel : ProofLevel
h1PhysicalDirectSelectedDecayLevel = H1.routeSH1PhysicalLevel

h1CompilerLevel : ProofLevel
h1CompilerLevel = H1.routeSH1CompilerLevel

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
