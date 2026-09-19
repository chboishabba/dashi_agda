{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayFullPhysicalFormalismExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact as RouteS
import DASHI.Physics.YangMills.YMClayRouteSSelectedLimitClosureExact as RouteSH2c
import DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact as RouteSH1
import DASHI.Physics.YangMills.YMClayRouteSH1ToR387DirectUpperExact as RouteSH1R387
import DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact as RouteG
import DASHI.Physics.YangMills.YMClayOSLiteralStressRouteParetoExact as StressPareto
import DASHI.Physics.YangMills.YMClayLevel2StressOPEMinCutExact as Level2
import DASHI.Physics.YangMills.YMClayLevel2R129CompositeTailAttachmentExact as D1Compat
import DASHI.Physics.YangMills.YMClayLevel2D1PhysicalMinCutExact as D1
import DASHI.Physics.YangMills.YMClayLevel2OPECoefficientCoordinateWeldExact as D2Compat
import DASHI.Physics.YangMills.YMClayLevel2D2PhysicalMinCutExact as D2
import DASHI.Physics.YangMills.YMClayLevel2ContinuumWardTransportExact as D3
import DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessExact as StrongF4
import DASHI.Physics.YangMills.BalabanClayT5MassScaleDimensionExact as Scale
import DASHI.Physics.YangMills.YMClayCMSDrellYanEmpiricalContactBoundaryExact as CMS

------------------------------------------------------------------------
-- FULL PHYSICAL FORMALISM / ROUTE PARETO
--
-- This is a closed-world architecture owner over the existing typed theorem
-- owners.  It introduces no new physical theorem and does not replace the
-- proof-bearing Route-S, Route-G, D1/D2/D3, F4, SI or empirical interfaces.
--
-- The purpose is to make the current whole-programme shape executable in the
-- source tree without returning to the obsolete linear
--
--   F1 -> F2 -> F3 -> F4
--
-- interpretation.
--
-- Current route hierarchy:
--
--   Route S  selected source / continuum expectation / OS spectral route
--            -> least-privilege physical mass-gap route.
--
--   Route G  uniform finite gap / varying carrier / P_a-E_a recovery route
--            -> stronger independent mass-gap route.
--
--   Level 2  R129 same-family recovery + D1 + D2 + D3
--            -> literal Clay local-QFT stress/OPE endpoint.
--
--   Strong F4
--            stress/Ward common-core data -> same self-adjoint generator
--            -> same Stone/OS evolution.  Useful, but not primitive for the
--            literal Clay stress/OPE endpoint.
--
--   SI / experiment
--            inverse correlation length -> explicit hbar/c mass conversion;
--            CMS/ATLAS-style empirical contact is downstream and orthogonal
--            to theorem closure.
--
-- Probability firewall:
--
--   positive Euclidean weight
--      != normalized Euclidean Gibbs probability
--      != reconstructed quantum measurement law.
--
-- This owner therefore imports no finite-Born toy as a YM proof donor.
------------------------------------------------------------------------

data YMPhysicalLayer : Set where
  finiteLiteralWilsonTheory : YMPhysicalLayer
  directSourceOSMassGap : YMPhysicalLayer
  strongFiniteGapRecovery : YMPhysicalLayer
  literalClayStressOPE : YMPhysicalLayer
  strongerStressGenerator : YMPhysicalLayer
  siMassCalibration : YMPhysicalLayer
  boundedColliderContact : YMPhysicalLayer

data YMPhysicalLayerStatus : Set where
  sourceConstructedSurface : YMPhysicalLayerStatus
  openPhysicalApplication : YMPhysicalLayerStatus
  routeSpecificPhysicalApplication : YMPhysicalLayerStatus
  conditionalCompilerSurface : YMPhysicalLayerStatus
  boundedEmpiricalContact : YMPhysicalLayerStatus

layerStatus : YMPhysicalLayer → YMPhysicalLayerStatus
layerStatus finiteLiteralWilsonTheory = sourceConstructedSurface
layerStatus directSourceOSMassGap = openPhysicalApplication
layerStatus strongFiniteGapRecovery = routeSpecificPhysicalApplication
layerStatus literalClayStressOPE = openPhysicalApplication
layerStatus strongerStressGenerator = routeSpecificPhysicalApplication
layerStatus siMassCalibration = routeSpecificPhysicalApplication
layerStatus boundedColliderContact = boundedEmpiricalContact

------------------------------------------------------------------------
-- Mass-gap route classification.
------------------------------------------------------------------------

directSourceOSIsLeastPrivilegeMassGapRoute : Bool
directSourceOSIsLeastPrivilegeMassGapRoute = true

directSourceOSIsLeastPrivilegeMassGapRouteIsTrue :
  directSourceOSIsLeastPrivilegeMassGapRoute ≡ true
directSourceOSIsLeastPrivilegeMassGapRouteIsTrue = refl

strongFiniteGapRecoveryIsOnlyTerminalRoute : Bool
strongFiniteGapRecoveryIsOnlyTerminalRoute =
  RouteG.strongFiniteGapRecoveryFrontierIsOnlyTerminalRoute

strongFiniteGapRecoveryIsOnlyTerminalRouteIsFalse :
  strongFiniteGapRecoveryIsOnlyTerminalRoute ≡ false
strongFiniteGapRecoveryIsOnlyTerminalRouteIsFalse =
  RouteG.strongFiniteGapRecoveryFrontierIsOnlyTerminalRouteIsFalse

routeSRequiresDenseL2Normalization : Bool
routeSRequiresDenseL2Normalization =
  RouteS.denseL2NormalizationMandatoryForDirectSourceRoute

routeSRequiresDenseL2NormalizationIsFalse :
  routeSRequiresDenseL2Normalization ≡ false
routeSRequiresDenseL2NormalizationIsFalse =
  RouteS.denseL2NormalizationMandatoryForDirectSourceRouteIsFalse

routeSRequiresFiniteTrajectoryGapCalibration : Bool
routeSRequiresFiniteTrajectoryGapCalibration =
  RouteS.finiteTrajectoryGapCalibrationMandatoryForDirectSourceRoute

routeSRequiresFiniteTrajectoryGapCalibrationIsFalse :
  routeSRequiresFiniteTrajectoryGapCalibration ≡ false
routeSRequiresFiniteTrajectoryGapCalibrationIsFalse =
  RouteS.finiteTrajectoryGapCalibrationMandatoryForDirectSourceRouteIsFalse

routeSRequiresPaEaMoscoRecovery : Bool
routeSRequiresPaEaMoscoRecovery =
  RouteS.paEaMoscoRecoveryMandatoryForDirectSourceRoute

routeSRequiresPaEaMoscoRecoveryIsFalse :
  routeSRequiresPaEaMoscoRecovery ≡ false
routeSRequiresPaEaMoscoRecoveryIsFalse =
  RouteS.paEaMoscoRecoveryMandatoryForDirectSourceRouteIsFalse

routeSStillRequiresContinuumMeasure : Bool
routeSStillRequiresContinuumMeasure =
  RouteS.continuumMeasureCarrierStillRequired

routeSStillRequiresContinuumMeasureIsTrue :
  routeSStillRequiresContinuumMeasure ≡ true
routeSStillRequiresContinuumMeasureIsTrue =
  RouteS.continuumMeasureCarrierStillRequiredIsTrue

routeSStillRequiresOSReconstruction : Bool
routeSStillRequiresOSReconstruction =
  RouteS.osReconstructionStillRequired

routeSStillRequiresOSReconstructionIsTrue :
  routeSStillRequiresOSReconstruction ≡ true
routeSStillRequiresOSReconstructionIsTrue =
  RouteS.osReconstructionStillRequiredIsTrue

routeSTerminalRequiresSequentialOrderClosureRecord : Bool
routeSTerminalRequiresSequentialOrderClosureRecord =
  RouteSH2c.terminalRouteRequiresSequentialOrderClosureRecord

routeSTerminalRequiresSequentialOrderClosureRecordIsFalse :
  routeSTerminalRequiresSequentialOrderClosureRecord ≡ false
routeSTerminalRequiresSequentialOrderClosureRecordIsFalse =
  RouteSH2c.terminalRouteRequiresSequentialOrderClosureRecordIsFalse

routeSTerminalRequiresSameConvergenceWeld : Bool
routeSTerminalRequiresSameConvergenceWeld =
  RouteSH2c.terminalRouteRequiresSameConvergenceWeld

routeSTerminalRequiresSameConvergenceWeldIsFalse :
  routeSTerminalRequiresSameConvergenceWeld ≡ false
routeSTerminalRequiresSameConvergenceWeldIsFalse =
  RouteSH2c.terminalRouteRequiresSameConvergenceWeldIsFalse

routeSTerminalRequiresSelectedLimitUpperClosure : Bool
routeSTerminalRequiresSelectedLimitUpperClosure =
  RouteSH2c.terminalRouteRequiresSelectedLimitUpperClosure

routeSTerminalRequiresSelectedLimitUpperClosureIsTrue :
  routeSTerminalRequiresSelectedLimitUpperClosure ≡ true
routeSTerminalRequiresSelectedLimitUpperClosureIsTrue =
  RouteSH2c.terminalRouteRequiresSelectedLimitUpperClosureIsTrue


routeSH1HasOneTheoremBearingField : Bool
routeSH1HasOneTheoremBearingField =
  RouteSH1.canonicalH1HasOneTheoremBearingField

routeSH1HasOneTheoremBearingFieldIsTrue :
  routeSH1HasOneTheoremBearingField ≡ true
routeSH1HasOneTheoremBearingFieldIsTrue =
  RouteSH1.canonicalH1HasOneTheoremBearingFieldIsTrue

routeSH1RequiresHistoricalPublishedWrapper : Bool
routeSH1RequiresHistoricalPublishedWrapper =
  RouteSH1.publishedLocalizationWrapperMandatoryForCanonicalH1

routeSH1RequiresHistoricalPublishedWrapperIsFalse :
  routeSH1RequiresHistoricalPublishedWrapper ≡ false
routeSH1RequiresHistoricalPublishedWrapperIsFalse =
  RouteSH1.publishedLocalizationWrapperMandatoryForCanonicalH1IsFalse

routeSH1ToR387RequiresSourceEnvelope : Bool
routeSH1ToR387RequiresSourceEnvelope =
  RouteSH1R387.sourceEnvelopeRequiredBetweenH1AndR387

routeSH1ToR387RequiresSourceEnvelopeIsFalse :
  routeSH1ToR387RequiresSourceEnvelope ≡ false
routeSH1ToR387RequiresSourceEnvelopeIsFalse =
  RouteSH1R387.sourceEnvelopeRequiredBetweenH1AndR387IsFalse

routeSH1TimeMeaningRemainsSeparate : Bool
routeSH1TimeMeaningRemainsSeparate =
  RouteSH1R387.selectedTimeMeaningRemainsOutsideH1

routeSH1TimeMeaningRemainsSeparateIsTrue :
  routeSH1TimeMeaningRemainsSeparate ≡ true
routeSH1TimeMeaningRemainsSeparateIsTrue =
  RouteSH1R387.selectedTimeMeaningRemainsOutsideH1IsTrue

routeSH1FastEnvelopeMeaningRemainsSeparate : Bool
routeSH1FastEnvelopeMeaningRemainsSeparate =
  RouteSH1R387.selectedFastEnvelopeMeaningRemainsOutsideH1

routeSH1FastEnvelopeMeaningRemainsSeparateIsTrue :
  routeSH1FastEnvelopeMeaningRemainsSeparate ≡ true
routeSH1FastEnvelopeMeaningRemainsSeparateIsTrue =
  RouteSH1R387.selectedFastEnvelopeMeaningRemainsOutsideH1IsTrue

f2PrimitiveResearchPayment : Bool
f2PrimitiveResearchPayment = RouteG.f2PrimitiveResearchPayment

f2PrimitiveResearchPaymentIsFalse :
  f2PrimitiveResearchPayment ≡ false
f2PrimitiveResearchPaymentIsFalse =
  RouteG.f2PrimitiveResearchPaymentIsFalse

varyingCarrierEmbeddingsRemainStrongRouteF3Data : Bool
varyingCarrierEmbeddingsRemainStrongRouteF3Data =
  RouteG.varyingCarrierEmbeddingsRemainF3Data

varyingCarrierEmbeddingsRemainStrongRouteF3DataIsTrue :
  varyingCarrierEmbeddingsRemainStrongRouteF3Data ≡ true
varyingCarrierEmbeddingsRemainStrongRouteF3DataIsTrue =
  RouteG.varyingCarrierEmbeddingsRemainF3DataIsTrue

------------------------------------------------------------------------
-- OS / Level-2 route classification.
------------------------------------------------------------------------

osReconstructionMachineryMissing : Bool
osReconstructionMachineryMissing =
  StressPareto.osReconstructionMachineryMissing

osReconstructionMachineryMissingIsFalse :
  osReconstructionMachineryMissing ≡ false
osReconstructionMachineryMissingIsFalse =
  StressPareto.osReconstructionMachineryMissingIsFalse

r129PaysR127AndStressDerivative : Bool
r129PaysR127AndStressDerivative =
  Level2.r129RecoveryPaysR127AndStressDerivative

r129PaysR127AndStressDerivativeIsTrue :
  r129PaysR127AndStressDerivative ≡ true
r129PaysR127AndStressDerivativeIsTrue =
  Level2.r129RecoveryPaysR127AndStressDerivativeIsTrue

d1IsSemanticWeldNotNewDecayAnalysis : Bool
d1IsSemanticWeldNotNewDecayAnalysis =
  D1.directSameObjectRemainderEqualityStillPhysical

d1IsSemanticWeldNotNewDecayAnalysisIsTrue :
  d1IsSemanticWeldNotNewDecayAnalysis ≡ true
d1IsSemanticWeldNotNewDecayAnalysisIsTrue =
  D1.directSameObjectRemainderEqualityStillPhysicalIsTrue

d1NewAnalyticInequalityRequired : Bool
d1NewAnalyticInequalityRequired =
  D1.newD1AnalyticInequalityRequired

d1NewAnalyticInequalityRequiredIsFalse :
  d1NewAnalyticInequalityRequired ≡ false
d1NewAnalyticInequalityRequiredIsFalse =
  D1.newD1AnalyticInequalityRequiredIsFalse

d1AuxiliaryProductRemainderFunctionRequired : Bool
d1AuxiliaryProductRemainderFunctionRequired =
  D1.auxiliaryProductRemainderFunctionRequiredByD1

d1AuxiliaryProductRemainderFunctionRequiredIsFalse :
  d1AuxiliaryProductRemainderFunctionRequired ≡ false
d1AuxiliaryProductRemainderFunctionRequiredIsFalse =
  D1.auxiliaryProductRemainderFunctionRequiredByD1IsFalse

d1IndependentCompositeCarrierRequiredAfterR129 : Bool
d1IndependentCompositeCarrierRequiredAfterR129 =
  D1.independentCompositeCarrierRequiredAfterR129

d1IndependentCompositeCarrierRequiredAfterR129IsFalse :
  d1IndependentCompositeCarrierRequiredAfterR129 ≡ false
d1IndependentCompositeCarrierRequiredAfterR129IsFalse =
  D1.independentCompositeCarrierRequiredAfterR129IsFalse

d2SameCoordinateAttachmentStillPhysical : Bool
d2SameCoordinateAttachmentStillPhysical =
  D2.positionDepthSemanticsIsIndependentPhysicalAttachment

d2SameCoordinateAttachmentStillPhysicalIsTrue :
  d2SameCoordinateAttachmentStillPhysical ≡ true
d2SameCoordinateAttachmentStillPhysicalIsTrue =
  D2.positionDepthSemanticsIsIndependentPhysicalAttachmentIsTrue

d2NewGlobalAFTheoremRequired : Bool
d2NewGlobalAFTheoremRequired =
  D2.newGlobalAFTheoremRequired

d2NewGlobalAFTheoremRequiredIsFalse :
  d2NewGlobalAFTheoremRequired ≡ false
d2NewGlobalAFTheoremRequiredIsFalse =
  D2.newGlobalAFTheoremRequiredIsFalse

d2SecondMixingMapRequired : Bool
d2SecondMixingMapRequired =
  D2.secondMixingMapResearchProblem

d2SecondMixingMapRequiredIsFalse :
  d2SecondMixingMapRequired ≡ false
d2SecondMixingMapRequiredIsFalse =
  D2.secondMixingMapResearchProblemIsFalse

d2LiteralCoefficientIsConstantNatFamily : Bool
d2LiteralCoefficientIsConstantNatFamily =
  D2.literalClayCoefficientCanBeTreatedAsConstantNatFamily

d2LiteralCoefficientIsConstantNatFamilyIsFalse :
  d2LiteralCoefficientIsConstantNatFamily ≡ false
d2LiteralCoefficientIsConstantNatFamilyIsFalse =
  D2.literalClayCoefficientCanBeTreatedAsConstantNatFamilyIsFalse


d2ParallelCompositeOperatorTheoryAllowed : Bool
d2ParallelCompositeOperatorTheoryAllowed =
  D2.parallelCompositeOperatorTheoryAllowed

d2ParallelCompositeOperatorTheoryAllowedIsFalse :
  d2ParallelCompositeOperatorTheoryAllowed ≡ false
d2ParallelCompositeOperatorTheoryAllowedIsFalse =
  D2.parallelCompositeOperatorTheoryAllowedIsFalse

d2R129SameFamilyOperatorAttachmentStillPhysical : Bool
d2R129SameFamilyOperatorAttachmentStillPhysical =
  D2.r129SameFamilyOperatorAttachmentStillPhysical

d2R129SameFamilyOperatorAttachmentStillPhysicalIsTrue :
  d2R129SameFamilyOperatorAttachmentStillPhysical ≡ true
d2R129SameFamilyOperatorAttachmentStillPhysicalIsTrue =
  D2.r129SameFamilyOperatorAttachmentStillPhysicalIsTrue

d3FiniteToContinuumTransportStillPhysical : Bool
d3FiniteToContinuumTransportStillPhysical =
  D3.finiteToContinuumSameCurrentTransportStillPhysical

d3FiniteToContinuumTransportStillPhysicalIsTrue :
  d3FiniteToContinuumTransportStillPhysical ≡ true
d3FiniteToContinuumTransportStillPhysicalIsTrue =
  D3.finiteToContinuumSameCurrentTransportStillPhysicalIsTrue

d3FiniteWardAlgebraNeedsNewPhysicalTheorem : Bool
d3FiniteWardAlgebraNeedsNewPhysicalTheorem =
  D3.finiteWardAlgebraNewPhysicalTheoremInD3

d3FiniteWardAlgebraNeedsNewPhysicalTheoremIsFalse :
  d3FiniteWardAlgebraNeedsNewPhysicalTheorem ≡ false
d3FiniteWardAlgebraNeedsNewPhysicalTheoremIsFalse =
  D3.finiteWardAlgebraNewPhysicalTheoremInD3IsFalse


d3PerturbationIndependentWardSequenceWouldBeTooWeak : Bool
d3PerturbationIndependentWardSequenceWouldBeTooWeak =
  D3.perturbationIndependentWardChargeSequenceWouldBeTooWeak

d3PerturbationIndependentWardSequenceWouldBeTooWeakIsTrue :
  d3PerturbationIndependentWardSequenceWouldBeTooWeak ≡ true
d3PerturbationIndependentWardSequenceWouldBeTooWeakIsTrue =
  D3.perturbationIndependentWardChargeSequenceWouldBeTooWeakIsTrue

d3CutoffIndependentChargeMapRequired : Bool
d3CutoffIndependentChargeMapRequired =
  D3.cutoffIndependentChargeRepresentationMapRequired

d3CutoffIndependentChargeMapRequiredIsFalse :
  d3CutoffIndependentChargeMapRequired ≡ false
d3CutoffIndependentChargeMapRequiredIsFalse =
  D3.cutoffIndependentChargeRepresentationMapRequiredIsFalse

literalClayStressOPERequiresStressChargeEqualsOSHamiltonian : Bool
literalClayStressOPERequiresStressChargeEqualsOSHamiltonian =
  StressPareto.stressChargeEqualsOSHamiltonianMandatoryForLiteralClayStressOPE

literalClayStressOPERequiresStressChargeEqualsOSHamiltonianIsFalse :
  literalClayStressOPERequiresStressChargeEqualsOSHamiltonian ≡ false
literalClayStressOPERequiresStressChargeEqualsOSHamiltonianIsFalse =
  StressPareto.stressChargeEqualsOSHamiltonianMandatoryForLiteralClayStressOPEIsFalse

strongF4EvolutionEqualityPrimitive : Bool
strongF4EvolutionEqualityPrimitive =
  StrongF4.evolutionEqualityPrimitivePhysicalInput

strongF4EvolutionEqualityPrimitiveIsFalse :
  strongF4EvolutionEqualityPrimitive ≡ false
strongF4EvolutionEqualityPrimitiveIsFalse =
  StrongF4.evolutionEqualityPrimitivePhysicalInputIsFalse

------------------------------------------------------------------------
-- SI / measurement / empirical firewalls.
------------------------------------------------------------------------

euclideanGibbsProbabilityIsBornMeasurementLaw : Bool
euclideanGibbsProbabilityIsBornMeasurementLaw = false

euclideanGibbsProbabilityIsBornMeasurementLawIsFalse :
  euclideanGibbsProbabilityIsBornMeasurementLaw ≡ false
euclideanGibbsProbabilityIsBornMeasurementLawIsFalse = refl

inverseCorrelationLengthSilentlyIsSIMass : Bool
inverseCorrelationLengthSilentlyIsSIMass =
  Scale.inverseLengthSilentlyIdentifiedWithSIMass

inverseCorrelationLengthSilentlyIsSIMassIsFalse :
  inverseCorrelationLengthSilentlyIsSIMass ≡ false
inverseCorrelationLengthSilentlyIsSIMassIsFalse =
  Scale.inverseLengthSilentlyIdentifiedWithSIMassIsFalse

explicitHBarOverCConversionStillRequired : Bool
explicitHBarOverCConversionStillRequired = true

explicitHBarOverCConversionStillRequiredIsTrue :
  explicitHBarOverCConversionStillRequired ≡ true
explicitHBarOverCConversionStillRequiredIsTrue = refl

cmsContactIsBoundedEmpiricalContact : Bool
cmsContactIsBoundedEmpiricalContact =
  CMS.cmsContactIsBoundedExperimentalQCDContact

cmsContactIsBoundedEmpiricalContactIsTrue :
  cmsContactIsBoundedEmpiricalContact ≡ true
cmsContactIsBoundedEmpiricalContactIsTrue =
  CMS.cmsContactIsBoundedExperimentalQCDContactIsTrue

cmsContactPaysClayProofFrontier : Bool
cmsContactPaysClayProofFrontier = false

cmsContactPaysClayProofFrontierIsFalse :
  cmsContactPaysClayProofFrontier ≡ false
cmsContactPaysClayProofFrontierIsFalse = refl

cmsContactOrthogonalToClayProofFrontier : Bool
cmsContactOrthogonalToClayProofFrontier =
  CMS.cmsContactOrthogonalToClayProofFrontier

cmsContactOrthogonalToClayProofFrontierIsTrue :
  cmsContactOrthogonalToClayProofFrontier ≡ true
cmsContactOrthogonalToClayProofFrontierIsTrue =
  CMS.cmsContactOrthogonalToClayProofFrontierIsTrue

------------------------------------------------------------------------
-- Proof-level summary.  These levels inherit authority from their owners.
------------------------------------------------------------------------

directSourceOSRouteLevel : ProofLevel
directSourceOSRouteLevel = RouteS.physicalDirectSourceOSRouteLevel

strongFiniteGapF1Level : ProofLevel
strongFiniteGapF1Level = RouteG.f1Level

strongRecoveryF3Level : ProofLevel
strongRecoveryF3Level = RouteG.f3Level

literalClayStressOPELevel : ProofLevel
literalClayStressOPELevel = Level2.level2StressOPEPhysicalMinCutLevel

strongStressGeneratorLevel : ProofLevel
strongStressGeneratorLevel = StrongF4.physicalStressOSCommonCoreLevel

siNaturalUnitMassConversionLevel : ProofLevel
siNaturalUnitMassConversionLevel = Scale.naturalUnitMassConversionLevel

unconditionalClayPromotion : Bool
unconditionalClayPromotion = false

unconditionalClayPromotionIsFalse :
  unconditionalClayPromotion ≡ false
unconditionalClayPromotionIsFalse = refl
