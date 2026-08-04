module DASHI.Physics.Closure.NSTriadKNLuoSubmissionDependencyCutsetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Charles L. Fefferman; Clay Mathematics Institute.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Millennium Prize Problems, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
-- Turn the entire route from the current Luo physical leaves to a
-- submission-grade periodic Navier--Stokes theorem into typed, non-overlapping
-- cutsets.  Each named proposition has a witness field; no generic
-- "analysis completed" token can silently discharge distinct obligations.
--
-- This module is an ownership and composition theorem.  It intentionally does
-- not inhabit the frontier PDE propositions.  Those remain visible to the
-- authoritative task ledger until proved on the official carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

record Equation42PhysicalCutset : Set₁ where
  field
    ShellProjectorCommutesWithTimeDerivative : Set
    shellProjectorCommutesWithTimeDerivative :
      ShellProjectorCommutesWithTimeDerivative

    ShellProjectorCommutesWithLaplacian : Set
    shellProjectorCommutesWithLaplacian :
      ShellProjectorCommutesWithLaplacian

    ShellProjectedNavierStokesEquation : Set
    shellProjectedNavierStokesEquation :
      ShellProjectedNavierStokesEquation

    ProjectedPressureCancellation : Set
    projectedPressureCancellation : ProjectedPressureCancellation

    ProjectedConvectionPairingMeaning : Set
    projectedConvectionPairingMeaning :
      ProjectedConvectionPairingMeaning

    TimeDerivativeOfShellL2Squared : Set
    timeDerivativeOfShellL2Squared :
      TimeDerivativeOfShellL2Squared

    ShellL2DifferentiabilityBeforeMaximalTime : Set
    shellL2DifferentiabilityBeforeMaximalTime :
      ShellL2DifferentiabilityBeforeMaximalTime

    HermitianPairingRealPartMeaning : Set
    hermitianPairingRealPartMeaning :
      HermitianPairingRealPartMeaning

    FactorTwoNormalizationAudit : Set
    factorTwoNormalizationAudit : FactorTwoNormalizationAudit

    LaplacianPairingEqualsNegativeGradientNormSquared : Set
    laplacianPairingEqualsNegativeGradientNormSquared :
      LaplacianPairingEqualsNegativeGradientNormSquared

    ShellDissipationEqualsFrequencyWeightedL2 : Set
    shellDissipationEqualsFrequencyWeightedL2 :
      ShellDissipationEqualsFrequencyWeightedL2

    DissipationNonnegative : Set
    dissipationNonnegative : DissipationNonnegative

    ViscosityNormalizationExact : Set
    viscosityNormalizationExact : ViscosityNormalizationExact

    ProjectedConvectionPairingEqualsFluxAtShell : Set
    projectedConvectionPairingEqualsFluxAtShell :
      ProjectedConvectionPairingEqualsFluxAtShell

    NonlinearPairingBelowAbsoluteFlux : Set
    nonlinearPairingBelowAbsoluteFlux :
      NonlinearPairingBelowAbsoluteFlux

    ShellEnergyInequalityAgainstPhysicalRHS : Set
    shellEnergyInequalityAgainstPhysicalRHS :
      ShellEnergyInequalityAgainstPhysicalRHS

    ConvectionFourierCoefficientFormula : Set
    convectionFourierCoefficientFormula :
      ConvectionFourierCoefficientFormula

    LerayProjectionCoefficientFormula : Set
    lerayProjectionCoefficientFormula :
      LerayProjectionCoefficientFormula

    DivergenceFreeSimplifiesConvectionKernel : Set
    divergenceFreeSimplifiesConvectionKernel :
      DivergenceFreeSimplifiesConvectionKernel

    ShellPairingAsResonantTriadSum : Set
    shellPairingAsResonantTriadSum :
      ShellPairingAsResonantTriadSum

    TriadSumEqualsPhysicalEnumeration : Set
    triadSumEqualsPhysicalEnumeration :
      TriadSumEqualsPhysicalEnumeration

    PhysicalEnumerationPartitionedIntoLuoPieces : Set
    physicalEnumerationPartitionedIntoLuoPieces :
      PhysicalEnumerationPartitionedIntoLuoPieces

    LuoPiecePartitionDisjoint : Set
    luoPiecePartitionDisjoint : LuoPiecePartitionDisjoint

    LuoPiecePartitionComplete : Set
    luoPiecePartitionComplete : LuoPiecePartitionComplete

    BoundaryTransitionCasesAssignedExactlyOnce : Set
    boundaryTransitionCasesAssignedExactlyOnce :
      BoundaryTransitionCasesAssignedExactlyOnce

    J1EqualsLowHighAndHighLowPieces : Set
    j1EqualsLowHighAndHighLowPieces :
      J1EqualsLowHighAndHighLowPieces

    J2EqualsHighHighPiece : Set
    j2EqualsHighHighPiece : J2EqualsHighHighPiece

    PhysicalRHSMatchesTotalInteractionFold : Set
    physicalRHSMatchesTotalInteractionFold :
      PhysicalRHSMatchesTotalInteractionFold

open Equation42PhysicalCutset public

record Section4PhysicalCutset : Set₁ where
  field
    J11LowerSingleInteractionBound : Set
    j11LowerSingleInteractionBound : J11LowerSingleInteractionBound

    J11LowerFixedOutputShellBound : Set
    j11LowerFixedOutputShellBound : J11LowerFixedOutputShellBound

    J11LowerLowShellSummation : Set
    j11LowerLowShellSummation : J11LowerLowShellSummation

    J11LowerTimeIntegratedBound : Set
    j11LowerTimeIntegratedBound : J11LowerTimeIntegratedBound

    PhysicalJ11LowerBound : Set
    physicalJ11LowerBound : PhysicalJ11LowerBound

    J11UpperComparableShellLocalization : Set
    j11UpperComparableShellLocalization :
      J11UpperComparableShellLocalization

    J11UpperFiniteNeighbourMultiplicity : Set
    j11UpperFiniteNeighbourMultiplicity :
      J11UpperFiniteNeighbourMultiplicity

    J11UpperSingleShellBound : Set
    j11UpperSingleShellBound : J11UpperSingleShellBound

    J11UpperRangeSumBound : Set
    j11UpperRangeSumBound : J11UpperRangeSumBound

    PhysicalJ11UpperBound : Set
    physicalJ11UpperBound : PhysicalJ11UpperBound

    J12CommutatorIdentity : Set
    j12CommutatorIdentity : J12CommutatorIdentity

    J12IncrementRepresentation : Set
    j12IncrementRepresentation : J12IncrementRepresentation

    J12KernelMomentCancellation : Set
    j12KernelMomentCancellation : J12KernelMomentCancellation

    J12SinglePairBound : Set
    j12SinglePairBound : J12SinglePairBound

    J12ShellSumBound : Set
    j12ShellSumBound : J12ShellSumBound

    PhysicalJ12Bound : Set
    physicalJ12Bound : PhysicalJ12Bound

    J2HighHighOutputConstraint : Set
    j2HighHighOutputConstraint : J2HighHighOutputConstraint

    J2InputShellComparability : Set
    j2InputShellComparability : J2InputShellComparability

    J2OutputRelocationDecay : Set
    j2OutputRelocationDecay : J2OutputRelocationDecay

    J2SignedCoefficientMajorant : Set
    j2SignedCoefficientMajorant : J2SignedCoefficientMajorant

    J2PositiveKernelDomination : Set
    j2PositiveKernelDomination : J2PositiveKernelDomination

    J2GeometricGapSummation : Set
    j2GeometricGapSummation : J2GeometricGapSummation

    J2UniformSchurBound : Set
    j2UniformSchurBound : J2UniformSchurBound

    PhysicalJ2Bound : Set
    physicalJ2Bound : PhysicalJ2Bound

open Section4PhysicalCutset public

record FractionalPowerGronwallCutset : Set₁ where
  field
    DyadicScaleDefinition : Set
    dyadicScaleDefinition : DyadicScaleDefinition

    DyadicShiftLaw : Set
    dyadicShiftLaw : DyadicShiftLaw

    RealPowerIntegerExponentAgreement : Set
    realPowerIntegerExponentAgreement :
      RealPowerIntegerExponentAgreement

    RealPowerRationalExponentAgreement : Set
    realPowerRationalExponentAgreement :
      RealPowerRationalExponentAgreement

    LambdaPowerShift : Set
    lambdaPowerShift : LambdaPowerShift

    AlphaThreeHalvesExponentMeaning : Set
    alphaThreeHalvesExponentMeaning :
      AlphaThreeHalvesExponentMeaning

    FourShiftFractionalFactor : Set
    fourShiftFractionalFactor : FourShiftFractionalFactor

    AnalyticGeometricRatioEqualsQuarter : Set
    analyticGeometricRatioEqualsQuarter :
      AnalyticGeometricRatioEqualsQuarter

    FractionalPowerTermsNonnegative : Set
    fractionalPowerTermsNonnegative :
      FractionalPowerTermsNonnegative

    FractionalPowerGeometricSeriesBound : Set
    fractionalPowerGeometricSeriesBound :
      FractionalPowerGeometricSeriesBound

    ShellEnergyAbsolutelyContinuous : Set
    shellEnergyAbsolutelyContinuous :
      ShellEnergyAbsolutelyContinuous

    IntegratedShellEnergyIdentity : Set
    integratedShellEnergyIdentity : IntegratedShellEnergyIdentity

    TerminalWindowMeanValueSelection : Set
    terminalWindowMeanValueSelection :
      TerminalWindowMeanValueSelection

    ExistsGoodInitialTimeInParabolicWindow : Set
    existsGoodInitialTimeInParabolicWindow :
      ExistsGoodInitialTimeInParabolicWindow

    GoodTimeEnergyBelowWindowAverage : Set
    goodTimeEnergyBelowWindowAverage :
      GoodTimeEnergyBelowWindowAverage

    IntegralDifferentialInequality : Set
    integralDifferentialInequality :
      IntegralDifferentialInequality

    GronwallExponentNonnegative : Set
    gronwallExponentNonnegative : GronwallExponentNonnegative

    GronwallBoundWithLocalizedGradient : Set
    gronwallBoundWithLocalizedGradient :
      GronwallBoundWithLocalizedGradient

    LocalizedGradientSmallnessAbsorbsExponent : Set
    localizedGradientSmallnessAbsorbsExponent :
      LocalizedGradientSmallnessAbsorbsExponent

    TerminalShellEnergyBound : Set
    terminalShellEnergyBound : TerminalShellEnergyBound

    TerminalShellDissipationBound : Set
    terminalShellDissipationBound : TerminalShellDissipationBound

open FractionalPowerGronwallCutset public

record FixedShiftPhysicalCutset : Set₁ where
  field
    TimeCutoffProductRule : Set
    timeCutoffProductRule : TimeCutoffProductRule

    TimeCutoffDerivativeSupport : Set
    timeCutoffDerivativeSupport : TimeCutoffDerivativeSupport

    TimeCutoffDerivativeBound : Set
    timeCutoffDerivativeBound : TimeCutoffDerivativeBound

    IntegrateProjectedEnergyIdentityAgainstCutoff : Set
    integrateProjectedEnergyIdentityAgainstCutoff :
      IntegrateProjectedEnergyIdentityAgainstCutoff

    InitialBoundaryTermVanishesOrIsControlled : Set
    initialBoundaryTermVanishesOrIsControlled :
      InitialBoundaryTermVanishesOrIsControlled

    TerminalBoundaryTermEqualsCurrentEnergy : Set
    terminalBoundaryTermEqualsCurrentEnergy :
      TerminalBoundaryTermEqualsCurrentEnergy

    TimeCutoffErrorBelowPreviousShellEnergy : Set
    timeCutoffErrorBelowPreviousShellEnergy :
      TimeCutoffErrorBelowPreviousShellEnergy

    IntegratedNonlinearFluxBelowIntegratedAbsoluteFlux : Set
    integratedNonlinearFluxBelowIntegratedAbsoluteFlux :
      IntegratedNonlinearFluxBelowIntegratedAbsoluteFlux

    IntegratedCutoffEnergyInequality : Set
    integratedCutoffEnergyInequality :
      IntegratedCutoffEnergyInequality

    CorrectionDecompositionByShellGap : Set
    correctionDecompositionByShellGap :
      CorrectionDecompositionByShellGap

    CorrectionTermwiseMajorant : Set
    correctionTermwiseMajorant : CorrectionTermwiseMajorant

    CorrectionSignedSumAbsoluteBound : Set
    correctionSignedSumAbsoluteBound :
      CorrectionSignedSumAbsoluteBound

    CorrectionMajorantFactorization : Set
    correctionMajorantFactorization :
      CorrectionMajorantFactorization

    CorrectionLowIndexGeometricEnvelope : Set
    correctionLowIndexGeometricEnvelope :
      CorrectionLowIndexGeometricEnvelope

    CorrectionGapGeometricEnvelope : Set
    correctionGapGeometricEnvelope :
      CorrectionGapGeometricEnvelope

    CorrectionBelowExplicitMajorant : Set
    correctionBelowExplicitMajorant :
      CorrectionBelowExplicitMajorant

    ExplicitMajorantBelowDyadicDecayTarget : Set
    explicitMajorantBelowDyadicDecayTarget :
      ExplicitMajorantBelowDyadicDecayTarget

    FluxCorrectionAbsorbedUniformly : Set
    fluxCorrectionAbsorbedUniformly :
      FluxCorrectionAbsorbedUniformly

    SequenceIsNonnegative : Set
    sequenceIsNonnegative : SequenceIsNonnegative

    FixedShiftPredecessorStrictlySmaller : Set
    fixedShiftPredecessorStrictlySmaller :
      FixedShiftPredecessorStrictlySmaller

    LargeShellClosedUnderPredecessor : Set
    largeShellClosedUnderPredecessor :
      LargeShellClosedUnderPredecessor

    BaseBlockFinite : Set
    baseBlockFinite : BaseBlockFinite

    BaseBlockUniformBound : Set
    baseBlockUniformBound : BaseBlockUniformBound

    RecursionCoefficientStrictlyBelowOne : Set
    recursionCoefficientStrictlyBelowOne :
      RecursionCoefficientStrictlyBelowOne

    CorrectionDecayCompatibleWithTarget : Set
    correctionDecayCompatibleWithTarget :
      CorrectionDecayCompatibleWithTarget

    BlockInductionHypothesisCloses : Set
    blockInductionHypothesisCloses : BlockInductionHypothesisCloses

    PhysicalBlockDecayCertificate : Set
    physicalBlockDecayCertificate : PhysicalBlockDecayCertificate

    ShellUniformDyadicDecay : Set
    shellUniformDyadicDecay : ShellUniformDyadicDecay

    EnergyDecayImpliesShellL2Decay : Set
    energyDecayImpliesShellL2Decay :
      EnergyDecayImpliesShellL2Decay

    DissipationDecayImpliesGradientShellDecay : Set
    dissipationDecayImpliesGradientShellDecay :
      DissipationDecayImpliesGradientShellDecay

    AlphaAboveOneSummability : Set
    alphaAboveOneSummability : AlphaAboveOneSummability

    ShellDecayImpliesRequiredRegularity : Set
    shellDecayImpliesRequiredRegularity :
      ShellDecayImpliesRequiredRegularity

open FixedShiftPhysicalCutset public

record OfficialShellAndMaximalTimeCutset : Set₁ where
  field
    OfficialShellField : Set
    officialShellField : OfficialShellField

    OfficialShellL2SquaredDefinition : Set
    officialShellL2SquaredDefinition :
      OfficialShellL2SquaredDefinition

    OfficialShellDissipationDefinition : Set
    officialShellDissipationDefinition :
      OfficialShellDissipationDefinition

    OfficialShellTimeDerivativeDefinition : Set
    officialShellTimeDerivativeDefinition :
      OfficialShellTimeDerivativeDefinition

    FiniteAssemblyShellFieldMatchesOfficialProjector : Set
    finiteAssemblyShellFieldMatchesOfficialProjector :
      FiniteAssemblyShellFieldMatchesOfficialProjector

    FiniteAssemblyShellL2MatchesOfficialL2 : Set
    finiteAssemblyShellL2MatchesOfficialL2 :
      FiniteAssemblyShellL2MatchesOfficialL2

    FiniteAssemblyDissipationMatchesOfficialGradientNorm : Set
    finiteAssemblyDissipationMatchesOfficialGradientNorm :
      FiniteAssemblyDissipationMatchesOfficialGradientNorm

    FiniteAssemblyTimeDerivativeMatchesOfficialDerivative : Set
    finiteAssemblyTimeDerivativeMatchesOfficialDerivative :
      FiniteAssemblyTimeDerivativeMatchesOfficialDerivative

    SmoothPeriodicInitialDatumHasLocalStrongSolution : Set
    smoothPeriodicInitialDatumHasLocalStrongSolution :
      SmoothPeriodicInitialDatumHasLocalStrongSolution

    StrongSolutionUniqueness : Set
    strongSolutionUniqueness : StrongSolutionUniqueness

    MaximalStrongSolutionExists : Set
    maximalStrongSolutionExists : MaximalStrongSolutionExists

    MaximalTimeEitherInfiniteOrFinite : Set
    maximalTimeEitherInfiniteOrFinite :
      MaximalTimeEitherInfiniteOrFinite

    RegularBeforeFiniteMaximalTime : Set
    regularBeforeFiniteMaximalTime :
      RegularBeforeFiniteMaximalTime

    MaximalStrongSolutionGivesOfficialLerayHopfCarrier : Set
    maximalStrongSolutionGivesOfficialLerayHopfCarrier :
      MaximalStrongSolutionGivesOfficialLerayHopfCarrier

    OfficialCarrierSolutionEqualsMaximalStrongSolution : Set
    officialCarrierSolutionEqualsMaximalStrongSolution :
      OfficialCarrierSolutionEqualsMaximalStrongSolution

    OfficialTerminalEqualsFiniteMaximalTime : Set
    officialTerminalEqualsFiniteMaximalTime :
      OfficialTerminalEqualsFiniteMaximalTime

    SourceSelectionAtArbitraryFiniteMaximalTime : Set
    sourceSelectionAtArbitraryFiniteMaximalTime :
      SourceSelectionAtArbitraryFiniteMaximalTime

    PreBudgetDataAtArbitraryFiniteMaximalTime : Set
    preBudgetDataAtArbitraryFiniteMaximalTime :
      PreBudgetDataAtArbitraryFiniteMaximalTime

    PhysicalLeavesAtArbitraryFiniteMaximalTime : Set
    physicalLeavesAtArbitraryFiniteMaximalTime :
      PhysicalLeavesAtArbitraryFiniteMaximalTime

    ContinuationContradictsMaximality : Set
    continuationContradictsMaximality :
      ContinuationContradictsMaximality

    MaximalTimeInfinite : Set
    maximalTimeInfinite : MaximalTimeInfinite

open OfficialShellAndMaximalTimeCutset public

record FiniteInfiniteRealPromotionCutset : Set₁ where
  field
    FourierPartialSumsConvergeInL2 : Set
    fourierPartialSumsConvergeInL2 :
      FourierPartialSumsConvergeInL2

    SmoothSolutionFourierCoefficientsRapidlyDecay : Set
    smoothSolutionFourierCoefficientsRapidlyDecay :
      SmoothSolutionFourierCoefficientsRapidlyDecay

    TensorConvolutionAbsolutelyConvergentAtRequiredRegularity : Set
    tensorConvolutionAbsolutelyConvergentAtRequiredRegularity :
      TensorConvolutionAbsolutelyConvergentAtRequiredRegularity

    FiniteShellProjectorsConvergeToInfiniteProjectors : Set
    finiteShellProjectorsConvergeToInfiniteProjectors :
      FiniteShellProjectorsConvergeToInfiniteProjectors

    FinitePairFoldsConvergeToPhysicalConvolution : Set
    finitePairFoldsConvergeToPhysicalConvolution :
      FinitePairFoldsConvergeToPhysicalConvolution

    FiniteFluxConvergesToPhysicalFlux : Set
    finiteFluxConvergesToPhysicalFlux :
      FiniteFluxConvergesToPhysicalFlux

    FiniteEnergyConvergesToPhysicalEnergy : Set
    finiteEnergyConvergesToPhysicalEnergy :
      FiniteEnergyConvergesToPhysicalEnergy

    FiniteDissipationConvergesToPhysicalDissipation : Set
    finiteDissipationConvergesToPhysicalDissipation :
      FiniteDissipationConvergesToPhysicalDissipation

    FiniteSchurBoundUniformInCutoff : Set
    finiteSchurBoundUniformInCutoff :
      FiniteSchurBoundUniformInCutoff

    PassSchurBoundToLimit : Set
    passSchurBoundToLimit : PassSchurBoundToLimit

    PassEquation42ToLimit : Set
    passEquation42ToLimit : PassEquation42ToLimit

    PassSection4BoundsToLimit : Set
    passSection4BoundsToLimit : PassSection4BoundsToLimit

    PassFixedShiftDecayToLimit : Set
    passFixedShiftDecayToLimit : PassFixedShiftDecayToLimit

    RationalEmbeddingPreservesAdditionMultiplicationOrder : Set
    rationalEmbeddingPreservesAdditionMultiplicationOrder :
      RationalEmbeddingPreservesAdditionMultiplicationOrder

    RationalFiniteSumEmbeddedEqualsRealFiniteSum : Set
    rationalFiniteSumEmbeddedEqualsRealFiniteSum :
      RationalFiniteSumEmbeddedEqualsRealFiniteSum

    RationalBoundTransfersToRealCarrier : Set
    rationalBoundTransfersToRealCarrier :
      RationalBoundTransfersToRealCarrier

    RealYoungEstimate : Set
    realYoungEstimate : RealYoungEstimate

    RealSchurEstimate : Set
    realSchurEstimate : RealSchurEstimate

    RealGronwall : Set
    realGronwall : RealGronwall

    RealGeometricSeries : Set
    realGeometricSeries : RealGeometricSeries

    RealFractionalPowers : Set
    realFractionalPowers : RealFractionalPowers

    RealLimitClosureOfInequalities : Set
    realLimitClosureOfInequalities :
      RealLimitClosureOfInequalities

open FiniteInfiniteRealPromotionCutset public

record GlobalPhysicalSolutionCutset : Set₁ where
  field
    ArbitrarySmoothDivergenceFreeDatumToOfficialInitialDatum : Set
    arbitrarySmoothDivergenceFreeDatumToOfficialInitialDatum :
      ArbitrarySmoothDivergenceFreeDatumToOfficialInitialDatum

    MeanZeroNormalizationOrConstantModeTreatment : Set
    meanZeroNormalizationOrConstantModeTreatment :
      MeanZeroNormalizationOrConstantModeTreatment

    ConstructionUniformOverInitialData : Set
    constructionUniformOverInitialData :
      ConstructionUniformOverInitialData

    FluxMeasurable : Set
    fluxMeasurable : FluxMeasurable

    LocalizedGradientIntegralWellDefined : Set
    localizedGradientIntegralWellDefined :
      LocalizedGradientIntegralWellDefined

    EnergyIdentityHoldsAlmostEverywhere : Set
    energyIdentityHoldsAlmostEverywhere :
      EnergyIdentityHoldsAlmostEverywhere

    IntegratedIdentityHoldsForAllIntervals : Set
    integratedIdentityHoldsForAllIntervals :
      IntegratedIdentityHoldsForAllIntervals

    StrongSolutionHasContinuousHsTrajectory : Set
    strongSolutionHasContinuousHsTrajectory :
      StrongSolutionHasContinuousHsTrajectory

    TerminalLimitExistsInRequiredSobolevSpace : Set
    terminalLimitExistsInRequiredSobolevSpace :
      TerminalLimitExistsInRequiredSobolevSpace

    ContinuationDatumAtTerminalIsAdmissible : Set
    continuationDatumAtTerminalIsAdmissible :
      ContinuationDatumAtTerminalIsAdmissible

    DecayExponentGivesHsBound : Set
    decayExponentGivesHsBound : DecayExponentGivesHsBound

    HsAboveFiveHalvesEmbedsIntoC1 : Set
    hsAboveFiveHalvesEmbedsIntoC1 :
      HsAboveFiveHalvesEmbedsIntoC1

    HsControlTriggersLocalContinuation : Set
    hsControlTriggersLocalContinuation :
      HsControlTriggersLocalContinuation

    ParabolicSmoothingAfterPositiveTime : Set
    parabolicSmoothingAfterPositiveTime :
      ParabolicSmoothingAfterPositiveTime

    HigherSobolevEnergyInduction : Set
    higherSobolevEnergyInduction : HigherSobolevEnergyInduction

    AllHigherSobolevNormsRemainFiniteOnFiniteIntervals : Set
    allHigherSobolevNormsRemainFiniteOnFiniteIntervals :
      AllHigherSobolevNormsRemainFiniteOnFiniteIntervals

    ProjectedSolutionHasPressure : Set
    projectedSolutionHasPressure : ProjectedSolutionHasPressure

    PressurePoissonEquation : Set
    pressurePoissonEquation : PressurePoissonEquation

    PressureMeanZeroNormalization : Set
    pressureMeanZeroNormalization : PressureMeanZeroNormalization

    PressureRegularityFromVelocity : Set
    pressureRegularityFromVelocity : PressureRegularityFromVelocity

    VelocityPressurePairSolvesOriginalNavierStokes : Set
    velocityPressurePairSolvesOriginalNavierStokes :
      VelocityPressurePairSolvesOriginalNavierStokes

    PressureUniqueModuloTimeDependentConstant : Set
    pressureUniqueModuloTimeDependentConstant :
      PressureUniqueModuloTimeDependentConstant

    DivergenceFreePreserved : Set
    divergenceFreePreserved : DivergenceFreePreserved

    MeanZeroPreserved : Set
    meanZeroPreserved : MeanZeroPreserved

    GlobalEnergyEquality : Set
    globalEnergyEquality : GlobalEnergyEquality

    FiniteEnergyAtEveryTime : Set
    finiteEnergyAtEveryTime : FiniteEnergyAtEveryTime

    ClassicalSolutionImpliesLerayHopf : Set
    classicalSolutionImpliesLerayHopf :
      ClassicalSolutionImpliesLerayHopf

    GlobalRegularSolutionIsUnique : Set
    globalRegularSolutionIsUnique : GlobalRegularSolutionIsUnique

open GlobalPhysicalSolutionCutset public

record SubmissionAuditCutset : Set₁ where
  field
    ExactTopLevelTheoremStatement : Set
    exactTopLevelTheoremStatement : ExactTopLevelTheoremStatement

    ApprovedFoundationsDependencyReceipt : Set
    approvedFoundationsDependencyReceipt :
      ApprovedFoundationsDependencyReceipt

    NoGlobalSmoothnessAssumedUpstream : Set
    noGlobalSmoothnessAssumedUpstream :
      NoGlobalSmoothnessAssumedUpstream

    NoFiniteBKMIntegralAssumedUpstream : Set
    noFiniteBKMIntegralAssumedUpstream :
      NoFiniteBKMIntegralAssumedUpstream

    NoContinuationAssumedUpstream : Set
    noContinuationAssumedUpstream : NoContinuationAssumedUpstream

    NoHighShellDecayAssumedUpstream : Set
    noHighShellDecayAssumedUpstream :
      NoHighShellDecayAssumedUpstream

    NoLocalizedCriterionAssumedUpstream : Set
    noLocalizedCriterionAssumedUpstream :
      NoLocalizedCriterionAssumedUpstream

    SourceTheoremNumbersAndHypothesesRecorded : Set
    sourceTheoremNumbersAndHypothesesRecorded :
      SourceTheoremNumbersAndHypothesesRecorded

    DomainAndFourierConventionsRecorded : Set
    domainAndFourierConventionsRecorded :
      DomainAndFourierConventionsRecorded

    ManuscriptFormalCrosswalkComplete : Set
    manuscriptFormalCrosswalkComplete :
      ManuscriptFormalCrosswalkComplete

    CleanPinnedBuildReceipt : Set
    cleanPinnedBuildReceipt : CleanPinnedBuildReceipt

    NoHolesPostulatesOrUnsafeFlags : Set
    noHolesPostulatesOrUnsafeFlags :
      NoHolesPostulatesOrUnsafeFlags

    FullDependencyGraphGenerated : Set
    fullDependencyGraphGenerated : FullDependencyGraphGenerated

    ArtifactHashesGenerated : Set
    artifactHashesGenerated : ArtifactHashesGenerated

    AssumptionInventoryGenerated : Set
    assumptionInventoryGenerated : AssumptionInventoryGenerated

    TheoremInventoryGenerated : Set
    theoremInventoryGenerated : TheoremInventoryGenerated

    SourceProvenanceInventoryGenerated : Set
    sourceProvenanceInventoryGenerated :
      SourceProvenanceInventoryGenerated

    FiniteInfiniteBoundaryReportGenerated : Set
    finiteInfiniteBoundaryReportGenerated :
      FiniteInfiniteBoundaryReportGenerated

    RationalRealBoundaryReportGenerated : Set
    rationalRealBoundaryReportGenerated :
      RationalRealBoundaryReportGenerated

open SubmissionAuditCutset public

record CompleteLuoSubmissionDependencyCutset : Set₁ where
  field
    equation42 : Equation42PhysicalCutset
    section4 : Section4PhysicalCutset
    fractionalPowerAndGronwall : FractionalPowerGronwallCutset
    fixedShift : FixedShiftPhysicalCutset
    officialShellAndMaximalTime : OfficialShellAndMaximalTimeCutset
    finiteInfiniteAndRealPromotion : FiniteInfiniteRealPromotionCutset
    globalPhysicalSolution : GlobalPhysicalSolutionCutset
    submissionAudit : SubmissionAuditCutset

open CompleteLuoSubmissionDependencyCutset public

completeLuoSubmissionDependencyCutset :
  Equation42PhysicalCutset →
  Section4PhysicalCutset →
  FractionalPowerGronwallCutset →
  FixedShiftPhysicalCutset →
  OfficialShellAndMaximalTimeCutset →
  FiniteInfiniteRealPromotionCutset →
  GlobalPhysicalSolutionCutset →
  SubmissionAuditCutset →
  CompleteLuoSubmissionDependencyCutset
completeLuoSubmissionDependencyCutset
  equation42 section4 fractional fixedShift official promotion global audit =
  record
    { equation42 = equation42
    ; section4 = section4
    ; fractionalPowerAndGronwall = fractional
    ; fixedShift = fixedShift
    ; officialShellAndMaximalTime = official
    ; finiteInfiniteAndRealPromotion = promotion
    ; globalPhysicalSolution = global
    ; submissionAudit = audit
    }

completeSubmissionDependencyCutsetConstructed : Bool
completeSubmissionDependencyCutsetConstructed = true

allSubmissionObligationsIndividuallyNamed : Bool
allSubmissionObligationsIndividuallyNamed = true

completeSubmissionDependencyCutsetConstructedIsTrue :
  completeSubmissionDependencyCutsetConstructed ≡ true
completeSubmissionDependencyCutsetConstructedIsTrue = refl

allSubmissionObligationsIndividuallyNamedIsTrue :
  allSubmissionObligationsIndividuallyNamed ≡ true
allSubmissionObligationsIndividuallyNamedIsTrue = refl
