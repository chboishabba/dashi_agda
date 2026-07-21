module DASHI.Physics.YangMills.BalabanOneStepAllScaleAnalyticInhabitation where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One coherent proof-relevant owner for the finite-background critical map,
-- one-step RG, Step V and all-scale analytic cutset.
------------------------------------------------------------------------

record OneStepAllScaleAnalyticInputs : Set₁ where
  field
    -- Critical map and finite-background endpoint.
    CriticalMapDefinition : Set
    criticalMapDefinition : CriticalMapDefinition
    CriticalMapDifference : Set
    criticalMapDifference : CriticalMapDifference
    GreenBound : Set
    greenBound : GreenBound
    NonlinearLipschitzBound : Set
    nonlinearLipschitzBound : NonlinearLipschitzBound
    CriticalMapNormIdentity : Set
    criticalMapNormIdentity : CriticalMapNormIdentity
    OrderMonotonicity : Set
    orderMonotonicity : OrderMonotonicity
    MultiplicationAssociativity : Set
    multiplicationAssociativity : MultiplicationAssociativity
    CriticalMapContraction : Set
    criticalMapContraction : CriticalMapContraction
    GreenTimesNonlinearBelowRho : Set
    greenTimesNonlinearBelowRho : GreenTimesNonlinearBelowRho
    RhoGStrict : Set
    rhoGStrict : RhoGStrict
    CommonRadiusPositive : Set
    commonRadiusPositive : CommonRadiusPositive
    SelectedRadiusInsideExpLogChart : Set
    selectedRadiusInsideExpLogChart : SelectedRadiusInsideExpLogChart
    SelectedRadiusSatisfiesHessianGap : Set
    selectedRadiusSatisfiesHessianGap : SelectedRadiusSatisfiesHessianGap
    SelectedRadiusSatisfiesResidualStrictness : Set
    selectedRadiusSatisfiesResidualStrictness :
      SelectedRadiusSatisfiesResidualStrictness
    SelectedRadiusSatisfiesNonlinearContraction : Set
    selectedRadiusSatisfiesNonlinearContraction :
      SelectedRadiusSatisfiesNonlinearContraction
    CriticalMapZeroDisplacementRelative : Set
    criticalMapZeroDisplacementRelative : CriticalMapZeroDisplacementRelative
    SigmaBelowOne : Set
    sigmaBelowOne : SigmaBelowOne
    CriticalBallComplete : Set
    criticalBallComplete : CriticalBallComplete
    CriticalMapPreservesBall : Set
    criticalMapPreservesBall : CriticalMapPreservesBall
    UniformCriticalFixedPointExists : Set
    uniformCriticalFixedPointExists : UniformCriticalFixedPointExists
    FixedPointImpliesEulerLagrange : Set
    fixedPointImpliesEulerLagrange : FixedPointImpliesEulerLagrange
    EulerLagrangeImpliesFixedPoint : Set
    eulerLagrangeImpliesFixedPoint : EulerLagrangeImpliesFixedPoint
    CoerciveCriticalPointIsStrictConstrainedMinimizer : Set
    coerciveCriticalPointIsStrictConstrainedMinimizer :
      CoerciveCriticalPointIsStrictConstrainedMinimizer
    CriticalPointsWithSameConstraintAreGaugeEquivalent : Set
    criticalPointsWithSameConstraintAreGaugeEquivalent :
      CriticalPointsWithSameConstraintAreGaugeEquivalent
    BackgroundFieldAnalyticInCoarseField : Set
    backgroundFieldAnalyticInCoarseField :
      BackgroundFieldAnalyticInCoarseField
    BackgroundFieldUniformlyLocal : Set
    backgroundFieldUniformlyLocal : BackgroundFieldUniformlyLocal
    BackgroundDerivativeExponentialDecay : Set
    backgroundDerivativeExponentialDecay :
      BackgroundDerivativeExponentialDecay

    -- Fluctuation coordinates and Jacobian.
    FluctuationCoordinatesExist : Set
    fluctuationCoordinatesExist : FluctuationCoordinatesExist
    FluctuationCoordinatesUnique : Set
    fluctuationCoordinatesUnique : FluctuationCoordinatesUnique
    FluctuationCoordinatesBijective : Set
    fluctuationCoordinatesBijective : FluctuationCoordinatesBijective
    FluctuationCoordinatesRespectGaugeOrbits : Set
    fluctuationCoordinatesRespectGaugeOrbits :
      FluctuationCoordinatesRespectGaugeOrbits
    FluctuationCoordinatesPreserveDomain : Set
    fluctuationCoordinatesPreserveDomain : FluctuationCoordinatesPreserveDomain
    FluctuationCoordinateJacobianFormula : Set
    fluctuationCoordinateJacobianFormula :
      FluctuationCoordinateJacobianFormula
    JacobianLocalDensityExpansion : Set
    jacobianLocalDensityExpansion : JacobianLocalDensityExpansion
    JacobianPolymerDecay : Set
    jacobianPolymerDecay : JacobianPolymerDecay
    JacobianContributionBound : Set
    jacobianContributionBound : JacobianContributionBound

    -- Determinant, background and BCH contributions.
    LogDetLocalExpansion : Set
    logDetLocalExpansion : LogDetLocalExpansion
    LogDetPolymerDecay : Set
    logDetPolymerDecay : LogDetPolymerDecay
    LogDetRemainderBound : Set
    logDetRemainderBound : LogDetRemainderBound
    BackgroundSubstitutionExact : Set
    backgroundSubstitutionExact : BackgroundSubstitutionExact
    BackgroundSubstitutionContributionBound : Set
    backgroundSubstitutionContributionBound :
      BackgroundSubstitutionContributionBound
    FluctuationBCHExpansionExact : Set
    fluctuationBCHExpansionExact : FluctuationBCHExpansionExact
    BCHContributionBound : Set
    bchContributionBound : BCHContributionBound

    -- Polymer localization and Ward identities.
    PolymerLocalizationStable : Set
    polymerLocalizationStable : PolymerLocalizationStable
    LocalizedRelevantPartBound : Set
    localizedRelevantPartBound : LocalizedRelevantPartBound
    IrrelevantTaylorRemainderContractive : Set
    irrelevantTaylorRemainderContractive :
      IrrelevantTaylorRemainderContractive
    LocalizationPreservesSupport : Set
    localizationPreservesSupport : LocalizationPreservesSupport
    LocalizationPreservesExponentialWeight : Set
    localizationPreservesExponentialWeight :
      LocalizationPreservesExponentialWeight
    FluctuationIntegralGaugeInvariant : Set
    fluctuationIntegralGaugeInvariant : FluctuationIntegralGaugeInvariant
    EffectiveActionWardIdentity : Set
    effectiveActionWardIdentity : EffectiveActionWardIdentity
    LocalizationPreservesWardIdentity : Set
    localizationPreservesWardIdentity : LocalizationPreservesWardIdentity

    -- Vacuum and coupling renormalization.
    VacuumEnergyRenormalization : Set
    vacuumEnergyRenormalization : VacuumEnergyRenormalization
    VacuumCountertermCancellation : Set
    vacuumCountertermCancellation : VacuumCountertermCancellation
    VacuumRemainderSummable : Set
    vacuumRemainderSummable : VacuumRemainderSummable
    CouplingRenormalization : Set
    couplingRenormalization : CouplingRenormalization
    BetaZeroHasYangMillsValue : Set
    betaZeroHasYangMillsValue : BetaZeroHasYangMillsValue
    CouplingRemainderBound : Set
    couplingRemainderBound : CouplingRemainderBound

    -- One-step component budgets and contraction.
    JacobianBudgetBound : Set
    jacobianBudgetBound : JacobianBudgetBound
    DeterminantBudgetBound : Set
    determinantBudgetBound : DeterminantBudgetBound
    BackgroundBudgetBound : Set
    backgroundBudgetBound : BackgroundBudgetBound
    BCHBudgetBound : Set
    bchBudgetBound : BCHBudgetBound
    LocalizationBudgetBound : Set
    localizationBudgetBound : LocalizationBudgetBound
    WardBudgetBound : Set
    wardBudgetBound : WardBudgetBound
    OneStepRawPolymerEstimate : Set
    oneStepRawPolymerEstimate : OneStepRawPolymerEstimate
    ComponentBudgetBelowPerturbativeError : Set
    componentBudgetBelowPerturbativeError :
      ComponentBudgetBelowPerturbativeError
    PolymerContractionStrict : Set
    polymerContractionStrict : PolymerContractionStrict
    OneStepPolymerContraction : Set
    oneStepPolymerContraction : OneStepPolymerContraction

    -- Step V / large-field and KP chain.
    LargeFieldActionLowerBound : Set
    largeFieldActionLowerBound : LargeFieldActionLowerBound
    LargeFieldPenaltyPositive : Set
    largeFieldPenaltyPositive : LargeFieldPenaltyPositive
    LargeFieldPenaltyAdditiveOnSeparatedBlocks : Set
    largeFieldPenaltyAdditiveOnSeparatedBlocks :
      LargeFieldPenaltyAdditiveOnSeparatedBlocks
    LargeFieldPolymerSuppressed : Set
    largeFieldPolymerSuppressed : LargeFieldPolymerSuppressed
    PolymerCardinalityEntropyBound : Set
    polymerCardinalityEntropyBound : PolymerCardinalityEntropyBound
    PolymerDiameterEntropyBound : Set
    polymerDiameterEntropyBound : PolymerDiameterEntropyBound
    SizeSuppressionBeatsEntropy : Set
    sizeSuppressionBeatsEntropy : SizeSuppressionBeatsEntropy
    DiameterSuppressionBeatsEntropy : Set
    diameterSuppressionBeatsEntropy : DiameterSuppressionBeatsEntropy
    AnisotropicNormDominatesPolymerDiameter : Set
    anisotropicNormDominatesPolymerDiameter :
      AnisotropicNormDominatesPolymerDiameter
    AnisotropicNormStableUnderBlocking : Set
    anisotropicNormStableUnderBlocking : AnisotropicNormStableUnderBlocking
    PolymerCrossingTransferCutControlled : Set
    polymerCrossingTransferCutControlled :
      PolymerCrossingTransferCutControlled
    TransferCutActivitySuppressed : Set
    transferCutActivitySuppressed : TransferCutActivitySuppressed
    WeightedSumBelowEntropy : Set
    weightedSumBelowEntropy : WeightedSumBelowEntropy
    EntropyBelowSizeMajorant : Set
    entropyBelowSizeMajorant : EntropyBelowSizeMajorant
    SizeBelowDiameterMajorant : Set
    sizeBelowDiameterMajorant : SizeBelowDiameterMajorant
    DiameterMajorantBelowKP : Set
    diameterMajorantBelowKP : DiameterMajorantBelowKP
    ConcreteKoteckyPreiss : Set
    concreteKoteckyPreiss : ConcreteKoteckyPreiss
    KPImpliesClusterExpansionConverges : Set
    kpImpliesClusterExpansionConverges :
      KPImpliesClusterExpansionConverges
    ClusterWeightsExponentiallyDecay : Set
    clusterWeightsExponentiallyDecay : ClusterWeightsExponentiallyDecay
    ConnectedCorrelationsClusterBound : Set
    connectedCorrelationsClusterBound : ConnectedCorrelationsClusterBound

    -- All-scale coupling, radius, polymer, analyticity, gauge and locality.
    CouplingInitial : Set
    couplingInitial : CouplingInitial
    CouplingStep : Set
    couplingStep : CouplingStep
    CouplingRemainsPositive : Set
    couplingRemainsPositive : CouplingRemainsPositive
    CouplingRemainsSmall : Set
    couplingRemainsSmall : CouplingRemainsSmall
    AsymptoticFreedomIteration : Set
    asymptoticFreedomIteration : AsymptoticFreedomIteration
    CouplingTendsToZero : Set
    couplingTendsToZero : CouplingTendsToZero
    FieldRadiusInitial : Set
    fieldRadiusInitial : FieldRadiusInitial
    FieldRadiusStep : Set
    fieldRadiusStep : FieldRadiusStep
    ChartRadiusRemainsPositive : Set
    chartRadiusRemainsPositive : ChartRadiusRemainsPositive
    SmallFieldRadiusPreserved : Set
    smallFieldRadiusPreserved : SmallFieldRadiusPreserved
    PolymerInitial : Set
    polymerInitial : PolymerInitial
    PolymerStep : Set
    polymerStep : PolymerStep
    PolymerNormContractsAtEveryScale : Set
    polymerNormContractsAtEveryScale : PolymerNormContractsAtEveryScale
    PolymerErrorsSummable : Set
    polymerErrorsSummable : PolymerErrorsSummable
    AnalyticityInitial : Set
    analyticityInitial : AnalyticityInitial
    AnalyticityStep : Set
    analyticityStep : AnalyticityStep
    AnalyticityRadiusLossSummable : Set
    analyticityRadiusLossSummable : AnalyticityRadiusLossSummable
    AnalyticityRadiusRemainsPositive : Set
    analyticityRadiusRemainsPositive : AnalyticityRadiusRemainsPositive
    GaugeFixingInitial : Set
    gaugeFixingInitial : GaugeFixingInitial
    GaugeFixingStep : Set
    gaugeFixingStep : GaugeFixingStep
    WardIdentityPreservedAtEveryScale : Set
    wardIdentityPreservedAtEveryScale : WardIdentityPreservedAtEveryScale
    LocalityInitial : Set
    localityInitial : LocalityInitial
    LocalityStep : Set
    localityStep : LocalityStep
    DecayRateLossSummable : Set
    decayRateLossSummable : DecayRateLossSummable
    PositiveDecayRateAtEveryScale : Set
    positiveDecayRateAtEveryScale : PositiveDecayRateAtEveryScale
    RGErrorsSummable : Set
    rgErrorsSummable : RGErrorsSummable
    InitialScaleAdmissible : Set
    initialScaleAdmissible : InitialScaleAdmissible
    OneStepAdmissible : Set
    oneStepAdmissible : OneStepAdmissible
    AllScaleRGAdmissible : Set
    allScaleRGAdmissible : AllScaleRGAdmissible

    -- Uniform effective action and relevant-direction classification.
    EffectiveActionUniformAtEveryScale : Set
    effectiveActionUniformAtEveryScale : EffectiveActionUniformAtEveryScale
    RelevantCouplingsUniformlyControlled : Set
    relevantCouplingsUniformlyControlled : RelevantCouplingsUniformlyControlled
    IrrelevantPolymerNormSummable : Set
    irrelevantPolymerNormSummable : IrrelevantPolymerNormSummable
    VacuumEnergyRenormalizationConverges : Set
    vacuumEnergyRenormalizationConverges :
      VacuumEnergyRenormalizationConverges
    LocalGaugeInvariantOperatorClassification : Set
    localGaugeInvariantOperatorClassification :
      LocalGaugeInvariantOperatorClassification
    OnlyVacuumAndGaugeCouplingRelevant : Set
    onlyVacuumAndGaugeCouplingRelevant : OnlyVacuumAndGaugeCouplingRelevant
    WardIdentitiesExcludeGaugeMassTerm : Set
    wardIdentitiesExcludeGaugeMassTerm : WardIdentitiesExcludeGaugeMassTerm
    AllOtherOperatorsIrrelevant : Set
    allOtherOperatorsIrrelevant : AllOtherOperatorsIrrelevant

open OneStepAllScaleAnalyticInputs public

oneStepAllScaleAssemblyLevel : ProofLevel
oneStepAllScaleAssemblyLevel = machineChecked

oneStepAllScaleAnalyticInputLevel : ProofLevel
oneStepAllScaleAnalyticInputLevel = conditional
