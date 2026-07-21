module DASHI.Physics.YangMills.BalabanOneStepAllScaleAnalyticInhabitation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B
open _×_ public

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,Σ_
  field
    witness : A
    proof : B witness
open Σ public

data ⊥ : Set where

record Unique {A : Set} (P : A → Set) : Set where
  field
    centre : A
    centreHasProperty : P centre
    unique : ∀ x → P x → x ≡ centre
open Unique public

------------------------------------------------------------------------
-- Critical map: one radius, one Green constant and one nonlinear constant.
------------------------------------------------------------------------

record CriticalMapAnalyticInputs
    (Index State Force Bound Radius : Set) : Set₁ where
  field
    zeroState : State
    negative : State → State
    subtractState : State → State → State
    addForce subtractForce : Force → Force → Force
    norm : State → Bound
    fullGreen : Index → Force → State
    nonlinear : Index → State → Force
    source : Index → Force
    Φ : Index → State → State

    multiply addBound : Bound → Bound → Bound
    LessEqual StrictLess : Bound → Bound → Set
    oneBound : Bound
    selectedRadius chartRadius CG LN rho sigma : Bound
    InCriticalBall : Index → State → Set

    criticalMapDefinitionInput : ∀ index h →
      Φ index h ≡
      negative (fullGreen index (addForce (nonlinear index h) (source index)))
    criticalMapDifferenceInput : ∀ index h h′ →
      subtractState (Φ index h) (Φ index h′) ≡
      negative (fullGreen index
        (subtractForce (nonlinear index h) (nonlinear index h′)))

    GreenBound : Set
    greenBoundInput : GreenBound
    NonlinearLipschitzBound : Set
    nonlinearLipschitzBoundInput : NonlinearLipschitzBound
    CriticalMapNormIdentity : Set
    criticalMapNormIdentityInput : CriticalMapNormIdentity
    OrderMonotonicity : Set
    orderMonotonicityInput : OrderMonotonicity
    MultiplicationAssociativity : Set
    multiplicationAssociativityInput : MultiplicationAssociativity

    criticalMapContractionInput : ∀ index h h′ →
      InCriticalBall index h → InCriticalBall index h′ →
      LessEqual (norm (subtractState (Φ index h) (Φ index h′)))
        (multiply (multiply CG LN) (norm (subtractState h h′)))

    greenTimesNonlinearBelowRhoInput : LessEqual (multiply CG LN) rho
    rhoGStrictInput : StrictLess rho oneBound
    commonRadiusPositiveInput : Set
    selectedRadiusInsideExpLogChartInput : LessEqual selectedRadius chartRadius

    SelectedRadiusSatisfiesHessianGap SelectedRadiusSatisfiesResidualStrictness
      SelectedRadiusSatisfiesNonlinearContraction : Set
    selectedRadiusSatisfiesHessianGapInput : SelectedRadiusSatisfiesHessianGap
    selectedRadiusSatisfiesResidualStrictnessInput :
      SelectedRadiusSatisfiesResidualStrictness
    selectedRadiusSatisfiesNonlinearContractionInput :
      SelectedRadiusSatisfiesNonlinearContraction

    criticalMapZeroDisplacementRelativeInput : ∀ index →
      LessEqual
        (addBound (norm (Φ index zeroState)) (multiply rho selectedRadius))
        (multiply sigma selectedRadius)
    sigmaBelowOneInput : LessEqual sigma oneBound

    CriticalBallComplete : Set
    criticalBallCompleteInput : CriticalBallComplete
    criticalMapPreservesBallInput : ∀ index h →
      InCriticalBall index h → InCriticalBall index (Φ index h)
    uniformCriticalFixedPointExistsInput : ∀ index →
      Unique (λ h → InCriticalBall index h × Φ index h ≡ h)

    EulerLagrange StrictConstrainedMinimizer : Index → State → Set
    SameConstraint GaugeEquivalent : State → State → Set
    fixedPointImpliesEulerLagrangeInput : ∀ index h →
      Φ index h ≡ h → EulerLagrange index h
    eulerLagrangeImpliesFixedPointInput : ∀ index h →
      EulerLagrange index h → Φ index h ≡ h
    coerciveCriticalPointIsStrictConstrainedMinimizerInput : ∀ index h →
      EulerLagrange index h → StrictConstrainedMinimizer index h
    criticalPointsWithSameConstraintAreGaugeEquivalentInput : ∀ index h h′ →
      EulerLagrange index h → EulerLagrange index h′ →
      SameConstraint h h′ → GaugeEquivalent h h′

    BackgroundFieldAnalyticInCoarseField BackgroundFieldUniformlyLocal
      BackgroundDerivativeExponentialDecay : Set
    backgroundFieldAnalyticInCoarseFieldInput : BackgroundFieldAnalyticInCoarseField
    backgroundFieldUniformlyLocalInput : BackgroundFieldUniformlyLocal
    backgroundDerivativeExponentialDecayInput : BackgroundDerivativeExponentialDecay

open CriticalMapAnalyticInputs public

criticalMapDefinition = criticalMapDefinitionInput
criticalMapDifference = criticalMapDifferenceInput
criticalMapContraction = criticalMapContractionInput
greenTimesNonlinearBelowRho = greenTimesNonlinearBelowRhoInput
rhoGStrict = rhoGStrictInput
commonRadiusPositive = commonRadiusPositiveInput
selectedRadiusInsideExpLogChart = selectedRadiusInsideExpLogChartInput
selectedRadiusSatisfiesHessianGap = selectedRadiusSatisfiesHessianGapInput
selectedRadiusSatisfiesResidualStrictness = selectedRadiusSatisfiesResidualStrictnessInput
selectedRadiusSatisfiesNonlinearContraction =
  selectedRadiusSatisfiesNonlinearContractionInput
criticalMapZeroDisplacementRelative = criticalMapZeroDisplacementRelativeInput
sigmaBelowOne = sigmaBelowOneInput
criticalBallComplete = criticalBallCompleteInput
criticalMapPreservesBall = criticalMapPreservesBallInput
uniformCriticalFixedPointExists = uniformCriticalFixedPointExistsInput
fixedPointImpliesEulerLagrange = fixedPointImpliesEulerLagrangeInput
eulerLagrangeImpliesFixedPoint = eulerLagrangeImpliesFixedPointInput
coerciveCriticalPointIsStrictConstrainedMinimizer =
  coerciveCriticalPointIsStrictConstrainedMinimizerInput
criticalPointsWithSameConstraintAreGaugeEquivalent =
  criticalPointsWithSameConstraintAreGaugeEquivalentInput
backgroundFieldAnalyticInCoarseField = backgroundFieldAnalyticInCoarseFieldInput
backgroundFieldUniformlyLocal = backgroundFieldUniformlyLocalInput
backgroundDerivativeExponentialDecay = backgroundDerivativeExponentialDecayInput

------------------------------------------------------------------------
-- One-step constructive RG producers and exact budget assembly.
------------------------------------------------------------------------

record OneStepRGAnalyticInhabitation
    (Configuration Background Fluctuation Polymer Region Coupling Bound : Set)
    : Set₁ where
  field
    SmallFieldConfiguration : Configuration → Set
    multiplyConfiguration : Background → Configuration → Configuration
    exp : Fluctuation → Configuration

    fluctuationCoordinatesExistInput : ∀ {U} →
      SmallFieldConfiguration U →
      Σ Background (λ Ubg →
        Σ Fluctuation (λ Z → U ≡ multiplyConfiguration Ubg (exp Z)))
    SameCoordinates : Background → Fluctuation → Background → Fluctuation → Set
    fluctuationCoordinatesUniqueInput : ∀ {U Ubg Z Ubg′ Z′} →
      SmallFieldConfiguration U →
      U ≡ multiplyConfiguration Ubg (exp Z) →
      U ≡ multiplyConfiguration Ubg′ (exp Z′) →
      SameCoordinates Ubg Z Ubg′ Z′

    FluctuationCoordinatesBijective FluctuationCoordinatesRespectGaugeOrbits
      FluctuationCoordinatesPreserveDomain : Set
    fluctuationCoordinatesBijectiveInput : FluctuationCoordinatesBijective
    fluctuationCoordinatesRespectGaugeOrbitsInput :
      FluctuationCoordinatesRespectGaugeOrbits
    fluctuationCoordinatesPreserveDomainInput : FluctuationCoordinatesPreserveDomain

    FluctuationCoordinateJacobianFormula JacobianLocalDensityExpansion
      JacobianPolymerDecay : Set
    fluctuationCoordinateJacobianFormulaInput : FluctuationCoordinateJacobianFormula
    jacobianLocalDensityExpansionInput : JacobianLocalDensityExpansion
    jacobianPolymerDecayInput : JacobianPolymerDecay

    LessEqual StrictLess : Bound → Bound → Set
    addBound multiplyBound : Bound → Bound → Bound
    oneBound : Bound

    jacobianContribution jacobianBudget : Region → Bound
    jacobianContributionBoundInput : ∀ region →
      LessEqual (jacobianContribution region) (jacobianBudget region)

    LogDetLocalExpansion LogDetPolymerDecay LogDetRemainderBound : Set
    logDetLocalExpansionInput : LogDetLocalExpansion
    logDetPolymerDecayInput : LogDetPolymerDecay
    logDetRemainderBoundInput : LogDetRemainderBound

    BackgroundSubstitutionExact BackgroundSubstitutionContributionBound
      FluctuationBCHExpansionExact BCHContributionBound : Set
    backgroundSubstitutionExactInput : BackgroundSubstitutionExact
    backgroundSubstitutionContributionBoundInput :
      BackgroundSubstitutionContributionBound
    fluctuationBCHExpansionExactInput : FluctuationBCHExpansionExact
    bchContributionBoundInput : BCHContributionBound

    PolymerLocalizationStable LocalizedRelevantPartBound
      IrrelevantTaylorRemainderContractive LocalizationPreservesSupport
      LocalizationPreservesExponentialWeight : Set
    polymerLocalizationStableInput : PolymerLocalizationStable
    localizedRelevantPartBoundInput : LocalizedRelevantPartBound
    irrelevantTaylorRemainderContractiveInput : IrrelevantTaylorRemainderContractive
    localizationPreservesSupportInput : LocalizationPreservesSupport
    localizationPreservesExponentialWeightInput :
      LocalizationPreservesExponentialWeight

    FluctuationIntegralGaugeInvariant EffectiveActionWardIdentity
      LocalizationPreservesWardIdentity : Set
    fluctuationIntegralGaugeInvariantInput : FluctuationIntegralGaugeInvariant
    effectiveActionWardIdentityInput : EffectiveActionWardIdentity
    localizationPreservesWardIdentityInput : LocalizationPreservesWardIdentity

    VacuumEnergyRenormalization VacuumCountertermCancellation
      VacuumRemainderSummable : Set
    vacuumEnergyRenormalizationInput : VacuumEnergyRenormalization
    vacuumCountertermCancellationInput : VacuumCountertermCancellation
    vacuumRemainderSummableInput : VacuumRemainderSummable

    g gNext beta0 couplingRemainder Cβ : Coupling
    addCoupling multiplyCoupling negateCoupling : Coupling → Coupling → Coupling
    cube fifth : Coupling → Coupling
    absCoupling : Coupling → Bound
    couplingRenormalizationInput :
      gNext ≡ addCoupling g
        (addCoupling
          (negateCoupling beta0 (cube g)) couplingRemainder)
    BetaZeroHasYangMillsValue : Set
    betaZeroHasYangMillsValueInput : BetaZeroHasYangMillsValue
    couplingRemainderBoundInput :
      LessEqual (absCoupling couplingRemainder)
        (absCoupling (multiplyCoupling Cβ (fifth g)))

    JacobianBudgetBound DeterminantBudgetBound BackgroundBudgetBound
      BCHBudgetBound LocalizationBudgetBound WardBudgetBound : Set
    jacobianBudgetBoundInput : JacobianBudgetBound
    determinantBudgetBoundInput : DeterminantBudgetBound
    backgroundBudgetBoundInput : BackgroundBudgetBound
    bchBudgetBoundInput : BCHBudgetBound
    localizationBudgetBoundInput : LocalizationBudgetBound
    wardBudgetBoundInput : WardBudgetBound

    E E-next : Polymer
    polymerNorm : Polymer → Bound
    lambdaPolymer componentBudget perturbativeError : Bound
    oneStepRawPolymerEstimateInput :
      LessEqual (polymerNorm E-next)
        (addBound (multiplyBound lambdaPolymer (polymerNorm E)) componentBudget)
    componentBudgetBelowPerturbativeErrorInput :
      LessEqual componentBudget perturbativeError
    lessEqualTransitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c
    addBoundMonotoneRight : ∀ prefix {a b} → LessEqual a b →
      LessEqual (addBound prefix a) (addBound prefix b)
    polymerContractionStrictInput : StrictLess lambdaPolymer oneBound

open OneStepRGAnalyticInhabitation public

fluctuationCoordinatesExist = fluctuationCoordinatesExistInput
fluctuationCoordinatesUnique = fluctuationCoordinatesUniqueInput
fluctuationCoordinatesBijective = fluctuationCoordinatesBijectiveInput
fluctuationCoordinatesRespectGaugeOrbits =
  fluctuationCoordinatesRespectGaugeOrbitsInput
fluctuationCoordinatesPreserveDomain = fluctuationCoordinatesPreserveDomainInput
fluctuationCoordinateJacobianFormula = fluctuationCoordinateJacobianFormulaInput
jacobianLocalDensityExpansion = jacobianLocalDensityExpansionInput
jacobianPolymerDecay = jacobianPolymerDecayInput
jacobianContributionBound = jacobianContributionBoundInput
logDetLocalExpansion = logDetLocalExpansionInput
logDetPolymerDecay = logDetPolymerDecayInput
logDetRemainderBound = logDetRemainderBoundInput
backgroundSubstitutionExact = backgroundSubstitutionExactInput
backgroundSubstitutionContributionBound = backgroundSubstitutionContributionBoundInput
fluctuationBCHExpansionExact = fluctuationBCHExpansionExactInput
bchContributionBound = bchContributionBoundInput
polymerLocalizationStable = polymerLocalizationStableInput
localizedRelevantPartBound = localizedRelevantPartBoundInput
irrelevantTaylorRemainderContractive = irrelevantTaylorRemainderContractiveInput
localizationPreservesSupport = localizationPreservesSupportInput
localizationPreservesExponentialWeight = localizationPreservesExponentialWeightInput
fluctuationIntegralGaugeInvariant = fluctuationIntegralGaugeInvariantInput
effectiveActionWardIdentity = effectiveActionWardIdentityInput
localizationPreservesWardIdentity = localizationPreservesWardIdentityInput
vacuumEnergyRenormalization = vacuumEnergyRenormalizationInput
vacuumCountertermCancellation = vacuumCountertermCancellationInput
vacuumRemainderSummable = vacuumRemainderSummableInput
couplingRenormalization = couplingRenormalizationInput
betaZeroHasYangMillsValue = betaZeroHasYangMillsValueInput
couplingRemainderBound = couplingRemainderBoundInput
jacobianBudgetBound = jacobianBudgetBoundInput
determinantBudgetBound = determinantBudgetBoundInput
backgroundBudgetBound = backgroundBudgetBoundInput
bchBudgetBound = bchBudgetBoundInput
localizationBudgetBound = localizationBudgetBoundInput
wardBudgetBound = wardBudgetBoundInput
oneStepRawPolymerEstimate = oneStepRawPolymerEstimateInput
componentBudgetBelowPerturbativeError = componentBudgetBelowPerturbativeErrorInput
polymerContractionStrict = polymerContractionStrictInput

oneStepPolymerContraction :
  ∀ {Configuration Background Fluctuation Polymer Region Coupling Bound} →
  (d : OneStepRGAnalyticInhabitation
    Configuration Background Fluctuation Polymer Region Coupling Bound) →
  LessEqual d (polymerNorm d (E-next d))
    (addBound d
      (multiplyBound d (lambdaPolymer d) (polymerNorm d (E d)))
      (perturbativeError d))
oneStepPolymerContraction d =
  lessEqualTransitive d
    (oneStepRawPolymerEstimateInput d)
    (addBoundMonotoneRight d
      (multiplyBound d (lambdaPolymer d) (polymerNorm d (E d)))
      (componentBudgetBelowPerturbativeErrorInput d))

------------------------------------------------------------------------
-- Step V: large fields, entropy, KP and clustering.
------------------------------------------------------------------------

record StepVAnalyticInhabitation
    (Site Polymer Bound : Set) : Set₁ where
  field
    activity weight size diameter anisotropicNorm actionPenalty : Polymer → Bound
    weightedSumAt entropyMajorantAt sizeMajorantAt diameterMajorantAt : Site → Bound
    kpThreshold : Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c

    LargeFieldActionLowerBound LargeFieldPenaltyPositive
      LargeFieldPenaltyAdditiveOnSeparatedBlocks LargeFieldPolymerSuppressed
      PolymerCardinalityEntropyBound PolymerDiameterEntropyBound
      SizeSuppressionBeatsEntropy DiameterSuppressionBeatsEntropy
      AnisotropicNormDominatesPolymerDiameter AnisotropicNormStableUnderBlocking
      PolymerCrossingTransferCutControlled TransferCutActivitySuppressed : Set
    largeFieldActionLowerBoundInput : LargeFieldActionLowerBound
    largeFieldPenaltyPositiveInput : LargeFieldPenaltyPositive
    largeFieldPenaltyAdditiveOnSeparatedBlocksInput :
      LargeFieldPenaltyAdditiveOnSeparatedBlocks
    largeFieldPolymerSuppressedInput : LargeFieldPolymerSuppressed
    polymerCardinalityEntropyBoundInput : PolymerCardinalityEntropyBound
    polymerDiameterEntropyBoundInput : PolymerDiameterEntropyBound
    sizeSuppressionBeatsEntropyInput : SizeSuppressionBeatsEntropy
    diameterSuppressionBeatsEntropyInput : DiameterSuppressionBeatsEntropy
    anisotropicNormDominatesPolymerDiameterInput :
      AnisotropicNormDominatesPolymerDiameter
    anisotropicNormStableUnderBlockingInput : AnisotropicNormStableUnderBlocking
    polymerCrossingTransferCutControlledInput :
      PolymerCrossingTransferCutControlled
    transferCutActivitySuppressedInput : TransferCutActivitySuppressed

    weightedSumBelowEntropyInput : ∀ site →
      LessEqual (weightedSumAt site) (entropyMajorantAt site)
    entropyBelowSizeMajorantInput : ∀ site →
      LessEqual (entropyMajorantAt site) (sizeMajorantAt site)
    sizeBelowDiameterMajorantInput : ∀ site →
      LessEqual (sizeMajorantAt site) (diameterMajorantAt site)
    diameterMajorantBelowKPInput : ∀ site →
      LessEqual (diameterMajorantAt site) kpThreshold

    ClusterExpansionConvergence ClusterWeightExponentialDecay
      ConnectedCorrelationClusterBound : Set
    kpImpliesClusterExpansionConvergesInput :
      (∀ site → LessEqual (weightedSumAt site) kpThreshold) →
      ClusterExpansionConvergence
    clusterWeightsExponentiallyDecayInput :
      ClusterExpansionConvergence → ClusterWeightExponentialDecay
    connectedCorrelationsClusterBoundInput :
      ClusterWeightExponentialDecay → ConnectedCorrelationClusterBound

open StepVAnalyticInhabitation public

largeFieldActionLowerBound = largeFieldActionLowerBoundInput
largeFieldPenaltyPositive = largeFieldPenaltyPositiveInput
largeFieldPenaltyAdditiveOnSeparatedBlocks =
  largeFieldPenaltyAdditiveOnSeparatedBlocksInput
largeFieldPolymerSuppressed = largeFieldPolymerSuppressedInput
polymerCardinalityEntropyBound = polymerCardinalityEntropyBoundInput
polymerDiameterEntropyBound = polymerDiameterEntropyBoundInput
sizeSuppressionBeatsEntropy = sizeSuppressionBeatsEntropyInput
diameterSuppressionBeatsEntropy = diameterSuppressionBeatsEntropyInput
anisotropicNormDominatesPolymerDiameter =
  anisotropicNormDominatesPolymerDiameterInput
anisotropicNormStableUnderBlocking = anisotropicNormStableUnderBlockingInput
polymerCrossingTransferCutControlled = polymerCrossingTransferCutControlledInput
transferCutActivitySuppressed = transferCutActivitySuppressedInput
weightedSumBelowEntropy = weightedSumBelowEntropyInput
entropyBelowSizeMajorant = entropyBelowSizeMajorantInput
sizeBelowDiameterMajorant = sizeBelowDiameterMajorantInput
diameterMajorantBelowKP = diameterMajorantBelowKPInput

concreteKoteckyPreiss :
  ∀ {Site Polymer Bound} →
  (d : StepVAnalyticInhabitation Site Polymer Bound) →
  ∀ site → LessEqual d (weightedSumAt d site) (kpThreshold d)
concreteKoteckyPreiss d site =
  transitive d (weightedSumBelowEntropyInput d site)
    (transitive d (entropyBelowSizeMajorantInput d site)
      (transitive d (sizeBelowDiameterMajorantInput d site)
        (diameterMajorantBelowKPInput d site)))

kpImpliesClusterExpansionConverges :
  ∀ {Site Polymer Bound} →
  (d : StepVAnalyticInhabitation Site Polymer Bound) →
  ClusterExpansionConvergence d
kpImpliesClusterExpansionConverges d =
  kpImpliesClusterExpansionConvergesInput d (concreteKoteckyPreiss d)

clusterWeightsExponentiallyDecay :
  ∀ {Site Polymer Bound} →
  (d : StepVAnalyticInhabitation Site Polymer Bound) →
  ClusterWeightExponentialDecay d
clusterWeightsExponentiallyDecay d =
  clusterWeightsExponentiallyDecayInput d
    (kpImpliesClusterExpansionConverges d)

connectedCorrelationsClusterBound :
  ∀ {Site Polymer Bound} →
  (d : StepVAnalyticInhabitation Site Polymer Bound) →
  ConnectedCorrelationClusterBound d
connectedCorrelationsClusterBound d =
  connectedCorrelationsClusterBoundInput d
    (clusterWeightsExponentiallyDecay d)

------------------------------------------------------------------------
-- All-scale invariant domain, summability and relevant-direction closure.
------------------------------------------------------------------------

record AllScaleAnalyticInhabitation (State ErrorBound : Set) : Set₁ where
  field
    state : Nat → State
    nextState : Nat → State → State
    stateStep : ∀ scale → state (suc scale) ≡ nextState scale (state scale)

    CouplingAdmissible FieldRadiusAdmissible PolymerAdmissible
      AnalyticityAdmissible GaugeFixingAdmissible LocalityAdmissible :
      Nat → State → Set

    couplingInitialInput : CouplingAdmissible zero (state zero)
    fieldRadiusInitialInput : FieldRadiusAdmissible zero (state zero)
    polymerInitialInput : PolymerAdmissible zero (state zero)
    analyticityInitialInput : AnalyticityAdmissible zero (state zero)
    gaugeFixingInitialInput : GaugeFixingAdmissible zero (state zero)
    localityInitialInput : LocalityAdmissible zero (state zero)

    couplingStepInput : ∀ scale current → CouplingAdmissible scale current →
      CouplingAdmissible (suc scale) (nextState scale current)
    fieldRadiusStepInput : ∀ scale current → FieldRadiusAdmissible scale current →
      FieldRadiusAdmissible (suc scale) (nextState scale current)
    polymerStepInput : ∀ scale current → PolymerAdmissible scale current →
      PolymerAdmissible (suc scale) (nextState scale current)
    analyticityStepInput : ∀ scale current → AnalyticityAdmissible scale current →
      AnalyticityAdmissible (suc scale) (nextState scale current)
    gaugeFixingStepInput : ∀ scale current → GaugeFixingAdmissible scale current →
      GaugeFixingAdmissible (suc scale) (nextState scale current)
    localityStepInput : ∀ scale current → LocalityAdmissible scale current →
      LocalityAdmissible (suc scale) (nextState scale current)

    CouplingRemainsPositive CouplingRemainsSmall AsymptoticFreedomIteration
      CouplingTendsToZero ChartRadiusRemainsPositive SmallFieldRadiusPreserved
      PolymerNormContractsAtEveryScale PolymerErrorsSummable
      AnalyticityRadiusLossSummable AnalyticityRadiusRemainsPositive
      WardIdentityPreservedAtEveryScale DecayRateLossSummable
      PositiveDecayRateAtEveryScale : Set
    couplingRemainsPositiveInput : CouplingRemainsPositive
    couplingRemainsSmallInput : CouplingRemainsSmall
    asymptoticFreedomIterationInput : AsymptoticFreedomIteration
    couplingTendsToZeroInput : CouplingTendsToZero
    chartRadiusRemainsPositiveInput : ChartRadiusRemainsPositive
    smallFieldRadiusPreservedInput : SmallFieldRadiusPreserved
    polymerNormContractsAtEveryScaleInput : PolymerNormContractsAtEveryScale
    polymerErrorsSummableInput : PolymerErrorsSummable
    analyticityRadiusLossSummableInput : AnalyticityRadiusLossSummable
    analyticityRadiusRemainsPositiveInput : AnalyticityRadiusRemainsPositive
    wardIdentityPreservedAtEveryScaleInput : WardIdentityPreservedAtEveryScale
    decayRateLossSummableInput : DecayRateLossSummable
    positiveDecayRateAtEveryScaleInput : PositiveDecayRateAtEveryScale

    partialErrorSum : Nat → ErrorBound
    totalError : ErrorBound
    LessEqual : ErrorBound → ErrorBound → Set
    partialErrorBoundInput : ∀ scale → LessEqual (partialErrorSum scale) totalError

    EffectiveActionUniformAtEveryScale RelevantCouplingsUniformlyControlled
      IrrelevantPolymerNormSummable VacuumEnergyRenormalizationConverges
      LocalGaugeInvariantOperatorClassification OnlyVacuumAndGaugeCouplingRelevant
      AllOtherOperatorsIrrelevant WardIdentitiesExcludeGaugeMassTerm : Set
    effectiveActionUniformAtEveryScaleInput : EffectiveActionUniformAtEveryScale
    relevantCouplingsUniformlyControlledInput : RelevantCouplingsUniformlyControlled
    irrelevantPolymerNormSummableInput : IrrelevantPolymerNormSummable
    vacuumEnergyRenormalizationConvergesInput :
      VacuumEnergyRenormalizationConverges
    localGaugeInvariantOperatorClassificationInput :
      LocalGaugeInvariantOperatorClassification
    onlyVacuumAndGaugeCouplingRelevantInput : OnlyVacuumAndGaugeCouplingRelevant
    allOtherOperatorsIrrelevantInput : AllOtherOperatorsIrrelevant
    wardIdentitiesExcludeGaugeMassTermInput : WardIdentitiesExcludeGaugeMassTerm

open AllScaleAnalyticInhabitation public

record AdmissibleAt
    {State ErrorBound : Set}
    (d : AllScaleAnalyticInhabitation State ErrorBound)
    (scale : Nat) (current : State) : Set where
  constructor admissible
  field
    coupling : CouplingAdmissible d scale current
    radius : FieldRadiusAdmissible d scale current
    polymer : PolymerAdmissible d scale current
    analytic : AnalyticityAdmissible d scale current
    gauge : GaugeFixingAdmissible d scale current
    local : LocalityAdmissible d scale current
open AdmissibleAt public

couplingInitial = couplingInitialInput
fieldRadiusInitial = fieldRadiusInitialInput
polymerInitial = polymerInitialInput
analyticityInitial = analyticityInitialInput
gaugeFixingInitial = gaugeFixingInitialInput
localityInitial = localityInitialInput
couplingStep = couplingStepInput
fieldRadiusStep = fieldRadiusStepInput
polymerStep = polymerStepInput
analyticityStep = analyticityStepInput
gaugeFixingStep = gaugeFixingStepInput
localityStep = localityStepInput
couplingRemainsPositive = couplingRemainsPositiveInput
couplingRemainsSmall = couplingRemainsSmallInput
asymptoticFreedomIteration = asymptoticFreedomIterationInput
couplingTendsToZero = couplingTendsToZeroInput
chartRadiusRemainsPositive = chartRadiusRemainsPositiveInput
smallFieldRadiusPreserved = smallFieldRadiusPreservedInput
polymerNormContractsAtEveryScale = polymerNormContractsAtEveryScaleInput
polymerErrorsSummable = polymerErrorsSummableInput
analyticityRadiusLossSummable = analyticityRadiusLossSummableInput
analyticityRadiusRemainsPositive = analyticityRadiusRemainsPositiveInput
wardIdentityPreservedAtEveryScale = wardIdentityPreservedAtEveryScaleInput
decayRateLossSummable = decayRateLossSummableInput
positiveDecayRateAtEveryScale = positiveDecayRateAtEveryScaleInput
effectiveActionUniformAtEveryScale = effectiveActionUniformAtEveryScaleInput
relevantCouplingsUniformlyControlled = relevantCouplingsUniformlyControlledInput
irrelevantPolymerNormSummable = irrelevantPolymerNormSummableInput
vacuumEnergyRenormalizationConverges = vacuumEnergyRenormalizationConvergesInput
localGaugeInvariantOperatorClassification =
  localGaugeInvariantOperatorClassificationInput
onlyVacuumAndGaugeCouplingRelevant = onlyVacuumAndGaugeCouplingRelevantInput
allOtherOperatorsIrrelevant = allOtherOperatorsIrrelevantInput
wardIdentitiesExcludeGaugeMassTerm = wardIdentitiesExcludeGaugeMassTermInput

initialScaleAdmissible :
  ∀ {State ErrorBound} (d : AllScaleAnalyticInhabitation State ErrorBound) →
  AdmissibleAt d zero (state d zero)
initialScaleAdmissible d = admissible
  (couplingInitialInput d)
  (fieldRadiusInitialInput d)
  (polymerInitialInput d)
  (analyticityInitialInput d)
  (gaugeFixingInitialInput d)
  (localityInitialInput d)

oneStepAdmissible :
  ∀ {State ErrorBound} (d : AllScaleAnalyticInhabitation State ErrorBound) →
  ∀ scale current → AdmissibleAt d scale current →
  AdmissibleAt d (suc scale) (nextState d scale current)
oneStepAdmissible d scale current hypothesis = admissible
  (couplingStepInput d scale current (coupling hypothesis))
  (fieldRadiusStepInput d scale current (radius hypothesis))
  (polymerStepInput d scale current (polymer hypothesis))
  (analyticityStepInput d scale current (analytic hypothesis))
  (gaugeFixingStepInput d scale current (gauge hypothesis))
  (localityStepInput d scale current (local hypothesis))

allScaleRGAdmissible :
  ∀ {State ErrorBound} (d : AllScaleAnalyticInhabitation State ErrorBound) →
  ∀ scale → AdmissibleAt d scale (state d scale)
allScaleRGAdmissible d zero = initialScaleAdmissible d
allScaleRGAdmissible d (suc scale) rewrite stateStep d scale =
  oneStepAdmissible d scale (state d scale) (allScaleRGAdmissible d scale)

rgErrorsSummable :
  ∀ {State ErrorBound} (d : AllScaleAnalyticInhabitation State ErrorBound) →
  Σ ErrorBound (λ total → ∀ scale → LessEqual d (partialErrorSum d scale) total)
rgErrorsSummable d = totalError d ,Σ partialErrorBoundInput d

record OneStepAllScaleAnalyticCertificate
    (Configuration Background Fluctuation Polymer Region Coupling Bound
      Site State ErrorBound Index CriticalState Force Radius : Set) : Set₁ where
  field
    criticalMap : CriticalMapAnalyticInputs Index CriticalState Force Bound Radius
    oneStep : OneStepRGAnalyticInhabitation
      Configuration Background Fluctuation Polymer Region Coupling Bound
    stepV : StepVAnalyticInhabitation Site Polymer Bound
    allScale : AllScaleAnalyticInhabitation State ErrorBound

open OneStepAllScaleAnalyticCertificate public

criticalMapAssemblyLevel : ProofLevel
criticalMapAssemblyLevel = machineChecked

criticalMapAnalyticInputLevel : ProofLevel
criticalMapAnalyticInputLevel = conditional

oneStepRGAssemblyLevel : ProofLevel
oneStepRGAssemblyLevel = machineChecked

oneStepRGAnalyticInputLevel : ProofLevel
oneStepRGAnalyticInputLevel = conditional

stepVAssemblyLevel : ProofLevel
stepVAssemblyLevel = machineChecked

stepVAnalyticInputLevel : ProofLevel
stepVAnalyticInputLevel = conditional

allScaleInductionLevel : ProofLevel
allScaleInductionLevel = machineChecked

allScaleAnalyticInputLevel : ProofLevel
allScaleAnalyticInputLevel = conditional
