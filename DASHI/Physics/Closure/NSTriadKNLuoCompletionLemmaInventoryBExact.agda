module DASHI.Physics.Closure.NSTriadKNLuoCompletionLemmaInventoryBExact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Stage-qualified, fail-closed lemma inventory for completion stages
-- 5 through 9. Each constructor names one distinct
-- obligation from the full Luo-to-submission dependency analysis.
--
-- Existing repository reducers are imported explicitly so these inventories
-- refine the current source-faithful architecture rather than forking it.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNLuoLemmaFamilyExact as Family
import DASHI.Physics.Closure.NSTriadKNLuoEquation42PhysicalIdentityAdapterExact
import DASHI.Physics.Closure.NSTriadKNLuoProjectedConvectionOfficialParsevalUpgradeExact
import DASHI.Physics.Closure.NSTriadKNLuoSection4PhysicalBoundsAdapterExact
import DASHI.Physics.Closure.NSTriadKNLuoSection4ContinuityProofExact
import DASHI.Physics.Closure.NSTriadKNLuoAnalyticFractionalPowerIdentificationExact
import DASHI.Physics.Closure.NSTriadKNLuoMeanValueGronwallReductionExact
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalBlockDecayReductionExact
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPerModeShellMeaningExact
import DASHI.Physics.Closure.NSTriadKNLuoMaximalTimeGlobalizationExact
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact

module Stage5 where

  data Lemma : Set where
    officialSolutionTimeDifferentiable
    officialSolutionSpatialH2OrHigher
    shellProjectionPreservesTimeDifferentiability
    shellProjectionPreservesSpatialRegularity
    shellEnergyAbsolutelyContinuous
    shellDissipationMeasurable
    nonlinearShellPairingIntegrable
    applyShellProjectorToNavierStokes
    shellProjectorCommutesWithTimeDerivative
    shellProjectorCommutesWithLaplacian
    shellProjectorCommutesWithLerayProjector
    shellProjectedEquation
    projectedPressureTermVanishes
    shellFieldRemainsDivergenceFree
    derivativeOfHermitianNormSquare
    realPartOfHermitianDerivative
    timeDerivativeShellL2SquaredFormula
    factorTwoNormalization
    officialShellEnergyDerivativeMeaning
    laplacianHermitianPairing
    integrationByPartsOnTorus
    negativeLaplacianPairingEqualsGradientNormSquare
    shellDissipationEqualsFrequencyWeightedEnergy
    viscousCoefficientNormalization
    shellDissipationNonnegative
    projectedConvectionPairingDefinition
    nonlinearPairingRealPart
    nonlinearPairingBoundedByAbsoluteFlux
    physicalNonlinearRHSDefinition
    shellEnergyInequalityAgainstPhysicalRHS
    convectionFourierCoefficient
    projectedConvectionFourierCoefficient
    shellPairingFourierExpansion
    realPartTriadCoefficientFormula
    resonantTriadConstraint
    conjugateOutputModeConvention
    triadCoefficientMatchesOfficialPairContribution
    physicalTriadEnumerationSound
    physicalTriadEnumerationComplete
    physicalTriadEnumerationDuplicateFree
    physicalTriadPartitionIntoJ1J2
    J1PartitionIntoJ11J12
    partitionDisjoint
    partitionComplete
    boundaryPairsAssignedExactlyOnce
    J1EqualsOfficialLowHighFold
    J2EqualsOfficialHighHighFold
    physicalRHSMatchesTotalInteractionFold
    officialEquation42
    officialEquation42ForAlmostEveryTime
    officialIntegratedEquation42
    officialEquation42NormalizationMatchesLuo
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "physical equation-(4.2) and nonlinear RHS/fold"

  occurrenceCount : Nat
  occurrenceCount = 52

module Stage6 where

  data Lemma : Set where
    periodicBernsteinL2ToLInfinity
    periodicBernsteinGradient
    shellLocalizationBernstein
    holderInfinityTwoTwo
    cauchySchwarzFiniteShellSum
    cauchySchwarzInfiniteShellSum
    boundedShellOverlap
    comparableShellCountUniform
    dyadicGeometricLowerTailSum
    dyadicGeometricUpperTailSum
    hardHighOutputConstraint
    frequencyTriangleConstraint
    divergenceFreeDerivativeTransfer
    commutatorKernelMomentCancellation
    J11LowerPairSupport
    J11LowerDerivativeFallsOnLowFactor
    J11LowerSingleTriadBound
    J11LowerSingleShellBound
    J11LowerLowShellSumBound
    J11LowerWeightedEnergyInsertion
    J11LowerLocalizedGradientInsertion
    J11LowerTimeIntegratedBound
    physicalJ11LowerBound
    J11UpperComparableFrequencySupport
    J11UpperFiniteNeighborCount
    J11UpperSingleTriadBound
    J11UpperSingleShellBound
    J11UpperFiniteOverlapBound
    J11UpperWeightedEnergyBound
    physicalJ11UpperBound
    J12SourceDefinition
    J12CommutatorIdentity
    J12IncrementKernelRepresentation
    J12KernelFirstMomentCancellation
    J12DerivativeGain
    J12SinglePairBound
    J12ShellGapDecay
    J12GeometricSumBound
    J12WeightedEnergyBound
    physicalJ12Bound
    J2HighHighSupport
    J2InputShellsComparable
    J2OutputLowerThanInputs
    J2OutputRelocationCoefficient
    J2SignedContributionMajorized
    J2PositiveKernelMajorant
    J2GapDecayFactor
    J2LowIndexEnvelope
    J2GapEnvelope
    J2TwoParameterGeometricSummation
    J2SchurRowColumnBound
    J2UniformConstant
    physicalJ2Bound
    fourSection4BoundsCombine
    J11EqualsLowerPlusUpper
    J1EqualsJ11PlusJ12
    J1J2TotalNonlinearBound
    section4Step1Estimate
    section4ModeDecayBootstrapInput
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "four source Section-4 analytic-estimate"

  occurrenceCount : Nat
  occurrenceCount = 59

module Stage7 where

  data Lemma : Set where
    realPowerDefinedForPositiveBase
    twoPositive
    dyadicScalePositive
    realPowerAdditiveExponent
    realPowerIntegerExponentAgreement
    realPowerNegativeExponent
    realPowerHalfExponent
    squareRootOfFourEqualsTwo
    twoToMinusTwoEqualsQuarter
    alphaThreeHalvesEqualsThreeOverTwo
    oneMinusAlphaEqualsMinusHalf
    fourTimesOneMinusAlphaEqualsMinusTwo
    analyticFourShellRatioEqualsQuarter
    realGeometricSeriesQuarterBound
    fractionalPowerNonnegative
    fractionalPowerMonotoneInScale
    lambdaDefinition
    lambdaShift
    lambdaPowerShift
    lambdaFourShiftAlphaThreeHalves
    analyticDecayFactorMatchesRationalCertificate
    shellEnergyAbsolutelyContinuous
    integralFundamentalTheoremForShellEnergy
    nonnegativeIntegralMonotone
    integralAdditivity
    constantPullsOutOfIntegral
    almostEverywhereInequalityIntegrates
    terminalWindowHasPositiveLength
    averageValueBound
    existsPointBelowAverage
    terminalWindowMeanValueSelection
    goodInitialTimeExists
    goodTimeShellEnergyBound
    goodTimeSimultaneousFiniteShellSelection
    goodTimeChoiceCompatibleWithBlock
    integralGronwall
    nonnegativeGronwallCoefficient
    gronwallExponentFinite
    gronwallExponentBoundedByLocalizedGradient
    smallLocalizedGradientControlsExponential
    gronwallWithInhomogeneousTerm
    terminalShellEnergyBound
    terminalShellDissipationBound
    terminalModeDecayBound
    terminalRegularityFromModeDecay
    terminalContinuityFromGronwall
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "real fractional-power, absolute-continuity, mean-value and Gronwall"

  occurrenceCount : Nat
  occurrenceCount = 46

module Stage8 where

  data Lemma : Set where
    officialTimeCutoffDefinition
    timeCutoffSupport
    timeCutoffEqualsOneNearTerminal
    timeCutoffVanishingAtWindowStart
    timeCutoffDerivativeSupport
    timeCutoffDerivativeBound
    timeCutoffNonnegative
    timeCutoffProductRule
    multiplyEquation42ByTimeCutoff
    integrateTimeCutoffEnergyDerivative
    integrationByPartsInTime
    initialBoundaryTermControlled
    terminalBoundaryTermEqualsCurrentEnergy
    timeCutoffDerivativeErrorBound
    integratedDissipationNonnegative
    integratedFluxBound
    integratedCutoffEnergyInequality
    fixedShiftPredecessorDefinition
    fixedShiftPredecessorStrictlyLower
    largeShellClosedUnderPredecessor
    fourAlignedResidueClassPreserved
    parabolicWindowNesting
    previousBlockEnergyControlsCutoffError
    fluxCorrectionDefinition
    fluxCorrectionDecomposition
    fluxCorrectionSignedTerms
    fluxCorrectionPositiveMajorant
    fluxCorrectionTermwiseBound
    fluxCorrectionAbsoluteSumBound
    fluxCorrectionLowIndexEnvelope
    fluxCorrectionGapEnvelope
    quarterEnvelope
    oneThirtySecondEnvelope
    combinedEnvelope128Over93
    fluxCorrectionBelowExplicitMajorant
    explicitMajorantBelowDecayTarget
    fluxCorrectionAbsorbedUniformly
    maximumBelowSum
    integratedEstimateImpliesFixedShiftRecursion
    fixedShiftRecursionCoefficient
    recursionCoefficientBelowOne
    recursionCorrectionCompatibleWithDecay
    fixedShiftRecursionUniformInShell
    fixedShiftRecursionUniformInTerminal
    baseResidueClassesFinite
    baseBlockFiniteEnergy
    baseBlockFiniteDissipation
    baseBlockUniformConstantExists
    baseBlockMatchesDecayTarget
    blockInductionStep
    blockInductionAcrossResidueClass
    blockInductionAcrossAllFourClasses
    physicalBlockDecayCertificate
    uniformDyadicEnergyDecay
    uniformDyadicDissipationDecay
    energyDecayImpliesL2ShellDecay
    dissipationDecayImpliesGradientShellDecay
    alphaAboveOneImpliesSummability
    shellDecayImpliesContinuationRegularity
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "integrated cutoff, correction and physical block-decay"

  occurrenceCount : Nat
  occurrenceCount = 59

module Stage9 where

  data Lemma : Set where
    officialShellFieldIsDeltaQu
    officialShellCoefficientDefinition
    officialShellL2SquaredDefinition
    officialShellDissipationDefinition
    officialShellTimeDerivativeDefinition
    finiteAssemblyShellFieldEqualsOfficialShellField
    finiteAssemblyEnergyEqualsOfficialEnergy
    finiteAssemblyDissipationEqualsOfficialDissipation
    finiteAssemblyDerivativeEqualsOfficialDerivative
    officialPerModeShellMeaningInhabited
    smoothDatumInHsForAlls
    localStrongSolutionExistence
    localStrongSolutionUniqueness
    localStrongSolutionContinuousInHs
    localStrongSolutionDifferentiableInHsMinusTwo
    localStrongSolutionPreservesDivergenceFree
    localStrongSolutionPreservesMeanZero
    localStrongSolutionEnergyIdentity
    strongSolutionsOrderedByExtension
    unionOfCompatibleStrongSolutions
    maximalStrongSolutionExists
    maximalStrongSolutionUnique
    maximalExistenceIntervalDefinition
    maximalTimeAlternativeFiniteOrInfinite
    solutionRegularOnEveryCompactSubinterval
    finiteMaximalTimeImpliesBlowupCriterion
    maximalStrongSolutionToOfficialSolution
    officialSolutionToMaximalStrongSolution
    officialAndMaximalSolutionsAgreeByUniqueness
    officialTerminalCanBeSelectedAsCandidateMaximalTime
    preBudgetDataConstructedAtCandidateTerminal
    canonicalPhysicalLeavesConstructedAtCandidateTerminal
    selectedTerminalMaximalityInhabited
    continuationBeyondCandidateTerminal
    continuationContradictsMaximality
    finiteMaximalTimeImpossible
    maximalTimeInfinite
    globalStrongSolutionForDatum
    officialSolutionNeededOnlyBeforeCandidateTerminal
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "official shell realization and arbitrary maximal-time"

  occurrenceCount : Nat
  occurrenceCount = 39
