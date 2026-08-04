module DASHI.Physics.Closure.NSTriadKNLuoCompletionLemmaInventoryAExact where

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
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Stage-qualified, fail-closed lemma inventory for completion stages
-- 0 through 4. Each constructor names one distinct
-- obligation from the full Luo-to-submission dependency analysis.
--
-- Existing repository reducers are imported explicitly so these inventories
-- refine the current source-faithful architecture rather than forking it.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNLuoLemmaFamilyExact as Family
import DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact
import DASHI.Physics.Closure.NSTriadKNPeriodicHardProjectorAlgebraExact
import DASHI.Physics.Closure.NSTriadKNHardSmoothLittlewoodPaleyTransferExact
import DASHI.Physics.Closure.NSTriadKNLuoWeightedIncrementFourierIntegrationCutsetExact
import DASHI.Physics.Closure.NSTriadKNLuoIncrementKernelFourierMultiplierExact
import DASHI.Physics.Closure.NSTriadKNLuoThreePairCoefficientCutsetExact
import DASHI.Physics.Closure.NSTriadKNLuoPointwisePairFoldReductionExact
import DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicMultiplierRealizationExact
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSourceSchurIdentificationExact
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact

module Stage0 where

  data Lemma : Set where
    officialTorusHasNormalizedHaarMeasure
    officialFourierCharacterDefinition
    officialFourierCoefficientDefinition
    officialInverseFourierSeriesDefinition
    fourierCharacterProduct
    fourierCharacterConjugate
    fourierCharacterOrthogonality
    fourierCoefficientLinear
    inverseFourierCoefficient
    finiteFourierExtensionality
    infiniteFourierExtensionality
    realFieldIffHermitianCoefficients
    vectorFourierCoefficientComponentwise
    tensorFourierCoefficientComponentwise
    gradientFourierMultiplier
    divergenceFourierMultiplier
    laplacianFourierMultiplier
    curlFourierMultiplier
    lerayProjectorMultiplier
    lerayProjectorIdempotent
    lerayProjectorSelfAdjoint
    lerayProjectorCommutesWithShellProjector
    lerayProjectorCommutesWithDerivative
    divergenceFreeCoefficientOrthogonality
    officialLittlewoodPaleyShellDefinition
    officialLowPassDefinition
    officialHardHighDefinition
    shellPartitionOfUnity
    shellSupportLowerBound
    shellSupportUpperBound
    shellSupportsHaveFiniteOverlap
    lowPassContainsAllLowerShells
    hardHighContainsAllHigherShells
    shellBoundaryConventionTotal
    everyModeHasUniqueOwnerOrDeclaredOverlap
    shellIndexShiftArithmetic
    dyadicScaleMonotone
    dyadicScalePositive
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "foundational periodic Fourier, differential-multiplier and shell-geometry"

  occurrenceCount : Nat
  occurrenceCount = 38

module Stage1 where

  data Lemma : Set where
    translatedFieldFourierCoefficient
    translatedFieldFourierSeries
    incrementFieldFourierCoefficient
    incrementZeroModeVanishes
    incrementPreservesReality
    incrementPreservesFiniteSupport
    incrementPreservesAbsoluteSummability
    tensorProductFourierCoefficient
    incrementTensorFourierCoefficient
    convolutionFiberFiniteForFiniteSupport
    convolutionFiberEnumerationSound
    convolutionFiberEnumerationComplete
    convolutionFiberMultiplicityOne
    pairOrderConventionMatchesTensorOrder
    tensorConvolutionPreservesHermitianReality
    kernelFourierTransformDefinition
    kernelIntegralOfCharacter
    kernelIntegralOfOne
    kernelIntegralOfCharacterDifference
    kernelIntegralOfIncrementCharacterProduct
    kernelTransformSymmetric
    kernelTransformRealForRadialKernel
    kernelTransformZeroModeNormalized
    periodizedKernelTransformMatchesEuclideanCutoff
    dyadicKernelTransformScaling
    finiteSumIntegralInterchange
    finiteTensorSumIntegralInterchange
    finiteCharacterExpansionUnderIntegral
    absoluteConvergenceOfIncrementTensorSeries
    dominatedConvergenceForKernelWeightedSeries
    bochnerIntegralInterchangeWithAbsolutelySummableSeries
    tensorValuedFubiniTonelli
    kernelWeightTimesIncrementTensorIntegrable
    weightedIncrementIntegralCoefficientEqualsConvolutionCoefficient
    weightedIncrementConvolutionCoefficientEqualsExactMultiplier
    weightedIncrementFourierCoefficientIdentity
    weightedIncrementFourierFieldIdentity
    weightedIncrementIdentityFiniteSupport
    weightedIncrementIdentityAbsoluteSummable
    weightedIncrementIdentityL2Distributional
    officialWeightedSpatialIntegralFourierIdentity
    officialFourierSignProducesPositiveSumMode
    officialMeasureNormalizationProducesNoExtraVolumeFactor
    officialTensorScalarActionMatchesIntegral
    officialKernelNormalizationMatchesLuo
    officialDyadicIndexMatchesLuoIndex
    officialIncrementOrientationMatchesSource
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "official weighted spatial-integral/Fourier"

  occurrenceCount : Nat
  occurrenceCount = 47

module Stage2 where

  data Lemma : Set where
    officialPhysicalPairDefinition
    officialPairLeftMode
    officialPairRightMode
    officialPairOutputMode
    officialPairResonance
    officialPairEnumerationSound
    officialPairEnumerationComplete
    officialPairEnumerationDuplicateFree
    officialPairRealityRepresentativePolicy
    officialPairConjugationPolicy
    officialPairTensorOrderingPolicy
    officialPairContributionAdditionPolicy
    sourcePairCarrierEquivalentToOfficialPairCarrier
    sourceAndOfficialOutputModeAgree
    sourceAndOfficialShellOwnerAgree
    rp1SourceDefinition
    rp1AllowedPairCharacterization
    rp1ForbiddenPairCharacterization
    rp1MultiplierFormula
    rp1ShellSupportFormula
    rp1BoundaryShellAssignment
    rp1CoefficientFromWeightedIncrementMultiplier
    rp1OfficialPhysicalContributionDefinition
    rp1SourceTensorOrderingMatchesOfficial
    rp1ConjugationConventionMatchesOfficial
    rp1ForbiddenPairsVanish
    rp1PairCoefficientIdentification
    rp1WholeFoldIdentification
    rp2SourceDefinition
    rp2AllowedPairCharacterization
    rp2TransitionRegionCharacterization
    rp2MultiplierFormula
    rp2LowPairCancellation
    rp2HighPairSupport
    rp2BoundaryShellAssignment
    rp2CoefficientFromWeightedIncrementMultiplier
    rp2OfficialPhysicalContributionDefinition
    rp2PairCoefficientIdentification
    rp2WholeFoldIdentification
    officialTailFieldDefinition
    tailCoefficientIffModeAboveCutoff
    tailTensorCoefficientAsConvolution
    tailPairSelectedIffBothInputsHigh
    tailBoundaryModePolicy
    tailTensorContributionMatchesOfficialPair
    tailPairCoefficientIdentification
    tailWholeFoldIdentification
    rp1Rp2TailPartitionSound
    rp1Rp2TailPartitionComplete
    partitionPiecesDisjointOrOverlapCorrected
    transitionPairsCountedExactlyOnce
    zeroModePairsHandledConsistently
    threePieceSumReconstructsFullIncrementKernel
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "three official physical pair-coefficient"

  occurrenceCount : Nat
  occurrenceCount = 53

module Stage3 where

  data Lemma : Set where
    officialSmoothMultiplierSymbol
    officialHardMultiplierSymbol
    smoothSupportContainedInHardNextSupport
    smoothSymbolFactorsThroughHardSymbol
    factorKernelSymbolDefinition
    factorKernelInverseFourierDefinition
    smoothGradientConvolutionIdentity
    periodicFactorKernelConstruction
    periodicConvolutionCoefficientIdentity
    periodicConvolutionFieldIdentity
    gradientConvolutionIndexSet
    gradientSignedTerm
    gradientPositiveMajorant
    gradientTermUpperBound
    gradientTermLowerBound
    gradientFiniteSignedSum
    gradientSignedSumEqualsOfficialSmoothGradient
    gradientMajorantEqualsKernelL1TimesHardSup
    gradientFiniteYoungReceipt
    hardGradientSupDominatesEachSample
    kernelAbsoluteCoefficientSumFinite
    periodicKernelL1BelowEuclideanKernelL1
    periodizedKernelL1UniformInShell
    kernelL1ConstantIndependentOfShell
    kernelL1ConstantIndependentOfState
    kernelL1ConstantIndependentOfTerminalTime
    kernelL1ConstantFinite
    kernelL1ConstantNonnegative
    officialTerminalWindowDefinition
    smoothTerminalIntegralDefinition
    hardTerminalIntegralDefinition
    pointwiseSmoothGradientBound
    pointwiseBoundIntegrableInTime
    timeIntegralMonotone
    constantPullsOutOfTimeIntegral
    smoothTerminalBoundByKernelConstantTimesHardTerminal
    terminalConvolutionSignedSumMeaning
    terminalConvolutionMajorantMeaning
    terminalFiniteYoungReceipt
    officialFinitePeriodicMultiplierInputs
    officialCanonicalMultiplierRealization
    officialSmoothGradientEstimate
    officialSmoothTerminalWindowEstimate
    sameConstantUsedInBothEstimates
    officialMultiplierReceiptsInhabited
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "official smooth-multiplier convolution-receipt"

  occurrenceCount : Nat
  occurrenceCount = 45

module Stage4 where

  data Lemma : Set where
    sourceAbsoluteHighFluxDefinition
    incrementKernelFluxDefinition
    sourceFluxEqualsIncrementKernelFlux
    incrementKernelFluxIntegrationByParts
    incrementKernelFluxEqualsProjectedConvectionFlux
    projectedConvectionFluxDefinition
    projectedConvectionFluxFourierExpansion
    projectedConvectionFluxEqualsOfficialPairFold
    officialPairFoldEqualsPhysicalSchurFlux
    absoluteValueTransportAcrossFluxEqualities
    sourceAbsoluteFluxMatchesPhysicalBridge
    sourceLowGradientDefinition
    sourceLowPassOperatorDefinition
    sourceLowPassSymbolEqualsOfficialSmoothSymbol
    sourceLowPassShellIndexMatchesOfficial
    sourceGradientNormEqualsOfficialSmoothGradientNorm
    sourceLowGradientMatchesPhysicalBridge
    physicalSchurProfileConstantDefinition
    profileConstantFiniteForEachShell
    profileConstantIndependentOfShell
    profileConstantIndependentOfState
    profileConstantIndependentOfTerminalTime
    profileConstantIndependentOfFourierCutoff
    commonSchurConstantSelected
    commonSchurConstantMatchesEveryPhysicalBridge
    commonSchurConstantNonnegative
    commonSchurConstantFinite
    commonSchurConstantExplicitBound
    sourceZeroMatchesRealZero
    sourceOneMatchesRealOne
    sourceAdditionMatchesRealAddition
    sourceMultiplicationMatchesRealMultiplication
    sourceNegationMatchesRealNegation
    sourceAbsoluteMatchesRealAbsolute
    sourceOrderMatchesRealOrder
    sourceFiniteSumMatchesRealFiniteSum
    sourceScalarActionMatchesRealScalarAction
    sourceNormSquareMatchesRealNormSquare
    sourceLowShellEnergyDefinition
    sourceHighShellEnergyDefinition
    physicalLowShellEnergyDefinition
    physicalHighShellEnergyDefinition
    sourceLowEnergyEqualsPhysicalLowEnergy
    sourceHighEnergyEqualsPhysicalHighEnergy
    sourceEnergySumEqualsPhysicalLowPlusHigh
    weightedPhysicalEnergyDefinition
    pairCoefficientAbsoluteBound
    pairKernelWeightBound
    lowHighSchurRowBound
    highLowSchurColumnBound
    highHighSchurBound
    weightedProfileRowSumBound
    weightedProfileColumnSumBound
    threePieceWeightedSchurBound
    lowPlusHighEnergyBelowWeightedMajorant
    sourceEnergyDominatedByCommonSchurWeightedEnergy
    physicalFluxBelowLowGradientTimesWeightedEnergy
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "nontrivial physical source-to-Schur"

  occurrenceCount : Nat
  occurrenceCount = 57
