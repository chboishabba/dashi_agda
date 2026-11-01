module DASHI.Physics.Closure.NSTriadKNLuoCompletionLemmaInventoryCExact where

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
-- Authors: Charles L. Fefferman; Clay Mathematics Institute.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Millennium Prize Problems, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
-- Stage-qualified, fail-closed lemma inventory for completion stages
-- 10 through 14. Each constructor names one distinct
-- obligation from the full Luo-to-submission dependency analysis.
--
-- Existing repository reducers are imported explicitly so these inventories
-- refine the current source-faithful architecture rather than forking it.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNLuoLemmaFamilyExact as Family
import DASHI.Physics.Closure.NSTriadKNLuoFiniteInfiniteRealPromotionExact
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact
import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact
import DASHI.Physics.Closure.NSTriadKNLuoSubmissionAuditReceiptExact
import DASHI.Physics.Closure.NSTriadKNLuoNoCircularityAuditExact
import DASHI.Physics.Closure.NSTriadKNLuoCoreSourceFidelityInventoryExact
import DASHI.Physics.Closure.NSTriadKNLuoSubmissionLemmaCrosswalkExact
import DASHI.Physics.Closure.NSTriadKNNavierStokesNormalizationTransportExact

module Stage10 where

  data Lemma : Set where
    officialFourierTruncationDefinition
    truncationFiniteSupport
    truncationPreservesDivergenceFree
    truncationPreservesReality
    truncationPreservesMeanZero
    truncationConvergesInL2
    truncationConvergesInHs
    truncationGradientConverges
    truncationShellProjectorCommutes
    truncationLowPassCommutes
    truncationHardHighCommutes
    truncatedTensorProductConverges
    truncatedConvectionConverges
    truncatedProjectedConvectionConverges
    truncatedFluxConverges
    truncatedIncrementKernelConverges
    truncatedPairFoldConverges
    truncatedEquation42RHSConverges
    truncatedSection4TermsConverge
    finiteSchurConstantUniformInTruncation
    finiteMultiplierConstantUniformInTruncation
    finiteEquation42BoundUniformInTruncation
    finiteSection4BoundsUniformInTruncation
    finiteGronwallConstantsUniformInTruncation
    finiteBlockDecayUniformInTruncation
    realOrderClosedUnderConvergence
    limitOfUniformUpperBounds
    limitOfTwoSidedBounds
    limitOfEqualities
    limitOfFiniteSums
    limitOfIntegrals
    limitOfNormSquares
    passSchurBoundToInfiniteLimit
    passEquation42ToInfiniteLimit
    passSection4BoundsToInfiniteLimit
    passBlockDecayToInfiniteLimit
    rationalEmbeddingInjective
    rationalEmbeddingPreservesZeroOne
    rationalEmbeddingPreservesAddition
    rationalEmbeddingPreservesMultiplication
    rationalEmbeddingPreservesNegation
    rationalEmbeddingPreservesOrder
    rationalEmbeddingPreservesFiniteSums
    rationalEmbeddingPreservesGeometricCertificates
    rationalBoundPromotesToRealBound
    realEnergyDefinitionMatchesEmbeddedRationalFiniteEnergy
    realFluxDefinitionMatchesEmbeddedRationalFiniteFlux
    realSchurEstimate
    realYoungEstimate
    realEquation42
    realSection4Bounds
    realBlockDecay
    officialInfiniteRealAnalyticInputs
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "uniform finite-to-infinite and rational-to-real promotion"

  occurrenceCount : Nat
  occurrenceCount = 53

module Stage11 where

  data Lemma : Set where
    smoothPeriodicVectorFieldDefinition
    divergenceFreeDatumDefinition
    meanZeroDatumDefinition
    finiteEnergyDatumDefinition
    smoothDatumEmbedsIntoHs
    datumFourierCoefficientsRapidlyDecay
    localExistenceTimeDependsOnHsNorm
    localSolutionConstructionForEveryDatum
    localSolutionUniquenessForEveryDatum
    localSolutionContinuousDependence
    localSolutionCarrierSelection
    localConstructionDoesNotUseGlobalRegularity
    maximalSolutionForEveryAdmissibleDatum
    maximalTimeForEveryAdmissibleDatum
    maximalSolutionUniquenessUniform
    maximalSolutionCompatibleWithOfficialCarrier
    preBudgetDataForEveryFiniteCandidateTerminal
    multiplierConstantIndependentOfDatum
    SchurConstantIndependentOfDatum
    Section4ConstantsDependOnlyOnApprovedParameters
    GronwallConstantsDependOnlyOnApprovedParameters
    blockDecayConstantsFiniteForEachDatum
    noConstantDependsOnUnknownFutureRegularity
    finiteMaximalTimeExcludedForEveryDatum
    maximalTimeInfiniteForEveryDatum
    globalStrongSolutionForEveryAdmissibleDatum
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "uniform local/maximal strong-solution"

  occurrenceCount : Nat
  occurrenceCount = 26

module Stage12 where

  data Lemma : Set where
    shellDecayImpliesBesovBound
    shellDecayImpliesHsBound
    requiredExponentExceedsContinuationThreshold
    HsNormFiniteAtTerminal
    terminalStateExistsInHs
    terminalStateDivergenceFree
    terminalStateMeanZero
    localExistenceFromTerminalHsDatum
    terminalTraceMatchesContinuationInitialDatum
    oldAndNewSolutionsAgreeOnOverlap
    solutionsGlueAcrossTerminal
    continuedSolutionExtendsOriginal
    positiveTimeParabolicSmoothing
    higherSobolevEnergyEstimate
    higherSobolevInduction
    allHsNormsFiniteOnCompactTimeIntervals
    SobolevAllOrdersImpliesSmooth
    initialSmoothnessPropagatesToZero
    globalVelocitySmooth
    projectedEquationImpliesGradientPressureExists
    pressurePoissonEquation
    pressureMeanZeroNormalization
    inverseLaplacianOnMeanZeroFunctions
    pressureSobolevRegularity
    pressureSmoothness
    velocityPressureSolveOriginalEquation
    pressureUniqueModuloSpatialConstant
    normalizedPressureUnique
    globalPressureSmooth
    weakStrongUniqueness
    globalStrongSolutionUnique
    globalEnergyEquality
    finiteEnergyAtEveryTime
    classicalSolutionImpliesLerayHopf
    globalSolutionPreservesDivergenceFree
    globalSolutionPreservesMeanZero
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "Sobolev continuation, smoothing, pressure, uniqueness and energy"

  occurrenceCount : Nat
  occurrenceCount = 36

module Stage13 where

  data Lemma : Set where
    cleanBuildFromEmptyEnvironment
    allPromotedModulesKernelCheck
    noHolesInPromotedDependencyClosure
    noPostulatesInPromotedDependencyClosure
    noUnsafeOptionsInPromotedDependencyClosure
    reproducibilityReceiptComplete
    generateTransitiveImportClosure
    generateDeclarationDependencyGraph
    classifyEveryLeaf
    listEveryStandardImportedTheorem
    listEveryAxiomOrPrimitive
    listEveryClassicalPrinciple
    listEveryChoiceUse
    listEveryExtensionalityUse
    listEveryRealAnalysisAuthority
    listEveryFiniteSupportAssumption
    listEveryTargetShapedField
    noGlobalSmoothnessAncestor
    noFiniteBKMAncestor
    noContinuationAncestor
    noTerminalRegularityAncestor
    noShellDecayAncestor
    noSection4ConclusionAncestor
    noFixedShiftConclusionAncestor
    noGlobalSolutionCarrierAncestor
    completeTransitiveNoCircularityReceipt
    sourceHypothesesMatchFormalTheorem
    sourceDomainTransportProved
    sourceNormalizationTransportProved
    sourceEndpointTransportProved
    sourceTheoremNotStrongerThanPublishedStatement
    globalRegularityUsesOnlyApprovedFoundations
    globalRegularityDependencyClosureAudited
    globalRegularitySourceFidelityComplete
    globalRegularityReproducible
    submissionAuditReceiptComplete
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "clean-build, transitive no-circularity and source-fidelity audit"

  occurrenceCount : Nat
  occurrenceCount = 36

module Stage14 where

  data Lemma : Set where
    periodicProblemStatementMatchesClayPeriodicAlternative
    wholeSpaceProblemHandledSeparately
    constantVelocityModeIsHarmless
    meanZeroReductionPreservesEquation
    subtractMeanVelocityGalileanTransform
    meanModePreserved
    pressureNormalizationCompatibleWithMeanMode
    positiveViscosityRescaling
    unitViscosityEquivalentToGeneralPositiveViscosity
    timeSpaceVelocityScalingPreservesSmoothness
    energyNormalizationTransport
    almostEverywhereEnergyInequalityToIntegratedEveryInterval
    absoluteContinuityUpgradesTerminalValues
    representativeChoiceDoesNotAffectContinuation
    terminalContinuityAtEveryFiniteCandidate
      : Lemma

  Specification : Set₁
  Specification = Family.LemmaSpecification Lemma

  Inhabitants : Specification → Set₁
  Inhabitants = Family.LemmaInhabitants

  stageDescription : String
  stageDescription = "problem scope, zero mode, viscosity, almost-everywhere and failure-mode"

  occurrenceCount : Nat
  occurrenceCount = 15
