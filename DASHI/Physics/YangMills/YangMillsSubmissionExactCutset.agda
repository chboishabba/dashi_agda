module DASHI.Physics.YangMills.YangMillsSubmissionExactCutset where

import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound6ExactCutset as Gate4
import DASHI.Physics.YangMills.YangMillsSubmissionObligationCardinalityExact as Counts
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact A--I submission cutset.
--
-- A is reused from the existing 58-field round-six Gate-4 cutset.  B--G form
-- the remaining theorem-critical spine, giving 191 theorem obligations in
-- total.  H--I add 28 foundational and gauge-structural obligations, for the
-- complete 219-item formal-submission inventory proved by Counts.
------------------------------------------------------------------------

record LocalStepVExactCutset : Set₁ where
  field
    finiteSupportGraphPathExistence : Set
    shortestPathMinimality : Set
    treePathLengthBoundedByTreeEdgeCount : Set
    uniformYMSupportGraphBoundedDegree : Set
    boundedDegreeRootBallGrowth : Set
    rootedConnectedSkeletonSpanningTree : Set
    rootedSpanningTreeControlledDFS : Set
    boundedDegreeRootedWalkCount : Set
    connectedSkeletonCoveredByDFSVisitedSet : Set
    rootedConnectedSkeletonSizeShellCount : Set
    diameterSizeShellRootBallContainment : Set
    reducedSkeletonComplexityLinearInDiameter : Set
    diameterShellSkeletonCount : Set
    polymerDecorationMultiplicity : Set
    skeletonDecorationEncoding : Set
    skeletonDecorationEncodingControlledMultiplicity : Set
    skeletonDecorationAnimalCount : Set
    p06ModelLeafDischargePackage : Set

    p0UniformPositivity : Set
    largeFieldCoerciveConstantLowerBound : Set
    entropyLargeFieldAbsorptionInequality : Set
    absorptionUniformityInScaleSupportBoundary : Set
    nonpostulatedImportedAbsorptionCondition : Set

    badFieldEventImpliesBlockTailLowerBound : Set
    badBlockGaussianTailSuppression : Set
    supportProductLocalization : Set
    localSuppressionProductOverPolymerSupport : Set
    totalBadFieldPenaltyControlsComplexity : Set
    complexityControlsOrdinaryDiameter : Set
    canonicalDiameterDecayEnvelope : Set
    uniformScaleConstantCompatibility : Set
    physicalP10LargeFieldSuppressionPackage : Set

    localLinkMetricReferencePerturbationDecomposition : Set
    linkMetricPerturbationNormBound : Set
    positiveBackgroundMetricFloor : Set
    perturbationBelowMetricFloor : Set
    positivePerturbedLinkMetricLowerBound : Set
    metricLowerBoundToLinkWeightComparison : Set
    linkEllipticityUniformInScalePolymerEdge : Set
    linkLowerBoundNormalisedToOne : Set
    weightedTreeDistanceDominatesOrdinaryDiameter : Set
    p33a1AnalyticDischargePackage : Set

    orderedRealTransitivityOnActualBackend : Set
    realExponentialConstructionAndLaws : Set
    stepVConstantNonnegative : Set
    exponentialAntitoneUnderNegativeArgument : Set
    nonnegativeConstantMultiplicationMonotone : Set
    expDecayMonotone : Set
    physicalWeightedActivityDecay : Set
    ordinaryDiameterDecayAfterP33b : Set
    kpNeighbourhoodShellDecomposition : Set
    p06DiameterShellCountApplied : Set
    geometricShellMajorantSummed : Set
    strictShellRatioGivesFiniteKPBound : Set
    allDiameterKPFromEntropyMargin : Set
    abstractConcreteStepVCertificateEquivalence : Set

record RGTransferExactCutset : Set₁ where
  field
    polymerDecayImpliesDLRSmallness : Set
    crossScaleInfluenceSummable : Set
    dlrSmallnessAndCrossScaleGiveUniformLSI : Set
    uniformLSIImpliesExponentialClustering : Set
    uniformLSIImpliesPositiveLatticeSpectralGap : Set
    stepVKPImpliesAssumptionA2 : Set
    a2ImpliesB6InfluenceBound : Set
    b6InfluenceImpliesRGCauchySummability : Set
    rgCauchyImpliesBlockedObservableConvergence : Set
    dlrSmallnessImpliesClusterExpansionStability : Set
    asymptoticallyFreeRunningCouplingControl : Set
    dlrAndRGCauchyLimitCompatibility : Set
    blockingChoiceIndependence : Set

record FixedLatticeGapExactCutset : Set₁ where
  field
    anisotropyCoefficientQuadraticBound : Set
    terminalKPInPhysicalNorm : Set
    localPolymerAssemblyMapCorrect : Set
    uniformFixedVolumeLSI : Set
    lsiImpliesGeneratorSpectralGap : Set
    spectralGapImpliesExponentialClustering : Set
    exponentialClusteringImpliesFixedLatticeMassGap : Set
    finiteVolumeUniformityOfGapConstants : Set
    admissibleBoundaryComparison : Set
    euclideanDecayTransferMatrixPhysicalMassEquivalence : Set

record ThermodynamicLimitExactCutset : Set₁ where
  field
    finiteVolumeGaugeMeasuresExist : Set
    uniformObservableExponentialMoments : Set
    finiteVolumeFamilyTight : Set
    infiniteVolumeSubsequenceExists : Set
    subsequentialLimitsDLRConsistent : Set
    infiniteVolumeLimitUnique : Set
    boundaryConditionIndependent : Set
    reflectionPositivityPreservedInVolumeLimit : Set
    gaugeInvariancePreservedInVolumeLimit : Set
    exponentialClusteringPreservedInVolumeLimit : Set
    fixedLatticeMassGapSurvivesVolumeLimit : Set
    allRequiredSchwingerFunctionsConverge : Set
    limitingSchwingerFamilyCompatibleAndSymmetric : Set

record ContinuumLimitExactCutset : Set₁ where
  field
    latticeSpacingSequenceTendsToZero : Set
    runningCouplingTunedAlongSequence : Set
    renormalizedLocalObservablesUniformlyControlled : Set
    continuumSchwingerDistributionsTight : Set
    continuumSubsequenceExists : Set
    rgCauchyMakesContinuumLimitUnique : Set
    continuumIndependentOfSequenceAndBlocking : Set
    reflectionPositivityPreservedUnderCutoffRemoval : Set
    translationInvarianceRestored : Set
    fullO4EuclideanCovarianceRestored : Set
    wardIdentityControlsRotationalBreaking : Set
    symanzikInvariantAnisotropicDecomposition : Set
    anisotropicCoefficientsVanish : Set
    triangularMixingExclusion : Set
    insertionIntegrabilityForWardLimit : Set
    osRegularityAndGrowth : Set
    continuumFieldTheoryNontrivial : Set
    physicalScaleExponentialClusteringPreserved : Set
    massGapSurvivesCutoffRemoval : Set
    dimensionfulContinuumGapStrictlyPositive : Set

record OSPhysicalGapExactCutset : Set₁ where
  field
    os0RegularityTemperedness : Set
    os1EuclideanInvariance : Set
    os2ReflectionPositivity : Set
    os3Symmetry : Set
    os4ClusterProperty : Set
    reconstructionAnalyticGrowth : Set
    gaugeInvariantObservableDomain : Set
    reflectionPositiveNullQuotient : Set
    hilbertSpaceCompletion : Set
    timeTranslationSemigroup : Set
    positiveSelfAdjointHamiltonian : Set
    vacuumExistenceAndUniqueness : Set
    wightmanDistributionReconstruction : Set
    poincareCovarianceAfterContinuation : Set
    spectrumCondition : Set
    localityOfGaugeInvariantFields : Set
    nontrivialQuantumYangMillsIdentification : Set
    euclideanClusteringImpliesVacuumSpectralGap : Set
    physicalUnitsGapStrictlyPositive : Set
    clayMassGapStatementIdentification : Set
    finalYangMillsQFTAndPhysicalMassGap : Set

record YangMillsTheoremSpineExactCutset : Set₁ where
  field
    gate4 : Gate4.PhysicalClosureRound6ExactCutset
    localStepV : LocalStepVExactCutset
    rgTransfer : RGTransferExactCutset
    fixedLattice : FixedLatticeGapExactCutset
    thermodynamicLimit : ThermodynamicLimitExactCutset
    continuumLimit : ContinuumLimitExactCutset
    osPhysicalGap : OSPhysicalGapExactCutset

record FoundationExactCutset : Set₁ where
  field
    theoremCriticalRealBackendBridge : Set
    constructedRealOrderedRingLaws : Set
    constructedRealCompletenessForUsedLimits : Set
    constructedRealExponentialAndLogarithm : Set
    powerSeriesDifferentiationUniformConvergence : Set
    finiteNormedVectorSpaceInfrastructure : Set
    complexMatrixInfrastructure : Set
    concreteSUNMatrixCarriers : Set
    haarOrChartMeasure : Set
    finiteDimensionalGaugeIntegration : Set
    covarianceAndGaussianIntegration : Set
    spectralTheoremForUsedOperators : Set
    measureTightnessWeakConvergence : Set
    schwingerDistributionFramework : Set
    hilbertAndUnboundedOperatorFramework : Set

record GaugeStructuralExactCutset : Set₁ where
  field
    concreteLatticeGaugeConfigurationSpace : Set
    gaugeGroupActionAndLaws : Set
    wilsonActionAndObservableGaugeInvariance : Set
    gaugeOrbitEquivalenceRelation : Set
    gaugeQuotientOrRepresentativeTheorem : Set
    faddeevPopovBackgroundGaugeDeterminant : Set
    restrictedChartGribovControl : Set
    chartMeasureGaugeCompatibility : Set
    reflectionActionOnLinksPlaquettesObservables : Set
    finiteLatticeWilsonReflectionPositivity : Set
    gaugeInvariancePreservedByRG : Set
    blockingCompatibleWithReflection : Set
    exactSUNScopeOfFinalTheorem : Set

record ConventionalImportAdmissibility : Set₁ where
  field
    importedTheoremHypothesesExact : Set
    constructedObjectSatisfiesImportedHypotheses : Set
    publishedAuthorityIdentifiable : Set
    noNovelCentralUnpublishedImport : Set
    noStringBooleanOrUnrestrictedPostulateAsProof : Set

record SubmissionAuditGates : Set₁ where
  field
    authoritativeTrackANixCompilation : Set
    noUnresolvedMetas : Set
    approvedPostulateBoundaryOnly : Set
    noUnsafeTerminationRewriteEscape : Set
    machineGeneratedDependencyAxiomInventory : Set
    theoremMatchesChosenClayFormulation : Set
    gaugeGroupAndSpacetimeAssumptionsExplicit : Set
    physicalMassGapDimensionalAudit : Set
    reproduciblePinnedToolchainAndSubmodules : Set
    independentCleanRoomBuild : Set
    manuscriptAlignedWithAgdaNames : Set
    completeAuthorTitleLocatorDOILedger : Set
    proofAuthorityClassesSeparated : Set
    externalExpertReviewBeforePromotion : Set

record YangMillsFullSubmissionExactCutset : Set₁ where
  field
    theoremSpine : YangMillsTheoremSpineExactCutset
    foundations : FoundationExactCutset
    gaugeStructure : GaugeStructuralExactCutset
    conventionalImports : ConventionalImportAdmissibility
    audit : SubmissionAuditGates

submissionTheoremSpineDefinitionLevel : ProofLevel
submissionTheoremSpineDefinitionLevel = machineChecked

submissionFullCutsetDefinitionLevel : ProofLevel
submissionFullCutsetDefinitionLevel = machineChecked

submissionTheoremSpineInhabitantsLevel : ProofLevel
submissionTheoremSpineInhabitantsLevel = conditional

submissionFullCutsetInhabitantsLevel : ProofLevel
submissionFullCutsetInhabitantsLevel = conditional
