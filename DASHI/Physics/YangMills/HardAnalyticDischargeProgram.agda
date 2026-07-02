module DASHI.Physics.YangMills.HardAnalyticDischargeProgram where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat renaming (Nat to ℕ) using (_+_; _*_)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.String using (String)

open import DASHI.Core.Prelude using (_×_)
open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _<ℝ_
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; dashi-internal-proof
  ; mixedReducer
  )

import DASHI.Physics.YangMills.AnalyticTheoremKernels as Kernels
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as AnisotropicDiameter
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.GraphCombinatorics as GraphCombinatorics
import DASHI.Physics.YangMills.LocalLatticeDischargePipeline as LocalLattice
open import DASHI.Physics.YangMills.P33BalabanMetricFaithfulnessBridge as P33Faithful using
  ( P33BalabanMetricFaithfulnessReceipt
  ; P33BalabanMetricDischarge
  )
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly

open Kernels using
  ( Block
  ; BadBlock
  ; LargeField
  ; complexity
  ; countBadBlocks
  ; blockPenalty
  ; sumBlockPenalties
  ; productBlockWeights
  ; Φ-large
  ; largeFieldActivity
  ; decayBase
  ; c-large
  ; c-block
  ; countPolymersByDiameter
  ; activity
  ; shellContribution
  ; shellConstant
  ; C-act
  ; C-ent
  ; p₀
  ; Skeleton
  ; Decoration
  ; SkeletonOf
  ; DecorationOf
  ; diamSkeleton
  ; diamPoly
  ; reducedComplexity
  ; K-skel
  ; B-skel
  ; C-dec
  ; countDecorations
  ; Edge
  ; Polymer
  ; SmallFieldRegularity
  ; isEdgeOf
  ; w-weight
  ; supEdgePerturbation
  ; ε-real-const
  ; m-background
  ; admissibleScale
  ; Summable
  ; Matrix
  ; PositiveDefinite
  ; det
  ; expℝ
  ; GaussianNormalization
  ; LocalGaussianNormalizationPositive
  ; SmallFieldReferenceWeightPositive
  ; P11bConstantsClose
  ; EntropyFactorBound
  ; DecorationFactorBound
  ; AbsorptionCondition
  ; LatticeSpacingSequence
  ; fromNat
  ; _≤_
  ; _^_
  ; _^ℝ_
  ; P10LargeFieldTheoremKernel
  ; P33SmallFieldEllipticityKernel
  ; P06PolymerEncodingTheoremKernel
  ; P07P09KPMarginKernel
  ; P08P11PositivityAbsorptionKernel
  ; RGTransferTheoremKernel
  ; FixedLatticeMassGapTheoremKernel
  ; ThermodynamicLimitTheoremKernel
  ; ContinuumCutoffRemovalTheoremKernel
  ; OSWightmanReconstructionTheoremKernel
  ; HardAnalyticFactsTheoremKernel
  ; P10AnalyticLeavesFromLargeFieldKernel
  ; P06ModelLeafDischargePackageFromKernel
  ; P09EntropyMarginDischargePackageFromKernel
  ; P08P11AbsorptionPackageFromKernel
  ; P12P19RGTransferPackageFromKernel
  ; FixedLatticeGapDischargePackageFromKernel
  ; ThermodynamicLimitPackageFromKernel
  ; ContinuumLimitPackageFromKernel
  ; OSWightmanEndpointPackageFromKernel
  ; P33a1AnalyticDischargePackageFromKernel
  ; YangMillsEndpointFromHardAnalyticFacts
  )

P06AnimalCountingBound : Set
P06AnimalCountingBound = Entropy.P06AnimalCountingReducer

NatPowerDecayMonotone : Set
NatPowerDecayMonotone = LocalLattice.NatPowerDecayMonotoneType

ComplexityLowerBoundByDiameterForDecay : Set
ComplexityLowerBoundByDiameterForDecay =
  LocalLattice.ComplexityLowerBoundByDiameterForDecayType

PositiveProduct : Set
PositiveProduct =
  ∀ x y →
  0ℝ <ℝ x →
  0ℝ <ℝ y →
  0ℝ <ℝ (x *ℝ y)

postulate
  PositiveFiniteProduct : Set
  LatticeSpacingTendsToZero : LatticeSpacingSequence → Set

ExpPositiveℝ : Set
ExpPositiveℝ = ∀ x → 0ℝ <ℝ expℝ x

PositiveDefiniteDeterminantPositive : Set
PositiveDefiniteDeterminantPositive =
  ∀ A →
  PositiveDefinite A →
  0ℝ <ℝ det A

GaussianNormalizationPositiveFromDet : Set
GaussianNormalizationPositiveFromDet =
  ∀ A →
  PositiveDefinite A →
  0ℝ <ℝ GaussianNormalization A

record HardAnalyticSprintPlan : Set₁ where
  field
    sprint1-P10-tail-kernel :
      Bool

    sprint2-P10-localisation-kernel :
      Bool

    sprint3-P10-diameter-coercivity :
      Bool

    sprint4-P10-canonical-assembly :
      Bool

    sprint5-P06-residual-counting :
      Bool

    sprint6-P07P09-semantic-closure :
      Bool

    sprint7-P33-faithfulness :
      Bool

    sprint8-stepV-local-lattice-closeout :
      Bool

    sprint9-P10-source-tail-semantics :
      Bool

    sprint10-P10-source-localisation-semantics :
      Bool

    sprint11-P10-source-coercivity-semantics :
      Bool

    sprint12-P10-canonical-decay-internalisation :
      Bool

    sprint13-P06-skeleton-decomposition :
      Bool

    sprint14-P06-endpoint-unblocking :
      Bool

    sprint15-P33-source-reconstruction :
      Bool

    sprint16-stepV-downstream-internalisation :
      Bool

    currentFocus :
      String

    noClayPromotion :
      clayYangMillsPromoted ≡ false

currentHardAnalyticSprintPlan : HardAnalyticSprintPlan
currentHardAnalyticSprintPlan = record
  { sprint1-P10-tail-kernel = true
  ; sprint2-P10-localisation-kernel = true
  ; sprint3-P10-diameter-coercivity = true
  ; sprint4-P10-canonical-assembly = true
  ; sprint5-P06-residual-counting = true
  ; sprint6-P07P09-semantic-closure = true
  ; sprint7-P33-faithfulness = true
  ; sprint8-stepV-local-lattice-closeout = true
  ; sprint9-P10-source-tail-semantics = true
  ; sprint10-P10-source-localisation-semantics = true
  ; sprint11-P10-source-coercivity-semantics = true
  ; sprint12-P10-canonical-decay-internalisation = true
  ; sprint13-P06-skeleton-decomposition = true
  ; sprint14-P06-endpoint-unblocking = true
  ; sprint15-P33-source-reconstruction = true
  ; sprint16-stepV-downstream-internalisation = true
  ; currentFocus =
      "Sprint 16 complete: the Step V downstream handoff is now routed through explicit semantic kernels and sprint witnesses. Remaining work is mathematical internalisation beyond the sprint ledger."
  ; noClayPromotion = refl
  }

record P06EncodingSubkernel : Set₁ where
  field
    reducedSkeleton :
      Polymer → Skeleton

    decoration :
      Polymer → Decoration

    encode :
      Polymer → Skeleton × Decoration

    decode :
      Skeleton × Decoration → Maybe Polymer

    encodeDecodeSound :
      ∀ P →
      decode (encode P) ≡ just P

    skeletonSound :
      ∀ P →
      SkeletonOf P (reducedSkeleton P)

    decorationSound :
      ∀ P →
      DecorationOf P (decoration P)

record P06CountingSubkernel : Set₁ where
  field
    skeletonDiameterControlled :
      (encoding : P06EncodingSubkernel) →
      ∀ P →
      diamSkeleton (P06EncodingSubkernel.reducedSkeleton encoding P) ≤ diamPoly P

    reducedComplexityControlledByDiameter :
      ∀ S →
      reducedComplexity S ≤ K-skel * diamSkeleton S + B-skel

    decorationMultiplicityByComplexity :
      ∀ S →
      countDecorations S ≤ C-dec ^ reducedComplexity S

    polymerCountingFromEncoding :
      P06EncodingSubkernel →
      Entropy.P06ModelLeafDischargePackage

P06KernelFromSubkernels :
  P06EncodingSubkernel →
  P06CountingSubkernel →
  P06PolymerEncodingTheoremKernel
P06KernelFromSubkernels encoding counting = record
  { reducedSkeleton =
      P06EncodingSubkernel.reducedSkeleton encoding
  ; decoration =
      P06EncodingSubkernel.decoration encoding
  ; encode =
      P06EncodingSubkernel.encode encoding
  ; decode =
      P06EncodingSubkernel.decode encoding
  ; encodeDecodeSound =
      P06EncodingSubkernel.encodeDecodeSound encoding
  ; skeletonDiameterControlled =
      P06CountingSubkernel.skeletonDiameterControlled counting encoding
  ; reducedComplexityControlledByDiameter =
      P06CountingSubkernel.reducedComplexityControlledByDiameter counting
  ; decorationMultiplicityByComplexity =
      P06CountingSubkernel.decorationMultiplicityByComplexity counting
  ; polymerDecompositionExhaustive =
      λ P →
      P06EncodingSubkernel.skeletonSound encoding P
      , P06EncodingSubkernel.decorationSound encoding P
  }

record P10LargeFieldGeometrySubkernel : Set₁ where
  field
    functionalDecomposition :
      ∀ k X →
      LargeField k X →
      Φ-large k X ≡ sumBlockPenalties k X

    badBlocksCoverComplexity :
      ∀ k X →
      LargeField k X →
      complexity X ≤ countBadBlocks k X

    badBlockPaysPenalty :
      ∀ k b →
      BadBlock k b →
      c-block ≤ℝ blockPenalty k b

    penaltySumCoercive :
      ∀ k X →
      LargeField k X →
      c-large *ℝ fromNat (complexity X) ≤ℝ Φ-large k X

record P10ActivitySuppressionSubkernel : Set₁ where
  field
    activityFactorsOverBlocks :
      ∀ k X →
      largeFieldActivity k X ≤ℝ productBlockWeights k X

    badBlockWeightSuppressed :
      ∀ k b →
      BadBlock k b →
      blockPenalty k b ≤ℝ c-large

    productWeightsSuppressed :
      ∀ k X →
      productBlockWeights k X
        ≤ℝ c-large *ℝ (decayBase ^ℝ Φ-large k X)

record P10DecayArithmeticSubkernel : Set₁ where
  field
    decayBaseAdmissible :
      (0ℝ <ℝ decayBase) × (decayBase <ℝ 1ℝ)

    powerDecayMonotone :
      NatPowerDecayMonotone

    complexityDiameter :
      ComplexityLowerBoundByDiameterForDecay

P10KernelFromSubkernels :
  P10LargeFieldGeometrySubkernel →
  P10ActivitySuppressionSubkernel →
  P10DecayArithmeticSubkernel →
  P10LargeFieldTheoremKernel
P10KernelFromSubkernels geometry activitySubkernel decayArithmetic = record
  { largeFieldFunctionalDefinition =
      P10LargeFieldGeometrySubkernel.functionalDecomposition geometry
  ; badBlocksControlComplexity =
      P10LargeFieldGeometrySubkernel.badBlocksCoverComplexity geometry
  ; eachBadBlockPaysCoercivePenalty =
      P10LargeFieldGeometrySubkernel.badBlockPaysPenalty geometry
  ; blockPenaltySumCoercive =
      P10LargeFieldGeometrySubkernel.penaltySumCoercive geometry
  ; polymerActivityFactorisation =
      P10ActivitySuppressionSubkernel.activityFactorsOverBlocks activitySubkernel
  ; badBlockWeightSuppression =
      P10ActivitySuppressionSubkernel.badBlockWeightSuppressed activitySubkernel
  ; productWeightsSuppressedByPenaltySum =
      P10ActivitySuppressionSubkernel.productWeightsSuppressed activitySubkernel
  }
  where
    _ = P10DecayArithmeticSubkernel.decayBaseAdmissible decayArithmetic

record P33MetricPerturbationSubkernel : Set₁ where
  field
    localMetric :
      ℕ → Polymer → Edge → ℝ

    backgroundMetric :
      ℕ → Edge → ℝ

    perturbation :
      ℕ → Polymer → Edge → ℝ

    metricDecomposition :
      ∀ k X e →
      localMetric k X e
        ≡ backgroundMetric k e +ℝ perturbation k X e

    smallFieldControlsPerturbation :
      ∀ k X →
      SmallFieldRegularity k X →
      supEdgePerturbation k X ≤ℝ ε-real-const

    backgroundMetricPositive :
      ∀ k e →
      admissibleScale k →
      m-background ≤ℝ backgroundMetric k e

record P33LinkStabilitySubkernel : Set₁ where
  field
    perturbationBelowMargin :
      ε-real-const <ℝ m-background

    perturbationStability :
      (metric : P33MetricPerturbationSubkernel) →
      ∀ k X e →
      supEdgePerturbation k X ≤ℝ ε-real-const →
      isEdgeOf e k X →
      AnisotropicDiameter.m-link
        ≤ℝ P33MetricPerturbationSubkernel.localMetric metric k X e

    linkWeightComparable :
      (metric : P33MetricPerturbationSubkernel) →
      ∀ k X e →
      isEdgeOf e k X →
      P33MetricPerturbationSubkernel.localMetric metric k X e
        ≤ℝ w-weight k e

P33KernelFromSubkernels :
  P33MetricPerturbationSubkernel →
  P33LinkStabilitySubkernel →
  P33SmallFieldEllipticityKernel
P33KernelFromSubkernels metric stability = record
  { localMetric =
      P33MetricPerturbationSubkernel.localMetric metric
  ; backgroundMetric =
      P33MetricPerturbationSubkernel.backgroundMetric metric
  ; perturbation =
      P33MetricPerturbationSubkernel.perturbation metric
  ; metricDecomposition =
      P33MetricPerturbationSubkernel.metricDecomposition metric
  ; smallFieldControlsPerturbation =
      P33MetricPerturbationSubkernel.smallFieldControlsPerturbation metric
  ; backgroundMetricUniformlyPositive =
      P33MetricPerturbationSubkernel.backgroundMetricPositive metric
  ; perturbationBelowMargin =
      P33LinkStabilitySubkernel.perturbationBelowMargin stability
  ; linkWeightComparableToMetric =
      P33LinkStabilitySubkernel.linkWeightComparable stability metric
  }

record P07P09ShellSummabilitySubkernel : Set₁ where
  field
    shellCountingFromP06 :
      P06AnimalCountingBound →
      ∀ n →
      countPolymersByDiameter n ≤ℝ C-ent ^ n

    activityDecayFromP10 :
      (∀ k Xpoly → LargeField.P10LargeFieldSuppressionPackage k Xpoly) →
      ∀ X →
      activity X ≤ℝ C-act *ℝ (decayBase ^ diamPoly X)

    explicitEntropyDecayRatio :
      C-ent *ℝ decayBase <ℝ 1ℝ

    shellContributionBound :
      ∀ n →
      shellContribution n ≤ℝ shellConstant ^ n

    geometricShellSummability :
      shellConstant <ℝ 1ℝ →
      Summable shellContribution

postulate
  P07P09ShellCountingClosedFromSubkernel :
    P07P09ShellSummabilitySubkernel →
    ∀ n →
    countPolymersByDiameter n ≤ℝ C-ent ^ n

  P07P09ActivityDiameterDecayClosedFromSubkernel :
    P07P09ShellSummabilitySubkernel →
    ∀ X →
    activity X ≤ℝ C-act *ℝ (decayBase ^ diamPoly X)

  P07P09ShellConstantBelowOneFromSubkernel :
    P07P09ShellSummabilitySubkernel →
    shellConstant <ℝ 1ℝ

P07P09KernelFromSubkernel :
  P07P09ShellSummabilitySubkernel →
  P07P09KPMarginKernel
P07P09KernelFromSubkernel shell = record
  { polymerShellCounting =
      P07P09ShellCountingClosedFromSubkernel shell
  ; activityDiameterDecay =
      P07P09ActivityDiameterDecayClosedFromSubkernel shell
  ; explicitRatio =
      P07P09ShellSummabilitySubkernel.explicitEntropyDecayRatio shell
  ; shellContributionBound =
      P07P09ShellSummabilitySubkernel.shellContributionBound shell
  ; shellConstantBelowOne =
      P07P09ShellConstantBelowOneFromSubkernel shell
  ; geometricShellSummability =
      P07P09ShellSummabilitySubkernel.geometricShellSummability shell
        (P07P09ShellConstantBelowOneFromSubkernel shell)
  }

record P08P11RealAnalysisSubkernel : Set₁ where
  field
    positiveProduct :
      PositiveProduct

    positiveFiniteProduct :
      PositiveFiniteProduct

    expPositive :
      ExpPositiveℝ

    determinantPositive :
      PositiveDefiniteDeterminantPositive

    gaussianPositive :
      GaussianNormalizationPositiveFromDet

    constantsClose :
      P11bConstantsClose

    absorptionFromConstants :
      P11bConstantsClose →
      EntropyFactorBound →
      DecorationFactorBound →
      AbsorptionCondition

postulate
  pZeroPositiveFromRealAnalysisSubkernel :
    P08P11RealAnalysisSubkernel →
    LocalGaussianNormalizationPositive →
    SmallFieldReferenceWeightPositive →
    0ℝ <ℝ p₀

P08P11KernelFromSubkernel :
  P08P11RealAnalysisSubkernel →
  P08P11PositivityAbsorptionKernel
P08P11KernelFromSubkernel realAnalysis = record
  { positiveProduct =
      P08P11RealAnalysisSubkernel.positiveProduct realAnalysis
  ; expPositive =
      P08P11RealAnalysisSubkernel.expPositive realAnalysis
  ; positiveDefiniteDetPositive =
      P08P11RealAnalysisSubkernel.determinantPositive realAnalysis
  ; gaussianNormalizationPositive =
      P08P11RealAnalysisSubkernel.gaussianPositive realAnalysis
  ; pZeroPositiveFromComponents =
      pZeroPositiveFromRealAnalysisSubkernel realAnalysis
  ; absorptionFromConstantsClose =
      P08P11RealAnalysisSubkernel.absorptionFromConstants realAnalysis
  }

record RGDLRTransferSubkernel : Set₁ where
  field
    kpToDLR :
      Assembly.StepVSpatialKPCertificate →
      Assembly.DLRSmallness

    kpToA2 :
      Assembly.StepVSpatialKPCertificate →
      Assembly.AssumptionA2

record RGInfluenceCauchySubkernel : Set₁ where
  field
    a2ToB6 :
      Assembly.AssumptionA2 →
      Assembly.B6InfluenceBound

    b6ToRGCauchy :
      Assembly.B6InfluenceBound →
      Assembly.RGCauchySummability

record RGUniformLSISubkernel : Set₁ where
  field
    crossScaleBound :
      Assembly.CrossScaleBound

    dlrCrossScaleToLSI :
      Assembly.DLRSmallness →
      Assembly.CrossScaleBound →
      Assembly.UniformLSI

RGKernelFromSubkernels :
  RGDLRTransferSubkernel →
  RGInfluenceCauchySubkernel →
  RGUniformLSISubkernel →
  RGTransferTheoremKernel
RGKernelFromSubkernels dlr influence lsi = record
  { stepVImpliesDLRSmallness =
      RGDLRTransferSubkernel.kpToDLR dlr
  ; stepVImpliesA2 =
      RGDLRTransferSubkernel.kpToA2 dlr
  ; a2ImpliesB6Influence =
      RGInfluenceCauchySubkernel.a2ToB6 influence
  ; b6ImpliesRGCauchy =
      RGInfluenceCauchySubkernel.b6ToRGCauchy influence
  ; dlrAndCrossScaleGiveUniformLSI =
      RGUniformLSISubkernel.dlrCrossScaleToLSI lsi
  }

record FixedLatticeGapSubkernel : Set₁ where
  field
    uniformLSI :
      Assembly.UniformLSI

    lsiToSpectralGap :
      Assembly.UniformLSI →
      Assembly.LatticeSpectralGap

    spectralGapToClustering :
      Assembly.LatticeSpectralGap →
      Assembly.ExponentialClustering

    clusteringToMassGap :
      Assembly.ExponentialClustering →
      Assembly.FixedLatticeMassGap

    finiteVolumeUniformity :
      Assembly.UniformAcrossFiniteVolumes

    uniformityPreservesGap :
      Assembly.UniformAcrossFiniteVolumes →
      Assembly.FixedLatticeMassGap →
      Assembly.UniformFixedLatticeMassGap

FixedLatticeKernelFromSubkernel :
  FixedLatticeGapSubkernel →
  FixedLatticeMassGapTheoremKernel
FixedLatticeKernelFromSubkernel fixed = record
  { uniformLSI =
      FixedLatticeGapSubkernel.uniformLSI fixed
  ; uniformLSIImpliesSpectralGap =
      FixedLatticeGapSubkernel.lsiToSpectralGap fixed
  ; spectralGapImpliesClustering =
      FixedLatticeGapSubkernel.spectralGapToClustering fixed
  ; clusteringImpliesMassGap =
      FixedLatticeGapSubkernel.clusteringToMassGap fixed
  ; finiteVolumeUniformity =
      FixedLatticeGapSubkernel.finiteVolumeUniformity fixed
  ; finiteVolumeUniformityPreservesGap =
      FixedLatticeGapSubkernel.uniformityPreservesGap fixed
  }

record ThermodynamicLimitSubkernel : Set₁ where
  field
    finiteVolumeTightness :
      ∀ m →
      Assembly.Tightness m

    subsequentialLimit :
      ∀ m →
      Assembly.Tightness m →
      Assembly.InfiniteVolumeSubsequentialLimit

    uniqueness :
      Assembly.UniqueInfiniteVolumeLimit

    uniquenessGivesFullLimit :
      Assembly.InfiniteVolumeSubsequentialLimit →
      Assembly.UniqueInfiniteVolumeLimit →
      Assembly.InfiniteVolumeLimit

    clusteringPreserved :
      Assembly.ExponentialClustering →
      Assembly.InfiniteVolumeLimit →
      Assembly.InfiniteVolumeExponentialClustering

    gapSurvives :
      Assembly.FixedLatticeMassGap →
      Assembly.InfiniteVolumeExponentialClustering →
      Assembly.InfiniteVolumeMassGap

ThermodynamicKernelFromSubkernel :
  ThermodynamicLimitSubkernel →
  ThermodynamicLimitTheoremKernel
ThermodynamicKernelFromSubkernel thermo = record
  { finiteVolumeMeasuresTight =
      ThermodynamicLimitSubkernel.finiteVolumeTightness thermo
  ; tightnessGivesSubsequentialLimit =
      ThermodynamicLimitSubkernel.subsequentialLimit thermo
  ; uniquenessGivesFullLimit =
      ThermodynamicLimitSubkernel.uniquenessGivesFullLimit thermo
  ; clusteringPreservedInLimit =
      ThermodynamicLimitSubkernel.clusteringPreserved thermo
  ; massGapSurvivesThermodynamicLimit =
      ThermodynamicLimitSubkernel.gapSurvives thermo
  }

record ContinuumCutoffRemovalSubkernel : Set₁ where
  field
    latticeSpacing :
      LatticeSpacingSequence

    spacingTendsToZero :
      LatticeSpacingTendsToZero latticeSpacing

    continuumTightness :
      Assembly.ContinuumTightness

    continuumSubsequence :
      Assembly.InfiniteVolumeMassGap →
      Assembly.ContinuumSubsequentialLimit

    osReflectionPositivityPreserved :
      Assembly.OSReflectionPositivityPreserved

    euclideanCovarianceRestored :
      Assembly.EuclideanCovarianceRestored

    massGapSurvivesCutoff :
      Assembly.InfiniteVolumeMassGap →
      Assembly.ContinuumSubsequentialLimit →
      Assembly.ContinuumMassGap

ContinuumKernelFromSubkernel :
  ContinuumCutoffRemovalSubkernel →
  ContinuumCutoffRemovalTheoremKernel
ContinuumKernelFromSubkernel continuum = record
  { latticeSpacingTendsToZero =
      LatticeSpacingTendsToZero
  ; continuumTightness =
      ContinuumCutoffRemovalSubkernel.continuumTightness continuum
  ; infiniteVolumeGapGivesContinuumSubsequence =
      λ seq gap seq-zero tightness →
      ContinuumCutoffRemovalSubkernel.continuumSubsequence continuum gap
  ; osReflectionPositivityPreserved =
      ContinuumCutoffRemovalSubkernel.osReflectionPositivityPreserved continuum
  ; euclideanCovarianceRestored =
      ContinuumCutoffRemovalSubkernel.euclideanCovarianceRestored continuum
  ; massGapSurvivesCutoffRemoval =
      ContinuumCutoffRemovalSubkernel.massGapSurvivesCutoff continuum
  }

record OSWightmanReconstructionSubkernel : Set₁ where
  field
    osInputsFromContinuum :
      Assembly.ContinuumMassGap →
      Assembly.OSReflectionPositivityPreserved →
      Assembly.EuclideanCovarianceRestored →
      Assembly.OSInputs

    osReconstruction :
      Assembly.OSInputs →
      Assembly.WightmanTheory

    ymAxioms :
      Assembly.WightmanTheory →
      Assembly.YangMillsQuantumFieldTheory

    physicalMassGapTransfer :
      Assembly.ContinuumMassGap →
      Assembly.WightmanTheory →
      Assembly.PhysicalMassGap

OSWightmanKernelFromSubkernel :
  OSWightmanReconstructionSubkernel →
  OSWightmanReconstructionTheoremKernel
OSWightmanKernelFromSubkernel os = record
  { osInputsFromContinuum =
      OSWightmanReconstructionSubkernel.osInputsFromContinuum os
  ; wightmanTheoryFromOS =
      OSWightmanReconstructionSubkernel.osReconstruction os
  ; ymAxiomsSatisfied =
      OSWightmanReconstructionSubkernel.ymAxioms os
  ; physicalMassGapFromContinuum =
      OSWightmanReconstructionSubkernel.physicalMassGapTransfer os
  }

record HardAnalyticSubkernelProgram : Set₁ where
  field
    p06Encoding :
      P06EncodingSubkernel

    p06Counting :
      P06CountingSubkernel

    p10Geometry :
      P10LargeFieldGeometrySubkernel

    p10Activity :
      P10ActivitySuppressionSubkernel

    p10DecayArithmetic :
      P10DecayArithmeticSubkernel

    p33Metric :
      P33MetricPerturbationSubkernel

    p33LinkStability :
      P33LinkStabilitySubkernel

    p07p09Shell :
      P07P09ShellSummabilitySubkernel

    p08p11RealAnalysis :
      P08P11RealAnalysisSubkernel

    rgDLR :
      RGDLRTransferSubkernel

    rgInfluence :
      RGInfluenceCauchySubkernel

    rgLSI :
      RGUniformLSISubkernel

    fixedLatticeGap :
      FixedLatticeGapSubkernel

    thermodynamic :
      ThermodynamicLimitSubkernel

    continuum :
      ContinuumCutoffRemovalSubkernel

    osWightman :
      OSWightmanReconstructionSubkernel

    noClayPromotion :
      clayYangMillsPromoted ≡ false

P06KernelFromProgram :
  HardAnalyticSubkernelProgram →
  P06PolymerEncodingTheoremKernel
P06KernelFromProgram program =
  P06KernelFromSubkernels
    (HardAnalyticSubkernelProgram.p06Encoding program)
    (HardAnalyticSubkernelProgram.p06Counting program)

record OwnedP06SourceSkeletonDecompositionSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceSkeletonDecompositionSemanticKernel :
      Entropy.P06SourceSkeletonDecompositionSemanticKernel

    skeletonDecompositionSemanticWitness :
      Entropy.OwnedP06SourceSkeletonDecompositionSprintWitness

    residualCountingWitness :
      Entropy.OwnedP06ResidualCountingSprintWitness

    decorationMultiplicityWitness :
      Entropy.OwnedP06bDecorationMultiplicityWitness

    animalCountingWitness :
      Entropy.OwnedP06AnimalCountingWitness

P06SourceSkeletonDecompositionSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP06SourceSkeletonDecompositionSprintWitness program
P06SourceSkeletonDecompositionSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06SourceSkeletonDecompositionSemanticKernel/currentOwnedP06SourceSkeletonDecompositionSprintWitness"
  ; status = mixedReducer
  ; sourceSkeletonDecompositionSemanticKernel =
      Entropy.currentP06SourceSkeletonDecompositionSemanticKernel
  ; skeletonDecompositionSemanticWitness =
      Entropy.currentOwnedP06SourceSkeletonDecompositionSprintWitness
  ; residualCountingWitness =
      Entropy.currentOwnedP06ResidualCountingSprintWitness
  ; decorationMultiplicityWitness =
      Entropy.currentOwnedP06bDecorationMultiplicityWitness
  ; animalCountingWitness =
      Entropy.currentOwnedP06AnimalCountingWitness
  }

record OwnedP06EndpointUnblockingSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    endpointSemanticKernel :
      Entropy.P06EndpointUnblockingSemanticKernel

    endpointSemanticWitness :
      Entropy.OwnedP06EndpointUnblockingSprintWitness

    skeletonDecompositionWitness :
      Entropy.OwnedP06SourceSkeletonDecompositionSprintWitness

P06EndpointUnblockingSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP06EndpointUnblockingSprintWitness program
P06EndpointUnblockingSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanPolymerDiameterEntropy.currentP06EndpointUnblockingSemanticKernel/currentOwnedP06EndpointUnblockingSprintWitness"
  ; status = mixedReducer
  ; endpointSemanticKernel =
      Entropy.currentP06EndpointUnblockingSemanticKernel
  ; endpointSemanticWitness =
      Entropy.currentOwnedP06EndpointUnblockingSprintWitness
  ; skeletonDecompositionWitness =
      Entropy.currentOwnedP06SourceSkeletonDecompositionSprintWitness
  }

P10KernelFromProgram :
  HardAnalyticSubkernelProgram →
  P10LargeFieldTheoremKernel
P10KernelFromProgram program =
  P10KernelFromSubkernels
    (HardAnalyticSubkernelProgram.p10Geometry program)
    (HardAnalyticSubkernelProgram.p10Activity program)
    (HardAnalyticSubkernelProgram.p10DecayArithmetic program)

P33KernelFromProgram :
  HardAnalyticSubkernelProgram →
  P33SmallFieldEllipticityKernel
P33KernelFromProgram program =
  P33KernelFromSubkernels
    (HardAnalyticSubkernelProgram.p33Metric program)
    (HardAnalyticSubkernelProgram.p33LinkStability program)

P07P09KernelFromProgram :
  HardAnalyticSubkernelProgram →
  P07P09KPMarginKernel
P07P09KernelFromProgram program =
  P07P09KernelFromSubkernel
    (HardAnalyticSubkernelProgram.p07p09Shell program)

record OwnedP07P09SemanticClosureSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    kernel :
      P07P09KPMarginKernel

    kpDischargePackage :
      Entropy.P07KPSummabilityDischargePackage

    entropyMarginDischargePackage :
      Entropy.P09EntropyMarginDischargePackage

    kpReducerBoundary :
      Entropy.P07KPSummabilityReducer

    entropyMarginBoundary :
      Entropy.P09EntropyMargin

P07P09SemanticClosureSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP07P09SemanticClosureSprintWitness program
P07P09SemanticClosureSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "HardAnalyticDischargeProgram.P07P09KernelFromProgram/AnalyticTheoremKernels.P07KPSummabilityDischargePackageFromKernel/AnalyticTheoremKernels.P09EntropyMarginDischargePackageFromKernel"
  ; status = mixedReducer
  ; kernel =
      P07P09KernelFromProgram program
  ; kpDischargePackage =
      Kernels.P07KPSummabilityDischargePackageFromKernel
        (P07P09KernelFromProgram program)
  ; entropyMarginDischargePackage =
      P09EntropyMarginDischargePackageFromKernel
        (P07P09KernelFromProgram program)
  ; kpReducerBoundary =
      Kernels.P07KPSummabilityReducerFromKernel
        (P07P09KernelFromProgram program)
  ; entropyMarginBoundary =
      Kernels.P09EntropyMarginFromKernel
        (P07P09KernelFromProgram program)
  }

record OwnedP10SourceTailSemanticSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceTailSemanticKernel :
      LargeField.P10SourceTailSemanticKernel

    tailSemanticWitness :
      LargeField.OwnedP10SourceTailSemanticSprintWitness

    tailKernelWitness :
      LargeField.OwnedP10TailKernelSprintWitness

P10SourceTailSemanticSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP10SourceTailSemanticSprintWitness program
P10SourceTailSemanticSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceTailSemanticKernel/currentOwnedP10SourceTailSemanticSprintWitness/currentOwnedP10TailKernelSprintWitness"
  ; status = mixedReducer
  ; sourceTailSemanticKernel =
      LargeField.currentP10SourceTailSemanticKernel
  ; tailSemanticWitness =
      LargeField.currentOwnedP10SourceTailSemanticSprintWitness
  ; tailKernelWitness =
      LargeField.currentOwnedP10TailKernelSprintWitness
  }

record OwnedP10SourceLocalisationSemanticSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceLocalisationSemanticKernel :
      LargeField.P10SourceLocalisationSemanticKernel

    localisationSemanticWitness :
      LargeField.OwnedP10SourceLocalisationSemanticSprintWitness

    localisationKernelWitness :
      LargeField.OwnedP10LocalisationKernelSprintWitness

P10SourceLocalisationSemanticSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP10SourceLocalisationSemanticSprintWitness program
P10SourceLocalisationSemanticSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceLocalisationSemanticKernel/currentOwnedP10SourceLocalisationSemanticSprintWitness/currentOwnedP10LocalisationKernelSprintWitness"
  ; status = mixedReducer
  ; sourceLocalisationSemanticKernel =
      LargeField.currentP10SourceLocalisationSemanticKernel
  ; localisationSemanticWitness =
      LargeField.currentOwnedP10SourceLocalisationSemanticSprintWitness
  ; localisationKernelWitness =
      LargeField.currentOwnedP10LocalisationKernelSprintWitness
  }

record OwnedP10SourceCoercivitySemanticSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceCoercivitySemanticKernel :
      LargeField.P10SourceCoercivitySemanticKernel

    coercivitySemanticWitness :
      LargeField.OwnedP10SourceCoercivitySemanticSprintWitness

    coercivityKernelWitness :
      LargeField.OwnedP10DiameterCoercivitySprintWitness

P10SourceCoercivitySemanticSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP10SourceCoercivitySemanticSprintWitness program
P10SourceCoercivitySemanticSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceCoercivitySemanticKernel/currentOwnedP10SourceCoercivitySemanticSprintWitness/currentOwnedP10DiameterCoercivitySprintWitness"
  ; status = mixedReducer
  ; sourceCoercivitySemanticKernel =
      LargeField.currentP10SourceCoercivitySemanticKernel
  ; coercivitySemanticWitness =
      LargeField.currentOwnedP10SourceCoercivitySemanticSprintWitness
  ; coercivityKernelWitness =
      LargeField.currentOwnedP10DiameterCoercivitySprintWitness
  }

record OwnedP10SourceCanonicalDecaySemanticSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceCanonicalDecaySemanticKernel :
      LargeField.P10SourceCanonicalDecaySemanticKernel

    canonicalDecaySemanticWitness :
      LargeField.OwnedP10SourceCanonicalDecaySemanticSprintWitness

    canonicalAssemblyWitness :
      LargeField.OwnedP10CanonicalAssemblySprintWitness

P10SourceCanonicalDecaySemanticSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP10SourceCanonicalDecaySemanticSprintWitness program
P10SourceCanonicalDecaySemanticSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "BalabanLargeFieldSuppression.currentP10SourceCanonicalDecaySemanticKernel/currentOwnedP10SourceCanonicalDecaySemanticSprintWitness/currentOwnedP10CanonicalAssemblySprintWitness"
  ; status = provedConditionalReducer
  ; sourceCanonicalDecaySemanticKernel =
      LargeField.currentP10SourceCanonicalDecaySemanticKernel
  ; canonicalDecaySemanticWitness =
      LargeField.currentOwnedP10SourceCanonicalDecaySemanticSprintWitness
  ; canonicalAssemblyWitness =
      LargeField.currentOwnedP10CanonicalAssemblySprintWitness
  }

record OwnedP33FaithfulnessSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    abstractKernel :
      P33SmallFieldEllipticityKernel

    faithfulnessReceipt :
      P33BalabanMetricFaithfulnessReceipt
        Polymer
        Edge
        SmallFieldRegularity
        Kernels.P33AbstractLocalMetric
        Kernels.P33AbstractBackgroundMetric
        Kernels.P33AbstractPerturbation
        w-weight

    metricDischarge :
      P33BalabanMetricDischarge
        Polymer
        Edge
        SmallFieldRegularity
        isEdgeOf
        Kernels.P33AbstractLocalMetric
        Kernels.P33AbstractBackgroundMetric
        Kernels.P33AbstractPerturbation
        supEdgePerturbation
        ε-real-const
        m-background
        admissibleScale
        w-weight

    anisotropicDischargePackage :
      AnisotropicDiameter.P33a1AnalyticDischargePackage

    graphDischargePackage :
      GraphCombinatorics.P33a1AnalyticDischargePackage

P33FaithfulnessSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP33FaithfulnessSprintWitness program
P33FaithfulnessSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "AnalyticTheoremKernels.currentP33BalabanMetricFaithfulnessReceipt/AnalyticTheoremKernels.currentP33BalabanMetricDischarge/AnalyticTheoremKernels.P33BalabanAnalyticDischargeFromNormalizedModelAndFaithfulness"
  ; status = mixedReducer
  ; abstractKernel =
      P33KernelFromProgram program
  ; faithfulnessReceipt =
      Kernels.currentP33BalabanMetricFaithfulnessReceipt
  ; metricDischarge =
      Kernels.currentP33BalabanMetricDischarge
  ; anisotropicDischargePackage =
      P33a1AnalyticDischargePackageFromKernel
        (P33KernelFromProgram program)
  ; graphDischargePackage =
      P33GraphCombinatoricsPackageFromAnisotropicPackage
        (P33a1AnalyticDischargePackageFromKernel
          (P33KernelFromProgram program))
  }

record OwnedP33SourceReconstructionSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    sourceReconstructionKernel :
      P33Faithful.P33BalabanSourceReconstructionKernel
        Polymer
        Edge
        SmallFieldRegularity
        isEdgeOf
        Kernels.P33AbstractLocalMetric
        Kernels.P33AbstractBackgroundMetric
        Kernels.P33AbstractPerturbation
        supEdgePerturbation
        admissibleScale
        w-weight
        ε-real-const
        m-background

    faithfulnessWitness :
      OwnedP33FaithfulnessSprintWitness program

P33SourceReconstructionSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedP33SourceReconstructionSprintWitness program
P33SourceReconstructionSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "AnalyticTheoremKernels.currentP33BalabanSourceReconstructionKernel/HardAnalyticDischargeProgram.P33FaithfulnessSprintWitnessFromProgram"
  ; status = mixedReducer
  ; sourceReconstructionKernel =
      Kernels.currentP33BalabanSourceReconstructionKernel
  ; faithfulnessWitness =
      P33FaithfulnessSprintWitnessFromProgram program
  }

P08P11KernelFromProgram :
  HardAnalyticSubkernelProgram →
  P08P11PositivityAbsorptionKernel
P08P11KernelFromProgram program =
  P08P11KernelFromSubkernel
    (HardAnalyticSubkernelProgram.p08p11RealAnalysis program)

RGKernelFromProgram :
  HardAnalyticSubkernelProgram →
  RGTransferTheoremKernel
RGKernelFromProgram program =
  RGKernelFromSubkernels
    (HardAnalyticSubkernelProgram.rgDLR program)
    (HardAnalyticSubkernelProgram.rgInfluence program)
    (HardAnalyticSubkernelProgram.rgLSI program)

FixedLatticeKernelFromProgram :
  HardAnalyticSubkernelProgram →
  FixedLatticeMassGapTheoremKernel
FixedLatticeKernelFromProgram program =
  FixedLatticeKernelFromSubkernel
    (HardAnalyticSubkernelProgram.fixedLatticeGap program)

ThermodynamicKernelFromProgram :
  HardAnalyticSubkernelProgram →
  ThermodynamicLimitTheoremKernel
ThermodynamicKernelFromProgram program =
  ThermodynamicKernelFromSubkernel
    (HardAnalyticSubkernelProgram.thermodynamic program)

ContinuumKernelFromProgram :
  HardAnalyticSubkernelProgram →
  ContinuumCutoffRemovalTheoremKernel
ContinuumKernelFromProgram program =
  ContinuumKernelFromSubkernel
    (HardAnalyticSubkernelProgram.continuum program)

OSWightmanKernelFromProgram :
  HardAnalyticSubkernelProgram →
  OSWightmanReconstructionTheoremKernel
OSWightmanKernelFromProgram program =
  OSWightmanKernelFromSubkernel
    (HardAnalyticSubkernelProgram.osWightman program)

HardAnalyticFactsFromSubkernelProgram :
  HardAnalyticSubkernelProgram →
  HardAnalyticFactsTheoremKernel
HardAnalyticFactsFromSubkernelProgram program = record
  { p06 = P06KernelFromProgram program
  ; p07p09 = P07P09KernelFromProgram program
  ; p08p11 = P08P11KernelFromProgram program
  ; p10 = P10KernelFromProgram program
  ; p33 = P33KernelFromProgram program
  ; rg = RGKernelFromProgram program
  ; fixedLattice = FixedLatticeKernelFromProgram program
  ; thermodynamic = ThermodynamicKernelFromProgram program
  ; continuum = ContinuumKernelFromProgram program
  ; osWightman = OSWightmanKernelFromProgram program
  }

postulate
  P33GraphCombinatoricsPackageFromAnisotropicPackage :
    AnisotropicDiameter.P33a1AnalyticDischargePackage →
    GraphCombinatorics.P33a1AnalyticDischargePackage

LocalLatticeAnalyticDischargePackageFromSubkernelProgram :
  HardAnalyticSubkernelProgram →
  LocalLattice.LocalLatticeAnalyticDischargePackage
LocalLatticeAnalyticDischargePackageFromSubkernelProgram program = record
  { p06ModelLeaves =
      P06ModelLeafDischargePackageFromKernel
        (P06KernelFromProgram program)
  ; p10AnalyticLeaves =
      P10AnalyticLeavesFromLargeFieldKernel
        (P10KernelFromProgram program)
  ; p33PerturbationStability =
      P33GraphCombinatoricsPackageFromAnisotropicPackage
        (P33a1AnalyticDischargePackageFromKernel
          (P33KernelFromProgram program))
  ; entropyDecayMargin =
      P09EntropyMarginDischargePackageFromKernel
        (P07P09KernelFromProgram program)
  ; p08p11Positivity =
      P08P11AbsorptionPackageFromKernel
        (P08P11KernelFromProgram program)
  ; natPowerDecay =
      P10DecayArithmeticSubkernel.powerDecayMonotone
        (HardAnalyticSubkernelProgram.p10DecayArithmetic program)
  ; complexityDiameter =
      P10DecayArithmeticSubkernel.complexityDiameter
        (HardAnalyticSubkernelProgram.p10DecayArithmetic program)
  ; noClayPromotion =
      HardAnalyticSubkernelProgram.noClayPromotion program
  }

record OwnedStepVLocalLatticeCloseoutSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    localLatticePackage :
      LocalLattice.LocalLatticeAnalyticDischargePackage

    stepVCertificate :
      Assembly.StepVSpatialKPCertificate

    rgTransferPackage :
      Assembly.P12P19RGTransferPackage

    fixedLatticePackage :
      Assembly.FixedLatticeGapDischargePackage

    thermodynamicPackage :
      Assembly.ThermodynamicLimitPackage

    continuumPackage :
      Assembly.ContinuumLimitPackage

    osWightmanPackage :
      Assembly.OSWightmanEndpointPackage

OwnedStepVLocalLatticeCloseoutSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedStepVLocalLatticeCloseoutSprintWitness program
OwnedStepVLocalLatticeCloseoutSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "HardAnalyticDischargeProgram.LocalLatticeAnalyticDischargePackageFromSubkernelProgram/LocalLatticeDischargePipeline.LocalLatticeStepVFromAnalyticDischarge/AnalyticTheoremKernels.{P12P19RGTransferPackageFromKernel,FixedLatticeGapDischargePackageFromKernel,ThermodynamicLimitPackageFromKernel,ContinuumLimitPackageFromKernel,OSWightmanEndpointPackageFromKernel}"
  ; status = mixedReducer
  ; localLatticePackage =
      LocalLatticeAnalyticDischargePackageFromSubkernelProgram program
  ; stepVCertificate =
      LocalLattice.LocalLatticeStepVFromAnalyticDischarge
        (LocalLatticeAnalyticDischargePackageFromSubkernelProgram program)
  ; rgTransferPackage =
      P12P19RGTransferPackageFromKernel
        (RGKernelFromProgram program)
  ; fixedLatticePackage =
      FixedLatticeGapDischargePackageFromKernel
        (FixedLatticeKernelFromProgram program)
  ; thermodynamicPackage =
      ThermodynamicLimitPackageFromKernel
        (ThermodynamicKernelFromProgram program)
  ; continuumPackage =
      ContinuumLimitPackageFromKernel
        (ContinuumKernelFromProgram program)
  ; osWightmanPackage =
      OSWightmanEndpointPackageFromKernel
        (OSWightmanKernelFromProgram program)
  }

record OwnedStepVDownstreamInternalisationSprintWitness
  (program : HardAnalyticSubkernelProgram) : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    localDownstreamKernel :
      LocalLattice.StepVDownstreamInternalisationKernel

    assemblyDownstreamKernel :
      Assembly.StepVDownstreamTransferSemanticKernel

    localLatticeWitness :
      OwnedStepVLocalLatticeCloseoutSprintWitness program

    stepVToRGDischarge :
      Assembly.StepVToRGDischargePackage

OwnedStepVDownstreamInternalisationSprintWitnessFromProgram :
  (program : HardAnalyticSubkernelProgram) →
  OwnedStepVDownstreamInternalisationSprintWitness program
OwnedStepVDownstreamInternalisationSprintWitnessFromProgram program = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "LocalLatticeDischargePipeline.currentStepVDownstreamInternalisationKernel/StepVAssemblyLemmaQueue.currentStepVDownstreamTransferSemanticKernel/HardAnalyticDischargeProgram.OwnedStepVLocalLatticeCloseoutSprintWitnessFromProgram"
  ; status = mixedReducer
  ; localDownstreamKernel =
      LocalLattice.currentStepVDownstreamInternalisationKernel
  ; assemblyDownstreamKernel =
      Assembly.currentStepVDownstreamTransferSemanticKernel
  ; localLatticeWitness =
      OwnedStepVLocalLatticeCloseoutSprintWitnessFromProgram program
  ; stepVToRGDischarge =
      Assembly.StepVToRGDischargePackageFromP12P19
        (P12P19RGTransferPackageFromKernel
          (RGKernelFromProgram program))
  }

YangMillsEndpointFromSubkernelProgram :
  HardAnalyticSubkernelProgram →
  Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap
YangMillsEndpointFromSubkernelProgram program =
  YangMillsEndpointFromHardAnalyticFacts
    (HardAnalyticFactsFromSubkernelProgram program)

data KernelFieldClass : Set where
  definitionUnfolding : KernelFieldClass
  finiteCombinatorics : KernelFieldClass
  standardRealAnalysis : KernelFieldClass
  latticeRGAnalysis : KernelFieldClass
  continuumAnalysis : KernelFieldClass
  osReconstruction : KernelFieldClass
  hardBalabanEstimate : KernelFieldClass
  openProblemLeaf : KernelFieldClass

record KernelFieldAuditRow : Set where
  field
    kernelName :
      String

    fieldName :
      String

    fieldClass :
      KernelFieldClass

    expectedNextMove :
      String

    promotesClay :
      Bool

P10FunctionalDecompositionRow : KernelFieldAuditRow
P10FunctionalDecompositionRow = record
  { kernelName = "P10"
  ; fieldName = "functionalDecomposition"
  ; fieldClass = definitionUnfolding
  ; expectedNextMove = "Unfold the large-field functional into block penalties, then isolate the coercive summands."
  ; promotesClay = false
  }

P10BadBlocksControlComplexityRow : KernelFieldAuditRow
P10BadBlocksControlComplexityRow = record
  { kernelName = "P10"
  ; fieldName = "badBlocksCoverComplexity"
  ; fieldClass = finiteCombinatorics
  ; expectedNextMove = "Prove complexity is covered by bad-block incidence before any analytic decay estimate is used."
  ; promotesClay = false
  }

P10BadBlockPaysPenaltyRow : KernelFieldAuditRow
P10BadBlockPaysPenaltyRow = record
  { kernelName = "P10"
  ; fieldName = "badBlockPaysPenalty"
  ; fieldClass = hardBalabanEstimate
  ; expectedNextMove = "Extract the per-block coercive penalty inequality as the first genuinely analytic P10 leaf."
  ; promotesClay = false
  }

P10ActivityFactorisationRow : KernelFieldAuditRow
P10ActivityFactorisationRow = record
  { kernelName = "P10"
  ; fieldName = "activityFactorsOverBlocks"
  ; fieldClass = hardBalabanEstimate
  ; expectedNextMove = "Factor the polymer activity across blocks before applying blockwise suppression."
  ; promotesClay = false
  }

P33SmallFieldControlsPerturbationRow : KernelFieldAuditRow
P33SmallFieldControlsPerturbationRow = record
  { kernelName = "P33"
  ; fieldName = "smallFieldControlsPerturbation"
  ; fieldClass = hardBalabanEstimate
  ; expectedNextMove = "Push the small-field regularity witness down to an explicit perturbation bound on every support edge."
  ; promotesClay = false
  }

P33LinkWeightComparableRow : KernelFieldAuditRow
P33LinkWeightComparableRow = record
  { kernelName = "P33"
  ; fieldName = "linkWeightComparable"
  ; fieldClass = hardBalabanEstimate
  ; expectedNextMove = "Show the local metric stays below the repo link-weight interface after the perturbation margin is applied."
  ; promotesClay = false
  }

P06EncodeDecodeSoundRow : KernelFieldAuditRow
P06EncodeDecodeSoundRow = record
  { kernelName = "P06"
  ; fieldName = "encodeDecodeSound"
  ; fieldClass = finiteCombinatorics
  ; expectedNextMove = "Make the polymer encoding injective enough for a repo-local decode witness."
  ; promotesClay = false
  }

P06DecorationMultiplicityRow : KernelFieldAuditRow
P06DecorationMultiplicityRow = record
  { kernelName = "P06"
  ; fieldName = "decorationMultiplicityByComplexity"
  ; fieldClass = finiteCombinatorics
  ; expectedNextMove = "Bound decoration multiplicity by reduced complexity inside the explicit polymer representation."
  ; promotesClay = false
  }

RGCrossScaleLSIRow : KernelFieldAuditRow
RGCrossScaleLSIRow = record
  { kernelName = "RG"
  ; fieldName = "dlrCrossScaleToLSI"
  ; fieldClass = latticeRGAnalysis
  ; expectedNextMove = "Consume DLR smallness together with the cross-scale estimate to obtain uniform LSI."
  ; promotesClay = false
  }

ThermoTightnessRow : KernelFieldAuditRow
ThermoTightnessRow = record
  { kernelName = "Thermodynamic"
  ; fieldName = "finiteVolumeTightness"
  ; fieldClass = continuumAnalysis
  ; expectedNextMove = "Replace the tightness import with a finite-volume compactness argument tracked inside the repo."
  ; promotesClay = false
  }

ContinuumMassGapSurvivalRow : KernelFieldAuditRow
ContinuumMassGapSurvivalRow = record
  { kernelName = "Continuum"
  ; fieldName = "massGapSurvivesCutoff"
  ; fieldClass = continuumAnalysis
  ; expectedNextMove = "Show the infinite-volume gap survives the cutoff-removal subsequence with explicit control of the limit."
  ; promotesClay = false
  }

OSReconstructionRow : KernelFieldAuditRow
OSReconstructionRow = record
  { kernelName = "OS/Wightman"
  ; fieldName = "osReconstruction"
  ; fieldClass = osReconstruction
  ; expectedNextMove = "Consume the OS inputs and produce the Wightman theory as a repo-local reconstruction step."
  ; promotesClay = false
  }

kernelFieldAuditLedger : List KernelFieldAuditRow
kernelFieldAuditLedger =
  P10FunctionalDecompositionRow
  ∷ P10BadBlocksControlComplexityRow
  ∷ P10BadBlockPaysPenaltyRow
  ∷ P10ActivityFactorisationRow
  ∷ P33SmallFieldControlsPerturbationRow
  ∷ P33LinkWeightComparableRow
  ∷ P06EncodeDecodeSoundRow
  ∷ P06DecorationMultiplicityRow
  ∷ RGCrossScaleLSIRow
  ∷ ThermoTightnessRow
  ∷ ContinuumMassGapSurvivalRow
  ∷ OSReconstructionRow
  ∷ []

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

AllKernelAuditRowsNoClayPromotion :
  ∀ {row} →
  row ∈ kernelFieldAuditLedger →
  KernelFieldAuditRow.promotesClay row ≡ false
AllKernelAuditRowsNoClayPromotion here = refl
AllKernelAuditRowsNoClayPromotion (there here) = refl
AllKernelAuditRowsNoClayPromotion (there (there here)) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there here))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there here)))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there (there here))))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there (there (there here)))))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there (there (there (there here))))))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there (there (there (there (there here)))))))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there (there (there (there (there (there here))))))))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there (there (there (there (there (there (there here)))))))))) = refl
AllKernelAuditRowsNoClayPromotion (there (there (there (there (there (there (there (there (there (there (there here))))))))))) = refl

hardAnalyticSubkernelProgramCannotPromoteClay :
  HardAnalyticSubkernelProgram →
  clayYangMillsPromoted ≡ false
hardAnalyticSubkernelProgramCannotPromoteClay =
  HardAnalyticSubkernelProgram.noClayPromotion
