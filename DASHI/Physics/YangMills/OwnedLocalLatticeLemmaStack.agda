module DASHI.Physics.YangMills.OwnedLocalLatticeLemmaStack where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Core.Prelude using (_×_; _≥_; false)
open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _<ℝ_
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _*ℝ_
  ; -ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as AnisotropicDiameter
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.GraphCombinatorics as GraphCombinatorics
import DASHI.Physics.YangMills.LocalLatticeDischargePipeline as LocalLattice
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly

Nat : Set
Nat = ℕ

Polymer : Set
Polymer = AnisotropicDiameter.Polymer

SourcePolymer : Set
SourcePolymer = LargeField.SourcePolymer

SourceBlock : Set
SourceBlock = LargeField.SourceBlock

Edge : Set
Edge = AnisotropicDiameter.Edge

SmallFieldRegularity : Nat → Polymer → Set
SmallFieldRegularity = AnisotropicDiameter.SmallFieldRegularity

AdmissibleScale : Nat → Set
AdmissibleScale = GraphCombinatorics.admissibleScale

isEdgeOf : Edge → Nat → Polymer → Set
isEdgeOf = AnisotropicDiameter.isEdgeOf

postulate
  Skeleton : Set
  Decoration : Set

  localMetric : Nat → Polymer → Edge → ℝ
  backgroundMetric : Nat → Edge → ℝ
  metricPerturbation : Nat → Polymer → Edge → ℝ
  supEdgePerturbation : Nat → Polymer → ℝ
  ε33 : ℝ
  m33 : ℝ
  c-link : ℝ
  C33 : ℝ
  graphDiameter : Nat → Polymer → ℝ
  metricDiameter : Nat → Polymer → ℝ
  PositiveLinkWeightField : Nat → Polymer → Set

  encodePolymer : Polymer → Skeleton × Decoration
  decodePolymer : Skeleton × Decoration → Maybe Polymer
  countPolymersByDiameter : Nat → ℝ
  countSkeletonDecorationPairsByDiameter : Nat → ℝ
  reducedSkeletonAdmissible : Skeleton → Set
  reducedComplexity : Skeleton → Nat
  diamSkeleton : Skeleton → Nat
  diamPoly : Polymer → Nat
  countDecorations : Skeleton → ℝ
  countSkeletonsByDiameter : Nat → ℝ
  K06 : Nat
  B06 : Nat
  C06 : ℝ
  A06 : ℝ
  B06-base : ℝ
  C-poly : ℝ

  sourceBadBlock : Nat → SourcePolymer → SourceBlock → Set
  tailThreshold : Nat → ℝ
  sourceTailSize : Nat → SourcePolymer → SourceBlock → ℝ
  sourceTailIntegral : Nat → SourcePolymer → SourceBlock → ℝ
  sourceBlockWeight : Nat → SourcePolymer → SourceBlock → ℝ
  sourceBlockPenalty : Nat → SourcePolymer → SourceBlock → ℝ
  decayBase : ℝ
  sourceLargeFieldActivity : Nat → SourcePolymer → ℝ
  C10 : ℝ
  p10 : ℝ
  κ10 : ℝ
  c-tail : ℝ
  C-loc : ℝ
  product : List ℝ → ℝ
  sum : List ℝ → ℝ
  map : {A B : Set} → (A → B) → List A → List B
  supportBlocks : Nat → SourcePolymer → List SourceBlock
  sourceΦ-large : Nat → SourcePolymer → ℝ
  complexity : SourcePolymer → Nat
  sourceDiameter : SourcePolymer → Nat
  LargeFieldPolymer : Nat → SourcePolymer → Set
  expℝ : ℝ → ℝ
  c10 : ℝ
  C-diam : ℝ
  _^ℝ_ : ℝ → ℝ → ℝ
  shellContribution : Nat → ℝ
  C-ent : ℝ
  C-act : ℝ
  C-shell : ℝ
  activity : SourcePolymer → ℝ
  Summable : (Nat → ℝ) → Set

  fromNat : Nat → ℝ

P33LocalMetricDecomposition : Set
P33LocalMetricDecomposition =
  ∀ k X e →
  localMetric k X e ≡ backgroundMetric k e +ℝ metricPerturbation k X e

P33SmallFieldControlsMetricPerturbation : Set
P33SmallFieldControlsMetricPerturbation =
  ∀ k X →
  SmallFieldRegularity k X →
  supEdgePerturbation k X ≤ℝ ε33

P33BackgroundMetricUniformPositive : Set
P33BackgroundMetricUniformPositive =
  ∀ k e →
  AdmissibleScale k →
  m33 ≤ℝ backgroundMetric k e

P33PerturbationMargin : Set
P33PerturbationMargin = ε33 <ℝ m33

P33LocalMetricPositive : Set
P33LocalMetricPositive =
  ∀ k X e →
  SmallFieldRegularity k X →
  AdmissibleScale k →
  isEdgeOf e k X →
  0ℝ <ℝ localMetric k X e

P33LinkWeightMetricComparison : Set
P33LinkWeightMetricComparison =
  ∀ k X e →
  isEdgeOf e k X →
  c-link *ℝ localMetric k X e ≤ℝ AnisotropicDiameter.w-weight k e

P33PositiveLinkWeightFromMetric : Set
P33PositiveLinkWeightFromMetric =
  P33LocalMetricPositive →
  P33LinkWeightMetricComparison →
  ∀ k X e →
  SmallFieldRegularity k X →
  AdmissibleScale k →
  isEdgeOf e k X →
  0ℝ <ℝ AnisotropicDiameter.w-weight k e

P33GraphDistanceControlledByMetricLength : Set
P33GraphDistanceControlledByMetricLength =
  ∀ k X →
  SmallFieldRegularity k X →
  graphDiameter k X ≤ℝ metricDiameter k X

P33MetricDiameterControlledByPolymerDiameter : Set
P33MetricDiameterControlledByPolymerDiameter =
  ∀ k X →
  SmallFieldRegularity k X →
  metricDiameter k X ≤ℝ C33 *ℝ fromNat (diamPoly X)

postulate
  P33a1AnalyticDischargeFromMetricLemmas :
    P33LocalMetricDecomposition →
    P33SmallFieldControlsMetricPerturbation →
    P33BackgroundMetricUniformPositive →
    P33PerturbationMargin →
    P33LinkWeightMetricComparison →
    P33GraphDistanceControlledByMetricLength →
    P33MetricDiameterControlledByPolymerDiameter →
    AnisotropicDiameter.P33a1AnalyticDischargePackage

P06SkeletonDecorationEncoding : Set
P06SkeletonDecorationEncoding =
  ∀ X →
  Σ Skeleton
    (λ S →
      Σ Decoration
        (λ D →
          encodePolymer X ≡ (S , D)))

P06EncodeDecodeSound : Set
P06EncodeDecodeSound =
  ∀ X →
  decodePolymer (encodePolymer X) ≡ just X

P06EncodingInjective : Set
P06EncodingInjective =
  ∀ X Y →
  encodePolymer X ≡ encodePolymer Y →
  X ≡ Y

P06PolymerCountBoundedBySkeletonDecorationCount : Set
P06PolymerCountBoundedBySkeletonDecorationCount =
  ∀ n →
  countPolymersByDiameter n ≤ℝ countSkeletonDecorationPairsByDiameter n

P06SkeletonComplexityDiameterBound : Set
P06SkeletonComplexityDiameterBound =
  ∀ S →
  reducedSkeletonAdmissible S →
  fromNat (reducedComplexity S)
    ≤ℝ
  fromNat (K06) *ℝ fromNat (diamSkeleton S) +ℝ fromNat (B06)

P06DecorationMultiplicityBound : Set
P06DecorationMultiplicityBound =
  ∀ S →
  countDecorations S ≤ℝ (C06 ^ℝ fromNat (reducedComplexity S))

P06BoundedDegreeSkeletonAnimalCounting : Set
P06BoundedDegreeSkeletonAnimalCounting =
  ∀ n →
  countSkeletonsByDiameter n ≤ℝ (A06 *ℝ (B06-base ^ℝ fromNat n))

P06PolymerAnimalCounting : Set
P06PolymerAnimalCounting =
  ∀ n →
  countPolymersByDiameter n ≤ℝ (C-poly ^ℝ fromNat n)

postulate
  P06ModelLeafDischargeFromCounting :
    P06EncodeDecodeSound →
    P06EncodingInjective →
    P06SkeletonComplexityDiameterBound →
    P06DecorationMultiplicityBound →
    P06BoundedDegreeSkeletonAnimalCounting →
    Entropy.P06ModelLeafDischargePackage

-- Owned P10 local stack.
-- These abstract local theorem shapes are intended to mirror the now-owned
-- source-side chain in BalabanLargeFieldSuppression: tail control →
-- localisation/product suppression → coercivity in diameter →
-- canonical large-field decay.
P10CanonicalLargeFieldDecay : Set
P10CanonicalLargeFieldDecay =
  ∀ k X →
  LargeFieldPolymer k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  C10 *ℝ expℝ (-ℝ p10) *ℝ expℝ (-ℝ (κ10 *ℝ fromNat (sourceDiameter X)))

P10BadBlockGivesTailLowerBound : Set
P10BadBlockGivesTailLowerBound =
  ∀ k X b →
  sourceBadBlock k X b →
  tailThreshold k ≤ℝ sourceTailSize k X b

P10GaussianTailIntegralSuppression : Set
P10GaussianTailIntegralSuppression =
  ∀ k X b →
  sourceBadBlock k X b →
  sourceTailIntegral k X b
    ≤ℝ
  expℝ (-ℝ (c-tail *ℝ sourceTailSize k X b))

P10BlockWeightBoundedByTailIntegral : Set
P10BlockWeightBoundedByTailIntegral =
  ∀ k X b →
  sourceBlockWeight k X b ≤ℝ sourceTailIntegral k X b

P10BlockWeightSuppression : Set
P10BlockWeightSuppression =
  ∀ k X b →
  sourceBadBlock k X b →
  sourceBlockWeight k X b
    ≤ℝ
  (decayBase ^ℝ sourceBlockPenalty k X b)

P10ActivityLocalisesToSupportProduct : Set
P10ActivityLocalisesToSupportProduct =
  ∀ k X →
  sourceLargeFieldActivity k X
    ≤ℝ
  C-loc *ℝ product (map (sourceBlockWeight k X) (supportBlocks k X))

P10ProductBlockWeightsSuppressed : Set
P10ProductBlockWeightsSuppressed =
  ∀ k X →
  product (map (sourceBlockWeight k X) (supportBlocks k X))
    ≤ℝ
  decayBase ^ℝ sourceΦ-large k X

P10ΦLargePenaltySum : Set
P10ΦLargePenaltySum =
  ∀ k X →
  sourceΦ-large k X
    ≡
  sum (map (sourceBlockPenalty k X) (supportBlocks k X))

P10PenaltySumCoerciveInComplexity : Set
P10PenaltySumCoerciveInComplexity =
  ∀ k X →
  LargeFieldPolymer k X →
  c10 *ℝ fromNat (complexity X) ≤ℝ sourceΦ-large k X

P10DiameterControlledByComplexity : Set
P10DiameterControlledByComplexity =
  ∀ X →
  fromNat (sourceDiameter X)
    ≤ℝ
  C-diam *ℝ fromNat (complexity X)

P10ΦLargeCoerciveInDiameter : Set
P10ΦLargeCoerciveInDiameter =
  ∀ k X →
  LargeFieldPolymer k X →
  κ10 *ℝ fromNat (sourceDiameter X) ≤ℝ sourceΦ-large k X

postulate
  P10LargeFieldSuppressionFromAnalyticLemmas :
    P10BlockWeightSuppression →
    P10ActivityLocalisesToSupportProduct →
    P10ProductBlockWeightsSuppressed →
    P10ΦLargeCoerciveInDiameter →
    P10CanonicalLargeFieldDecay

  P10LargeFieldSuppressionPackageFromCanonicalDecay :
    P10CanonicalLargeFieldDecay →
    ∀ k X →
    LargeField.P10LargeFieldSuppressionPackage k X

P07ShellCountingFromP06 : Set
P07ShellCountingFromP06 =
  ∀ n →
  countPolymersByDiameter n ≤ℝ (C-ent ^ℝ fromNat n)

P07ActivityShellDecayFromP10 : Set
P07ActivityShellDecayFromP10 =
  ∀ X →
  activity X ≤ℝ C-act *ℝ (decayBase ^ℝ fromNat (sourceDiameter X))

P09EntropyDecayRatioBelowOne : Set
P09EntropyDecayRatioBelowOne = C-ent *ℝ decayBase <ℝ 1ℝ

P07ShellContributionBound : Set
P07ShellContributionBound =
  ∀ n →
  shellContribution n
    ≤ℝ
  C-shell *ℝ ((C-ent *ℝ decayBase) ^ℝ fromNat n)

P07GeometricShellSummability : Set
P07GeometricShellSummability =
  (C-ent *ℝ decayBase <ℝ 1ℝ) →
  Summable shellContribution

record P07P09KPSummabilityPackage : Set₁ where
  field
    shellCountingFromP06 :
      ∀ n →
      countPolymersByDiameter n ≤ℝ (C-ent ^ℝ fromNat n)

    activityShellDecayFromP10 :
      ∀ X →
      activity X ≤ℝ C-act *ℝ (decayBase ^ℝ fromNat (sourceDiameter X))

    entropyDecayRatioBelowOne :
      C-ent *ℝ decayBase <ℝ 1ℝ

    shellContributionBound :
      ∀ n →
      shellContribution n
        ≤ℝ
      C-shell *ℝ ((C-ent *ℝ decayBase) ^ℝ fromNat n)

    geometricShellSummability :
      Summable shellContribution

    p07Reducer :
      Entropy.P07KPSummabilityReducer

    p09Margin :
      Entropy.P09EntropyMargin

    p09MarginDischarge :
      Entropy.P09EntropyMarginDischargePackage

P07P09KPSummabilityFromCountingDecayMargin :
  P07ShellCountingFromP06 →
  P07ActivityShellDecayFromP10 →
  P09EntropyDecayRatioBelowOne →
  P07ShellContributionBound →
  P07GeometricShellSummability →
  Entropy.P07KPSummabilityReducer →
  Entropy.P09EntropyMargin →
  Entropy.P09EntropyMarginDischargePackage →
  P07P09KPSummabilityPackage
P07P09KPSummabilityFromCountingDecayMargin
  shellCounting
  activityDecay
  ratio
  shellBound
  shellSummable
  p07
  p09
  margin =
  record
    { shellCountingFromP06 =
        shellCounting
    ; activityShellDecayFromP10 =
        activityDecay
    ; entropyDecayRatioBelowOne =
        ratio
    ; shellContributionBound =
        shellBound
    ; geometricShellSummability =
        shellSummable ratio
    ; p07Reducer =
        p07
    ; p09Margin =
        p09
    ; p09MarginDischarge =
        margin
    }

P08ExpPositive : Set
P08ExpPositive = GraphCombinatorics.ExpPositiveℝ

P08PositiveFiniteProduct : Set
P08PositiveFiniteProduct = GraphCombinatorics.PositiveProduct

P08PositiveDefiniteDeterminantPositive : Set
P08PositiveDefiniteDeterminantPositive =
  GraphCombinatorics.PositiveDefiniteDeterminantPositive

P08GaussianNormalizationPositive : Set
P08GaussianNormalizationPositive =
  GraphCombinatorics.GaussianNormalizationPositiveFromDet

P11ConstantsCloseAbsorption : Set
P11ConstantsCloseAbsorption =
  ∀ (C-entropy C-dec : Nat) →
  GraphCombinatorics.c-large ≥ C-entropy + C-dec

P08P11AbsorptionPackageFromRealAnalysis :
  P08ExpPositive →
  P08PositiveFiniteProduct →
  P08PositiveDefiniteDeterminantPositive →
  P08GaussianNormalizationPositive →
  P11ConstantsCloseAbsorption →
  (∀ k X → GraphCombinatorics.P08P11AbsorptionPackage k X)
P08P11AbsorptionPackageFromRealAnalysis
  expPositive
  positiveProduct
  determinantPositive
  gaussianPositive
  constantsClose
  k
  X =
  GraphCombinatorics.P08P11FromStandardPositivityAndConstants
    k
    X
    positiveProduct
    expPositive
    determinantPositive
    gaussianPositive
    constantsClose

LocalLatticeAnalyticDischargeFromOwnedLemmas :
  Entropy.BalabanP06MixedReducerPayload →
  LargeField.P10AnalyticLeaves →
  AnisotropicDiameter.P33a1AnalyticDischargePackage →
  P07P09KPSummabilityPackage →
  (∀ k X → GraphCombinatorics.P08P11AbsorptionPackage k X) →
  LocalLattice.NatPowerDecayMonotoneType →
  LocalLattice.ComplexityLowerBoundByDiameterForDecayType →
  LocalLattice.LocalLatticeAnalyticDischargePackage
-- The P10 input here is already the owned canonical large-field package from
-- BalabanLargeFieldSuppression; the remaining external authority boundary in
-- the local lattice package sits in P06/P11 and downstream RG/endpoint data.
LocalLatticeAnalyticDischargeFromOwnedLemmas
  p06
  p10
  p33
  p07p09
  p08p11
  natPowerDecay
  complexityDiameter =
  record
    { p06MixedReducerPayload =
        p06
    ; p10AnalyticLeaves =
        p10
    ; p33PerturbationStability =
        p33
    ; entropyDecayMargin =
        P07P09KPSummabilityPackage.p09MarginDischarge p07p09
    ; p08p11Positivity =
        p08p11
    ; natPowerDecay =
        natPowerDecay
    ; complexityDiameter =
        complexityDiameter
    ; noClayPromotion =
        refl
    }

StepVSpatialKPFromOwnedLocalLemmas :
  LocalLattice.LocalLatticeAnalyticDischargePackage →
  Assembly.StepVSpatialKPCertificate
StepVSpatialKPFromOwnedLocalLemmas =
  LocalLattice.LocalLatticeStepVFromAnalyticDischarge

postulate

  StepVImpliesDLRSmallness :
    Assembly.StepVSpatialKPCertificate →
    Assembly.DLRSmallness

  StepVImpliesA2 :
    Assembly.StepVSpatialKPCertificate →
    Assembly.AssumptionA2

  A2ImpliesB6Influence :
    Assembly.AssumptionA2 →
    Assembly.B6InfluenceBound

  B6InfluenceImpliesRGCauchy :
    Assembly.B6InfluenceBound →
    Assembly.RGCauchySummability

  DLRSmallnessAndCrossScaleToUniformLSI :
    Assembly.DLRSmallness →
    Assembly.CrossScaleBound →
    Assembly.UniformLSI

  UniformLSIImpliesSpectralGap :
    Assembly.UniformLSI →
    Assembly.LatticeSpectralGap

  SpectralGapImpliesExponentialClustering :
    Assembly.LatticeSpectralGap →
    Assembly.ExponentialClustering

  ExponentialClusteringImpliesFixedLatticeMassGap :
    Assembly.ExponentialClustering →
    Assembly.FixedLatticeMassGap

  FiniteVolumeMeasuresTight :
    (m : Assembly.FiniteVolumeGibbsMeasures) →
    Assembly.Tightness m

  UniquenessGivesFullInfiniteVolumeLimit :
    Assembly.InfiniteVolumeSubsequentialLimit →
    Assembly.UniqueInfiniteVolumeLimit →
    Assembly.InfiniteVolumeLimit

  MassGapSurvivesThermodynamicLimit :
    Assembly.FixedLatticeMassGap →
    Assembly.InfiniteVolumeExponentialClustering →
    Assembly.InfiniteVolumeMassGap

  MassGapSurvivesCutoffRemoval :
    Assembly.InfiniteVolumeMassGap →
    Assembly.ContinuumSubsequentialLimit →
    Assembly.ContinuumMassGap

  OSInputsFromContinuumLimit :
    Assembly.ContinuumMassGap →
    Assembly.OSReflectionPositivityPreserved →
    Assembly.EuclideanCovarianceRestored →
    Assembly.OSInputs

  WightmanTheoryFromOS :
    Assembly.OSInputs →
    Assembly.WightmanTheory

  PhysicalMassGapFromContinuumMassGap :
    Assembly.ContinuumMassGap →
    Assembly.WightmanTheory →
    Assembly.PhysicalMassGap

ownedLocalLatticeNoClayPromotion : clayYangMillsPromoted ≡ false
ownedLocalLatticeNoClayPromotion = refl
