module DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; _+_; _≤_)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (_∈_)

import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalRootedShellInjectionExact as Shell
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Physical cluster expansion through moment/tightness/projective limits.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci, "Cluster Expansion for Abstract Polymer
-- Models. New Bounds from an Old Approach", Communications in Mathematical
-- Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2; arXiv:math-ph/0605041.
------------------------------------------------------------------------

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ values) = value + sumℚ values

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

record FiniteVolumeClusterExpansion
    (Volume Boundary Observable Polymer Cluster : Set) : Set₁ where
  field
    polymers : Volume → List Polymer
    clusters : Volume → List Cluster
    clusterPolymers : Cluster → List Polymer

    compatible : Polymer → Polymer → Set
    connectedCluster : Cluster → Set
    clusterCoefficient : Cluster → ℚ
    activity : Boundary → Polymer → ℚ
    observableInsertion : Observable → Cluster → ℚ

    partitionFunction : Volume → Boundary → ℚ
    observablePartitionFunction : Volume → Boundary → Observable → ℚ
    expectation : Volume → Boundary → Observable → ℚ

    clusterWeight : Boundary → Observable → Cluster → ℚ
    clusterWeightDefinition : ∀ (boundary : Boundary) (observable : Observable) (cluster : Cluster) → Set

    neutralObservable : Observable

    partitionClusterExpansionExact : ∀ volume boundary →
      partitionFunction volume boundary
      ≡ sumℚ (map (clusterWeight boundary neutralObservable) (clusters volume))

    observableClusterExpansionExact : ∀ volume boundary observable →
      observablePartitionFunction volume boundary observable
      ≡ sumℚ (map (clusterWeight boundary observable) (clusters volume))

    expectationAsPartitionRatioExact : ∀ (volume : Volume) (boundary : Boundary) (observable : Observable) → Set

    fpPolymerModel : FP.AbstractPolymerModel Polymer
    fpCriterion : FP.FernandezProcacciCriterion Polymer fpPolymerModel
    physicalActivitiesAgreeWithFPModel : ∀ (boundary : Boundary) (polymer : Polymer) → Set
    physicalClusterExpansionAbsolutelyConvergent : ∀ (volume : Volume) (boundary : Boundary) → Set
    partitionFunctionNonzero : ∀ (volume : Volume) (boundary : Boundary) → Set

open FiniteVolumeClusterExpansion public

record BoundaryCancellation
    {Volume Boundary Observable Polymer Cluster : Set}
    (expansion :
      FiniteVolumeClusterExpansion
        Volume Boundary Observable Polymer Cluster) : Set₁ where
  field
    clusterTouchesObservable : Observable → Cluster → Set
    clusterTouchesBoundary : Volume → Cluster → Set
    clusterInterior : Volume → Observable → Cluster → Set

    interiorClusterActivityBoundaryIndependent :
      ∀ volume observable cluster leftBoundary rightBoundary →
      clusterInterior volume observable cluster →
      clusterWeight expansion leftBoundary observable cluster
      ≡ clusterWeight expansion rightBoundary observable cluster

    clusterDifferenceCancelsUnlessBoundaryCrossing :
      ∀ (volume : Volume) (observable : Observable) (cluster : Cluster) (leftBoundary rightBoundary : Boundary) → Set

    boundaryDifferenceClusters :
      Volume → Observable → List Cluster

    boundaryDifferenceExpansionExact :
      ∀ (volume : Volume) (observable : Observable) (leftBoundary rightBoundary : Boundary) → Set

open BoundaryCancellation public

record BoundaryShellEstimate
    {Volume Boundary Observable Polymer Cluster Block : Set}
    (expansion :
      FiniteVolumeClusterExpansion
        Volume Boundary Observable Polymer Cluster)
    (cancellation : BoundaryCancellation expansion) : Set₁ where
  field
    geometry : Shell.BoundaryGeometry Block Volume Observable
    clusterCarrier : Shell.PhysicalClusterCarrier Block Polymer Cluster
    trace : Shell.CanonicalRootedTrace Block Polymer
    injection :
      Shell.PhysicalRootedShellInjection
        Block Volume Observable Polymer Cluster geometry clusterCarrier trace

    boundaryCrossingWitness : ∀ volume observable cluster →
      cluster ∈ boundaryDifferenceClusters cancellation volume observable →
      Shell.BoundaryCrossingWitness
        geometry clusterCarrier volume observable cluster

    boundaryClusterWeightInjectionBound : ∀ (volume : Volume) (observable : Observable) (depth : Nat) → Set
    boundaryExpectationDifferenceBelowRootedTail :
      ∀ (volume : Volume) (observable : Observable) (leftBoundary rightBoundary : Boundary) → Set
    boundaryTailVanishesWithVolume : ∀ (observable : Observable) → Set
    boundaryConditionIndependence : ∀ (observable : Observable) → Set

open BoundaryShellEstimate public

record OneStepRGDefect
    (Cutoff Observable DefectTerm : Set) : Set₁ where
  field
    nextCutoff : Cutoff → Cutoff
    cutoffDepth : Cutoff → Nat
    blockedObservable : Cutoff → Observable → Observable
    expectation : Cutoff → Observable → ℚ

    defectTerms : Cutoff → Observable → List DefectTerm
    defectTermValue : DefectTerm → ℚ
    oneStepDefect : Cutoff → Observable → ℚ

    blockedObservableConsistencyExact : ∀ (cutoff : Cutoff) (observable : Observable) → Set
    observableRGTransformExact : ∀ (cutoff : Cutoff) (observable : Observable) → Set

    oneStepDefectPolymerExpansionExact : ∀ cutoff observable →
      oneStepDefect cutoff observable
      ≡ sumℚ (map defectTermValue (defectTerms cutoff observable))

    relevantTermsCancelByRenormalizationCondition : ∀ (cutoff : Cutoff) (observable : Observable) → Set
    everyRemainingTermIrrelevant : ∀ (cutoff : Cutoff) (observable : Observable) (term : DefectTerm) → Set
    irrelevantNormGainBound : ∀ (cutoff : Cutoff) (observable : Observable) → Set

    oneStepDefectBelowQuarterHalfPower : ∀ (cutoff : Cutoff) (observable : Observable) →
      oneStepDefect cutoff observable
      ≤ Tail.rootedShellTail (cutoffDepth cutoff)

    expectationDifferenceIsDefect : ∀ (cutoff : Cutoff) (observable : Observable) → Set

open OneStepRGDefect public

finiteTail : Nat → Nat → ℚ
finiteTail depth zero = 0ℚ
finiteTail depth (suc count) =
  Tail.rootedShellTail depth + finiteTail (suc depth) count

finiteTailStepExact : ∀ depth count →
  finiteTail depth (suc count)
  ≡ Tail.rootedShellTail depth + finiteTail (suc depth) count
finiteTailStepExact depth count = refl

record ContinuumDefectClosure
    {Cutoff Observable DefectTerm : Set}
    (defect : OneStepRGDefect Cutoff Observable DefectTerm) : Set₁ where
  field
    iterateCutoff : Cutoff → Nat → Cutoff
    telescopingExpectationDifferenceExact : ∀ (cutoff : Cutoff) (count : Nat) (observable : Observable) → Set
    finiteTailControlsTelescopingDifference : ∀ (cutoff : Cutoff) (count : Nat) (observable : Observable) → Set
    cutoffDepthEscapes : Set
    geometricTailSummable : Set
    continuumExpectationCauchy : ∀ (observable : Observable) → Set
    continuumExpectationLimitExists : ∀ (observable : Observable) → Set
    diagonalVolumeChoice : Nat → Nat
    diagonalChoiceDominatesBoundaryAndScaleTails : ∀ (observable : Observable) → Set

open ContinuumDefectClosure public

record MarkedMomentClosure
    (Polymer Observable : Set)
    (model : FP.AbstractPolymerModel Polymer)
    (marked : FP.MarkedActivityData Polymer Observable model) : Set₁ where
  field
    fpClosure : FP.MarkedFernandezProcacciClosure Polymer Observable model marked

    exponentialMoment : Nat → Observable → ℚ
    singleScaleMomentBound : Observable → ℚ
    uniformMomentBound : Observable → ℚ

    singleScaleMomentFromMarkedPartitionRatio : ∀ (observable : Observable) → Set
    singleScaleExponentialMomentBound : ∀ (cutoff : Nat) (observable : Observable) → Set

    momentCost : Nat → Observable → ℚ
    momentCostBelowDyadicTail : ∀ (cutoff : Nat) (observable : Observable) →
      momentCost cutoff observable ≤ Tail.rootedShellTail cutoff

    multiscaleMomentRecursionLiteral : ∀ (cutoff : Nat) (observable : Observable) → Set
    momentCostsSummable : ∀ (observable : Observable) → Set
    uniformExponentialMomentBoundLiteral : ∀ (observable : Observable) → Set

    factorial : Nat → ℚ
    powerMoment : Nat → Nat → Observable → ℚ
    powerBelowFactorialExponentialLiteral : ∀ (degree : Nat) (observable : Observable) → Set

    reflectedProduct : Observable → Observable → Observable
    reflectedProductYoungBoundLiteral : ∀ (left right : Observable) → Set
    reflectedProductMomentBoundLiteral : ∀ (left right : Observable) → Set
    uniformIntegrabilityOfReflectedProductsLiteral : ∀ (left right : Observable) → Set

open MarkedMomentClosure public

record FiniteMarginalCompactness
    (Dimension Marginal Measure Observable Index : Set) : Set₁ where
  field
    finiteMarginal : Dimension → Marginal
    marginalMomentOrder : Dimension → Nat
    marginalMomentBound : Dimension → ℚ
    marginalRadius : Dimension → ℚ
    marginalTailProbability : Dimension → ℚ

    finiteFamilyMarkovTailBound : ∀ (dimension : Dimension) → Set
    finiteDimensionalMarginalTightLiteral : ∀ (dimension : Dimension) → Set
    gaugeInvariantMarginalTightLiteral : ∀ (dimension : Dimension) → Set

    weaklyConvergentSubsequence : Measure
    finiteDimensionalProkhorov : Set
    diagonalSubsequenceForCountableTestFamily : Set

    marginal : Index → Marginal
    restriction : Index → Index → Marginal → Marginal
    continuumMeasure : Measure

    finiteMarginalRestrictionExact : ∀ (lower upper : Index) → Set
    blockingCompatibilityOfMarginals : ∀ (lower upper : Index) → Set
    projectiveFamilyConsistencyLiteral : ∀ (lower upper : Index) → Set
    subsequenceLimitPreservesConsistency : ∀ (lower upper : Index) → Set
    projectiveLimitMeasureExists : Set

    cylinderExpectation : Measure → Observable → ℚ
    continuumCylinderExpectationUnique : Set
    twoLimitsAgreeOnCylinderFunctions : ∀ (left right : Measure) → Set
    cylinderAlgebraSeparatesMeasures : Set
    continuumMeasureUniquenessLiteral : Set

open FiniteMarginalCompactness public

record PhysicalT5Closure
    (Volume Boundary Observable Polymer Cluster Block Cutoff DefectTerm
     Dimension Marginal Measure Index : Set) : Set₂ where
  field
    clusterExpansion :
      FiniteVolumeClusterExpansion
        Volume Boundary Observable Polymer Cluster
    cancellation : BoundaryCancellation clusterExpansion
    shellEstimate : BoundaryShellEstimate {Block = Block} clusterExpansion cancellation

    defect : OneStepRGDefect Cutoff Observable DefectTerm
    continuum : ContinuumDefectClosure defect

    fpModel : FP.AbstractPolymerModel Polymer
    marked : FP.MarkedActivityData Polymer Observable fpModel
    moments : MarkedMomentClosure Polymer Observable fpModel marked

    compactness :
      FiniteMarginalCompactness Dimension Marginal Measure Observable Index

    finiteVolumeToContinuumCoherent : Set
    momentsControlChosenMarginals : Set
    continuumMeasureCarriesOSGramLimits : Set

open PhysicalT5Closure public

finiteDyadicTelescopingLevel : ProofLevel
finiteDyadicTelescopingLevel = machineChecked

physicalClusterExpansionAdapterLevel : ProofLevel
physicalClusterExpansionAdapterLevel = machineChecked

physicalMarkedMomentAdapterLevel : ProofLevel
physicalMarkedMomentAdapterLevel = machineChecked

physicalClusterCancellationInputsLevel : ProofLevel
physicalClusterCancellationInputsLevel = conditional

physicalRGDefectInputsLevel : ProofLevel
physicalRGDefectInputsLevel = conditional

physicalMomentCompactnessInputsLevel : ProofLevel
physicalMomentCompactnessInputsLevel = conditional
