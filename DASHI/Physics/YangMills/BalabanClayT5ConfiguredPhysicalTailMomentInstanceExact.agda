module DASHI.Physics.YangMills.BalabanClayT5ConfiguredPhysicalTailMomentInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanClayT5BoundaryContinuumMomentMeasureExact as Primitive

------------------------------------------------------------------------
-- Configured quantitative T5 instance.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions II", Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Relationship: the physical leaves below are boundary-crossing cancellation,
-- one-step RG localization, marked-activity moment control and projective
-- consistency.  Their numerical tail is no longer abstract: every occurrence
-- uses the configured quarter-times-half-power sequence.
------------------------------------------------------------------------

quarter half : ℚ
quarter = + 1 / 4
half = + 1 / 2

finiteDyadicTail : Nat → Nat → ℚ
finiteDyadicTail depth zero = 0ℚ
finiteDyadicTail depth (suc count) =
  Tail.rootedShellTail depth + finiteDyadicTail (suc depth) count

configuredInfiniteTailMajorant : Nat → ℚ
configuredInfiniteTailMajorant depth = half * Tail.powHalf depth

finiteDyadicTailStep : ∀ depth count →
  finiteDyadicTail depth (suc count)
  ≡ Tail.rootedShellTail depth + finiteDyadicTail (suc depth) count
finiteDyadicTailStep depth count = refl

configuredTailMajorantStep : ∀ depth →
  configuredInfiniteTailMajorant depth
  ≡ Tail.rootedShellTail depth + configuredInfiniteTailMajorant (suc depth)
configuredTailMajorantStep depth = ℚRing.solve-∀

record PhysicalBoundaryCrossingInstance
    (Cutoff Volume Observable Cluster : Set) : Set₁ where
  field
    observableSupportDistanceToBoundary : Volume → Observable → Nat
    clusterDiameter : Cluster → Nat
    shellIndex : Cluster → Nat
    clusterWeight : Cutoff → Volume → Cluster → ℚ

    contributesToBoundaryDifference :
      Cutoff → Volume → Observable → Cluster → Set

    clusterDifferenceSupportedOnBoundaryCrossingClusters :
      ∀ cutoff volume observable cluster →
      contributesToBoundaryDifference cutoff volume observable cluster → Set

    boundaryCrossingClusterDiameterAtLeastDistance :
      ∀ cutoff volume observable cluster →
      contributesToBoundaryDifference cutoff volume observable cluster →
      Set

    boundaryCrossingClusterRootedShellInjection :
      ∀ cutoff volume observable cluster →
      contributesToBoundaryDifference cutoff volume observable cluster → Set

    rootedShellWeightBound : ∀ cutoff volume observable depth → Set

    finiteExpectation thermodynamicExpectation :
      Cutoff → Volume → Observable → ℚ
    absoluteDifference : ℚ → ℚ → ℚ

    expectationDifferenceExpansionExact : ∀ cutoff volume observable → Set
    boundaryCrossingActivityTailBound : ∀ cutoff volume observable →
      absoluteDifference
        (finiteExpectation cutoff volume observable)
        (thermodynamicExpectation cutoff volume observable)
      ≤ Tail.rootedShellTail
          (observableSupportDistanceToBoundary volume observable)

    supportDistanceEscapesWithVolume : ∀ cutoff observable depth → Set
    halfPowerVanishes : Set

open PhysicalBoundaryCrossingInstance public

asBoundaryEscapeClusterData :
  ∀ {Cutoff Volume Observable Cluster} →
  PhysicalBoundaryCrossingInstance Cutoff Volume Observable Cluster →
  Primitive.BoundaryEscapeClusterData Cutoff Volume Observable Cluster ℚ
asBoundaryEscapeClusterData dataSet = record
  { observableSupportDistanceToBoundary = observableSupportDistanceToBoundary dataSet
  ; clusterDiameter = clusterDiameter dataSet
  ; shellIndex = shellIndex dataSet
  ; clusterWeight = clusterWeight dataSet
  ; boundaryTail = Tail.rootedShellTail
  ; ClusterContributesToBoundaryDifference = contributesToBoundaryDifference dataSet
  ; clusterDifferenceSupportedOnBoundaryCrossingClusters =
      clusterDifferenceSupportedOnBoundaryCrossingClusters dataSet
  ; boundaryCrossingClusterDiameterAtLeastDistance =
      boundaryCrossingClusterDiameterAtLeastDistance dataSet
  ; boundaryCrossingClusterRootedShellInjection =
      boundaryCrossingClusterRootedShellInjection dataSet
  ; configuredRootedShellBound = λ cutoff volume observable →
      rootedShellWeightBound dataSet cutoff volume observable
        (observableSupportDistanceToBoundary dataSet volume observable)
  ; boundaryCrossingActivityTailBound = boundaryCrossingActivityTailBound dataSet
  ; expectationDifference = λ cutoff volume observable →
      absoluteDifference dataSet
        (finiteExpectation dataSet cutoff volume observable)
        (thermodynamicExpectation dataSet cutoff volume observable)
  ; finiteVolumeExpectationDifferenceBound = λ cutoff volume observable →
      boundaryCrossingActivityTailBound dataSet cutoff volume observable
  ; boundaryTailVanishesWithVolume = λ cutoff observable →
      supportDistanceEscapesWithVolume dataSet cutoff observable
  ; boundaryConditionIndependence = λ cutoff observable →
      supportDistanceEscapesWithVolume dataSet cutoff observable
  }

record PhysicalContinuumDefectInstance (Observable : Set) : Set₁ where
  field
    blockedObservable : Nat → Observable → Observable
    expectation : Nat → Observable → ℚ
    oneStepDefect : Nat → Observable → ℚ

    blockedObservableConsistencyExact : ∀ cutoff observable → Set
    observableRenormalizationStepExact : ∀ cutoff observable → Set
    oneStepExpectationDefectExpansion : ∀ cutoff observable → Set
    oneStepDefectLocalizedToIrrelevantActivities : ∀ cutoff observable → Set

    oneStepDefectBelowRootedTail : ∀ cutoff observable →
      oneStepDefect cutoff observable ≤ Tail.rootedShellTail cutoff

    expectationDifferenceIsDefect : ∀ cutoff observable → Set
    finiteTailControlsTelescopingDifference : ∀ cutoff count observable → Set
    continuumDefectLimitExists : ∀ observable → Set

open PhysicalContinuumDefectInstance public

asContinuumStepDefectData :
  ∀ {Observable} → PhysicalContinuumDefectInstance Observable →
  Primitive.ContinuumStepDefectData Nat Observable ℚ
asContinuumStepDefectData dataSet = record
  { blockedObservable = blockedObservable dataSet
  ; expectation = expectation dataSet
  ; oneStepDefect = oneStepDefect dataSet
  ; defectTail = λ cutoff _ → Tail.rootedShellTail cutoff
  ; blockedObservableConsistencyExact = blockedObservableConsistencyExact dataSet
  ; observableRenormalizationStepExact = observableRenormalizationStepExact dataSet
  ; oneStepExpectationDefectExpansion = oneStepExpectationDefectExpansion dataSet
  ; oneStepDefectLocalizedToIrrelevantActivities =
      oneStepDefectLocalizedToIrrelevantActivities dataSet
  ; oneStepDefectBoundByConfiguredTail = oneStepDefectBelowRootedTail dataSet
  ; continuumStepDefectSummable = λ observable → continuumDefectLimitExists dataSet observable
  ; continuumExpectationSequenceCauchy = λ observable → continuumDefectLimitExists dataSet observable
  ; diagonalVolumeChoice = λ cutoff → suc cutoff
  ; diagonalVolumeChoiceDominatesBoundaryTail = λ cutoff observable →
      finiteTailControlsTelescopingDifference dataSet cutoff (suc cutoff) observable
  }

record PhysicalExponentialMomentInstance
    (Observable : Set) : Set₁ where
  field
    absoluteObservable : Observable → Observable
    exponentialObservable : ℚ → Observable → Observable
    powerObservable : Nat → Observable → Observable
    expectation : Nat → Observable → ℚ

    lambda : Observable → ℚ
    singleScaleBound uniformBound : Observable → ℚ

    singleScaleInsertionActivityExpansion : ∀ cutoff observable → Set
    momentGeneratingActivitySmallness : ∀ cutoff observable → Set
    singleScaleExponentialMomentBound : ∀ cutoff observable → Set

    multiscaleMomentCost : Nat → Observable → ℚ
    multiscaleExponentialMomentRecursion : ∀ cutoff observable → Set
    multiscaleMomentCostsSummable : ∀ observable → Set
    uniformExponentialMomentBound : ∀ observable → Set

    factorial : Nat → ℚ
    powerBelowFactorialTimesExponential : ∀ degree observable → Set

    reflectedProduct : Observable → Observable → Observable
    reflectedProductYoungBound : ∀ left right → Set
    reflectedProductExponentialMomentBound : ∀ left right → Set
    uniformIntegrabilityOfReflectedProducts : ∀ left right → Set

open PhysicalExponentialMomentInstance public

record PhysicalMarginalMeasureInstance
    (Dimension Marginal Measure Observable Index : Set) : Set₁ where
  field
    finiteDimensionalMarginal : Dimension → Marginal
    momentOrder : Dimension → Nat
    momentBound radius tailProbability : Dimension → ℚ

    uniformMomentImpliesMarginalTailBound : ∀ dimension → Set
    finiteDimensionalMarginalTight : ∀ dimension → Set
    simultaneousFiniteFamilyTightness : ∀ dimension → Set
    gaugeInvariantMarginalTightness : ∀ dimension → Set

    prokhorovSubsequence : Measure
    prokhorovSubsequenceExists : Set

    marginal : Index → Marginal
    restrictMarginal : Index → Index → Marginal → Marginal
    continuumMeasure : Measure

    finiteMarginalRestrictionExact : ∀ lower upper → Set
    blockingCompatibilityOfMarginals : ∀ lower upper → Set
    projectiveFamilyConsistency : ∀ lower upper → Set
    subsequenceLimitPreservesConsistency : ∀ lower upper → Set
    kolmogorovOrProjectiveLimitMeasureExists : Set

    cylinderExpectation : Measure → Observable → ℚ
    clusterDecayDeterminesCylinderExpectations : Set
    twoContinuumLimitsAgreeOnCylinderAlgebra : ∀ left right → Set
    cylinderAlgebraMeasureDetermining : Set
    continuumMeasureUniquenessFromClustering : Set

open PhysicalMarginalMeasureInstance public

asFiniteMarginalTightnessData :
  ∀ {Dimension Marginal Measure Observable Index} →
  PhysicalMarginalMeasureInstance Dimension Marginal Measure Observable Index →
  Primitive.FiniteMarginalTightnessData Dimension Marginal Measure ℚ
asFiniteMarginalTightnessData dataSet = record
  { finiteDimensionalMarginal = finiteDimensionalMarginal dataSet
  ; momentOrder = momentOrder dataSet
  ; momentBound = momentBound dataSet
  ; radius = radius dataSet
  ; tailProbability = tailProbability dataSet
  ; uniformMomentImpliesMarginalTailBound = uniformMomentImpliesMarginalTailBound dataSet
  ; finiteDimensionalMarginalTight = finiteDimensionalMarginalTight dataSet
  ; simultaneousFiniteFamilyTightness = simultaneousFiniteFamilyTightness dataSet
  ; gaugeInvariantMarginalTightness = gaugeInvariantMarginalTightness dataSet
  ; prokhorovSubsequence = prokhorovSubsequence dataSet
  ; prokhorovSubsequenceExists = prokhorovSubsequenceExists dataSet
  }

asProjectiveContinuumMeasureData :
  ∀ {Dimension Marginal Measure Observable Index} →
  PhysicalMarginalMeasureInstance Dimension Marginal Measure Observable Index →
  Primitive.ProjectiveContinuumMeasureData Index Marginal Measure Observable ℚ
asProjectiveContinuumMeasureData dataSet = record
  { marginal = marginal dataSet
  ; restrictMarginal = restrictMarginal dataSet
  ; continuumMeasure = continuumMeasure dataSet
  ; finiteMarginalRestrictionExact = finiteMarginalRestrictionExact dataSet
  ; blockingCompatibilityOfMarginals = blockingCompatibilityOfMarginals dataSet
  ; projectiveFamilyConsistency = projectiveFamilyConsistency dataSet
  ; subsequenceLimitPreservesConsistency = subsequenceLimitPreservesConsistency dataSet
  ; kolmogorovOrProjectiveLimitMeasureExists =
      kolmogorovOrProjectiveLimitMeasureExists dataSet
  ; cylinderExpectation = cylinderExpectation dataSet
  ; clusterDecayDeterminesCylinderExpectations =
      clusterDecayDeterminesCylinderExpectations dataSet
  ; twoContinuumLimitsAgreeOnCylinderAlgebra =
      twoContinuumLimitsAgreeOnCylinderAlgebra dataSet
  ; cylinderAlgebraMeasureDetermining = cylinderAlgebraMeasureDetermining dataSet
  ; continuumMeasureUniquenessFromClustering =
      continuumMeasureUniquenessFromClustering dataSet
  }

configuredFiniteDyadicTailLevel : ProofLevel
configuredFiniteDyadicTailLevel = machineChecked

physicalBoundaryAndContinuumAdapterLevel : ProofLevel
physicalBoundaryAndContinuumAdapterLevel = machineChecked

physicalMomentMarginalAdapterLevel : ProofLevel
physicalMomentMarginalAdapterLevel = machineChecked

literalClusterMomentMeasureInputsLevel : ProofLevel
literalClusterMomentMeasureInputsLevel = conditional
