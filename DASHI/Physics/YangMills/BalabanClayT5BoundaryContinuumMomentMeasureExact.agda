module DASHI.Physics.YangMills.BalabanClayT5BoundaryContinuumMomentMeasureExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
-- Relationship: connected cluster cancellation and thermodynamic locality.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
-- Relationship: convergent connected-polymer sums.
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions", Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions II", Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978
-- Relationship: continuum measure and reconstruction target after the physical
-- tails, moments and compactness inputs below are supplied.
------------------------------------------------------------------------

record BoundaryEscapeClusterData
    (Cutoff Volume Observable Cluster Scalar : Set) : Set₁ where
  field
    observableSupportDistanceToBoundary : Volume → Observable → Nat
    clusterDiameter shellIndex : Cluster → Nat
    clusterWeight : Cutoff → Volume → Cluster → Scalar
    boundaryTail : Nat → Scalar

    ClusterContributesToBoundaryDifference :
      Cutoff → Volume → Observable → Cluster → Set
    clusterDifferenceSupportedOnBoundaryCrossingClusters :
      ∀ cutoff volume observable cluster → Set

    boundaryCrossingClusterDiameterAtLeastDistance :
      ∀ cutoff volume observable cluster →
      ClusterContributesToBoundaryDifference cutoff volume observable cluster → Set

    boundaryCrossingClusterRootedShellInjection :
      ∀ cutoff volume observable cluster →
      ClusterContributesToBoundaryDifference cutoff volume observable cluster → Set

    configuredRootedShellBound : ∀ cutoff volume observable → Set
    boundaryCrossingActivityTailBound : ∀ cutoff volume observable → Set

    expectationDifference : Cutoff → Volume → Observable → Scalar
    finiteVolumeExpectationDifferenceBound : ∀ cutoff volume observable → Set
    boundaryTailVanishesWithVolume : ∀ cutoff observable → Set
    boundaryConditionIndependence : ∀ cutoff observable → Set

open BoundaryEscapeClusterData public

record ContinuumStepDefectData
    (Cutoff Observable Scalar : Set) : Set₁ where
  field
    blockedObservable : Cutoff → Observable → Observable
    expectation : Cutoff → Observable → Scalar
    oneStepDefect defectTail : Cutoff → Observable → Scalar

    blockedObservableConsistencyExact : ∀ cutoff observable → Set
    observableRenormalizationStepExact : ∀ cutoff observable → Set
    oneStepExpectationDefectExpansion : ∀ cutoff observable → Set
    oneStepDefectLocalizedToIrrelevantActivities : ∀ cutoff observable → Set
    oneStepDefectBoundByConfiguredTail : ∀ cutoff observable → Set

    continuumStepDefectSummable : ∀ observable → Set
    continuumExpectationSequenceCauchy : ∀ observable → Set

    diagonalVolumeChoice : Cutoff → Nat
    diagonalVolumeChoiceDominatesBoundaryTail : ∀ cutoff observable → Set

open ContinuumStepDefectData public

record ExponentialMomentPhysicalData
    (Cutoff Observable Scalar : Set) : Set₁ where
  field
    absoluteObservable : Observable → Observable
    exponentialObservable : Scalar → Observable → Observable
    powerObservable : Nat → Observable → Observable

    expectation : Cutoff → Observable → Scalar
    lambda : Observable → Scalar
    singleScaleBound uniformBound : Observable → Scalar

    singleScaleInsertionActivityExpansion : ∀ cutoff observable → Set
    momentGeneratingActivitySmallness : ∀ cutoff observable → Set
    singleScaleExponentialMomentBound : ∀ cutoff observable → Set
    multiscaleExponentialMomentRecursion : ∀ cutoff observable → Set
    uniformExponentialMomentBound : ∀ observable → Set

    factorial : Nat → Scalar
    multiply divide : Scalar → Scalar → Scalar
    powerBelowFactorialTimesExponential : ∀ degree observable → Set

    reflectedProduct : Observable → Observable → Observable
    reflectedProductYoungBound : ∀ left right → Set
    reflectedProductExponentialMomentBound : ∀ left right → Set
    uniformIntegrabilityOfReflectedProducts : ∀ left right → Set

open ExponentialMomentPhysicalData public

record FiniteMarginalTightnessData
    (Dimension Marginal Measure Scalar : Set) : Set₁ where
  field
    finiteDimensionalMarginal : Dimension → Marginal
    momentOrder : Dimension → Nat
    momentBound radius tailProbability : Dimension → Scalar

    uniformMomentImpliesMarginalTailBound : ∀ dimension → Set
    finiteDimensionalMarginalTight : ∀ dimension → Set
    simultaneousFiniteFamilyTightness : ∀ dimension → Set
    gaugeInvariantMarginalTightness : ∀ dimension → Set

    prokhorovSubsequence : Measure
    prokhorovSubsequenceExists : Set

open FiniteMarginalTightnessData public

record ProjectiveContinuumMeasureData
    (Index Marginal Measure Observable Scalar : Set) : Set₁ where
  field
    marginal : Index → Marginal
    restrictMarginal : Index → Index → Marginal → Marginal
    continuumMeasure : Measure

    finiteMarginalRestrictionExact : ∀ lower upper → Set
    blockingCompatibilityOfMarginals : ∀ lower upper → Set
    projectiveFamilyConsistency : ∀ lower upper → Set
    subsequenceLimitPreservesConsistency : ∀ lower upper → Set
    kolmogorovOrProjectiveLimitMeasureExists : Set

    cylinderExpectation : Measure → Observable → Scalar
    clusterDecayDeterminesCylinderExpectations : Set
    twoContinuumLimitsAgreeOnCylinderAlgebra : ∀ left right → Set
    cylinderAlgebraMeasureDetermining : Set
    continuumMeasureUniquenessFromClustering : Set

open ProjectiveContinuumMeasureData public

record LiteralT5PhysicalClosure
    (Cutoff Volume Observable Cluster Scalar Dimension Marginal Measure Index : Set) : Set₂ where
  field
    boundary : BoundaryEscapeClusterData Cutoff Volume Observable Cluster Scalar
    continuum : ContinuumStepDefectData Cutoff Observable Scalar
    moments : ExponentialMomentPhysicalData Cutoff Observable Scalar
    tightness : FiniteMarginalTightnessData Dimension Marginal Measure Scalar
    projective : ProjectiveContinuumMeasureData
      Index Marginal Measure Observable Scalar

    commonObservableBlockingConvention : Set
    commonContinuumCandidate : Set
    diagonalBoundaryAndScaleTailsCompatible : Set
    momentBoundsApplyToCylinderAlgebra : Set

open LiteralT5PhysicalClosure public

finiteVolumeExpectationCauchyFromBoundaryEscape =
  BoundaryEscapeClusterData.boundaryTailVanishesWithVolume

continuumExpectationCauchyFromSummableDefect =
  ContinuumStepDefectData.continuumExpectationSequenceCauchy

uniformIntegrabilityFromExponentialMoment =
  ExponentialMomentPhysicalData.uniformIntegrabilityOfReflectedProducts

continuumMeasureExistsFromTightProjectiveFamily =
  ProjectiveContinuumMeasureData.kolmogorovOrProjectiveLimitMeasureExists

continuumMeasureUniqueFromClustering =
  ProjectiveContinuumMeasureData.continuumMeasureUniquenessFromClustering

boundaryEscapeReductionLevel : ProofLevel
boundaryEscapeReductionLevel = machineChecked

continuumDefectReductionLevel : ProofLevel
continuumDefectReductionLevel = machineChecked

exponentialMomentReductionLevel : ProofLevel
exponentialMomentReductionLevel = machineChecked

measureCompactnessProjectiveReductionLevel : ProofLevel
measureCompactnessProjectiveReductionLevel = machineChecked

literalT5BoundaryDefectMomentMeasureInputsLevel : ProofLevel
literalT5BoundaryDefectMomentMeasureInputsLevel = conditional
