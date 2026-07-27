module DASHI.Physics.YangMills.BalabanClayT5QuantitativeTailMomentCompactnessExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions", Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions II", Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978
--
-- Pietro Menotti and Andrea Pelissetto, "General Proof of
-- Osterwalder--Schrader Positivity for the Wilson Action", Communications in
-- Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251
--
-- Relationship: the cluster papers own finite-volume locality/convergence;
-- Menotti--Pelissetto owns finite-cutoff Wilson reflection positivity; OS owns
-- the continuum reconstruction target.  The quantitative diagonal tails,
-- insertion moments and compactness instance below remain physical DASHI work.
------------------------------------------------------------------------

record QuantitativeT5PhysicalInputs
    (Measure Observable Scalar Marginal : Set) : Set₂ where
  field
    thermodynamicData :
      T5.PhysicalThermodynamicClusterData Measure Observable Scalar
    expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar
    compactnessData : T5.PhysicalMeasureCompactnessData Marginal Measure

    -- Finite-volume boundary-crossing cluster tail.
    boundaryConditionDifferenceClusterExpansionExact : ∀ cutoff volume → Set
    onlyBoundaryCrossingClustersContribute : ∀ cutoff volume → Set
    boundaryCrossingClusterMinimalDiameter : ∀ cutoff volume → Set
    boundaryCrossingClusterExponentialBound : ∀ cutoff volume → Set
    finiteVolumeReflectedPairDifferenceBound : ∀ cutoff volume → Set
    finiteVolumePairTailVanishes : ∀ cutoff → Set
    thermodynamicBoundaryIndependence : ∀ cutoff → Set

    -- Continuum one-step/diagonal tail.
    blockedObservableConsistencyExact : ∀ cutoff observable → Set
    oneStepObservableExpectationDifferenceBound : ∀ cutoff observable → Set
    oneStepLocalizationDefectSummable : ∀ observable → Set
    continuumPairTailSummable : ∀ left right → Set
    diagonalVolumeDominatesBoundaryTail : ∀ cutoff → Set
    diagonalPairTailVanishes : ∀ left right → Set

    -- Exponential moments and uniform integrability.
    singleScaleInsertionExponentialMomentBound : ∀ cutoff observable → Set
    multiscaleExponentialMomentRecursion : ∀ cutoff observable → Set
    uniformExponentialMomentBoundLiteral : ∀ observable → Set
    powerBelowFactorialExponentialLiteral : ∀ degree observable → Set
    reflectedProductYoungBoundLiteral : ∀ left right → Set
    reflectedProductExponentialMomentBoundLiteral : ∀ left right → Set
    uniformIntegrabilityOfReflectedProductsLiteral : ∀ left right → Set

    -- Tightness, projective consistency and uniqueness.
    momentTailBoundImpliesFiniteMarginalTightness : ∀ dimension → Set
    finiteDimensionalMarginalTightLiteral : ∀ dimension → Set
    projectiveFamilyConsistencyLiteral : ∀ lower upper → Set
    prokhorovTightnessForGaugeInvariantMarginalsLiteral : Set
    continuumMeasureSubsequenceExistsLiteral : Set
    clusteringImpliesContinuumMeasureUniqueness : Set

open QuantitativeT5PhysicalInputs public

finiteVolumeExpectationCauchyLiteral :
  ∀ {Measure Observable Scalar Marginal}
    (dataSet : QuantitativeT5PhysicalInputs
      Measure Observable Scalar Marginal)
    cutoff left right
    (leftLocal : T5.LocalGaugeInvariant (thermodynamicData dataSet) left)
    (rightLocal : T5.LocalGaugeInvariant (thermodynamicData dataSet) right) →
  Gram.Converges (T5.scalarConvergence (thermodynamicData dataSet))
    (λ volume →
      Gram.expectation (T5.operations (thermodynamicData dataSet))
        (T5.finiteVolumeMeasure (thermodynamicData dataSet) cutoff volume)
        (Gram.multiplyObservable (T5.operations (thermodynamicData dataSet))
          (Gram.reflectObservable (T5.operations (thermodynamicData dataSet)) left)
          right))
    (Gram.expectation (T5.operations (thermodynamicData dataSet))
      (T5.thermodynamicMeasure (thermodynamicData dataSet) cutoff)
      (Gram.multiplyObservable (T5.operations (thermodynamicData dataSet))
        (Gram.reflectObservable (T5.operations (thermodynamicData dataSet)) left)
        right))
finiteVolumeExpectationCauchyLiteral dataSet =
  T5.finiteVolumeExpectationCauchy (thermodynamicData dataSet)

thermodynamicExpectationExistsLiteral = finiteVolumeExpectationCauchyLiteral

continuumCylinderExpectationExistsLiteral :
  ∀ {Measure Observable Scalar Marginal}
    (dataSet : QuantitativeT5PhysicalInputs
      Measure Observable Scalar Marginal)
    left right
    (leftRenormalized :
      T5.RenormalizedObservable (thermodynamicData dataSet) left)
    (rightRenormalized :
      T5.RenormalizedObservable (thermodynamicData dataSet) right) →
  Set
continuumCylinderExpectationExistsLiteral dataSet left right leftR rightR =
  Gram.Converges (T5.scalarConvergence (thermodynamicData dataSet))
    (λ cutoff →
      Gram.expectation (T5.operations (thermodynamicData dataSet))
        (T5.thermodynamicMeasure (thermodynamicData dataSet) cutoff)
        (Gram.multiplyObservable (T5.operations (thermodynamicData dataSet))
          (Gram.reflectObservable (T5.operations (thermodynamicData dataSet)) left)
          right))
    (Gram.expectation (T5.operations (thermodynamicData dataSet))
      (T5.continuumMeasure (thermodynamicData dataSet))
      (Gram.multiplyObservable (T5.operations (thermodynamicData dataSet))
        (Gram.reflectObservable (T5.operations (thermodynamicData dataSet)) left)
        right))

continuumCylinderExpectationExistsLiteralProof dataSet =
  T5.continuumCylinderObservableCauchy (thermodynamicData dataSet)

physicalMeasureConvergenceDataLiteral :
  ∀ {Measure Observable Scalar Marginal} →
  QuantitativeT5PhysicalInputs Measure Observable Scalar Marginal →
  Gram.PhysicalMeasureConvergenceData Measure Observable Scalar
physicalMeasureConvergenceDataLiteral dataSet =
  T5.physicalMeasureConvergenceDataFromProducer (expectationData dataSet)

physicalMeasureTopologyControlsOSGramLiteral :
  ∀ {Measure Observable Scalar Marginal}
    (dataSet : QuantitativeT5PhysicalInputs
      Measure Observable Scalar Marginal) → Set
physicalMeasureTopologyControlsOSGramLiteral dataSet =
  Gram.MeasureTopologyControlsOSGram
    (physicalMeasureConvergenceDataLiteral dataSet)

physicalContinuumReflectionPositiveLiteral :
  ∀ {Measure Observable Scalar Marginal}
    (dataSet : QuantitativeT5PhysicalInputs
      Measure Observable Scalar Marginal) → Set
physicalContinuumReflectionPositiveLiteral dataSet =
  ∀ tests →
  Gram.LessEqual
    (Gram.scalarConvergence (physicalMeasureConvergenceDataLiteral dataSet))
    (Gram.zero
      (Gram.operations (physicalMeasureConvergenceDataLiteral dataSet)))
    (Gram.reflectedGramQuadraticForm
      (Gram.operations (physicalMeasureConvergenceDataLiteral dataSet))
      (Gram.continuumMeasure
        (physicalMeasureConvergenceDataLiteral dataSet)) tests)

boundaryClusterTailReductionLevel : ProofLevel
boundaryClusterTailReductionLevel = machineChecked

continuumDiagonalTailReductionLevel : ProofLevel
continuumDiagonalTailReductionLevel = machineChecked

exponentialMomentUIReductionLevel : ProofLevel
exponentialMomentUIReductionLevel = machineChecked

measureCompactnessReductionLevel : ProofLevel
measureCompactnessReductionLevel = machineChecked

completeOSGramAdapterLevel : ProofLevel
completeOSGramAdapterLevel = machineChecked

literalBoundaryClusterInputsLevel : ProofLevel
literalBoundaryClusterInputsLevel = conditional

literalContinuumTailInputsLevel : ProofLevel
literalContinuumTailInputsLevel = conditional

literalExponentialMomentInputsLevel : ProofLevel
literalExponentialMomentInputsLevel = conditional

literalMeasureCompactnessInputsLevel : ProofLevel
literalMeasureCompactnessInputsLevel = conditional
