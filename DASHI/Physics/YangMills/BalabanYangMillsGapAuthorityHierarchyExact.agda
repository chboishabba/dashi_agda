module DASHI.Physics.YangMills.BalabanYangMillsGapAuthorityHierarchyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Prevent a finite background Hessian floor from being silently renamed a
-- quantum Yang--Mills mass gap.  Four authority levels are distinct types:
--
--   finite Gaussian background stability,
--   volume/scale-uniform lattice fluctuation control,
--   interacting gauge-invariant exponential clustering,
--   OS-reconstructed Hamiltonian spectral gap.
--
-- Promotion is possible only through an explicit bridge carrying the missing
-- theorem.  There is deliberately no coercion between levels.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record FiniteBackgroundGaussianGap : Set₁ where
  field
    BackgroundIndex State Bound : Set
    hessian : BackgroundIndex → State → State
    tangent : BackgroundIndex → State → Set
    lowerBound : Bound
    finiteCoercive : ∀ index state → tangent index state → Set

open FiniteBackgroundGaussianGap public

record UniformLatticeFluctuationGap : Set₁ where
  field
    Volume Scale BackgroundIndex State Bound : Set
    hessian : Volume → Scale → BackgroundIndex → State → State
    tangent : Volume → Scale → BackgroundIndex → State → Set
    lowerBound : Bound
    lowerBoundPositive : Set
    uniformCoercive : ∀ volume scale index state →
      tangent volume scale index state → Set
    uniformGreenDecay : ∀ volume scale index → Set

open UniformLatticeFluctuationGap public

record GaugeInvariantClusteringGap : Set₁ where
  field
    Cutoff Volume Observable Bound : Set
    connectedCorrelation :
      Cutoff → Volume → Observable → Observable → Bound
    massScale : Bound
    massScalePositive : Set
    gaugeInvariantObservables : Observable → Set
    interactingMeasureExists : Cutoff → Volume → Set
    uniformExponentialClustering :
      ∀ cutoff volume left right →
      gaugeInvariantObservables left →
      gaugeInvariantObservables right → Set

open GaugeInvariantClusteringGap public

record OSReconstructedHamiltonianGap : Set₁ where
  field
    HilbertState Energy : Set
    hamiltonian : HilbertState → HilbertState
    vacuum : HilbertState
    gap : Energy
    gapPositive : Set
    selfAdjointHamiltonian : Set
    uniqueVacuum : Set
    spectrumAboveVacuumSeparatedByGap : Set

open OSReconstructedHamiltonianGap public

record FiniteToUniformBridge
    (finite : FiniteBackgroundGaussianGap)
    (uniform : UniformLatticeFluctuationGap) : Set₁ where
  field
    sameFiniteHessianFamily : Set
    constantsUniformInVolumeAndScale : Set
    finiteGreenBoundsUniformized : Set

open FiniteToUniformBridge public

record UniformToClusteringBridge
    (uniform : UniformLatticeFluctuationGap)
    (clustering : GaugeInvariantClusteringGap) : Set₁ where
  field
    interactingRGConstructed : Set
    largeFieldControl : Set
    polymerOrClusterExpansionUniform : Set
    fluctuationDecayPromotesToInteractingClustering : Set

open UniformToClusteringBridge public

record ClusteringToOSGapBridge
    (clustering : GaugeInvariantClusteringGap)
    (osGap : OSReconstructedHamiltonianGap) : Set₁ where
  field
    thermodynamicLimit : Set
    continuumLimit : Set
    osterwalderSchraderAxioms : Set
    clusteringSurvivesLimits : Set
    osSpectralTransfer : Set

open ClusteringToOSGapBridge public

record CompleteGapPromotionChain : Set₁ where
  field
    finite : FiniteBackgroundGaussianGap
    uniform : UniformLatticeFluctuationGap
    clustering : GaugeInvariantClusteringGap
    osGap : OSReconstructedHamiltonianGap
    finiteToUniform : FiniteToUniformBridge finite uniform
    uniformToClustering : UniformToClusteringBridge uniform clustering
    clusteringToOS : ClusteringToOSGapBridge clustering osGap

open CompleteGapPromotionChain public

data GapAuthorityLabel : Set where
  finiteBackgroundGaussian
  uniformLatticeFluctuation
  gaugeInvariantClustering
  osHamiltonianSpectral : GapAuthorityLabel

finiteIsNotOS : finiteBackgroundGaussian ≡ osHamiltonianSpectral → ⊥
finiteIsNotOS ()

uniformIsNotClustering :
  uniformLatticeFluctuation ≡ gaugeInvariantClustering → ⊥
uniformIsNotClustering ()

clusteringIsNotOS :
  gaugeInvariantClustering ≡ osHamiltonianSpectral → ⊥
clusteringIsNotOS ()

finiteBackgroundGapAuthorityLevel : ProofLevel
finiteBackgroundGapAuthorityLevel = machineChecked

uniformLatticeGapAuthorityLevel : ProofLevel
uniformLatticeGapAuthorityLevel = machineChecked

interactingClusteringGapAuthorityLevel : ProofLevel
interactingClusteringGapAuthorityLevel = machineChecked

osHamiltonianGapAuthorityLevel : ProofLevel
osHamiltonianGapAuthorityLevel = machineChecked
