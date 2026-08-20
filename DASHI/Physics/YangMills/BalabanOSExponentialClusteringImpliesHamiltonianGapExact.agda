module DASHI.Physics.YangMills.BalabanOSExponentialClusteringImpliesHamiltonianGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in Mathematical
-- Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- O. Penrose and J. L. Lebowitz,
-- "On the Exponential Decay of Correlation Functions", Communications in
-- Mathematical Physics 39 (1974), 165--184. DOI: 10.1007/BF01614239.
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", second edition,
-- Springer, 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- DASHI CONTRIBUTION
--
-- Give the revised Clay cutset its exact theorem name.  The hard Yang--Mills
-- input is uniform physical exponential clustering of the continuum Schwinger
-- family.  Once OS reconstruction supplies the positive spectral
-- representation and observable overlap, the absence of positive spectral
-- mass below the clustering exponent is standard spectral calculus.
--
-- The underlying repository theorem already proves the finite contradiction:
-- a positive subgap mode supplies a slower spectral lower envelope while OS4
-- supplies a faster exponential upper envelope.  This file exposes that result
-- under the frontier name
--
--   OSExponentialClusteringImpliesHamiltonianGap
--
-- so the physical producer is not conflated with its standard closure.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

OSExponentialClusteringImpliesHamiltonianGap :
  ∀ {Measure Schwinger Observable Energy Bound}
    {closure : Limit.FiniteToContinuumOSClosure Measure Schwinger}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  Gap.OS4SpectralInterpretation closure spectrum →
  Limit.Clustered closure
    (Limit.schwinger closure (Limit.continuumMeasure closure)) →
  Gap.PositiveTransferGap spectrum
OSExponentialClusteringImpliesHamiltonianGap = Gap.positiveTransferGapFromOS4

osExponentialClusteringImpliesHamiltonianGapAdapterLevel : ProofLevel
osExponentialClusteringImpliesHamiltonianGapAdapterLevel = machineChecked

-- The spectral theorem / OS reconstruction used by the physical
-- OS4SpectralInterpretation is standard imported mathematics.  It is not a new
-- Yang--Mills estimate and therefore does not belong in the hard-producer count.
osSpectralRepresentationAndLaplaceSupportLevel : ProofLevel
osSpectralRepresentationAndLaplaceSupportLevel = standardImported

-- This remains the actual physical frontier input.
physicalUniformExponentialClusteringLevel : ProofLevel
physicalUniformExponentialClusteringLevel = conditional
