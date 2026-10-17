module DASHI.Physics.Plasma.Phase243SOTABenchmarkAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.Phase243FreeBoundarySixExact as FB6
import DASHI.Physics.Plasma.Phase243ProducedFieldOrbitAtlasExact as Orbit

------------------------------------------------------------------------
-- P7: SOURCE-TYPED SOTA BENCHMARK ATLAS
--
-- This module registers comparison targets and their source roles.  It does
-- not copy numerical performance claims into DASHI authority.  A literature
-- reference can motivate a benchmark protocol; an actual comparison still
-- requires source-backed data under the same population, integrator,
-- normalization and configuration definitions used for the DASHI candidate.
------------------------------------------------------------------------

data SourceRole : Set where
  peerReviewedTheoryOrSimulation : SourceRole
  peerReviewedExperiment : SourceRole
  preprintTheoryOrSimulation : SourceRole
  repositoryArtifact : SourceRole
  companyStatement : SourceRole

record BenchmarkSource : Set where
  constructor benchmark-source
  field
    benchmarkName : String
    sourceIdentifier : String
    sourceRole : SourceRole
    authorityNote : String

open BenchmarkSource public

-- Direct-from-coil finite-beta free-boundary single-stage optimization.
SmietLoizuBalkovic2025 : BenchmarkSource
SmietLoizuBalkovic2025 =
  benchmark-source
    "finite-beta direct-from-coil single-stage stellarator optimization"
    "Phys. Plasmas 32, 012504 (2025); DOI 10.1063/5.0226402"
    peerReviewedTheoryOrSimulation
    "Method/source authority for direct-from-coil finite-beta free-boundary optimization; does not become evidence that a Phase243 candidate satisfies equilibrium."

-- Quasi-single-stage boundary/coil co-optimization.
YuXieLiuZhu2026 : BenchmarkSource
YuXieLiuZhu2026 =
  benchmark-source
    "quasi-single-stage optimization for advanced stellarators"
    "arXiv:2608.03122"
    preprintTheoryOrSimulation
    "Method/source authority for coil-feasibility-aware boundary optimization; any numerical values remain source claims until separately acquired and normalized."

-- Reactor-relevant QI benchmark with divertor-compatible edge islands and coils.
CIEMATQI4X2025 : BenchmarkSource
CIEMATQI4X2025 =
  benchmark-source
    "CIEMAT-QI4X reactor-relevant quasi-isodynamic configuration"
    "arXiv:2512.08825"
    preprintTheoryOrSimulation
    "Benchmark-candidate authority for a coil-realizable quasi-isodynamic reactor configuration; no same-object equality with DASHI candidates is implied."

-- Maximum-J target benchmark.
MaximumJ2023 : BenchmarkSource
MaximumJ2023 =
  benchmark-source
    "maximum-J property in quasi-isodynamic stellarators"
    "arXiv:2311.14439"
    preprintTheoryOrSimulation
    "Benchmark-candidate authority for maximum-J trapped-particle optimization; maximum-J is distinct from the Phase243 zero-bounce target."

-- Reactor transport benchmark including inward turbulent particle transport.
SQuIDTau2026 : BenchmarkSource
SQuIDTau2026 =
  benchmark-source
    "SQuID-tau quasi-isodynamic max-J stellarator"
    "Phys. Rev. E 113, 045215 (2026); DOI 10.1103/3q3b-q8nj"
    peerReviewedTheoryOrSimulation
    "Benchmark-candidate authority for reactor transport with turbulent particle pinch; does not transfer gyrokinetic or reactor performance to DASHI artifacts."

-- Particle-transport optimization showing passing-electron / mirror-ratio relevance.
ParticleTransportQI2026 : BenchmarkSource
ParticleTransportQI2026 =
  benchmark-source
    "optimized particle transport in quasi-isodynamic stellarators"
    "Phys. Rev. E 113, L043204 (2026); DOI 10.1103/fbbl-ps5l"
    peerReviewedTheoryOrSimulation
    "Benchmark-candidate authority for particle-transport optimization; useful because zero-bounce design must still survive turbulent particle and energy transport."

-- Coil engineering reference.
AugmentedLagrangianCoils2026 : BenchmarkSource
AugmentedLagrangianCoils2026 =
  benchmark-source
    "stellarator coils for future fusion reactors via augmented Lagrangian optimization"
    "Phys. Rev. Lett. 137, 065101 (2026); DOI 10.1103/n7gk-922h"
    peerReviewedTheoryOrSimulation
    "Engineering-method authority for constrained coil optimization; it does not certify Phase243 coil feasibility."

record SameNormalizationBenchmark
    (candidate : FB6.Candidate6) : Set₁ where
  constructor same-normalization-benchmark
  field
    dashRow : Orbit.ProducedFieldOrbitRow candidate
    source : BenchmarkSource

    externalConfigurationIdentityReceipt : Set
    externalPopulationDefinitionReceipt : Set
    externalFieldOrEquilibriumReceipt : Set
    externalOrbitOrTransportDataReceipt : Set

    samePopulationReceipt : Set
    samePitchRadiusEnergyDomainReceipt : Set
    sameIntegratorOrValidatedConversionReceipt : Set
    sameNormalizationReceipt : Set
    sameMetricDefinitionReceipt : Set

    mirrorTurningComparisonReceipt : Set
    trappedFractionComparisonReceipt : Set
    parallelInvariantComparisonReceipt : Set
    driftComparisonReceipt : Set
    effectiveRippleComparisonReceipt : Set
    finiteOrbitWidthComparisonReceipt : Set
    energeticParticleComparisonReceipt : Set

    benchmarkProvenance : String

open SameNormalizationBenchmark public

record SOTABenchmarkBoundary : Set where
  constructor sota-benchmark-boundary
  field
    sourceCitationAlonePaysComparison : Bool
    sourceCitationAlonePaysComparisonIsFalse : sourceCitationAlonePaysComparison ≡ false
    sharedMetricNameImpliesSharedNormalization : Bool
    sharedMetricNameImpliesSharedNormalizationIsFalse :
      sharedMetricNameImpliesSharedNormalization ≡ false
    maximumJIsSameClaimAsZeroBounce : Bool
    maximumJIsSameClaimAsZeroBounceIsFalse : maximumJIsSameClaimAsZeroBounce ≡ false
    coilRealizabilitySourceProvesDashCoils : Bool
    coilRealizabilitySourceProvesDashCoilsIsFalse : coilRealizabilitySourceProvesDashCoils ≡ false
    literaturePerformanceMayBecomeArtifactAuthority : Bool
    literaturePerformanceMayBecomeArtifactAuthorityIsFalse :
      literaturePerformanceMayBecomeArtifactAuthority ≡ false

canonicalSOTABenchmarkBoundary : SOTABenchmarkBoundary
canonicalSOTABenchmarkBoundary =
  sota-benchmark-boundary
    false refl
    false refl
    false refl
    false refl
    false refl

benchmarkRule : String
benchmarkRule =
  "P7 may say same-or-better only after acquiring the reference data required to instantiate SameNormalizationBenchmark. The citation itself supplies source identity/authority, not a DASHI numerical receipt. Missing reference coordinates remain missing rather than being reconstructed from narrative proximity."
