module DASHI.Physics.YangMills.BalabanCMP122PublishedFourDimensionalUVStabilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- SOURCE-SCOPE NOTE
--
-- CMP122 II states its Theorem 1 as completion of ultraviolet stability for
-- four-dimensional pure lattice gauge theories.  That published theorem is
-- therefore stronger than a generic one-step RG lemma, but it is NOT by itself
-- a construction of continuum Schwinger functions, an Osterwalder--Schrader
-- reconstruction theorem, a non-Gaussianity theorem, or a cutoff-uniform
-- physical mass gap.
--
-- DASHI CONTRIBUTION
--
-- Make this boundary impossible to blur in the dependency graph.  Combine the
-- machine-checked finite beta history coupling hypothesis with the imported
-- CMP122 theorem witness into ONE finite-cutoff UV-stability family.  Every
-- active-scale Section-2 invariant is then projected from that family.  The
-- later continuum/OS/clustering producers remain separate proof levels rather
-- than being hidden inside the phrase "UV stability".
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as CMP122

record PublishedFourDimensionalUVStableFamily
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom Density : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    (flow : CMP122.ActiveEffectiveDensityFlow
      trajectory Mode Atom Density betaData history) : Set₁ where
  field
    couplingHypothesis : CMP122.ActiveTheorem1CouplingHypothesis flow
    publishedTheorem1 : CMP122.ActiveBalaban1989Theorem1Witness flow

open PublishedFourDimensionalUVStableFamily public

assemblePublishedFourDimensionalUVStableFamily :
  ∀ {trajectory Mode Atom Density betaData history}
    (flow : CMP122.ActiveEffectiveDensityFlow
      trajectory Mode Atom Density betaData history) →
  CMP122.ActiveBalaban1989Theorem1Witness flow →
  PublishedFourDimensionalUVStableFamily flow
assemblePublishedFourDimensionalUVStableFamily flow theorem1 = record
  { couplingHypothesis =
      CMP122.finiteModeHistorySuppliesTheorem1CouplingHypothesis flow
  ; publishedTheorem1 = theorem1
  }

publishedUVStabilityAtActiveScale :
  ∀ {trajectory Mode Atom Density betaData history}
    {flow : CMP122.ActiveEffectiveDensityFlow
      trajectory Mode Atom Density betaData history} →
  (family : PublishedFourDimensionalUVStableFamily flow) →
  (scale : Nat) →
  (active : History.ActiveScale history scale) →
  CMP122.ActiveSection2Invariant flow
    (publishedTheorem1 family)
    scale active
publishedUVStabilityAtActiveScale family scale active =
  CMP122.activeSection2Invariant
    (publishedTheorem1 family) scale active

cmp122FiniteHistoryToPublishedUVFamilyLevel : ProofLevel
cmp122FiniteHistoryToPublishedUVFamilyLevel = machineChecked

cmp122PublishedFourDimensionalUVStabilitySourceLevel : ProofLevel
cmp122PublishedFourDimensionalUVStabilitySourceLevel = standardImported

-- Exact post-Bałaban Clay boundary.  These are not conclusions of CMP122 II.
-- They remain independent physical producers even after the finite-cutoff UV
-- family above is instantiated literally.
continuumSchwingerFamilyConstructionLevel : ProofLevel
continuumSchwingerFamilyConstructionLevel = conditional

continuumOsterwalderSchraderAxiomsLevel : ProofLevel
continuumOsterwalderSchraderAxiomsLevel = conditional

continuumNonGaussianSurvivalLevel : ProofLevel
continuumNonGaussianSurvivalLevel = conditional

cutoffUniformPhysicalExponentialClusteringLevel : ProofLevel
cutoffUniformPhysicalExponentialClusteringLevel = conditional
