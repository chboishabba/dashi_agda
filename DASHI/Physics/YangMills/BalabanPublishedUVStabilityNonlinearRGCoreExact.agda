module DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact where

------------------------------------------------------------------------
-- ROUND65: DO NOT RE-PROVE THE GENERIC 4D NONLINEAR RG CORE
--
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
-- DASHI CONTRIBUTION
--
-- Round64/early Round65 language made "uniform nonlinear one-step RG
-- stability" sound like a fresh Clay-scale theorem.  The repository already
-- has the correct source boundary: Bałaban CMP122 Theorem 1 is admitted as the
-- published completion of ultraviolet stability for four-dimensional pure
-- lattice gauge theory, and the finite beta-history bridge supplies its coupling
-- hypothesis.
--
-- Therefore the generic nonlinear RG stability mechanism is source-owned.  The
-- live physical work is narrower: identify the literal Wilson/ghost/Haar and
-- selected-background producers with the source-native CMP119/CMP122 carrier,
-- plus the finite signed G2 / one-loop / transfer seams.  Continuum construction
-- remains separate and is NOT inferred here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as CMP122
import DASHI.Physics.YangMills.BalabanCMP122PublishedFourDimensionalUVStabilityExact as Published

record PublishedNonlinearRGCore
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom Density : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    (flow : CMP122.ActiveEffectiveDensityFlow
      trajectory Mode Atom Density betaData history) : Set₁ where
  field
    uvStableFamily : Published.PublishedFourDimensionalUVStableFamily flow

open PublishedNonlinearRGCore public

activeScaleInvariantFromPublishedCore :
  ∀ {trajectory Mode Atom Density betaData history}
    {flow : CMP122.ActiveEffectiveDensityFlow
      trajectory Mode Atom Density betaData history} →
    (core : PublishedNonlinearRGCore flow) →
    (scale : Nat) →
    (active : History.ActiveScale history scale) →
  CMP122.ActiveSection2Invariant flow
    (Published.publishedTheorem1 (uvStableFamily core))
    scale active
activeScaleInvariantFromPublishedCore core =
  Published.publishedUVStabilityAtActiveScale (uvStableFamily core)

publishedNonlinearRGCoreAssembly :
  ∀ {trajectory Mode Atom Density betaData history}
    (flow : CMP122.ActiveEffectiveDensityFlow
      trajectory Mode Atom Density betaData history) →
  CMP122.ActiveBalaban1989Theorem1Witness flow →
  PublishedNonlinearRGCore flow
publishedNonlinearRGCoreAssembly flow theorem1 = record
  { uvStableFamily =
      Published.assemblePublishedFourDimensionalUVStableFamily flow theorem1
  }

publishedFourDimensionalNonlinearRGCoreLevel : ProofLevel
publishedFourDimensionalNonlinearRGCoreLevel = standardImported

finiteHistoryToPublishedCoreCompilerLevel : ProofLevel
finiteHistoryToPublishedCoreCompilerLevel = machineChecked

-- Remaining physical seam: literal same-object identification of the active
-- Wilson/ghost/Haar selected-background RG state with the CMP119/CMP122 flow.
literalPhysicalStateToPublishedRGCarrierLevel : ProofLevel
literalPhysicalStateToPublishedRGCarrierLevel = conditional
