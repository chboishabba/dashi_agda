module DASHI.Physics.YangMills.BalabanCMP109CorrectedPatchMarginCrossProverExact where

------------------------------------------------------------------------
-- ROW A1: CORRECTED PATCH / MARGIN CROSS-PROVER SYNCHRONIZATION
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- CROSS-PROVER INPUT
--
-- The parallel Lean Row-A1 lane now proves, without sorry/axiom/unsafe:
--
--   * all-equal Wilson cubic Lorentz components vanish identically;
--   * at zero background momentum the equal-fluctuation-index component
--     vanishes at Brillouin-boundary momenta, including normalized 1/2;
--   * one fixed Fourier mode cannot produce a normalized volume-uniform floor;
--   * one positive-measure patch plus complement nonnegativity does produce a
--     Gaussian floor;
--   * the constrained first variation must be treated as V = W + Q + R, and a
--     lower bound on W alone loses an explicit |Q|+|R| error;
--   * five channelwise fourth-order majorants give betaInt >= - C_beta g^4;
--   * localized irrelevant memory is uniformly summable, but marginal memory
--     must remain a separate budget unless the source proves it vanishes;
--   * the current uniform margin therefore has the shape
--
--       b_patch
--       - C_beta gamma^4
--       - (C_H gamma / 2 + H_marg) B.
--
-- These are CROSS-PROVER results only in this Agda working tree.  Nothing below
-- upgrades a physical/source claim to machineChecked solely because Lean built.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact as Patch
import DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact as WQR
import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact as Debt

------------------------------------------------------------------------
-- Current source-facing corrected package
------------------------------------------------------------------------

record CMP109CorrectedPatchMarginSourcePackage : Set₁ where
  field
    -- Literal constrained Gaussian first variation.
    literalWilsonHessianVariation : Set
    literalAveragingConstraintVariation : Set
    literalGaugeProjectionVariation : Set
    literalWQRAssembly : Set

    -- One positive-measure patch for the SAME constrained first variation.
    literalMixedComponentPatch : Set
    literalQRErrorBudgetOnPatch : Set
    literalPatchGaussianFloor : Set

    -- Current-step nonlinear debt from the five literal physical channels.
    literalFiveChannelFourthOrderData : Set
    literalFiveChannelCoefficientTotal : Set

    -- Historical debt: irrelevant/localized plus separately declared marginal
    -- memory.  Do not infer H_marg = 0 from the localized-memory theorem.
    literalLocalizedMemoryCoefficient : Set
    literalMarginalMemoryBound : Set

    -- Same-object / same-trajectory coherence.
    sameLiteralCMP109BetaCoefficient : Set
    sameCouplingCeiling : Set
    sameDisplacementBudget : Set

    -- Corrected closing inequality:
    --   b_patch
    --   - C_beta gamma^4
    --   - (C_H gamma / 2 + H_marg) B > 0.
    correctedMarginPositive : Set

open CMP109CorrectedPatchMarginSourcePackage public

------------------------------------------------------------------------
-- Cross-prover theorem surfaces: intentionally non-promotable in Agda here
------------------------------------------------------------------------

cmp109WilsonCubicCornerDisqualificationCrossProverLevel : ProofLevel
cmp109WilsonCubicCornerDisqualificationCrossProverLevel = conditional

cmp109SingleModeUniformFloorNoGoCrossProverLevel : ProofLevel
cmp109SingleModeUniformFloorNoGoCrossProverLevel = conditional

cmp109QuarterPatchLowerBoundCrossProverLevel : ProofLevel
cmp109QuarterPatchLowerBoundCrossProverLevel = conditional

cmp109WQRInterferenceCrossProverLevel : ProofLevel
cmp109WQRInterferenceCrossProverLevel = conditional

cmp109CorrectedMarginCompilerCrossProverLevel : ProofLevel
cmp109CorrectedMarginCompilerCrossProverLevel = conditional

cmp109UniversalCoefficientCircularityAuditCrossProverLevel : ProofLevel
cmp109UniversalCoefficientCircularityAuditCrossProverLevel = conditional

------------------------------------------------------------------------
-- Literal/source blockers inherited from the source-facing Agda owners
------------------------------------------------------------------------

cmp109LiteralWilsonHessianVariationCurrentLevel : ProofLevel
cmp109LiteralWilsonHessianVariationCurrentLevel =
  WQR.cmp109LiteralWilsonHessianVariationLevel

cmp109LiteralAveragingConstraintVariationCurrentLevel : ProofLevel
cmp109LiteralAveragingConstraintVariationCurrentLevel =
  WQR.cmp109LiteralAveragingConstraintVariationLevel

cmp109LiteralGaugeProjectionVariationCurrentLevel : ProofLevel
cmp109LiteralGaugeProjectionVariationCurrentLevel =
  WQR.cmp109LiteralGaugeProjectionVariationLevel

cmp109LiteralWQRAssemblyCurrentLevel : ProofLevel
cmp109LiteralWQRAssemblyCurrentLevel = WQR.cmp109LiteralWQRAssemblyLevel

cmp109LiteralPositivePatchCurrentLevel : ProofLevel
cmp109LiteralPositivePatchCurrentLevel = Patch.cmp109LiteralGaussianPositivePatchLevel

cmp109LiteralFiveChannelCurrentLevel : ProofLevel
cmp109LiteralFiveChannelCurrentLevel =
  Debt.cmp109LiteralFiveChannelQuotientMajorantLevel

cmp109LiteralLocalizedMemoryCurrentLevel : ProofLevel
cmp109LiteralLocalizedMemoryCurrentLevel =
  Debt.cmp109LiteralIrrelevantMemoryInfluenceLevel

-- Newly explicit source seam after the Lean no-go: either prove the marginal
-- contribution vanishes/gets absorbed into the current local remainder, or give
-- a separate uniform H_marg bound.
cmp109LiteralMarginalMemoryBoundCurrentLevel : ProofLevel
cmp109LiteralMarginalMemoryBoundCurrentLevel = conditional

cmp109CorrectedPatchMarginSourcePackageLevel : ProofLevel
cmp109CorrectedPatchMarginSourcePackageLevel = conditional
