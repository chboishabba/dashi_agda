module DASHI.Physics.YangMills.BalabanCMP109ReducedMarginSourceCutsetExact where

------------------------------------------------------------------------
-- ROW A1 REDUCED-MARGIN SOURCE CUTSET
--
-- Primary source:
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Constrained-propagator source:
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
--
-- CROSS-PROVER REDUCTION
--
-- The parallel Lean Row-A1 calculation now reduces the remaining source data
-- further, without closing Row A1:
--
--   A1a Gaussian floor:
--     on the project's transverse lattice symbol
--
--       G(p) = (1 / phat^2) (I - phat phat^T / phat^2),
--
--     choose the explicit corner momentum q = (0, 1/2, 0, 0).  In the
--     transverse mu = 0 direction the projector is the identity and phat^2=4,
--     so the reduced bubble entry satisfies exactly
--
--       M_00(q) = V_00(q) / 4.
--
--     Hence a source-derived uniform scalar
--
--       |V_00(q)| >= v > 0
--
--     yields the uniform Gaussian floor
--
--       betaZ_j >= v^2 / 32.
--
--   finite-g interaction debt:
--     a Cauchy majorant |a_(j,m)| <= A K^m and K gamma < 1 gives
--
--       |betaInt_j| <= (A / (1-K gamma)) g_j^rho
--
--     on g_j <= gamma.
--
--   history debt:
--     the final margin needs only
--
--       sum_{k<j} |R_(j,k)| <= D
--
--     uniformly.  A summable profile, average contraction of chain products,
--     or asymptotic contraction with finite summable excess can each produce D;
--     pointwise |J_i|<1 is sufficient but no longer the canonical requirement.
--
-- Therefore the current literal source numbers are
--
--       v, A, K, gamma, rho, D, B
--
-- and the source-facing margin is
--
--       v^2/32 - (A/(1-K gamma)) gamma^rho - D B > 0.
--
-- None of the project-lattice identities or debt lemmas below are promoted to
-- Agda theorem authority merely because they are proved in Lean.  This module
-- records the current exact dependency surface so the Agda graph cannot drift
-- back to stronger global requirements.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109UniformFloorSummableHistoryRefinementExact

------------------------------------------------------------------------
-- A1a: one literal first-variation scalar at one explicit corner momentum
------------------------------------------------------------------------

record CMP109LiteralCornerBubbleScalar
    (Scale Scalar : Set) : Set₁ where
  field
    -- Source-derived first background-variation component at the canonical
    -- project corner q=(0,1/2,0,0), transverse direction mu=0.
    firstVariation00AtCorner : Scale → Scalar

    v : Scalar
    AbsoluteValue : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    Positive : Scalar → Set

    vPositive : Positive v
    firstVariationUniformLowerBound : (scale : Scale) →
      LessEqual v (AbsoluteValue (firstVariation00AtCorner scale))

    -- Same-object/project-lattice obligations returned by the Lean calculation.
    cornerMomentumExistsAtEveryScale : Set
    cornerMomentumIsOnEveryEvenTorus : Set
    transverseProjectorIdentityInDirection0 : Set
    cornerPhatSquareEqualsFour : Set
    reducedBubble00EqualsFirstVariation00OverFour : Set

    -- Quantitative consequence in the project's normalization:
    -- betaZ_j >= v^2 / 32.
    gaussianFloorValue : Scalar
    gaussianFloorIsVSquaredOver32 : Set
    gaussianFloorUniformLowerBound : (scale : Scale) → Set

open CMP109LiteralCornerBubbleScalar public

------------------------------------------------------------------------
-- A1a finite-g interaction: Cauchy-majorant source data
------------------------------------------------------------------------

record CMP109LiteralCauchyInteractionDebt
    (Scale Scalar : Set) : Set₁ where
  field
    coupling : Scale → Scalar
    betaInteraction : Scale → Scalar

    A K gamma rho : Scalar

    Nonnegative : Scalar → Set
    LessEqual : Scalar → Scalar → Set
    StrictLess : Scalar → Scalar → Set

    trajectoryCouplingBound : (scale : Scale) → LessEqual (coupling scale) gamma
    sourceCauchyMajorant : Set
    KGammaStrictlyBelowOne : Set

    -- C_int = A/(1-K gamma), derived from the source Cauchy pair.
    interactionConstant : Scalar
    interactionConstantIsCauchySum : Set

    -- |betaInt_j| <= C_int g_j^rho, hence <= C_int gamma^rho.
    interactionDebtBound : (scale : Scale) → Set
    interactionDebtAtGamma : Scalar
    interactionDebtAtGammaExact : Set

open CMP109LiteralCauchyInteractionDebt public

------------------------------------------------------------------------
-- A1b: weakest currently known history datum
------------------------------------------------------------------------

record CMP109LiteralUniformHistorySummability
    (Scale Scalar : Set) : Set₁ where
  field
    response : Scale → Scale → Scalar
    D : Scalar

    -- Same-object source obligation: R_(j,k) is the literal sensitivity of the
    -- CMP109 beta coefficient to the earlier effective-coupling coordinate.
    responseIsLiteralBetaHistoryDerivative : Set

    -- sup_j sum_{k<j} |R_(j,k)| <= D.
    uniformAbsoluteResponseSum : (j : Scale) → Set
    cutoffVolumeScaleUniform : Set

    -- The Lean lane proves these as alternative sufficient producers of D.
    -- They are deliberately not required simultaneously.
    summableProfileCanProduceD : Set
    averageProductContractionCanProduceD : Set
    summableExcessProductBoundCanProduceD : Set
    geometricOneStepContractionIsSpecialCase : Set

    -- Load-bearing boundary: marginal J_i=1 with a nonvanishing head response
    -- can make the response sum grow without bound.
    marginalNondecayObstruction : Set

open CMP109LiteralUniformHistorySummability public

------------------------------------------------------------------------
-- Current literal Row-A1 residual obligation
------------------------------------------------------------------------

record CMP109A1ResidualObligation
    (Scale Scalar : Set) : Set₁ where
  field
    corner : CMP109LiteralCornerBubbleScalar Scale Scalar
    interaction : CMP109LiteralCauchyInteractionDebt Scale Scalar
    history : CMP109LiteralUniformHistorySummability Scale Scalar

    displacementBudget : Scalar
    reducedMargin : Scalar

    -- Exact project/source-facing formula:
    --
    --   reducedMargin
    --     = v^2/32
    --       - (A/(1-K gamma)) gamma^rho
    --       - D * B.
    reducedMarginEquation : Set
    reducedMarginPositive : Set

    -- Existing Lean consumer consequence: every literal shell coefficient is
    -- positive once this package is supplied.  Kept conditional in Agda until
    -- the source numbers and bridge are actually inhabited here.
    everyShellBetaPositive : Set

open CMP109A1ResidualObligation public

------------------------------------------------------------------------
-- Frozen scoreboard / authority boundary
------------------------------------------------------------------------

currentFrozenResearchCount : Nat
currentFrozenResearchCount = 4

cmp109ReducedMarginDependencyRefinementLevel : ProofLevel
cmp109ReducedMarginDependencyRefinementLevel = machineChecked

-- These are now the actual Row-A1 source-extraction obligations.
cmp109LiteralCornerFirstVariationScalarLevel : ProofLevel
cmp109LiteralCornerFirstVariationScalarLevel = conditional

cmp109LiteralCauchyInteractionPairLevel : ProofLevel
cmp109LiteralCauchyInteractionPairLevel = conditional

cmp109LiteralUniformHistorySummabilityLevel : ProofLevel
cmp109LiteralUniformHistorySummabilityLevel = conditional

cmp109A1ResidualObligationLevel : ProofLevel
cmp109A1ResidualObligationLevel = conditional
