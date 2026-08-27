module DASHI.Physics.YangMills.BalabanCMP109UniformFloorSummableHistoryRefinementExact where

------------------------------------------------------------------------
-- ROW A1 SOURCE REFINEMENT: ONE BUBBLE ENTRY + SUMMABLE HISTORY KERNEL
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
-- CROSS-PROVER UPDATE
--
-- The parallel Lean Row-A1 lane proves two further dependency reductions.
-- They are recorded here as sharper source-facing interfaces only; the Lean
-- build is not an Agda kernel receipt.
--
-- (A1a quantitative floor)
-- For a Gram propagator G = C^T C and symmetric first variation V,
--
--   Tr(G V G V) = sum_ab M_ab^2,   M = C V C^T.
--
-- Under the already-separated paramagnetic seagull sign, one uniformly
-- nonvanishing entry |M_ab| >= c > 0 at one contributing momentum yields
--
--   betaZ_j >= c^2 / 2
--
-- uniformly.  Thus a full global Brillouin lower estimate is stronger than
-- necessary for the Gaussian floor.
--
-- (A1b history debt)
-- The final margin consumes only a uniform summability bound
--
--   sum_{k<j} |R_{j,k}| <= D.
--
-- A geometric one-step chain |J_i| <= theta < 1 is one sufficient producer,
-- with D = C_R theta/(1-theta), but it is not logically required if the source
-- supplies summability by another route.  Conversely marginal factors J_i=1
-- with nonvanishing head response give linearly growing debt, so some genuine
-- summability input is load-bearing.
--
-- CURRENT FROZEN SCOREBOARD
-- The current source-facing research scoreboard has four open rows A,B,C,D.
-- This module does not close A and does not change that count.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109SeagullHistorySourceRefinementExact
import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact

------------------------------------------------------------------------
-- A1a: weaker sufficient datum for a uniform Gaussian floor
------------------------------------------------------------------------

record CMP109LiteralUniformBubbleEntryDatum
    (Scale Momentum Index Scalar : Set) : Set₁ where
  field
    reducedBubbleEntry : Scale → Momentum → Index → Index → Scalar
    chosenMomentum : Scale → Momentum
    row column : Scale → Index

    lowerEntryBound : Scalar
    Positive : Scalar → Set
    AbsoluteValue : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    lowerEntryBoundPositive : Positive lowerEntryBound

    -- Literal same-object/source obligation: this entry must come from the
    -- reduced bubble kernel C V C^T built from the exact CMP109/CMP99 Gaussian
    -- operator and first background variation used in betaZ.
    entryIsLiteralReducedBubbleKernel : Set

    -- |M_ab(q_j)| >= c uniformly in scale/cutoff/volume.
    entryUniformlyNonvanishing : ∀ scale →
      LessEqual lowerEntryBound
        (AbsoluteValue
          (reducedBubbleEntry scale
            (chosenMomentum scale) (row scale) (column scale)))

    cutoffVolumeScaleUniform : Set

open CMP109LiteralUniformBubbleEntryDatum public

record CMP109BubbleEntryProducesGaussianFloor
    (Scale Momentum Index Scalar : Set) : Set₁ where
  field
    entryDatum : CMP109LiteralUniformBubbleEntryDatum Scale Momentum Index Scalar
    betaZ : Scale → Scalar
    halfEntrySquare : Scalar

    -- Cross-prover theorem shape:
    -- paramagnetic seagull + literal bubble identity + one entry lower bound
    -- imply betaZ_j >= c^2/2.
    halfEntrySquareIsSourceNormalization : Set
    gaussianFloorFromEntry : (scale : Scale) → Set

open CMP109BubbleEntryProducesGaussianFloor public

------------------------------------------------------------------------
-- A1b: weakest margin-facing history datum
------------------------------------------------------------------------

record CMP109LiteralSummableHistoryKernel
    (Scale Scalar : Set) : Set₁ where
  field
    response : Scale → Scale → Scalar
    historyBudget : Scalar

    -- Exact source identification R_{j,k} = d beta_j / d g_k (or the source's
    -- equivalent finite response coefficient).
    responseIsLiteralBetaHistoryDerivative : Set

    -- Uniform source-facing summability:
    --   sum_{k<j} |R_{j,k}| <= D.
    -- The finite sum implementation lives in the concrete arithmetic consumer.
    uniformResponseSummability : (j : Scale) → Set
    cutoffVolumeScaleUniform : Set

open CMP109LiteralSummableHistoryKernel public

record CMP109GeometricHistoryProducesSummability
    (Scale Scalar : Set) : Set₁ where
  field
    oneStep :
      BalabanCMP109SeagullHistorySourceRefinementExact.CMP109LiteralOneStepHistoryResponse
        Scale Scalar
    summable : CMP109LiteralSummableHistoryKernel Scale Scalar

    -- Geometric chain-rule decay is sufficient, not definitionally necessary.
    geometricBoundProducesSummability : Set

open CMP109GeometricHistoryProducesSummability public

------------------------------------------------------------------------
-- Updated A1 source package
------------------------------------------------------------------------

record CMP109CurrentLiteralA1SourcePackage
    (Scale Background Operator Momentum Index Scalar : Set) : Set₁ where
  field
    seagull :
      BalabanCMP109SeagullHistorySourceRefinementExact.CMP109LiteralParamagneticSeagullDatum
        Scale Background Operator Momentum Scalar

    bubbleEntry : CMP109LiteralUniformBubbleEntryDatum Scale Momentum Index Scalar
    gaussianFloor : CMP109BubbleEntryProducesGaussianFloor Scale Momentum Index Scalar

    interactionDebt :
      BalabanCMP109DirectBetaSourceCutsetExact.CMP109LiteralInteractionBetaDebt
        Scale Scalar

    history : CMP109LiteralSummableHistoryKernel Scale Scalar

    -- Final margin, in the weakest current form:
    --
    --   b_- = b_Z - C_int gamma^rho - D B > 0.
    --
    -- Geometric response is one way to instantiate D, not the only way.
    finalLiteralMarginPositive : Set

open CMP109CurrentLiteralA1SourcePackage public

------------------------------------------------------------------------
-- Scoreboard / authority boundary
------------------------------------------------------------------------

frozenResearchCount : Nat
frozenResearchCount = 4

cmp109UniformFloorSummableHistoryDependencyLevel : ProofLevel
cmp109UniformFloorSummableHistoryDependencyLevel = machineChecked

-- Literal Bałaban source extraction remains open.
cmp109LiteralUniformBubbleEntryLevel : ProofLevel
cmp109LiteralUniformBubbleEntryLevel = conditional

cmp109LiteralSummableHistoryKernelLevel : ProofLevel
cmp109LiteralSummableHistoryKernelLevel = conditional

cmp109CurrentLiteralA1SourcePackageLevel : ProofLevel
cmp109CurrentLiteralA1SourcePackageLevel = conditional
