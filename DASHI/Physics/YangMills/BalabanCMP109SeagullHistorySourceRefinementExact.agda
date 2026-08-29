module DASHI.Physics.YangMills.BalabanCMP109SeagullHistorySourceRefinementExact where

------------------------------------------------------------------------
-- ROW A1 SOURCE REFINEMENT: SEAGULL SIGN + ONE-STEP HISTORY RESPONSE
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
-- This module records the sharper dependency graph returned by the parallel
-- Lean Row-A1 calculation.  It does NOT import Lean proof authority into Agda.
-- The Lean return proves that, once the literal source symbols are supplied:
--
--   * the bubble term is nonnegative;
--   * a negative-semidefinite (paramagnetic) mixed second variation makes the
--     seagull contribution nonnegative in the beta trace;
--   * strict positivity follows if the bubble is nonzero;
--   * a purely affine Gram / squared-covariant-derivative second variation is
--     diamagnetic and cannot provide this sign for free;
--   * a one-step chain-rule response bound with factor theta < 1 generates the
--     full geometric history-response decay and uniform history debt.
--
-- Hence the remaining SOURCE extraction has become qualitative/one-step in
-- shape, but the Clay-facing closure is still quantitative: a sign proof alone
-- does not supply a cutoff/volume/scale-uniform numerical floor b_Z capable of
-- beating the finite-g and history debts.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact

------------------------------------------------------------------------
-- A1a: literal seagull sign datum
------------------------------------------------------------------------

record CMP109LiteralParamagneticSeagullDatum
    (Scale Background Operator Momentum Scalar : Set) : Set₁ where
  field
    directProducer :
      BalabanCMP109DirectBetaSourceCutsetExact.CMP109LiteralGaussianBetaProducer
        Scale Background Operator Momentum Scalar

    -- The actual source-derived mixed second background variation.  This field
    -- must denote the same operator/symbol consumed by the direct beta trace.
    literalMixedSecondVariation : Scale → Momentum → Scalar
    sameAsDirectProducerSecondVariation : Set

    -- Source-facing qualitative sign obligation.  The concrete semantics are
    -- supplied by the finite-dimensional matrix/order implementation.
    NegativeSemidefinite : Scalar → Set
    paramagneticSecondVariation : ∀ scale momentum →
      NegativeSemidefinite (literalMixedSecondVariation scale momentum)

    -- The strict-positivity criterion also needs a genuinely nonzero bubble.
    bubbleNonzeroOnSomeMomentum : ∀ scale → Set

open CMP109LiteralParamagneticSeagullDatum public

------------------------------------------------------------------------
-- A1a quantitative floor remains separate
------------------------------------------------------------------------

record CMP109LiteralUniformGaussianFloor
    (Scale Scalar : Set) : Set₁ where
  field
    betaZ : Scale → Scalar
    lowerBound : Scalar
    LessEqual : Scalar → Scalar → Set
    Positive : Scalar → Set

    lowerBoundPositive : Positive lowerBound
    uniformFloor : ∀ scale → LessEqual lowerBound (betaZ scale)

open CMP109LiteralUniformGaussianFloor public

------------------------------------------------------------------------
-- A1b: literal one-step chain-response datum
------------------------------------------------------------------------

record CMP109LiteralOneStepHistoryResponse
    (Scale Scalar : Set) : Set₁ where
  field
    -- Local chain-rule factors whose products generate R_{j,k}.
    endpointSensitivity : Scale → Scalar
    oneStepJacobian : Scale → Scalar

    responseConstant theta : Scalar

    -- Exact source identification of these factors with the derivative of the
    -- literal beta coefficient along the effective-coupling history.
    chainFactorisationIsLiteralBetaDerivative : Set

    -- One-step source datum.  The already-proved Lean chain-rule theorem shows
    -- that this generates |R_{j,k}| <= C_R theta^(j-k).
    oneStepJacobianUniformlyBoundedByTheta : ∀ scale → Set
    endpointSensitivityUniformlyBounded : ∀ scale → Set
    thetaStrictlyBelowOne : Set
    cutoffVolumeScaleUniform : Set

open CMP109LiteralOneStepHistoryResponse public

------------------------------------------------------------------------
-- Updated physical Row-A1 source package
------------------------------------------------------------------------

record CMP109SeagullHistoryPhysicalPackage
    (Scale Background Operator Momentum Scalar : Set) : Set₁ where
  field
    seagull :
      CMP109LiteralParamagneticSeagullDatum
        Scale Background Operator Momentum Scalar
    gaussianFloor : CMP109LiteralUniformGaussianFloor Scale Scalar
    historyStep : CMP109LiteralOneStepHistoryResponse Scale Scalar

    -- Finite-g nonlinear interaction debt remains independent and source-facing.
    interactionDebt :
      BalabanCMP109DirectBetaSourceCutsetExact.CMP109LiteralInteractionBetaDebt
        Scale Scalar

    -- Final quantitative gate remains the existing three-number inequality:
    --
    --   b_Z - C_int gamma^rho - C_R B theta/(1-theta) > 0.
    --
    -- This module intentionally does not duplicate the ordered-field arithmetic.
    finalRowA1MarginPositive : Set

open CMP109SeagullHistoryPhysicalPackage public

------------------------------------------------------------------------
-- Authority / status boundary
------------------------------------------------------------------------

-- Dependency refinement only: the theorem pattern was established in Lean,
-- while these Agda declarations merely expose the sharper physical interfaces.
cmp109SeagullHistoryDependencyRefinementLevel : ProofLevel
cmp109SeagullHistoryDependencyRefinementLevel = machineChecked

-- Literal source identification/sign remains open in Agda/source extraction.
cmp109LiteralParamagneticSeagullSignLevel : ProofLevel
cmp109LiteralParamagneticSeagullSignLevel = conditional

-- Strict positivity from the sign is not yet a uniform numerical Clay margin.
cmp109LiteralUniformGaussianFloorLevel : ProofLevel
cmp109LiteralUniformGaussianFloorLevel = conditional

-- Literal one-step response factors/constants remain source inputs.
cmp109LiteralOneStepHistoryResponseLevel : ProofLevel
cmp109LiteralOneStepHistoryResponseLevel = conditional

-- No Clay leaf decrement occurs until the entire physical package is inhabited
-- with a strictly positive quantitative final margin.
cmp109SeagullHistoryClosesA1Level : ProofLevel
cmp109SeagullHistoryClosesA1Level = conditional
