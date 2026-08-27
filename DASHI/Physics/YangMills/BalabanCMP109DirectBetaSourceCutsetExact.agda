module DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact where

------------------------------------------------------------------------
-- CMP109 DIRECT-BETA SOURCE CUTSET
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Source-critical equations:
--
--   (1.4)   constrained Gaussian normalization Z^(j)(U)
--   (1.5)   background-dependent quadratic form used in that normalization
--   (2.10)--(2.13) fluctuation rescaling and nonlinear interaction
--   (2.15)  inverse-square coupling recurrence
--   (5.9), (5.15) Ward/transversality
--   (5.37)  marginal transverse beta term + higher-derivative remainder
--   (5.38)  remainder starts at third order in lattice derivatives
--   (5.42)  beta is the off-diagonal mixed p=0 second derivative of Pi
--
-- Earlier constrained-propagator source used by the determinant calculation:
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
-- especially the constrained/gauge-fixed covariance formulas around
-- (3.185)--(3.186).
--
-- MATHEMATICAL UPDATE
--
-- The Row-A1 leading coefficient does not logically require a global bound on
-- the full polarization tensor.  CMP109 defines beta from its mixed second jet
-- at p=0, while the remainder in (5.38) begins at third lattice-derivative
-- order.  Therefore the shortest source-facing route is
--
--   exact constrained Gaussian operator
--     -> second background variation of log det
--     -> constrained Ward cancellation inside the trace
--     -> translation-invariant Fourier symbols at U=1
--     -> one scalar Brillouin trace/sum
--     -> betaZ_j.
--
-- The existing global near/far polarization machinery remains a valid fallback
-- numerical enclosure once the literal scalar has been produced; it is no
-- longer a logically mandatory first gate for beta determination.
--
-- IMPORTANT SOURCE BOUNDARY
--
-- CMP109 itself does not supply the separate perturbative proof promised for
-- Theorem 2 and does not derive DASHI's comparison checksum 11/24 C_A.
-- No field below imports that number as a physical theorem.  The coefficient
-- must first be calculated in the source/project normalization and only then
-- compared with a universal continuum convention as a normalization audit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound82FiveAnalyticLeafExact

------------------------------------------------------------------------
-- 1. DIRECT GAUSSIAN COEFFICIENT PRODUCER
------------------------------------------------------------------------

record CMP109LiteralGaussianBetaProducer
    (Scale Background Operator Momentum Scalar : Set) : Set₁ where
  field
    -- Exact finite constrained operator \hat Delta^(j)(U).
    constrainedOperator : Scale → Background → Operator

    -- Translation-invariant U=1 inverse symbol and the first / mixed-second
    -- background-variation symbols required by the trace-log Hessian.
    inverseSymbol : Scale → Momentum → Scalar
    firstVariationSymbol : Scale → Momentum → Scalar
    mixedSecondVariationSymbol : Scale → Momentum → Scalar

    -- The exact scalar summand obtained after trace-log Hessian, constrained
    -- Ward cancellation, and Fourier diagonalization.
    betaTraceSummand : Scale → Momentum → Scalar
    betaZ : Scale → Scalar

    -- Same-object obligations.  These prevent replacing the CMP109 constrained
    -- carrier by a flat continuum or unconstrained lattice surrogate.
    operatorIsCMP109Equation14And15Carrier : Set
    constrainedInverseMatchesCMP99Source : Set
    traceLogSecondVariationExact : Set
    constrainedWardCancellationInsideTrace : Set
    fourierSymbolsAreOfSameOperator : Set
    brillouinReductionExact : Set

    -- Physical theorem required from the literal calculation.
    UniformPositive : Scalar → Set
    positiveLowerBound : Scalar
    betaZUniformlyPositive : ∀ scale → UniformPositive positiveLowerBound

open CMP109LiteralGaussianBetaProducer public

------------------------------------------------------------------------
-- 2. FINITE-g NONLINEAR INTERACTION DEBT
------------------------------------------------------------------------

record CMP109LiteralInteractionBetaDebt
    (Scale Scalar : Set) : Set₁ where
  field
    coupling : Scale → Scalar
    betaInteraction : Scale → Scalar
    constant exponent : Scalar

    -- Source-derived power/order from CMP109 (2.12)--(2.13).  It must not be
    -- inserted from continuum perturbative folklore.
    sourcePowerFromFluctuationIntegral : Set
    twiceBackgroundDifferentiableUniformly : Set

    -- |betaInt_j| <= C_int * g_j^rho, uniformly on the admissible history.
    interactionDebtBound : ∀ scale → Set

open CMP109LiteralInteractionBetaDebt public

------------------------------------------------------------------------
-- 3. HISTORY-RESPONSE DEBT
------------------------------------------------------------------------

record CMP109LiteralBetaHistoryResponseDecay
    (Scale Scalar : Set) : Set₁ where
  field
    response : Scale → Scale → Scalar
    responseConstant contraction : Scalar

    -- R_{j,k} is the literal derivative/response of beta_j to the earlier
    -- effective coupling coordinate g_k.  CMP109 explicitly warns that the
    -- notation beta_j(g_(j-1)) suppresses dependence on preceding couplings.
    responseIsLiteralBetaHistoryDerivative : Set

    -- Uniform geometric response decay, or an equivalent source-native bound:
    -- |R_{j,k}| <= C_R theta^(j-k), theta < 1.
    contractionStrictlyBelowOne : Set
    historyResponseDecay : ∀ j k → Set

    -- This is deliberately a coefficient-relative theorem; no contraction of
    -- the entire RG state is required if the beta response itself is summable.
    cutoffVolumeScaleUniform : Set

open CMP109LiteralBetaHistoryResponseDecay public

------------------------------------------------------------------------
-- 4. THE THREE-NUMBER ROW-A1 CLOSURE GATE
------------------------------------------------------------------------

record CMP109DirectRowA1PhysicalClosure
    (Scale Background Operator Momentum Scalar : Set) : Set₁ where
  field
    gaussian :
      CMP109LiteralGaussianBetaProducer
        Scale Background Operator Momentum Scalar
    interaction : CMP109LiteralInteractionBetaDebt Scale Scalar
    history : CMP109LiteralBetaHistoryResponseDecay Scale Scalar

    -- The literal source-facing margin is conceptually
    --
    --   b_- = b_Z - interactionDebt - historyDebt.
    --
    -- We intentionally keep the ordered-field arithmetic in the existing
    -- positive-beta/history consumers instead of creating another arithmetic
    -- owner here.
    gaussianLowerBound : Scalar
    finiteGInteractionDebt : Scalar
    historyDebt : Scalar
    totalMarginPositive : Set

open CMP109DirectRowA1PhysicalClosure public

------------------------------------------------------------------------
-- CURRENT SCOREBOARD
------------------------------------------------------------------------

-- The official Round82 count remains five until this source-facing A1 package
-- is physically inhabited.  This module sharpens A1; it does not decrement it.
round82AnalyticLeafCountStillFive : Nat
round82AnalyticLeafCountStillFive = 5

-- Source transcription and dependency recut are machine-checked declarations.
cmp109DirectBetaCutsetLevel : ProofLevel
cmp109DirectBetaCutsetLevel = machineChecked

-- Physical producers remain open.
cmp109LiteralGaussianSymbolsAndPositiveBetaZLevel : ProofLevel
cmp109LiteralGaussianSymbolsAndPositiveBetaZLevel = conditional

cmp109LiteralFiniteGInteractionDebtLevel : ProofLevel
cmp109LiteralFiniteGInteractionDebtLevel = conditional

cmp109LiteralHistoryResponseDecayLevel : ProofLevel
cmp109LiteralHistoryResponseDecayLevel = conditional

-- The direct p=0 jet route is primary; global near/far remains available only
-- as a fallback enclosure after the literal Brillouin scalar exists.
cmp109GlobalPolarizationNearFarFallbackLevel : ProofLevel
cmp109GlobalPolarizationNearFarFallbackLevel = machineChecked
