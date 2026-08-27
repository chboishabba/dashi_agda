module DASHI.Physics.YangMills.BalabanCMP109SourceTranscriptionExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary-source transcription seam for the four-dimensional coupling law.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Source roles used here:
--
--   * Eq. (1.4): Z^(j)(U) is the background-dependent Gaussian
--     normalization on the constrained fluctuation carrier.
--   * Eq. (1.5): the Gaussian quadratic form is the source's
--     background-dependent constrained fluctuation operator; it is not to be
--     silently replaced by a flat continuum Laplacian.
--   * Eqs. (2.10)--(2.13): after the source's fluctuation rescaling, the
--     nonlinear interaction is separated from that Gaussian normalization.
--   * Eq. (2.15): 1/g_k^2 = 1/g_(k+1)^2 + beta_(k+1)(g_k).
--   * Eqs. (5.9), (5.15): lattice Ward/transversality identities for the
--     vacuum-polarization tensor.
--   * Eq. (5.37):
--       Pi_mn(p) = beta (delta_mn Delta(p) - dbar_m(p) d_n(p)) + Pi'_mn(p).
--   * Eq. (5.38): Pi' is third and higher order in lattice derivatives, with
--     analytic coefficient functions.
--   * Eq. (5.42): for m /= n,
--       beta = - d_pm d_pn Pi_mn(0)
--            = sum_x Pi_mn(x) x_m x_n.
--
-- SOURCE / CLAIM BOUNDARY
--
-- CMP109 does NOT supply the separate perturbative calculation promised for
-- Theorem 2.  In particular it does not prove a cutoff/volume-uniform positive
-- numerical lower bound for beta, and it does not print a ready-made
-- Wilson-bubble + reduced-Faddeev--Popov + Haar momentum integrand.  The
-- source-native leading object is instead the exact constrained Gaussian
-- normalization and its second background variation.
--
-- The direct A1 route is therefore determinant/second-jet first:
--
--   constrained Gaussian operator
--     -> D^2 log det
--     -> Ward cancellation inside the trace
--     -> Fourier scalar at U=1
--     -> betaZ_j via the p=0 mixed second derivative in (5.42).
--
-- Because the remainder in (5.38) begins at third lattice-derivative order,
-- global control of Pi'(p) is not logically required merely to determine the
-- beta coefficient.  Global near/far polarization control remains a useful
-- fallback numerical enclosure, not the mandatory first source gate.
--
-- CMP109 also states after (5.42) that beta_j depends on all preceding
-- couplings although the notation beta_j(g_(j-1)) suppresses that dependence.
-- The shortest A1b source target is therefore coefficient-history response
-- decay/summability, not necessarily contraction of an entire RG state.
------------------------------------------------------------------------

record CMP109ConstrainedGaussianNormalization
    (Background Fluctuation Scalar : Set) : Set₁ where
  field
    Z : Background → Scalar
    Delta : Background → Fluctuation → Fluctuation
    Constraint : Fluctuation → Set

    -- Eq. (1.4), kept as a source identity boundary because DASHI does not
    -- identify an abstract integral with a determinant without an explicit
    -- finite carrier and measure implementation.
    equation14ConstrainedGaussianNormalization : Set

    -- Eq. (1.5) same-carrier requirement for the background quadratic form.
    equation15BackgroundQuadraticForm : Set

open CMP109ConstrainedGaussianNormalization public

record CMP109CouplingRecurrence
    (Scale Scalar : Set) : Set₁ where
  field
    next : Scale → Scale
    coupling : Scale → Scalar
    betaCoefficient : Scale → Scalar

    inverseSquare add : Scalar → Scalar → Scalar
    Equal : Scalar → Scalar → Set

    -- Eq. (2.15): 1/g_k^2 = 1/g_(k+1)^2 + beta_(k+1)(g_k).
    equation215 : ∀ scale →
      Equal
        (inverseSquare (coupling scale) (coupling scale))
        (add
          (inverseSquare (coupling (next scale)) (coupling (next scale)))
          (betaCoefficient (next scale)))

open CMP109CouplingRecurrence public

record CMP109PolarizationSourceShape
    (Momentum Index Scalar : Set) : Set₁ where
  field
    polarization remainder : Index → Index → Momentum → Scalar
    beta : Scalar

    kronecker : Index → Index → Scalar
    latticeLaplacian : Momentum → Scalar
    d dbar : Index → Momentum → Scalar

    add subtract multiply : Scalar → Scalar → Scalar
    Equal : Scalar → Scalar → Set

    -- Eq. (5.37), represented literally as the source's marginal transverse
    -- second-order term plus its higher-derivative remainder.
    equation537 : ∀ mu nu momentum →
      Equal
        (polarization mu nu momentum)
        (add
          (multiply beta
            (subtract
              (multiply (kronecker mu nu) (latticeLaplacian momentum))
              (multiply (dbar mu momentum) (d nu momentum))))
          (remainder mu nu momentum))

    -- Eq. (5.38): the remainder starts at third order in lattice derivatives
    -- with analytic coefficient functions.  This source property is kept
    -- separate from any quantitative bound used by a Clay-facing consumer.
    remainderThirdOrderDerivativeStructure538 : Set
    remainderCoefficientAnalyticity538 : Set

    -- Eqs. (5.9)/(5.15): Ward/transversality for the same polarization tensor.
    wardTransversality : Set

open CMP109PolarizationSourceShape public

record CMP109BetaProjection
    (Momentum Index Scalar : Set)
    (shape : CMP109PolarizationSourceShape Momentum Index Scalar) : Set₁ where
  field
    Distinct : Index → Index → Set
    zeroMomentum : Momentum
    negate : Scalar → Scalar

    mixedMomentumDerivativeAtZero :
      (Index → Index → Momentum → Scalar) → Index → Index → Scalar

    positionMoment : Index → Index → Scalar

    -- Eq. (5.42), first equality.
    equation542Derivative : ∀ mu nu → Distinct mu nu →
      Equal shape
        (beta shape)
        (negate
          (mixedMomentumDerivativeAtZero
            (polarization shape) mu nu))

    -- Eq. (5.42), second equality.  The actual lattice sum is represented by
    -- positionMoment until a concrete finite/infinite-volume summation carrier
    -- is supplied.
    equation542PositionMoment : ∀ mu nu → Distinct mu nu →
      Equal shape (beta shape) (positionMoment mu nu)

open CMP109BetaProjection public

------------------------------------------------------------------------
-- Same-source packaging
------------------------------------------------------------------------

record CMP109SourceExactCouplingPolarizationChain
    (Scale Background Fluctuation Momentum Index Scalar : Set) : Set₁ where
  field
    gaussian :
      CMP109ConstrainedGaussianNormalization Background Fluctuation Scalar
    recurrence : CMP109CouplingRecurrence Scale Scalar
    polarizationShape : CMP109PolarizationSourceShape Momentum Index Scalar
    betaProjection : CMP109BetaProjection Momentum Index Scalar polarizationShape

open CMP109SourceExactCouplingPolarizationChain public

cmp109SourceChainCarriesEquation215 :
  ∀ {Scale Background Fluctuation Momentum Index Scalar}
    (chain :
      CMP109SourceExactCouplingPolarizationChain
        Scale Background Fluctuation Momentum Index Scalar) →
  ∀ scale →
  Equal (recurrence chain)
    (inverseSquare (recurrence chain)
      (coupling (recurrence chain) scale)
      (coupling (recurrence chain) scale))
    (add (recurrence chain)
      (inverseSquare (recurrence chain)
        (coupling (recurrence chain) (next (recurrence chain) scale))
        (coupling (recurrence chain) (next (recurrence chain) scale)))
      (betaCoefficient (recurrence chain) (next (recurrence chain) scale)))
cmp109SourceChainCarriesEquation215 chain = equation215 (recurrence chain)

cmp109SourceChainCarriesBetaProjection :
  ∀ {Scale Background Fluctuation Momentum Index Scalar}
    (chain :
      CMP109SourceExactCouplingPolarizationChain
        Scale Background Fluctuation Momentum Index Scalar) →
  ∀ mu nu → Distinct (betaProjection chain) mu nu →
  Equal (polarizationShape chain)
    (beta (polarizationShape chain))
    (negate (betaProjection chain)
      (mixedMomentumDerivativeAtZero (betaProjection chain)
        (polarization (polarizationShape chain)) mu nu))
cmp109SourceChainCarriesBetaProjection chain =
  equation542Derivative (betaProjection chain)

------------------------------------------------------------------------
-- Proof levels
------------------------------------------------------------------------

-- These levels certify only the typed transcription and projection plumbing.
-- They do not certify the physical determinant evaluation or positivity.
cmp109SourceTranscriptionLevel : ProofLevel
cmp109SourceTranscriptionLevel = machineChecked

cmp109EquationPlumbingLevel : ProofLevel
cmp109EquationPlumbingLevel = machineChecked

-- Source-native leading A1a producer still open:
-- identify/evaluate the exact constrained Gaussian operator, differentiate its
-- trace-log twice, perform constrained Ward cancellation, Fourier reduce at U=1,
-- and prove a cutoff/volume/scale-uniform positive lower bound for betaZ.
cmp109LiteralGaussianBetaZLevel : ProofLevel
cmp109LiteralGaussianBetaZLevel = conditional

-- Finite-g interaction beta debt from (2.12)--(2.13), with the positive power
-- and uniform differentiability derived from the source rather than folklore.
cmp109LiteralFiniteGInteractionDebtLevel : ProofLevel
cmp109LiteralFiniteGInteractionDebtLevel = conditional

-- History response/sensitivity of beta_j to preceding effective couplings.
cmp109LiteralHistoryResponseDecayLevel : ProofLevel
cmp109LiteralHistoryResponseDecayLevel = conditional

-- Kept for compatibility with older consumers that named the combined seam.
cmp109LiteralConstrainedDeterminantEvaluationLevel : ProofLevel
cmp109LiteralConstrainedDeterminantEvaluationLevel = conditional

cmp109LiteralInteractionRemainderAndHistoryLevel : ProofLevel
cmp109LiteralInteractionRemainderAndHistoryLevel = conditional
