module DASHI.Physics.YangMills.BalabanCMP109FixedConstraintCoordinateGaussianExact where

------------------------------------------------------------------------
-- ROW A1: FIXED-CONSTRAINT COORDINATE GAUSSIAN
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- SOURCE CORRECTION
--
-- In CMP109 Sect. 2 Bałaban first changes variables to LINEARIZE the nonlinear
-- fluctuation averaging Q(B').  The Gaussian stage then uses the fixed linear
-- constraint delta(Q B').  Eliminating the constrained coordinates gives
--
--     B' = C(U) B,
--
-- and the source states that the covariance in the remaining variables is
--
--     ( C(U)^* A(U) C(U) )^{-1}.
--
-- Therefore the background derivative of the final finite Gaussian should not
-- be modelled as an independent derivative of a moving delta-constraint.  On
-- the fixed free-coordinate carrier the differentiated quadratic operator has
-- the source-native three-part form
--
--   D(C* A C) = (DC)* A C + C* (DA) C + C* A (DC).
--
-- Here DA contains the literal Wilson/background Hessian derivative and any
-- gauge-fixing contribution already present in A; DC is the derivative of the
-- source coordinate embedding produced by the linearization/elimination step.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP109FixedConstraintCoordinateGaussian
    (Background FreeField ConstrainedField Operator : Set) : Set₁ where
  field
    fixedConstraint : ConstrainedField → Set

    coordinateEmbedding : Background → FreeField → ConstrainedField
    quadraticOperator : Background → ConstrainedField → ConstrainedField
    restrictedQuadraticOperator : Background → FreeField → FreeField

    -- Source statements surrounding CMP109 (2.10)--(2.13): the nonlinear
    -- fluctuation constraint has already been linearized before the Gaussian is
    -- written in the free B-coordinates.
    nonlinearConstraintLinearized : Set
    deltaConstraintIsFixedLinearQ : Set
    eliminatedCoordinatesGiveBPrimeEqualsCB : Set
    covarianceIsInverseOfCStarAC : Set

    -- Same-object identification with the quadratic form defining Z^(k).
    restrictedOperatorIsCMP109GaussianQuadratic : Set

open CMP109FixedConstraintCoordinateGaussian public

record CMP109RestrictedQuadraticFirstVariation
    (Background FreeField ConstrainedField Operator Variation : Set)
    (source :
      CMP109FixedConstraintCoordinateGaussian
        Background FreeField ConstrainedField Operator) : Set₁ where
  field
    embeddingVariation : Background → Variation → FreeField → ConstrainedField
    quadraticVariation :
      Background → Variation → ConstrainedField → ConstrainedField
    restrictedVariation : Background → Variation → FreeField → FreeField

    leftConnectionTerm middlePhysicalTerm rightConnectionTerm :
      Background → Variation → FreeField → FreeField

    -- Exact product-rule target on the fixed coordinate carrier:
    --   restrictedVariation = leftConnection + middlePhysical + rightConnection.
    leftTermIsDCStarAC : Set
    middleTermIsCStarDAC : Set
    rightTermIsCStarADC : Set
    restrictedVariationThreeTermExact : Set

open CMP109RestrictedQuadraticFirstVariation public

------------------------------------------------------------------------
-- Authority / current physical frontier
------------------------------------------------------------------------

cmp109FixedConstraintCoordinateGaussianSourceRecutLevel : ProofLevel
cmp109FixedConstraintCoordinateGaussianSourceRecutLevel = machineChecked

-- Literal physical producer: instantiate C(U), A(U) and their derivatives from
-- the source formulas and prove the three-term restricted derivative identity.
cmp109LiteralCoordinateEmbeddingVariationLevel : ProofLevel
cmp109LiteralCoordinateEmbeddingVariationLevel = conditional

cmp109LiteralQuadraticOperatorVariationLevel : ProofLevel
cmp109LiteralQuadraticOperatorVariationLevel = conditional

cmp109LiteralRestrictedThreeTermVariationLevel : ProofLevel
cmp109LiteralRestrictedThreeTermVariationLevel = conditional

-- Any measure/Jacobian factor from the source change of variables must either be
-- shown background independent/cancelled or included explicitly in the same
-- Gaussian beta projection.  Do not silently drop it.
cmp109LiteralCoordinateJacobianContributionLevel : ProofLevel
cmp109LiteralCoordinateJacobianContributionLevel = conditional
