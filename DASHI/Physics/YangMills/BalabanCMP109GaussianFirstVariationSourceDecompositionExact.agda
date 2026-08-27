module DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact where

------------------------------------------------------------------------
-- ROW A1: SOURCE-EXACT FIRST-VARIATION DECOMPOSITION
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
-- DOI: 10.1007/BF01239013.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- SOURCE CHAIN
--
-- CMP109 (1.4) defines the constrained Gaussian normalization.  CMP109 (1.5)
-- states that its background-dependent quadratic form uses the H_{1,j}, Delta_1
-- operators from Sect. D of reference [13]; reference [13] is the CMP99
-- background-propagator paper.  CMP99 derives the basic Wilson Hessian Delta(U)
-- from the second-order expansion of the Wilson action and writes it as a
-- covariant D*D term plus a small local background-dependent perturbation.
-- CMP99 also defines Q_j(U) as the background-dependent LINEAR part of the
-- composed averaging map.  CMP98 supplies the explicit contour-log averaging
-- operation whose small-field linear term is the ordinary averaging operator.
--
-- Therefore the first background derivative entering D log det of the CMP109
-- constrained Gaussian is not one anonymous scalar V.  At minimum it has the
-- following same-object source contributions:
--
--   (W) D_background Delta(U)       -- Wilson Hessian / cubic vertex;
--   (Q) D_background Q_j(U)         -- averaging/constraint variation;
--   (R) D_background gauge fixing   -- constrained/gauge projection variation.
--
-- Their combination, after restricting to the source constrained carrier, is the
-- literal first-variation operator consumed by the trace-log bubble.
--
-- Existing DASHI dexp/inverse-dexp cancellation algebra should be reused for the
-- contour-log/trivialisation part of (Q); do not reprove BCH calculus here.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact as Patch

------------------------------------------------------------------------
-- Source decomposition carrier
------------------------------------------------------------------------

record CMP109GaussianFirstVariationSourceDecomposition
    (Background Variation Operator ConstrainedOperator : Set) : Set₁ where
  field
    -- Literal source objects.
    cmp99WilsonHessian : Background → Operator
    cmp99AveragingConstraint : Background → Operator
    cmp99GaugeProjection : Background → Operator
    cmp109ConstrainedQuadratic : Background → ConstrainedOperator

    -- First background variations of those SAME source objects.
    wilsonHessianVariation : Background → Variation → Operator
    averagingConstraintVariation : Background → Variation → Operator
    gaugeProjectionVariation : Background → Variation → Operator
    constrainedQuadraticVariation : Background → Variation → ConstrainedOperator

    -- Source identities / same-object obligations.
    wilsonHessianIsCMP99Delta : Set
    averagingConstraintIsCMP98CMP99Q : Set
    gaugeProjectionIsCMP99GaugeFixing : Set
    constrainedQuadraticIsCMP109Equation14And15Carrier : Set

    -- The derivative of the constrained quadratic form must be assembled from
    -- W/Q/R after differentiating the restriction/projection, not by replacing
    -- the constrained Gaussian with an unconstrained flat propagator.
    constrainedVariationAssembledFromWQR : Set

open CMP109GaussianFirstVariationSourceDecomposition public

------------------------------------------------------------------------
-- Finite calculation checklist for the physical producer
------------------------------------------------------------------------

record CMP109GaussianFirstVariationCalculation
    (Background Variation Operator ConstrainedOperator Momentum Lorentz Color Scalar : Set)
    : Set₁ where
  field
    source :
      CMP109GaussianFirstVariationSourceDecomposition
        Background Variation Operator ConstrainedOperator

    flatBackground : Background
    backgroundVariation : Lorentz → Color → Variation

    -- Step W: Fourier symbol of D Delta(U) at U=1.  This is the Wilson cubic
    -- background vertex.  Keep all three Lorentz/color indices visible so an
    -- all-equal or Brillouin-boundary zero cannot be mistaken for positivity.
    wilsonFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar
    wilsonSymbolDerivedFromCMP99Delta : Set

    -- Step Q: derivative of the background-dependent averaging constraint.  The
    -- existing inverse-dexp cancellation theorem removes the purely algebraic
    -- left/right trivialisation ambiguity once the CMP98 conventions are
    -- literally identified.
    averagingFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar
    averagingSymbolDerivedFromCMP98Q : Set
    cmp98TrivialisationUsesExistingDexpCancellation :
      Dexp.cmp109LiteralLeftRightDexpIdentificationLevel ≡ conditional

    -- Step R: gauge-fixing/constrained-projection derivative.
    gaugeProjectionFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar
    gaugeProjectionSymbolDerivedFromCMP99Constraint : Set

    -- Same-object assembly into the operator used by the Gaussian trace-log.
    literalConstrainedFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar
    WQRAssemblyExact : Set

    -- Do not use one Brillouin-boundary point.  Produce one positive-measure box
    -- on which a mixed Lorentz/color component stays uniformly away from zero.
    positivePatch : Patch.CMP109LiteralGaussianPositivePatch
    patchUsesLiteralConstrainedFirstVariation : Set

open CMP109GaussianFirstVariationCalculation public

------------------------------------------------------------------------
-- Authority / frontier
------------------------------------------------------------------------

cmp109GaussianFirstVariationSourceDecompositionLevel : ProofLevel
cmp109GaussianFirstVariationSourceDecompositionLevel = machineChecked

cmp109LiteralWilsonHessianVariationLevel : ProofLevel
cmp109LiteralWilsonHessianVariationLevel = conditional

cmp109LiteralAveragingConstraintVariationLevel : ProofLevel
cmp109LiteralAveragingConstraintVariationLevel = conditional

cmp109LiteralGaugeProjectionVariationLevel : ProofLevel
cmp109LiteralGaugeProjectionVariationLevel = conditional

cmp109LiteralWQRAssemblyLevel : ProofLevel
cmp109LiteralWQRAssemblyLevel = conditional

cmp109LiteralMixedVertexPositivePatchLevel : ProofLevel
cmp109LiteralMixedVertexPositivePatchLevel = conditional
