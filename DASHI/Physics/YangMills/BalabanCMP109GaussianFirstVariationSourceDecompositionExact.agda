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
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP109GaussianPositivePatchCorrectionExact as Patch

record CMP109GaussianFirstVariationSourceDecomposition
    (Background Variation Operator ConstrainedOperator : Set) : Set₁ where
  field
    cmp99WilsonHessian : Background → Operator
    cmp99AveragingConstraint : Background → Operator
    cmp99GaugeProjection : Background → Operator
    cmp109ConstrainedQuadratic : Background → ConstrainedOperator

    wilsonHessianVariation : Background → Variation → Operator
    averagingConstraintVariation : Background → Variation → Operator
    gaugeProjectionVariation : Background → Variation → Operator
    constrainedQuadraticVariation : Background → Variation → ConstrainedOperator

    wilsonHessianIsCMP99Delta : Set
    averagingConstraintIsCMP98CMP99Q : Set
    gaugeProjectionIsCMP99GaugeFixing : Set
    constrainedQuadraticIsCMP109Equation14And15Carrier : Set
    constrainedVariationAssembledFromWQR : Set

open CMP109GaussianFirstVariationSourceDecomposition public

------------------------------------------------------------------------
-- Finite calculation checklist for the physical producer.
--
-- Round117 removes three opaque "symbol derived from ..." receipts.  A caller
-- must now supply the actual Fourier-symbol operation and prove pointwise that W,
-- Q and R are the symbols of the corresponding source first variations.  The
-- constrained symbol is likewise tied pointwise to the constrained quadratic
-- variation before the W+Q+R assembly equality is used.
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

    operatorFirstVariationSymbol :
      (Background → Variation → Operator) →
      Background → (Lorentz → Color → Variation) →
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar

    constrainedFirstVariationSymbol :
      (Background → Variation → ConstrainedOperator) →
      Background → (Lorentz → Color → Variation) →
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar

    wilsonFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar
    wilsonSymbolDerivedFromCMP99Delta :
      ∀ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      wilsonFirstVariationSymbol
        momentum output input backgroundDirection outputColor inputColor backgroundColor
      ≡ operatorFirstVariationSymbol
          (wilsonHessianVariation source)
          flatBackground backgroundVariation
          momentum output input backgroundDirection outputColor inputColor backgroundColor

    averagingFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar
    averagingSymbolDerivedFromCMP98Q :
      ∀ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      averagingFirstVariationSymbol
        momentum output input backgroundDirection outputColor inputColor backgroundColor
      ≡ operatorFirstVariationSymbol
          (averagingConstraintVariation source)
          flatBackground backgroundVariation
          momentum output input backgroundDirection outputColor inputColor backgroundColor

    cmp98TrivialisationUsesExistingDexpCancellation :
      Dexp.cmp109LiteralLeftRightDexpIdentificationLevel ≡ conditional

    gaugeProjectionFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar
    gaugeProjectionSymbolDerivedFromCMP99Constraint :
      ∀ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      gaugeProjectionFirstVariationSymbol
        momentum output input backgroundDirection outputColor inputColor backgroundColor
      ≡ operatorFirstVariationSymbol
          (gaugeProjectionVariation source)
          flatBackground backgroundVariation
          momentum output input backgroundDirection outputColor inputColor backgroundColor

    add : Scalar → Scalar → Scalar

    literalConstrainedFirstVariationSymbol :
      Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → Scalar

    constrainedSymbolIsCMP109Variation :
      ∀ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      literalConstrainedFirstVariationSymbol
        momentum output input backgroundDirection outputColor inputColor backgroundColor
      ≡ constrainedFirstVariationSymbol
          (constrainedQuadraticVariation source)
          flatBackground backgroundVariation
          momentum output input backgroundDirection outputColor inputColor backgroundColor

    WQRAssemblyExact :
      ∀ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      literalConstrainedFirstVariationSymbol
          momentum output input backgroundDirection
          outputColor inputColor backgroundColor
      ≡ add
          (wilsonFirstVariationSymbol
            momentum output input backgroundDirection
            outputColor inputColor backgroundColor)
          (add
            (averagingFirstVariationSymbol
              momentum output input backgroundDirection
              outputColor inputColor backgroundColor)
            (gaugeProjectionFirstVariationSymbol
              momentum output input backgroundDirection
              outputColor inputColor backgroundColor))

    positivePatch : Patch.CMP109LiteralGaussianPositivePatch
    patchUsesLiteralConstrainedFirstVariation : Set

open CMP109GaussianFirstVariationCalculation public

cmp109GaussianFirstVariationSourceDecompositionLevel : ProofLevel
cmp109GaussianFirstVariationSourceDecompositionLevel = machineChecked

cmp109WQRSourceSymbolInterfaceLevel : ProofLevel
cmp109WQRSourceSymbolInterfaceLevel = machineChecked

cmp109WQRAssemblyInterfaceLevel : ProofLevel
cmp109WQRAssemblyInterfaceLevel = machineChecked

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
