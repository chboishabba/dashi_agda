module DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact where

------------------------------------------------------------------------
-- ROW A1: SOURCE-EXACT FIRST-VARIATION DECOMPOSITION
--
-- PRIMARY SOURCES
-- Tadeusz Bałaban, CMP109 (1987), DOI 10.1007/BF01215223.
-- Tadeusz Bałaban, CMP98  (1985), DOI 10.1007/BF01211042.
-- Tadeusz Bałaban, CMP99  (1985), DOI 10.1007/BF01240355.
--
-- The record below is the source interface itself.  It deliberately does NOT
-- contain fields of the form `fooIsCMP99 : Set`: such a field would merely rename
-- the physical binding rather than express it.  Concrete callers must provide
-- the actual operators/variations and the calculation record must identify their
-- Fourier symbols pointwise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP109GaussianFirstVariationSourceDecomposition
    (Background Variation Operator ConstrainedOperator : Set) : Set₁ where
  field
    -- Source objects: CMP99 Wilson Hessian/background propagator sector,
    -- CMP98/99 averaging constraint, gauge projection, and the CMP109 (1.4)--(1.5)
    -- constrained quadratic carrier.
    cmp99WilsonHessian : Background → Operator
    cmp99AveragingConstraint : Background → Operator
    cmp99GaugeProjection : Background → Operator
    cmp109ConstrainedQuadratic : Background → ConstrainedOperator

    -- Their literal first background variations.
    wilsonHessianVariation : Background → Variation → Operator
    averagingConstraintVariation : Background → Variation → Operator
    gaugeProjectionVariation : Background → Variation → Operator
    constrainedQuadraticVariation : Background → Variation → ConstrainedOperator

open CMP109GaussianFirstVariationSourceDecomposition public

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

    -- Exact W+Q+R assembly on the constrained source symbol.
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

open CMP109GaussianFirstVariationCalculation public

cmp109GaussianFirstVariationSourceDecompositionLevel : ProofLevel
cmp109GaussianFirstVariationSourceDecompositionLevel = machineChecked

cmp109WQRSourceSymbolInterfaceLevel : ProofLevel
cmp109WQRSourceSymbolInterfaceLevel = machineChecked

cmp109WQRAssemblyInterfaceLevel : ProofLevel
cmp109WQRAssemblyInterfaceLevel = machineChecked

-- Physical source work is no longer represented by opaque receipt fields in the
-- record.  It consists precisely in constructing the source operator/variation
-- functions above and their pointwise Fourier-symbol/WQR equalities.
cmp109LiteralWilsonHessianVariationLevel : ProofLevel
cmp109LiteralWilsonHessianVariationLevel = conditional

cmp109LiteralAveragingConstraintVariationLevel : ProofLevel
cmp109LiteralAveragingConstraintVariationLevel = conditional

cmp109LiteralGaugeProjectionVariationLevel : ProofLevel
cmp109LiteralGaugeProjectionVariationLevel = conditional

cmp109LiteralWQRAssemblyLevel : ProofLevel
cmp109LiteralWQRAssemblyLevel = conditional
