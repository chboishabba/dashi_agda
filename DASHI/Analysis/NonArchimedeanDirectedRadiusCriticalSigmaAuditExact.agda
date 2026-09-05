module DASHI.Analysis.NonArchimedeanDirectedRadiusCriticalSigmaAuditExact where

------------------------------------------------------------------------
-- DIRECTED RADIUS / CRITICAL-SIGMA AUDIT
--
-- The non-Archimedean spectral paper states
--
--   r_n = 2^(2^(-(n-1)))
--
-- and then says that convergence is governed by a critical scaling exponent
-- sigma = 1/2.
--
-- Those are not the same statement.  Taking logarithms gives exactly
--
--   log r_n = (log 2) / 2^(n-1).
--
-- With system size N = 2^n this is
--
--   log r_n = 2 log 2 / N.
--
-- Thus the radius formula has:
--   * a per-level contraction ratio 1/2 in n;
--   * an N^(-1) size law for log r_n.
--
-- A sigma=1/2 statement may be independently meaningful if sigma is defined as
-- a conformal/dynamical parameter, but it is not a consequence of the radius
-- formula interpreted as the power exponent of N.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record DirectedRadiusSigmaAudit : Set where
  constructor directedRadiusSigmaAudit
  field
    radiusFormulaAdvertised : Bool
    criticalSigmaHalfAdvertised : Bool
    locatedLeanTheoremDefinesDirectedSigmaHalf : Bool

    logRadiusContractsByHalfPerLevel : Bool
    logRadiusScalesAsInverseSystemSize : Bool
    inverseSystemSizePowerExponentIsOne : Bool

    perLevelHalfFactorEqualsSizePowerExponentHalf : Bool
    radiusFormulaAloneImpliesSigmaHalf : Bool
    independentSigmaDefinitionRequired : Bool

    undirectedGapAlphaIsSameQuantity : Bool
    undirectedGapAlphaHasSeparateLeanOwner : Bool

canonicalDirectedRadiusSigmaAudit : DirectedRadiusSigmaAudit
canonicalDirectedRadiusSigmaAudit =
  directedRadiusSigmaAudit
    true true false
    true true true
    false false true
    false true

radiusFormulaDoesNotByItselfProveSigmaHalf :
  DirectedRadiusSigmaAudit.radiusFormulaAloneImpliesSigmaHalf
    canonicalDirectedRadiusSigmaAudit
  ≡ false
radiusFormulaDoesNotByItselfProveSigmaHalf = refl

levelRatioIsNotSizeExponent :
  DirectedRadiusSigmaAudit.perLevelHalfFactorEqualsSizePowerExponentHalf
    canonicalDirectedRadiusSigmaAudit
  ≡ false
levelRatioIsNotSizeExponent = refl

undirectedAlphaIsSeparate :
  DirectedRadiusSigmaAudit.undirectedGapAlphaIsSameQuantity
    canonicalDirectedRadiusSigmaAudit
  ≡ false
undirectedAlphaIsSeparate = refl

record ExactScalingReading : Set where
  constructor exactScalingReading
  field
    depthVariable : Bool
    sizeVariableNEqualsTwoPowN : Bool
    exactLogRadiusProportionalToTwoPowMinusN : Bool
    exactLogRadiusProportionalToInverseN : Bool
    asymptoticRadiusMinusOneNeedsExpLinearisation : Bool

canonicalExactScalingReading : ExactScalingReading
canonicalExactScalingReading =
  exactScalingReading true true true true true
