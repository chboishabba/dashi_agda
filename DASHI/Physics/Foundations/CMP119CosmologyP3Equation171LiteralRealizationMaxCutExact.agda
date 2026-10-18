{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3Equation171LiteralRealizationMaxCutExact where

------------------------------------------------------------------------
-- S3b SOURCE MAX-CUT: THE LIPSCHITZ THEOREM MUST BE ABOUT THE LITERAL
-- EQ.(1.71) INTEGRAND, NOT THE ABSTRACT CALLBACK.
--
-- The generic CMP122 owner intentionally leaves Fine, SlowField, the exponential
-- density and constrained integral abstract.  Therefore a continuity/Lipschitz
-- theorem over that interface is impossible without first paying the physical
-- realization theorem that identifies those objects with Bałaban's finite
-- localized Eq.(1.71) integration problem.
--
-- Keep this payment inside S3b.  It is not extra adapter debt; it is precisely
-- the same-object source realization on which the cell oscillation estimate is
-- to be proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171

literalEquation171FiniteRealizationLevel : ProofLevel
literalEquation171FiniteRealizationLevel =
  Eq171.literalCMP122Equation171FiniteRealizationLevel

abstractEquation171CallbackAloneDeterminesLipschitzBound : Bool
abstractEquation171CallbackAloneDeterminesLipschitzBound = false

literalEquation171FiniteCarrierDensityIntegralRealizationRequired : Bool
literalEquation171FiniteCarrierDensityIntegralRealizationRequired = true

lipschitzEstimateMustUseLiteralRealization : Bool
lipschitzEstimateMustUseLiteralRealization = true
