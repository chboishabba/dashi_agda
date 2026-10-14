module DASHI.Moonshine.OggSSP2BUniqueRangeNormWeldExact where

------------------------------------------------------------------------
-- UNIQUE-TARGET-RANGE NORM WELD
--
-- This is the Agda mirror of the shortest Lean image-level route.
--
-- If the target Sym2(24) has a unique invariant 24-dimensional submodule,
-- namely the Frobenius-square image, and the actual residual norm image is
-- invariant and 24-dimensional, then the actual residual image is literally
-- Frobenius.  A separate quotient-source chart M/ker(residual) ~= V24 is not
-- required.
--
-- The exterior-square quotient compiler is kept abstract here because the
-- concrete linear quotient construction is Lean-owned.  The same-object input
-- is nevertheless proof-relevant: an actual residual image receipt must be
-- supplied to the unique-target theorem before exterior promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Moonshine.OggSSP2BUniqueInvariant24RangeExact

record ExteriorFromFrobeniusRangeCompiler
    (target : UniqueInvariant24TargetReceipt) : Set₁ where
  constructor exterior-from-frobenius-range-compiler
  field
    ExteriorModel : Set
    compile :
      (actual : ActualResidualImageReceipt target) ->
      residualRange actual ≡ FrobeniusRange target ->
      ExteriorModel

open ExteriorFromFrobeniusRangeCompiler public

actualResidualImageForcesExterior :
  (target : UniqueInvariant24TargetReceipt) ->
  (actual : ActualResidualImageReceipt target) ->
  (compiler : ExteriorFromFrobeniusRangeCompiler target) ->
  ExteriorModel compiler
actualResidualImageForcesExterior target actual compiler =
  compile compiler actual (actualResidualRangeIsFrobenius target actual)

uniqueRangeNormWeldCompilerPaid : Bool
uniqueRangeNormWeldCompilerPaid = true
