{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalA3ContinuationResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES A3 CONTINUATION RESIDUAL
--
-- Source boundary: the literal whole-space target ultimately serves the
-- Fefferman Clay statement.  The separation of continuation from already-
-- closed field/signed-Lebesgue compilers is a DASHI extension.
------------------------------------------------------------------------

record CanonicalA3ContinuationResidual
    (SelectedContinuumSource : Set)
    (selectedSource : SelectedContinuumSource)
    (ContinuationCriterionLiteralNS : SelectedContinuumSource → Set) : Set₁ where
  field
    continuationCriterionLiteralNS :
      ContinuationCriterionLiteralNS selectedSource
