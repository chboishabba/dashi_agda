{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalBContinuationResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES B CONTINUATION-INPUT RESIDUAL
--
-- DASHI extension: the generic compactness/continuation compiler is already a
-- separate concern; this owner keeps only the selected-family physical input
-- population required to use that compiler on the literal periodic object.
------------------------------------------------------------------------

record CanonicalBContinuationResidual
    (SelectedPeriodicSource : Set)
    (selectedSource : SelectedPeriodicSource)
    (SelectedFamilyContinuationInputs : SelectedPeriodicSource → Set) : Set₁ where
  field
    selectedFamilyContinuationInputs :
      SelectedFamilyContinuationInputs selectedSource
