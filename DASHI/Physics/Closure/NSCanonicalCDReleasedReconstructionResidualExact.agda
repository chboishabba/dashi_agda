{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalCDReleasedReconstructionResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES C/D RELEASED-RECONSTRUCTION RESIDUAL
--
-- Source boundary: the C/D alternatives belong to the Fefferman Clay problem
-- statement.  Independent kernel build / DASHI reconstruction are publication
-- and formal-reconstruction coordinates, not source claims.  This split is a
-- DASHI extension distilled from the current non-Round C/D audit frontier.
------------------------------------------------------------------------

record CanonicalCDReleasedReconstructionResidual
    (SelectedReleasedSource : Set)
    (selectedSource : SelectedReleasedSource)
    (IndependentKernelBuild : SelectedReleasedSource → Set)
    (IndependentDASHIReconstruction : SelectedReleasedSource → Set) : Set₁ where
  field
    independentKernelBuild : IndependentKernelBuild selectedSource
    independentDASHIReconstruction :
      IndependentDASHIReconstruction selectedSource
