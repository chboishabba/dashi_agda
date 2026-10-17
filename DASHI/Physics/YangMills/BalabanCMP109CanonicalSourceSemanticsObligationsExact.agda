{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109CanonicalSourceSemanticsObligationsExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanCMP109CanonicalResidualInstantiationExact as Inst

------------------------------------------------------------------------
-- Canonical non-Round owner for the residual CMP109 source-semantics package.
--
-- Historical scheduler labels are provenance only.  This owner now names the
-- three residuals by their actual non-Round theorem carriers, all attached to
-- the SAME selected source value:
--
--   * generated-history response -> Ward/quartic producer reconstruction;
--   * beta difference -> selected shooting-map attachment, with decomposition
--     compiled by the existing non-Round beta-prefix theorem;
--   * physical composite D1 -> selected first-order transport equality.
--
-- No scheduler state, citation, or proof-level receipt inhabits these fields.
------------------------------------------------------------------------

record CMP109CanonicalSourceSemanticsObligations
    {SelectedSource : Set}
    (selectedSource : SelectedSource)
    (TubePoint : Set)
    (cutoff : Nat)
    (Component Background Tangent Scalar : Set) : Set₁ where
  field
    generatedHistoryResponseProducer :
      Inst.CMP109GeneratedHistoryResponseResidual selectedSource cutoff

    betaDifferenceDecomposition :
      Inst.SelectedCMP109BetaDifferenceAttachment selectedSource TubePoint

    physicalCompositeD1ChainRule :
      Inst.PhysicalCompositeD1TransportResidual
        selectedSource Component Background Tangent Scalar

------------------------------------------------------------------------

open CMP109CanonicalSourceSemanticsObligations public

sourceSemanticsExtractionCreatesInhabitant : Bool
sourceSemanticsExtractionCreatesInhabitant = false

clayPromotion : Bool
clayPromotion = false
