{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109CanonicalSourceSemanticsObligationsExact where

open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- Canonical non-Round owner for the residual CMP109 source-semantics package.
--
-- Historical scheduler states are provenance only.  This module does not turn
-- an `open`, `blocked`, source-citation, or proof-level receipt into an
-- inhabitant.  The three fields below are deliberately the remaining typed
-- payments to be instantiated on the selected literal Balaban source object.
------------------------------------------------------------------------

record CMP109CanonicalSourceSemanticsObligations
    (GeneratedHistoryResponse
     BetaDifferenceDecomposition
     PhysicalCompositeD1ChainRule : Set) : Set₁ where
  field
    generatedHistoryResponseProducer : GeneratedHistoryResponse
    betaDifferenceDecomposition : BetaDifferenceDecomposition
    physicalCompositeD1ChainRule : PhysicalCompositeD1ChainRule

open CMP109CanonicalSourceSemanticsObligations public

-- Extraction is a scheduler contraction only; it does not assert that any of
-- the three residual source-semantic payments has been discharged.
sourceSemanticsExtractionCreatesInhabitant : Bool
sourceSemanticsExtractionCreatesInhabitant = false
