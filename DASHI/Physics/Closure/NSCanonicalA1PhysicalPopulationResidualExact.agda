{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalA1PhysicalPopulationResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES A1 PHYSICAL POPULATION RESIDUAL
--
-- Source boundary:
--   Charles L. Fefferman, "Existence and Smoothness of the Navier--Stokes
--   Equation", Clay Mathematics Institute Millennium Prize Problem (2000).
--
-- The split below is a DASHI extension extracted from the current non-Round
-- whole-space frontier.  It is not source content and it does not prove A.
-- The selected source, canonical pair data, heat/envelope data, and the two
-- same-object relations are fixed before the residual can be inhabited.
------------------------------------------------------------------------

record CanonicalA1PhysicalPopulationResidual
    (SelectedContinuumSource : Set)
    (CanonicalPairData : Set)
    (HighFrequencyHeatEnvelopeData : Set)
    (selectedSource : SelectedContinuumSource)
    (selectedPairData : CanonicalPairData)
    (selectedHeatEnvelopeData : HighFrequencyHeatEnvelopeData)
    (ActualContinuumPopulatesCanonicalPair :
      SelectedContinuumSource → CanonicalPairData → Set)
    (HighFrequencyPhysicalHeatEnvelopeWeld :
      SelectedContinuumSource → HighFrequencyHeatEnvelopeData → Set) : Set₁ where
  field
    actualCanonicalPairPopulation :
      ActualContinuumPopulatesCanonicalPair selectedSource selectedPairData
    highFrequencyHeatEnvelopeWeld :
      HighFrequencyPhysicalHeatEnvelopeWeld selectedSource selectedHeatEnvelopeData
