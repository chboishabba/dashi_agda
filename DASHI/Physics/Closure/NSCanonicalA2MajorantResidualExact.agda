{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalA2MajorantResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES A2 MAJORANT RESIDUAL
--
-- Source boundary: Fefferman's Clay Navier--Stokes problem statement fixes the
-- whole-space theorem target.  The low/high majorant decomposition below is a
-- DASHI extension distilled from the current non-Round A-frontier.
--
-- All reference objects and domination predicates are external parameters.
------------------------------------------------------------------------

record CanonicalA2MajorantResidual
    (SelectedContinuumSource : Set)
    (LowPhysicalMajorant : Set)
    (HighPhysicalMajorant : Set)
    (LowConvolutionEnvelope : Set)
    (HighInverseSixthEnvelope : Set)
    (selectedSource : SelectedContinuumSource)
    (selectedLowMajorant : LowPhysicalMajorant)
    (selectedHighMajorant : HighPhysicalMajorant)
    (selectedLowEnvelope : LowConvolutionEnvelope)
    (selectedHighEnvelope : HighInverseSixthEnvelope)
    (LowPhysicalMajorantDomination :
      SelectedContinuumSource → LowPhysicalMajorant → LowConvolutionEnvelope → Set)
    (HighPhysicalMajorantDomination :
      SelectedContinuumSource → HighPhysicalMajorant → HighInverseSixthEnvelope → Set) : Set₁ where
  field
    lowPhysicalMajorantDomination :
      LowPhysicalMajorantDomination selectedSource selectedLowMajorant selectedLowEnvelope
    highPhysicalMajorantDomination :
      HighPhysicalMajorantDomination selectedSource selectedHighMajorant selectedHighEnvelope
