module DASHI.Physics.Closure.NSTriadKNLuoClayContractRound23Validation where

------------------------------------------------------------------------
-- Cumulative validation root for Round Twenty-Three.
--
-- Imports the complete Round Twenty-Two Galerkin defect-diffusion tranche and
-- checks the normalized terminal contract:
--
-- * literal Fefferman periodic alternative (B);
-- * no extra mean-zero, uniqueness or periodic-energy requirement;
-- * pressure periodicity from the official erratum;
-- * typed mean-zero centering and Galilean restoration;
-- * legacy submission witness to literal Fefferman witness adapter;
-- * end-to-end composition through the existing global physical reducer;
-- * explicit Clay preconditions, postconditions, proof invariants and gap
--   states;
-- * paper-facing fail-closed status surface.
--
-- The literal theorem type is implemented.  The physical theorem remains
-- uninhabited.  No uniform five-source tax, strict total coefficient,
-- periodic principal-value/CZ theorem, analytic cutoff convergence, local
-- critical restart producer, Galilean PDE proof or unconditional regularity
-- theorem is asserted.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoGalerkinDefectDiffusionRound22Validation
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMeanZeroGalileanReductionExact
import DASHI.Physics.Closure.NSTriadKNLuoLegacySubmissionToFeffermanAdapterExact
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact
import DASHI.Physics.Closure.NSTriadKNLuoClayPrePostInvariantContractRound23Exact
import DASHI.Papers.NavierStokes.ClayContractRound23
