module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary where

------------------------------------------------------------------------
-- PROVENANCE / PURPOSE
--
-- Classical finite Hölder inequality.  Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- COMPILER BOUNDARY
--
-- The historical eight-point proof is expensive under Agda 2.9 because its
-- elementary rational/ring normalization graph is large.  Downstream NS
-- consumers do not need to normalize that proof again: they need only its
-- checked public theorem surface.
--
-- This module is therefore the canonical compiled import boundary for the
-- legacy eight-point theorem.  Compile it once with the persistent cache;
-- consumers should import this module rather than the implementation module.
-- No postulate, new analytic authority, or weakened theorem is introduced.
--
-- The implementation remains fail-closed mathematics in
-- NSTriadKNLuoFiniteEightPointSixThreeHolderExact.  This boundary deliberately
-- re-exports the complete legacy surface so existing record projections and
-- theorem names retain exactly the same types.
------------------------------------------------------------------------

open import
  DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact
  public
