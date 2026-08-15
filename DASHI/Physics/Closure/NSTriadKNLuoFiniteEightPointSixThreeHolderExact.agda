module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality, specialized to the finite eight-point
-- periodic carrier. Repository-original radical-free Agda proof; no DOI is
-- assigned.
--
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- COMPILER WRAPPER
--
-- Agda 2.9 profiling showed that even after the elementary rational algebra
-- was moved behind its own compiled boundary, the historical legacy module
-- still spent ~17 GB elaborating the final concrete Holder assembly.  The
-- remaining cause was repeated dependent substitution through concrete
-- eight-entry list proofs.
--
-- The implementation now lives in the transport boundary, where the internal
-- low/high masses are definitionally aligned with the recursive finite-list
-- quantities consumed by the proof.  This file deliberately contains no
-- proof body: it preserves the historical import path and public theorem
-- surface while downstream consumers pay only the compiled interface cost.
--
-- Validation order under the pinned Agda 2.9 toolchain is therefore:
--   1. algebra boundary;
--   2. transport boundary;
--   3. this legacy wrapper;
--   4. the immediate six-three kernel consumer;
--   5. ABC consumers last.
--
-- No postulate, theorem weakening, or new analytic authority is introduced.
------------------------------------------------------------------------

open import
  DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderTransportBoundary
  public
