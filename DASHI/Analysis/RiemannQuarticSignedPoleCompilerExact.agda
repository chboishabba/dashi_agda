module DASHI.Analysis.RiemannQuarticSignedPoleCompilerExact where

open import Agda.Primitive using (Level; lsuc)

------------------------------------------------------------------------
-- Signed four-window quartic terminal compiler
--
-- This module mirrors the current Lean reduction without promoting either
-- remaining analytic theorem.  The concrete Lean side owns the same-object
-- identity
--
--   signed external = 1/2 <N-mu,Psi_t> + H_comb
--
-- and an explicit quantitative fourth-order target radius.  At the Agda
-- control layer we keep the two genuinely analytic inputs abstract:
--
--   * BandCoverage: 8/t lies inside that explicit radius;
--   * ExternalStrict: the signed N-mu + horizontal residual is below the
--     reflected target-pair contribution.
--
-- Everything after those inputs is compiler logic.
------------------------------------------------------------------------

data Contradiction : Set where

record QuarticSignedPoleCompiler {ell : Level} : Set (lsuc ell) where
  field
    BandCoverage : Set ell
    SignedNMuDiscrepancyControl : Set ell
    HorizontalRemainderControl : Set ell
    ExternalStrict : Set ell
    TargetPairLower : Set ell

    -- G1 consumer: explicit band coverage gives the target-pair lower bound.
    target-pair-from-band :
      BandCoverage -> TargetPairLower

    -- G2/G3 consumer: after the exact N-mu representation is installed,
    -- the two analytic controls compile to the single strict external bound.
    external-strict-from-controls :
      SignedNMuDiscrepancyControl ->
      HorizontalRemainderControl ->
      ExternalStrict

    -- G4: existing same-object cluster identity + strict upper closes.
    close :
      TargetPairLower ->
      ExternalStrict ->
      Contradiction

open QuarticSignedPoleCompiler public

compileQuarticSignedPoleContradiction :
  {ell : Level} ->
  (C : QuarticSignedPoleCompiler {ell}) ->
  BandCoverage C ->
  SignedNMuDiscrepancyControl C ->
  HorizontalRemainderControl C ->
  Contradiction
compileQuarticSignedPoleContradiction C band nmu horizontal =
  close C
    (target-pair-from-band C band)
    (external-strict-from-controls C nmu horizontal)
