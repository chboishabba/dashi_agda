module DASHI.Analysis.RiemannQuarticSignedPoleCompilerExact where

open import Agda.Primitive using (Level; lsuc)

------------------------------------------------------------------------
-- Signed four-window quartic terminal compiler
--
-- Clay-facing primitive cut:
--
--   G1  BandCoverage
--   G3  JointSignedCompletedResidual
--
-- The exact same-object assembly
--
--   signed external = 1/2 <N-mu,Psi_t> + H_comb
--
-- is compiler-owned on the Lean side.  Therefore the Clay-facing theorem
-- should not expose separate N-mu and horizontal inequalities unless proof
-- search genuinely needs them.
--
-- A stronger optional producer below retains the useful split
--
--   G3a  SignedNMuDiscrepancyControl
--   G3b  HorizontalRemainderControl
--   budget closure
--
-- without making that decomposition primitive.
------------------------------------------------------------------------

data Contradiction : Set where

record QuarticSignedPoleCompiler {ell : Level} : Set (lsuc ell) where
  field
    BandCoverage : Set ell
    JointSignedCompletedResidual : Set ell
    TargetPairLower : Set ell

    -- G1 consumer: explicit band coverage gives the target-pair lower bound.
    target-pair-from-band :
      BandCoverage -> TargetPairLower

    -- G3 is already stated on the exact signed completed residual.
    close :
      BandCoverage ->
      JointSignedCompletedResidual ->
      Contradiction

open QuarticSignedPoleCompiler public

compileQuarticSignedPoleContradiction :
  {ell : Level} ->
  (C : QuarticSignedPoleCompiler {ell}) ->
  BandCoverage C ->
  JointSignedCompletedResidual C ->
  Contradiction
compileQuarticSignedPoleContradiction C band joint =
  close C band joint

------------------------------------------------------------------------
-- Optional proof-search decomposition of G3.
--
-- This interface is deliberately stronger than the Clay-facing compiler.
-- It is retained because separate N-mu / horizontal estimates may be useful
-- analytically, but neither becomes a primitive final-paper obligation.
------------------------------------------------------------------------

record QuarticSignedResidualSplitProducer
    {ell : Level}
    (C : QuarticSignedPoleCompiler {ell}) : Set (lsuc ell) where
  field
    SignedNMuDiscrepancyControl : Set ell
    HorizontalRemainderControl : Set ell
    SplitBudgetClosure : Set ell

    joint-from-split :
      SignedNMuDiscrepancyControl ->
      HorizontalRemainderControl ->
      SplitBudgetClosure ->
      JointSignedCompletedResidual C

open QuarticSignedResidualSplitProducer public

compileJointSignedResidualFromSplit :
  {ell : Level} ->
  {C : QuarticSignedPoleCompiler {ell}} ->
  (P : QuarticSignedResidualSplitProducer C) ->
  SignedNMuDiscrepancyControl P ->
  HorizontalRemainderControl P ->
  SplitBudgetClosure P ->
  JointSignedCompletedResidual C
compileJointSignedResidualFromSplit P nmu horizontal budget =
  joint-from-split P nmu horizontal budget

compileQuarticSignedPoleContradictionFromSplit :
  {ell : Level} ->
  (C : QuarticSignedPoleCompiler {ell}) ->
  (P : QuarticSignedResidualSplitProducer C) ->
  BandCoverage C ->
  SignedNMuDiscrepancyControl P ->
  HorizontalRemainderControl P ->
  SplitBudgetClosure P ->
  Contradiction
compileQuarticSignedPoleContradictionFromSplit C P band nmu horizontal budget =
  compileQuarticSignedPoleContradiction C band
    (compileJointSignedResidualFromSplit P nmu horizontal budget)
