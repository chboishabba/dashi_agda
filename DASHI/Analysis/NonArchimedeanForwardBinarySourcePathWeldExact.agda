module DASHI.Analysis.NonArchimedeanForwardBinarySourcePathWeldExact where

------------------------------------------------------------------------
-- FORWARD WORD / BINARY WORD / SOURCE BOOL WELD
--
-- The DASHI forward compiler uses
--
--   useA -> a(x) = 3x
--   useB -> b(x) = 3x-1.
--
-- HittingWordPadding maps useA -> bit0 and useB -> bit1.  The external Lean
-- source uses the opposite conventional Bool labels:
--
--   rw_step x true  = a x
--   rw_step x false = b x.
--
-- Therefore the exact source convention is bit0 <-> true, bit1 <-> false.
-- This module proves that the BinaryWord evaluator is exactly Forward.run and
-- packages the Bool-label inversion explicitly so no later stopping consumer
-- can silently swap the two affine branches.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact as Forward
import DASHI.Analysis.NonArchimedeanHittingWordPaddingExact as Padding
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary

runBinary :
  (data : Forward.ForwardTranslationData) →
  {n : Nat} →
  Binary.BinaryWord n →
  Forward.State data →
  Forward.State data
runBinary data Binary.end state = state
runBinary data (Binary.bit0 word) state =
  runBinary data word (Forward.a data state)
runBinary data (Binary.bit1 word) state =
  runBinary data word (Forward.b data state)

forwardToBinaryRunExact :
  (data : Forward.ForwardTranslationData) →
  (word : Forward.ForwardWord data) →
  (state : Forward.State data) →
  runBinary data (Padding.forwardToBinary word) state
  ≡ Forward.run data word state
forwardToBinaryRunExact data Forward.done state = refl
forwardToBinaryRunExact data (Forward.useA word) state =
  forwardToBinaryRunExact data word (Forward.a data state)
forwardToBinaryRunExact data (Forward.useB word) state =
  forwardToBinaryRunExact data word (Forward.b data state)

sourceBoolStep :
  (data : Forward.ForwardTranslationData) →
  Bool →
  Forward.State data →
  Forward.State data
sourceBoolStep data true = Forward.a data
sourceBoolStep data false = Forward.b data

bit0UsesSourceTrue :
  (data : Forward.ForwardTranslationData) →
  {n : Nat} →
  (word : Binary.BinaryWord n) →
  (state : Forward.State data) →
  runBinary data (Binary.bit0 word) state
  ≡ runBinary data word (sourceBoolStep data true state)
bit0UsesSourceTrue data word state = refl

bit1UsesSourceFalse :
  (data : Forward.ForwardTranslationData) →
  {n : Nat} →
  (word : Binary.BinaryWord n) →
  (state : Forward.State data) →
  runBinary data (Binary.bit1 word) state
  ≡ runBinary data word (sourceBoolStep data false state)
bit1UsesSourceFalse data word state = refl

record SourceRwStepWeld
    (data : Forward.ForwardTranslationData) : Set₁ where
  field
    sourceStep : Bool → Forward.State data → Forward.State data
    sourceTrueIsA :
      (state : Forward.State data) →
      sourceStep true state ≡ Forward.a data state
    sourceFalseIsB :
      (state : Forward.State data) →
      sourceStep false state ≡ Forward.b data state

open SourceRwStepWeld public

record SourcePathWeldBoundary : Set where
  constructor sourcePathWeldBoundary
  field
    forwardBinaryRunEqualityOwned : Bool
    sourceTrueBranchIsA : Bool
    sourceFalseBranchIsB : Bool
    bit0MeansSourceFalse : Bool
    bit0MeansSourceTrue : Bool
    endpointBranchActionWeldClosedFromSourceDefinitions : Bool
    prefixAbsorptionNeedsSourceEndpointTheorem : Bool

canonicalSourcePathWeldBoundary : SourcePathWeldBoundary
canonicalSourcePathWeldBoundary =
  sourcePathWeldBoundary true true true false true true false

bitConventionExplicitlyCorrected :
  SourcePathWeldBoundary.bit0MeansSourceTrue
    canonicalSourcePathWeldBoundary
  ≡ true
bitConventionExplicitlyCorrected = refl

prefixAbsorptionDoesNotNeedSeparateSourceEndpointTheorem :
  SourcePathWeldBoundary.prefixAbsorptionNeedsSourceEndpointTheorem
    canonicalSourcePathWeldBoundary
  ≡ false
prefixAbsorptionDoesNotNeedSeparateSourceEndpointTheorem = refl
