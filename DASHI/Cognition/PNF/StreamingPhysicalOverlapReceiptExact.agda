module DASHI.Cognition.PNF.StreamingPhysicalOverlapReceiptExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Physical receipt shape for parser/semantic overlap.
--
-- StreamingSemanticPacmanKernelExact owns the semantic prefix/suffix theorem.
-- This module does not re-prove or redefine that semantics.  It records the
-- physical obligations of an implementation that overlaps parser production
-- with semantic consumption.
------------------------------------------------------------------------

record BoundedStreamingOverlapReceipt : Set where
  constructor boundedStreamingOverlapReceipt
  field
    maxBufferedParserItems : Nat
    parserPrefixReplayCount : Nat
    semanticConsumerCountAtParserEOF : Nat
    totalSemanticConsumerCount : Nat

    -- A streaming implementation must have an explicit finite non-zero bound;
    -- zero would mean no producer/consumer handoff exists at all.  The live
    -- SensibLaw Gate-A implementation currently uses a one-item queue.
    bufferBoundWitness : Nat
    bufferBoundExact : maxBufferedParserItems ≡ suc bufferBoundWitness

    -- Consumed parser history is never replayed merely because later parser
    -- output arrives.
    noPrefixReplay : parserPrefixReplayCount ≡ zero

open BoundedStreamingOverlapReceipt public

------------------------------------------------------------------------
-- The literal amount completed by parser EOF is empirical.  The formal layer
-- exposes the numerator/denominator but fabricates no percentage threshold.
------------------------------------------------------------------------

record ParserEOFCompletionReceipt : Set where
  constructor parserEOFCompletionReceipt
  field
    semanticConsumerCountAtParserEOF : Nat
    totalSemanticConsumerCount : Nat
    postParserTailWork : Nat

open ParserEOFCompletionReceipt public

data StaticFormalismProvesRuntimeOverlapFraction : Set where

formalismDoesNotFabricateOverlapFraction :
  StaticFormalismProvesRuntimeOverlapFraction → ⊥
formalismDoesNotFabricateOverlapFraction ()

------------------------------------------------------------------------
-- Architectural regressions.
------------------------------------------------------------------------

data UnboundedParserHistoryIsStreaming : Set where

data PrefixReplayIsStreaming : Set where

data PhysicalOverlapCreatesSecondSemanticCompiler : Set where

unboundedParserHistoryIsNotStreaming :
  UnboundedParserHistoryIsStreaming → ⊥
unboundedParserHistoryIsNotStreaming ()

prefixReplayIsNotStreaming : PrefixReplayIsStreaming → ⊥
prefixReplayIsNotStreaming ()

physicalOverlapDoesNotCreateSecondSemanticCompiler :
  PhysicalOverlapCreatesSecondSemanticCompiler → ⊥
physicalOverlapDoesNotCreateSecondSemanticCompiler ()
