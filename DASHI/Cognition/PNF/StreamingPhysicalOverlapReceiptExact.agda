module DASHI.Cognition.PNF.StreamingPhysicalOverlapReceiptExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Physical receipt shape for parser/semantic overlap.
--
-- StreamingSemanticPacmanKernelExact owns the semantic prefix/suffix theorem.
-- This module does not re-prove or redefine that semantics. It records the
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
    parserSemanticOverlapWork : Nat

    -- A streaming implementation must have an explicit finite non-zero bound;
    -- zero would mean no producer/consumer handoff exists at all. The live
    -- SensibLaw Gate-A implementation currently uses a one-item queue.
    bufferBoundWitness : Nat
    bufferBoundExact : maxBufferedParserItems ≡ suc bufferBoundWitness

    -- Consumed parser history is never replayed merely because later parser
    -- output arrives.
    noPrefixReplay : parserPrefixReplayCount ≡ zero

open BoundedStreamingOverlapReceipt public

------------------------------------------------------------------------
-- EOF completion must be interpreted relative to physical partition shape.
--
-- A coarse serial pipeline can report a very high fraction complete at parser
-- EOF whenever the final parser partition is tiny. Therefore the meaningful
-- count is the amount completed at EOF *above* the serial partition floor.
--
--   pre-final work + final-partition work = all semantic work
--   pre-final work + overlap gain         = work complete at parser EOF
--
-- If overlap gain is zero, a high EOF completion percentage is entirely
-- explained by partition geometry and is not evidence of useful concurrency.
------------------------------------------------------------------------

record ParserEOFCompletionReceipt : Set where
  constructor parserEOFCompletionReceipt
  field
    preFinalPartitionConsumerCount : Nat
    finalPartitionConsumerCount : Nat
    totalSemanticConsumerCount : Nat
    semanticConsumerCountAtParserEOF : Nat
    overlapConsumerGainAtEOF : Nat
    postParserTailWork : Nat

    partitionAccounting :
      preFinalPartitionConsumerCount + finalPartitionConsumerCount
        ≡ totalSemanticConsumerCount

    eofAccounting :
      preFinalPartitionConsumerCount + overlapConsumerGainAtEOF
        ≡ semanticConsumerCountAtParserEOF

open ParserEOFCompletionReceipt public

data StaticFormalismProvesRuntimeOverlapFraction : Set where

data RawEOFPercentageAloneProvesUsefulOverlap : Set where

formalismDoesNotFabricateOverlapFraction :
  StaticFormalismProvesRuntimeOverlapFraction → ⊥
formalismDoesNotFabricateOverlapFraction ()

rawEOFPercentageIsNotOverlapProof :
  RawEOFPercentageAloneProvesUsefulOverlap → ⊥
rawEOFPercentageIsNotOverlapProof ()

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
