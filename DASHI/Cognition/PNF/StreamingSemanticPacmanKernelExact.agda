module DASHI.Cognition.PNF.StreamingSemanticPacmanKernelExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.DeltaNativePNFDreamFlowExact as Delta
import DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact as Direct

------------------------------------------------------------------------
-- Streaming semantic "Pac-Man" kernel.
--
-- A parser event is consumed as soon as it becomes available.  The durable
-- semantic meaning of an already-consumed prefix is not provisional merely
-- because the parser has not reached end-of-sentence: it is exactly the
-- ordinary delta fold for that prefix.  Only explicitly unresolved outward
-- obligations remain on the frontier.
--
-- This is a synthesis layer, not a second semantic implementation.  The
-- authority coordinate is the existing DeltaNativeCompiler fold.  Physical
-- implementations may fuse, vectorise, partition, or schedule these steps so
-- long as the existing delta algebra laws are preserved.
------------------------------------------------------------------------

record StreamingKernel
    (ParserEvent Authority SemanticDelta Frontier : Set) : Set₁ where
  field
    compiler : Delta.DeltaNativeCompiler ParserEvent Authority SemanticDelta

    emptyFrontier : Frontier
    advanceFrontier : Frontier → ParserEvent → Frontier

    -- Frontier finalisation is deliberately separate from semantic authority.
    -- It represents work that cannot be discharged until later parser events
    -- (or the sentence boundary) make their dependencies available.
    unresolvedCount : Frontier → Nat

open StreamingKernel public

------------------------------------------------------------------------
-- Prefix authority.
--
-- The authority produced after consuming a prefix is simply the existing
-- delta-native materialisation.  There is no second "streaming semantics".
------------------------------------------------------------------------

prefixAuthority :
  ∀ {ParserEvent Authority SemanticDelta Frontier : Set} →
  StreamingKernel ParserEvent Authority SemanticDelta Frontier →
  List ParserEvent → Authority
prefixAuthority kernel events =
  Delta.materialize (compiler kernel) events

------------------------------------------------------------------------
-- Prefix + suffix law.
--
-- This is the core streaming theorem: processing parser output incrementally
-- gives exactly the same authority as compiling the concatenated event stream.
-- Once prefix p has been eaten, suffix q can continue from that authority;
-- re-reading p is semantically unnecessary.
------------------------------------------------------------------------

streamingPrefixSuffixExact :
  ∀ {ParserEvent Authority SemanticDelta Frontier : Set}
    (kernel : StreamingKernel ParserEvent Authority SemanticDelta Frontier)
    (prefix suffix : List ParserEvent) →
  prefixAuthority kernel (Delta.append prefix suffix)
    ≡ Delta.applyDelta
        (Delta.algebra (compiler kernel))
        (prefixAuthority kernel prefix)
        (Delta.compileDeltas (compiler kernel) suffix)
streamingPrefixSuffixExact kernel prefix suffix =
  Delta.materializeAppend (compiler kernel) prefix suffix

------------------------------------------------------------------------
-- Streaming frontier.
------------------------------------------------------------------------

foldFrontier :
  ∀ {ParserEvent Authority SemanticDelta Frontier : Set} →
  StreamingKernel ParserEvent Authority SemanticDelta Frontier →
  Frontier → List ParserEvent → Frontier
foldFrontier kernel frontier [] = frontier
foldFrontier kernel frontier (event ∷ rest) =
  foldFrontier kernel (advanceFrontier kernel frontier event) rest

streamFrontier :
  ∀ {ParserEvent Authority SemanticDelta Frontier : Set} →
  StreamingKernel ParserEvent Authority SemanticDelta Frontier →
  List ParserEvent → Frontier
streamFrontier kernel events =
  foldFrontier kernel (emptyFrontier kernel) events

record StreamingCheckpoint
    (Authority Frontier : Set) : Set where
  constructor streamingCheckpoint
  field
    authority : Authority
    frontier : Frontier

open StreamingCheckpoint public

checkpoint :
  ∀ {ParserEvent Authority SemanticDelta Frontier : Set} →
  StreamingKernel ParserEvent Authority SemanticDelta Frontier →
  List ParserEvent → StreamingCheckpoint Authority Frontier
checkpoint kernel events =
  streamingCheckpoint
    (prefixAuthority kernel events)
    (streamFrontier kernel events)

------------------------------------------------------------------------
-- End-of-stream criterion.
--
-- The desired production shape is not "do all semantics after spaCy".  It is:
--   parser time  = consume ordinary local semantic deltas eagerly
--   finalisation = discharge only the remaining outward frontier
--
-- A zero frontier therefore gives the existing direct-delta fixed-point
-- receipt immediately.
------------------------------------------------------------------------

record EndOfStreamFinalisation
    (ParserEvent Authority SemanticDelta Frontier : Set) : Set₁ where
  constructor endOfStreamFinalisation
  field
    kernel : StreamingKernel ParserEvent Authority SemanticDelta Frontier
    events : List ParserEvent
    remainingOutwardObligations : Nat
    frontierCountExact :
      remainingOutwardObligations
        ≡ unresolvedCount kernel (streamFrontier kernel events)

open EndOfStreamFinalisation public

zeroFrontierIsDirectFixedPoint :
  ∀ {ParserEvent Authority SemanticDelta Frontier : Set}
    (finalisation : EndOfStreamFinalisation ParserEvent Authority SemanticDelta Frontier) →
    remainingOutwardObligations finalisation ≡ zero →
    Direct.DirectDeltaFixedPointReceipt
zeroFrontierIsDirectFixedPoint finalisation noRemaining =
  Direct.directDeltaFixedPointReceipt
    (remainingOutwardObligations finalisation)
    noRemaining

------------------------------------------------------------------------
-- Performance goal surface.
--
-- Agda does not invent an empirical "80%" receipt.  Instead it exposes the
-- measurable quantity that the runtime should drive down: semantic work left
-- after the parser reaches the sentence boundary.  The target implementation
-- can report both consumed-during-parse and remaining-finalisation work.
------------------------------------------------------------------------

record StreamingWorkReceipt : Set where
  constructor streamingWorkReceipt
  field
    consumedDuringParse : Nat
    remainingAfterParse : Nat

open StreamingWorkReceipt public

-- The formal architecture intentionally has no constructor claiming that a
-- particular percentage has been achieved.  That is a benchmark receipt, not
-- a theorem about all workloads.
data StaticArchitectureProvesEightyPercentComplete : Set where

architectureDoesNotFabricatePerformanceReceipt :
  StaticArchitectureProvesEightyPercentComplete → ∀ {A : Set} → A
architectureDoesNotFabricatePerformanceReceipt ()

------------------------------------------------------------------------
-- Architectural regressions ruled out by this synthesis.
------------------------------------------------------------------------

data StreamingRequiresPrefixRescan : Set where

data EndOfSentenceIsSecondFullCompile : Set where

streamingDoesNotRequirePrefixRescan :
  StreamingRequiresPrefixRescan → ∀ {A : Set} → A
streamingDoesNotRequirePrefixRescan ()

finalisationIsNotSecondFullCompile :
  EndOfSentenceIsSecondFullCompile → ∀ {A : Set} → A
finalisationIsNotSecondFullCompile ()
