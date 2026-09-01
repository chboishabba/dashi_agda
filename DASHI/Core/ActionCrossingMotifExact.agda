module DASHI.Core.ActionCrossingMotifExact where

open import DASHI.Core.Prelude
open import Data.List using (List; []; _∷_; length; map)

import DASHI.Core.ActionCrossingTraceCalculusExact as Trace
import DASHI.Core.ActionCrossingConsumerQuotientExact as Consumer
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- ACTION-CROSSING MOTIFS
--
-- Motifs are proof-bearing local shapes inside ordered action traces.  They do
-- not infer intent, legality, or semantics from shape alone.
------------------------------------------------------------------------

record RelayMotif {Strand Action : Set}
    (trace : Trace.ActionTrace Strand Action) : Set where
  constructor relay-motif
  field
    first second : Trace.CrossingEvent Strand Action
    traceExact : trace ≡ first ∷ second ∷ []
    relayJoin : Trace.rightStrand first ≡ Trace.leftStrand second

record ReturnCycleMotif {Strand Action : Set}
    (trace : Trace.ActionTrace Strand Action) : Set where
  constructor return-cycle-motif
  field
    out back : Trace.CrossingEvent Strand Action
    traceExact : trace ≡ out ∷ back ∷ []
    turnsBackAtRelay : Trace.rightStrand out ≡ Trace.leftStrand back
    returnsToOrigin : Trace.leftStrand out ≡ Trace.rightStrand back

record SplitMotif {Strand Action : Set}
    (trace : Trace.ActionTrace Strand Action) : Set where
  constructor split-motif
  field
    first second : Trace.CrossingEvent Strand Action
    traceExact : trace ≡ first ∷ second ∷ []
    commonSource : Trace.leftStrand first ≡ Trace.leftStrand second

record MergeMotif {Strand Action : Set}
    (trace : Trace.ActionTrace Strand Action) : Set where
  constructor merge-motif
  field
    first second : Trace.CrossingEvent Strand Action
    traceExact : trace ≡ first ∷ second ∷ []
    commonTarget : Trace.rightStrand first ≡ Trace.rightStrand second

record AlternatingMotif {Strand Action : Set}
    (trace : Trace.ActionTrace Strand Action) : Set where
  constructor alternating-motif
  field
    first middle last : Trace.CrossingEvent Strand Action
    traceExact : trace ≡ first ∷ middle ∷ last ∷ []
    firstLastLeft : Trace.leftStrand first ≡ Trace.leftStrand last
    firstLastRight : Trace.rightStrand first ≡ Trace.rightStrand last
    middleStartsAtFirstRight : Trace.rightStrand first ≡ Trace.leftStrand middle

------------------------------------------------------------------------
-- Action-erased support graph: the incidence skeleton survives independently
-- from action labels.  It is intentionally a list of support edges, not a claim
-- that the full trace is determined by the graph.
------------------------------------------------------------------------

record SupportEdge (Strand : Set) : Set where
  constructor support-edge
  field
    left right : Strand

open SupportEdge public

forgetAction :
  ∀ {Strand Action} →
  Trace.CrossingEvent Strand Action → SupportEdge Strand
forgetAction event =
  support-edge (Trace.leftStrand event) (Trace.rightStrand event)

supportGraph :
  ∀ {Strand Action} →
  Trace.ActionTrace Strand Action → List (SupportEdge Strand)
supportGraph = map forgetAction

------------------------------------------------------------------------
-- Finite calibration: equal crossing count can hide different motifs.
------------------------------------------------------------------------

data S : Set where a b c : S
data A : Set where transfer split merge return : A

ab : A → Trace.CrossingEvent S A
ab action = Trace.crossing-event a b action

bc : A → Trace.CrossingEvent S A
bc action = Trace.crossing-event b c action

ba : A → Trace.CrossingEvent S A
ba action = Trace.crossing-event b a action

ac : A → Trace.CrossingEvent S A
ac action = Trace.crossing-event a c action

relayTrace : Trace.ActionTrace S A
relayTrace = ab transfer ∷ bc transfer ∷ []

returnTrace : Trace.ActionTrace S A
returnTrace = ab transfer ∷ ba return ∷ []

splitTrace : Trace.ActionTrace S A
splitTrace = ab split ∷ ac split ∷ []

canonicalRelay : RelayMotif relayTrace
canonicalRelay = relay-motif (ab transfer) (bc transfer) refl refl

canonicalReturn : ReturnCycleMotif returnTrace
canonicalReturn = return-cycle-motif (ab transfer) (ba return) refl refl refl

canonicalSplit : SplitMotif splitTrace
canonicalSplit = split-motif (ab split) (ac split) refl refl

relayAndReturnHaveSameCrossingCount :
  length relayTrace ≡ length returnTrace
relayAndReturnHaveSameCrossingCount = refl

data MotifCode : Set where relayCode returnCode splitCode : MotifCode

motifCode : Trace.ActionTrace S A → MotifCode
motifCode (e1 ∷ e2 ∷ []) with Trace.leftStrand e1 | Trace.rightStrand e1 | Trace.leftStrand e2 | Trace.rightStrand e2
... | a | b | b | a = returnCode
... | a | b | b | c = relayCode
... | a | b | a | c = splitCode
... | _ | _ | _ | _ = relayCode
motifCode _ = relayCode

crossingCount : Trace.ActionTrace S A → Nat
crossingCount = length

countCannotRecoverMotif : INF.FactorsThrough crossingCount motifCode → ⊥
countCannotRecoverMotif =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      relayTrace returnTrace refl (λ ()))

------------------------------------------------------------------------
-- Consumer-relative motif survival.
------------------------------------------------------------------------

countConsumer : Consumer.TraceConsumer S A
countConsumer = Consumer.trace-consumer Nat crossingCount

motifConsumer : Consumer.TraceConsumer S A
motifConsumer = Consumer.trace-consumer MotifCode motifCode

relayReturnRewrite : Consumer.TraceRewrite {S} {A}
relayReturnRewrite = Consumer.trace-rewrite relayTrace returnTrace

countConsumerCollapsesRelayReturn : Consumer.InvisibleTo countConsumer relayReturnRewrite
countConsumerCollapsesRelayReturn = Consumer.invisible-to refl

motifConsumerSeparatesRelayReturn : Consumer.VisibleTo motifConsumer relayReturnRewrite
motifConsumerSeparatesRelayReturn = Consumer.visible-to (λ ())

relayReturnConsumerSplit :
  Consumer.ConsumerSplit countConsumer motifConsumer relayReturnRewrite
relayReturnConsumerSplit =
  Consumer.consumer-split
    countConsumerCollapsesRelayReturn
    motifConsumerSeparatesRelayReturn

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data MotifDeterminesIntent : Set where
data MotifDeterminesLegality : Set where
data SupportGraphDeterminesActionTrace : Set where
data SameCrossingCountDeterminesMotif : Set where
data RelayMeansObfuscation : Set where
data ReturnCycleMeansWashTrading : Set where

data MotifComplexityIsScalarWrongdoing : Set where

motifDoesNotDetermineIntent : MotifDeterminesIntent → ⊥
motifDoesNotDetermineIntent ()

motifDoesNotDetermineLegality : MotifDeterminesLegality → ⊥
motifDoesNotDetermineLegality ()

supportGraphDoesNotDetermineActionTrace : SupportGraphDeterminesActionTrace → ⊥
supportGraphDoesNotDetermineActionTrace ()

sameCrossingCountDoesNotDetermineMotif : SameCrossingCountDeterminesMotif → ⊥
sameCrossingCountDoesNotDetermineMotif ()

relayDoesNotMeanObfuscation : RelayMeansObfuscation → ⊥
relayDoesNotMeanObfuscation ()

returnCycleDoesNotMeanWashTrading : ReturnCycleMeansWashTrading → ⊥
returnCycleDoesNotMeanWashTrading ()

motifComplexityIsNotScalarWrongdoing : MotifComplexityIsScalarWrongdoing → ⊥
motifComplexityIsNotScalarWrongdoing ()

record ActionCrossingMotifBoundary : Set where
  constructor action-crossing-motif-boundary
  field
    relayMotifConstructed : Bool
    returnCycleMotifConstructed : Bool
    splitMotifConstructed : Bool
    supportGraphExplicit : Bool
    equalCrossingCountCanHideMotif : Bool
    motifVisibilityConsumerRelative : Bool
    motifDeterminesIntent : Bool
    supportGraphDeterminesTrace : Bool

canonicalActionCrossingMotifBoundary : ActionCrossingMotifBoundary
canonicalActionCrossingMotifBoundary =
  action-crossing-motif-boundary true true true true true true false false
