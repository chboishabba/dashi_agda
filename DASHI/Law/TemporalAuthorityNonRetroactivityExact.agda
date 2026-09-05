module DASHI.Law.TemporalAuthorityNonRetroactivityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A later-produced predicate cannot serve as the historical producer of an
-- earlier intervention.  This is a generic temporal provenance theorem shape.
------------------------------------------------------------------------

data TimeOrder : Set where
  before sameTime after : TimeOrder

data PredicateKind : Set where
  initialAuthority downstreamPredicate contrabandDiscovery nonCompliance : PredicateKind

data InterventionKind : Set where
  stop wand search arrest : InterventionKind

record TemporalProducerClaim : Set where
  constructor temporalProducerClaim
  field
    predicate : PredicateKind
    intervention : InterventionKind
    relation : TimeOrder
    claimsToJustifyEarlierIntervention : Bool
    temporalReference : String

open TemporalProducerClaim public

record RetroactiveProducer (claim : TemporalProducerClaim) : Set where
  constructor retroactiveProducer
  field
    predicateOccursAfter : relation claim ≡ after
    assertedAsEarlierProducer : claimsToJustifyEarlierIntervention claim ≡ true

open RetroactiveProducer public

record TemporalAuthorityBoundary : Set where
  constructor temporalAuthorityBoundary
  field
    laterPredicateAutomaticallyJustifiesEarlierIntervention : Bool
    laterPredicateAutomaticallyJustifiesEarlierInterventionIsFalse :
      laterPredicateAutomaticallyJustifiesEarlierIntervention ≡ false
    downstreamLawfulnessRetroactivelyClosesUpstreamLawfulness : Bool
    downstreamLawfulnessRetroactivelyClosesUpstreamLawfulnessIsFalse :
      downstreamLawfulnessRetroactivelyClosesUpstreamLawfulness ≡ false
    newDownstreamPredicateMayAuthoriseLaterTransition : Bool
    newDownstreamPredicateMayAuthoriseLaterTransitionIsTrue :
      newDownstreamPredicateMayAuthoriseLaterTransition ≡ true

canonicalTemporalAuthorityBoundary : TemporalAuthorityBoundary
canonicalTemporalAuthorityBoundary =
  temporalAuthorityBoundary false refl false refl true refl

------------------------------------------------------------------------
-- Concrete chronology examples.
------------------------------------------------------------------------

contrabandAfterSearch : TemporalProducerClaim
contrabandAfterSearch = temporalProducerClaim
  contrabandDiscovery search after true
  "contraband discovered after search cannot be the historical producer of that search"

nonComplianceAfterInitialStop : TemporalProducerClaim
nonComplianceAfterInitialStop = temporalProducerClaim
  nonCompliance stop after true
  "later non-compliance may affect downstream powers but cannot produce the earlier stop"

contrabandAfterSearchIsRetroactive : RetroactiveProducer contrabandAfterSearch
contrabandAfterSearchIsRetroactive = retroactiveProducer refl refl

nonComplianceAfterStopIsRetroactive : RetroactiveProducer nonComplianceAfterInitialStop
nonComplianceAfterStopIsRetroactive = retroactiveProducer refl refl

------------------------------------------------------------------------
-- BIDI: temporal provenance is an independent closure coordinate.
------------------------------------------------------------------------

data TemporalClosure : Set where
  chronologyClosed chronologyOpen : TemporalClosure

data TemporalReverseResult : Set where
  temporalClosed : TemporalReverseResult
  temporalProducerRequired : TemporalReverseResult

reverseTemporal : TemporalClosure → TemporalReverseResult
reverseTemporal chronologyClosed = temporalClosed
reverseTemporal chronologyOpen = temporalProducerRequired

missingChronologyReopensTemporalProducer :
  reverseTemporal chronologyOpen ≡ temporalProducerRequired
missingChronologyReopensTemporalProducer = refl

record UpstreamDownstreamLawfulness : Set where
  constructor upstreamDownstreamLawfulness
  field
    upstreamClosed : Bool
    downstreamClosed : Bool
    downstreamClosesUpstream : Bool
    downstreamClosesUpstreamIsFalse : downstreamClosesUpstream ≡ false

open UpstreamDownstreamLawfulness public

canonicalDownstreamCannotRetroactivelyCloseUpstream : UpstreamDownstreamLawfulness
canonicalDownstreamCannotRetroactivelyCloseUpstream =
  upstreamDownstreamLawfulness false true false refl
