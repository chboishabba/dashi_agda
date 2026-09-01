module DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Stratified options, bracketed enablement, and TSFV worlds.
--
-- Stratum = which typed continuations exist here.
-- Bracket = which available continuations may plug in now, given prerequisites.
-- TSFV world = one admissible history through those enabled choices.
------------------------------------------------------------------------

data OptionId : Set where
  option : Nat → OptionId

data EventId : Set where
  event : Nat → EventId

record StratifiedOption : Set where
  constructor stratifiedOption
  field
    optionId : OptionId
    phaseRoles : Context.OrientedRolePair
    primeLane : Signed.SSPPrime
    candidateFraction : Context.FractranFraction

open StratifiedOption public

record Stratum : Set where
  constructor stratum
  field
    available : List StratifiedOption

open Stratum public

record BracketDependency : Set where
  constructor bracketDependency
  field
    prerequisite : EventId
    dependent : EventId
    prerequisitePrime : Signed.SSPPrime
    dependentPrime : Signed.SSPPrime

open BracketDependency public

record Bracket : Set where
  constructor bracket
  field
    dependencies : List BracketDependency

open Bracket public

record EventOccurrence : Set where
  constructor eventOccurrence
  field
    eventId : EventId
    chosenOption : StratifiedOption
    contextualState : Context.ContextualOccurrenceState

open EventOccurrence public

record WorldHistory : Set where
  constructor worldHistory
  field
    worldId : Context.WorldId
    events : List EventOccurrence
    currentStratum : Stratum
    currentBracket : Bracket

open WorldHistory public

------------------------------------------------------------------------
-- Bracket evidence is intentionally explicit.  FRACTRAN divisibility is the
-- executable analogue of prerequisite satisfaction, but this formal semantic
-- layer does not infer semantic authority from divisibility alone.
------------------------------------------------------------------------

record BracketEnablement : Set where
  constructor bracketEnablement
  field
    option : StratifiedOption
    prerequisiteSatisfied : Bool
    fractionExecutable : Bool
    semanticTypeCompatible : Bool

open BracketEnablement public

enabled : BracketEnablement → Bool
enabled (bracketEnablement option true true true) = true
enabled _ = false

record AdmissibleEventExtension : Set where
  constructor admissibleEventExtension
  field
    before : WorldHistory
    next : EventOccurrence
    enablement : BracketEnablement
    isEnabled : enabled enablement ≡ true

open AdmissibleEventExtension public

extendWorld : AdmissibleEventExtension → WorldHistory
extendWorld extension =
  worldHistory
    (worldId (before extension))
    (next extension ∷ events (before extension))
    (currentStratum (before extension))
    (currentBracket (before extension))

------------------------------------------------------------------------
-- Multiverse is all supplied admissible histories.  No eager choice between
-- observationally equivalent histories is required.
------------------------------------------------------------------------

record TSFVMultiverse : Set where
  constructor tsfvMultiverse
  field
    worlds : List WorldHistory

open TSFVMultiverse public

record WorldPairResidual : Set where
  constructor worldPairResidual
  field
    left right : WorldHistory
    sameCurrentObservation : Bool
    historiesRemainDistinct : Bool

open WorldPairResidual public

------------------------------------------------------------------------
-- Hypercomplex/fine zero: the ternary zero is a query-relative quotient state,
-- not definitionally the unique fine fixed point.  It can retain several live
-- admissible continuations and several worlds above the same observation.
------------------------------------------------------------------------

data ZeroReason : Set where
  exactFixedPoint : ZeroReason
  orientationUnobserved : ZeroReason
  orientationUnresolved : ZeroReason
  bracketDeferred : ZeroReason
  alternativesRetained : ZeroReason
  projectionCollapsed : ZeroReason

record ZeroFibre : Set where
  constructor zeroFibre
  field
    reason : ZeroReason
    liveOptions : List StratifiedOption
    liveWorlds : List WorldHistory
    coarseValue : Trit.SSPTrit
    coarseIsZero : coarseValue ≡ Trit.sspZero

open ZeroFibre public

------------------------------------------------------------------------
-- Situated inversion.  Any fine component may have an ambient involution;
-- only a receipt-bearing lift through current stratum/bracket/world is lawful.
------------------------------------------------------------------------

record SituatedPhaseInversion : Set where
  constructor situatedPhaseInversion
  field
    world : WorldHistory
    phase : Context.PhaseInversionCandidate
    stratumReceipt : Bool
    bracketReceipt : Bool
    historyReceipt : Bool
    typeReceipt : Bool

open SituatedPhaseInversion public

phaseInversionAdmissible : SituatedPhaseInversion → Bool
phaseInversionAdmissible
  (situatedPhaseInversion world phase true true true true) = true
phaseInversionAdmissible _ = false

record LawfulWorldPhaseInversion : Set where
  constructor lawfulWorldPhaseInversion
  field
    situated : SituatedPhaseInversion
    lawful : phaseInversionAdmissible situated ≡ true

open LawfulWorldPhaseInversion public

------------------------------------------------------------------------
-- Consumer quotient: same requested observation does not erase the tail/world
-- order fibre.  This is the semantic analogue of retaining linear extensions
-- that a current SSSP consumer cannot distinguish.
------------------------------------------------------------------------

record ConsumerQuotient : Set where
  constructor consumerQuotient
  field
    requestedPrime : Signed.SSPPrime
    visibleTrit : Trit.SSPTrit
    residualWorlds : List WorldHistory
    residualOptions : List StratifiedOption

open ConsumerQuotient public

record BracketedTSFVBoundary : Set where
  constructor bracketedTSFVBoundary
  field
    availableMeansEnabled : Bool
    ambientInverseMeansLawfulInverse : Bool
    zeroMeansUniqueFineState : Bool
    sameObservationErasesWorldHistory : Bool
    bracketMayDependOnEarlierPredicate : Bool
    multiverseRetainsAdmissibleWorldAlternatives : Bool

canonicalBracketedTSFVBoundary : BracketedTSFVBoundary
canonicalBracketedTSFVBoundary =
  bracketedTSFVBoundary false false false false true true
