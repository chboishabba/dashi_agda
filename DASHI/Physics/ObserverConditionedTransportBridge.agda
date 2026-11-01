module DASHI.Physics.ObserverConditionedTransportBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.CandidateOnlyCore as CandidateOnly

------------------------------------------------------------------------
-- Observer-conditioned transport.
--
-- This module records the formal shape discussed for engine acoustics,
-- light transport, caustics, and temporally persistent observer queries.
-- It does not claim that a quotient implementation, caustic solver,
-- asymptotic speedup, physical fidelity theorem, or RTX comparison has
-- already been proved.

record TransportSystem : Set₁ where
  field
    State : Set
    Source : Set
    Observer : Set
    Sample : Set

    advance : Source → State → State
    observe : Observer → State → Sample

open TransportSystem public

------------------------------------------------------------------------
-- Two full transport states are observer-equivalent when the selected
-- observer cannot distinguish them.

_≈[_]_ :
  {system : TransportSystem} →
  State system →
  Observer system →
  State system →
  Set
_≈[_]_ {system} left observer right =
  observe system observer left ≡ observe system observer right

observerEquivalentRefl :
  {system : TransportSystem} →
  (observer : Observer system) →
  (state : State system) →
  state ≈[ observer ] state
observerEquivalentRefl observer state = refl

------------------------------------------------------------------------
-- A relevance carrier is intentionally weaker than a constructed
-- mathematical quotient.  It stores a representative together with a
-- decoder into the observer sample and a certificate that the decoder
-- agrees with direct observation for that representative.

record ObserverRelevantCarrier
  (system : TransportSystem)
  (observer : Observer system) :
  Set₁ where
  field
    RelevantState : Set

    encodeRelevant :
      State system →
      RelevantState

    decodeRelevant :
      RelevantState →
      Sample system

    representativeSound :
      (state : State system) →
      decodeRelevant (encodeRelevant state) ≡
      observe system observer state

open ObserverRelevantCarrier public

------------------------------------------------------------------------
-- The temporal form persists a relevant carrier across frames rather than
-- rediscovering it independently.  This is the typed distinction between
-- screen-space motion-vector reuse and transport-state evolution.

record TemporalObserverTransport
  (system : TransportSystem)
  (observer : Observer system)
  (carrier : ObserverRelevantCarrier system observer) :
  Set₁ where
  field
    Input : Set

    seed :
      RelevantState carrier

    evolveRelevant :
      Input →
      RelevantState carrier →
      RelevantState carrier

    predict :
      RelevantState carrier →
      Sample system

    predictIsDecode :
      (relevant : RelevantState carrier) →
      predict relevant ≡ decodeRelevant carrier relevant

open TemporalObserverTransport public

------------------------------------------------------------------------
-- Candidate transport vocabulary.  These labels make explicit what is
-- shared with RTX / wave solvers and what is distinct in the proposed
-- DASHI bridge.

data TransportBridgeFeature : Set where
  sourceTransportObservation : TransportBridgeFeature
  observerEquivalence : TransportBridgeFeature
  relevantCarrier : TransportBridgeFeature
  temporalPersistence : TransportBridgeFeature
  acousticInstantiation : TransportBridgeFeature
  lightTransportInstantiation : TransportBridgeFeature
  causticOrStationaryPathReading : TransportBridgeFeature
  measuredSpeedupObligation : TransportBridgeFeature

canonicalTransportBridgeFeatures : List TransportBridgeFeature
canonicalTransportBridgeFeatures =
  sourceTransportObservation
  ∷ observerEquivalence
  ∷ relevantCarrier
  ∷ temporalPersistence
  ∷ acousticInstantiation
  ∷ lightTransportInstantiation
  ∷ causticOrStationaryPathReading
  ∷ measuredSpeedupObligation
  ∷ []

transportBridgeFeatureName : TransportBridgeFeature → String
transportBridgeFeatureName sourceTransportObservation =
  "source / transport / observation factorisation"
transportBridgeFeatureName observerEquivalence =
  "observer-induced equivalence"
transportBridgeFeatureName relevantCarrier =
  "observer-relevant carrier"
transportBridgeFeatureName temporalPersistence =
  "cross-frame transport-state persistence"
transportBridgeFeatureName acousticInstantiation =
  "microphone-conditioned acoustic instance"
transportBridgeFeatureName lightTransportInstantiation =
  "pixel-conditioned light-transport instance"
transportBridgeFeatureName causticOrStationaryPathReading =
  "caustic or stationary-path candidate reading"
transportBridgeFeatureName measuredSpeedupObligation =
  "measured computational speedup obligation"

transportBridgeFeatureStatement : TransportBridgeFeature → String
transportBridgeFeatureStatement sourceTransportObservation =
  "Acoustics and rendering share a source, transport update, and observer projection shape."
transportBridgeFeatureStatement observerEquivalence =
  "States with equal selected-observer samples are observationally equivalent for that query."
transportBridgeFeatureStatement relevantCarrier =
  "A reduced carrier may retain only data needed to decode the selected observer sample."
transportBridgeFeatureStatement temporalPersistence =
  "The reduced transport state may evolve across frames rather than being reconstructed framewise."
transportBridgeFeatureStatement acousticInstantiation =
  "A microphone is an observer and its waveform sample is an observer projection."
transportBridgeFeatureStatement lightTransportInstantiation =
  "A camera pixel is an observer and its radiance sample is an observer projection."
transportBridgeFeatureStatement causticOrStationaryPathReading =
  "A small path, mode, or caustic skeleton is a candidate realization of the relevant carrier."
transportBridgeFeatureStatement measuredSpeedupObligation =
  "Computational advantage must be established by implementation, error, and cost measurements."

transportBridgeFeatureRemainingGap : TransportBridgeFeature → String
transportBridgeFeatureRemainingGap sourceTransportObservation =
  "The shared factorisation alone proves neither physical fidelity nor computational superiority."
transportBridgeFeatureRemainingGap observerEquivalence =
  "Equality at one observer does not imply equality of the full field or equality for other observers."
transportBridgeFeatureRemainingGap relevantCarrier =
  "No minimal quotient, sufficient-statistic theorem, or bounded carrier construction is supplied here."
transportBridgeFeatureRemainingGap temporalPersistence =
  "No contraction, stability, occlusion, bifurcation, or long-horizon error theorem is supplied here."
transportBridgeFeatureRemainingGap acousticInstantiation =
  "No nonlinear engine-flow, duct, shock, turbulence, or calibrated microphone theorem is promoted."
transportBridgeFeatureRemainingGap lightTransportInstantiation =
  "No unbiased renderer, arbitrary-scene completeness, caustic completeness, or RTX replacement theorem is promoted."
transportBridgeFeatureRemainingGap causticOrStationaryPathReading =
  "The relevant carrier need not be one point; multiple paths, modes, branches, and diffuse contributions may be required."
transportBridgeFeatureRemainingGap measuredSpeedupObligation =
  "No asymptotic or empirical speedup is claimed until matched-quality benchmarks are discharged."

------------------------------------------------------------------------
-- Fail-closed governance.

record ObserverConditionedTransportGovernance : Set where
  field
    quotientConstructed : Bool
    quotientConstructedIsFalse : quotientConstructed ≡ false

    singleCausticAlwaysSufficient : Bool
    singleCausticAlwaysSufficientIsFalse :
      singleCausticAlwaysSufficient ≡ false

    physicallyEquivalentToFullSolver : Bool
    physicallyEquivalentToFullSolverIsFalse :
      physicallyEquivalentToFullSolver ≡ false

    fasterThanRTXProved : Bool
    fasterThanRTXProvedIsFalse : fasterThanRTXProved ≡ false

    fasterThanWaveSolverProved : Bool
    fasterThanWaveSolverProvedIsFalse :
      fasterThanWaveSolverProved ≡ false

    candidateBridgeOnly : Bool
    candidateBridgeOnlyIsTrue : candidateBridgeOnly ≡ true

open ObserverConditionedTransportGovernance public

canonicalObserverConditionedTransportGovernance :
  ObserverConditionedTransportGovernance
canonicalObserverConditionedTransportGovernance =
  record
    { quotientConstructed = false
    ; quotientConstructedIsFalse = refl
    ; singleCausticAlwaysSufficient = false
    ; singleCausticAlwaysSufficientIsFalse = refl
    ; physicallyEquivalentToFullSolver = false
    ; physicallyEquivalentToFullSolverIsFalse = refl
    ; fasterThanRTXProved = false
    ; fasterThanRTXProvedIsFalse = refl
    ; fasterThanWaveSolverProved = false
    ; fasterThanWaveSolverProvedIsFalse = refl
    ; candidateBridgeOnly = true
    ; candidateBridgeOnlyIsTrue = refl
    }

------------------------------------------------------------------------
-- Candidate-only receipt row linking this module to the repository's
-- existing non-promotion core.

observerConditionedTransportOwner : String
observerConditionedTransportOwner =
  "DASHI.Physics.ObserverConditionedTransportBridge"

observerConditionedTransportRow : CandidateOnly.CandidateOnlyRow
observerConditionedTransportRow =
  CandidateOnly.candidateOnlyRow
    "observer-conditioned transport"
    observerConditionedTransportOwner
    "transport + observer quotient candidate surface"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "Track a temporally persistent observer-relevant carrier for acoustic or light transport."
    "A quotient construction, fidelity theorem, complexity theorem, and matched-quality benchmark remain open."
    true
    false
    false
    false
    false
    false
    false
    false

observerConditionedTransportReceipt :
  CandidateOnly.CandidateOnlyReceipt observerConditionedTransportRow
observerConditionedTransportReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
