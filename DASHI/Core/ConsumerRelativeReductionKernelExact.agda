module DASHI.Core.ConsumerRelativeReductionKernelExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- REPOSITORY-NATIVE GENERIC KERNEL
--
-- This module is a DASHI abstraction assembled from the repository's existing
-- future-equivalence, residual-reopening, observer-refinement and intervention
-- patterns.  It is not attributed to an external paper and does not impose a
-- symmetry on applications which do not possess one.
------------------------------------------------------------------------

run :
  ∀ {State Action : Set} →
  (Action → State → State) →
  List Action → State → State
run step [] state = state
run step (action ∷ rest) state = run step rest (step action state)

record ConsumerRelativeReduction
    (Fine Action Observation : Set) : Set₁ where
  constructor consumerRelativeReduction
  field
    Reduced : Set
    encode : Fine → Reduced
    fineStep : Action → Fine → Fine
    reducedStep : Action → Reduced → Reduced
    fineObserve : Fine → Observation
    reducedObserve : Reduced → Observation
    stepCommutes :
      (action : Action) (state : Fine) →
      encode (fineStep action state)
      ≡ reducedStep action (encode state)
    observationFactors :
      (state : Fine) →
      fineObserve state ≡ reducedObserve (encode state)

open ConsumerRelativeReduction public

runCommutes :
  ∀ {Fine Action Observation}
    (rom : ConsumerRelativeReduction Fine Action Observation) →
  (actions : List Action) →
  (state : Fine) →
  encode rom (run (fineStep rom) actions state)
  ≡ run (reducedStep rom) actions (encode rom state)
runCommutes rom [] state = refl
runCommutes rom (action ∷ rest) state =
  trans
    (runCommutes rom rest (fineStep rom action state))
    (cong (run (reducedStep rom) rest) (stepCommutes rom action state))

consumerFuturePreserved :
  ∀ {Fine Action Observation}
    (rom : ConsumerRelativeReduction Fine Action Observation) →
  (actions : List Action) →
  (state : Fine) →
  fineObserve rom (run (fineStep rom) actions state)
  ≡ reducedObserve rom (run (reducedStep rom) actions (encode rom state))
consumerFuturePreserved rom actions state =
  trans
    (observationFactors rom (run (fineStep rom) actions state))
    (cong (reducedObserve rom) (runCommutes rom actions state))

encodedEqualityImpliesConsumerFutureEquality :
  ∀ {Fine Action Observation}
    (rom : ConsumerRelativeReduction Fine Action Observation) →
  {left right : Fine} →
  encode rom left ≡ encode rom right →
  (actions : List Action) →
  fineObserve rom (run (fineStep rom) actions left)
  ≡ fineObserve rom (run (fineStep rom) actions right)
encodedEqualityImpliesConsumerFutureEquality rom encodedEq actions =
  trans
    (consumerFuturePreserved rom actions _)
    (trans
      (cong
        (λ reduced → reducedObserve rom (run (reducedStep rom) actions reduced))
        encodedEq)
      (sym (consumerFuturePreserved rom actions _)))

record ExactResidualReopening
    {Fine Action Observation : Set}
    (rom : ConsumerRelativeReduction Fine Action Observation) : Set₁ where
  constructor exactResidualReopening
  field
    Residual : Set
    residual : Fine → Residual
    reopen : Reduced rom → Residual → Fine
    reopenExact : (state : Fine) → reopen (encode rom state) (residual state) ≡ state

open ExactResidualReopening public

------------------------------------------------------------------------
-- Explicit target realization.  Consumer safety and even exact reopening do
-- not by themselves identify the reduced coordinates with an external target
-- phenomenon; that identification gets its own commuting witness.
------------------------------------------------------------------------

record ReductionRealizationWitness
    {Fine Action Observation Target : Set}
    (rom : ConsumerRelativeReduction Fine Action Observation)
    (target : Fine → Target) : Set₁ where
  constructor reductionRealizationWitness
  field
    realize : Reduced rom → Target
    realizationCommutes : (state : Fine) → target state ≡ realize (encode rom state)

open ReductionRealizationWitness public

record SymmetryAction (State : Set) : Set₁ where
  constructor symmetryAction
  field
    Symmetry : Set
    act : Symmetry → State → State

open SymmetryAction public

record SymmetryCompatibleReduction
    {Fine Action Observation : Set}
    (rom : ConsumerRelativeReduction Fine Action Observation)
    (fineSymmetry : SymmetryAction Fine)
    (reducedSymmetry : SymmetryAction (Reduced rom)) : Set₁ where
  constructor symmetryCompatibleReduction
  field
    symmetryMap : Symmetry fineSymmetry → Symmetry reducedSymmetry
    encodeEquivariant :
      (g : Symmetry fineSymmetry) (state : Fine) →
      encode rom (act fineSymmetry g state)
      ≡ act reducedSymmetry (symmetryMap g) (encode rom state)

open SymmetryCompatibleReduction public

symmetryPreservesEncodedEquality :
  ∀ {Fine Action Observation}
    {rom : ConsumerRelativeReduction Fine Action Observation}
    {fineSymmetry : SymmetryAction Fine}
    {reducedSymmetry : SymmetryAction (Reduced rom)} →
  (compatible : SymmetryCompatibleReduction rom fineSymmetry reducedSymmetry) →
  {left right : Fine} →
  encode rom left ≡ encode rom right →
  (g : Symmetry fineSymmetry) →
  encode rom (act fineSymmetry g left)
  ≡ encode rom (act fineSymmetry g right)
symmetryPreservesEncodedEquality {rom = rom} {fineSymmetry = fineSymmetry}
  {reducedSymmetry = reducedSymmetry} compatible encodedEq g =
  trans
    (encodeEquivariant compatible g _)
    (trans
      (cong (act reducedSymmetry (symmetryMap compatible g)) encodedEq)
      (sym (encodeEquivariant compatible g _)))

------------------------------------------------------------------------
-- Symmetry can also fail.  This is the exact "ask the symmetry question"
-- interface: a candidate symmetry is useful only if the equivariance square
-- closes; a witnessed failure is positive evidence not to force that symmetry.
------------------------------------------------------------------------

record SymmetryIncompatibilityWitness
    {Fine ReducedState Symmetry : Set}
    (encode : Fine → ReducedState)
    (fineAct : Symmetry → Fine → Fine)
    (reducedAct : Symmetry → ReducedState → ReducedState) : Set where
  constructor symmetryIncompatibilityWitness
  field
    symmetry : Symmetry
    state : Fine
    equivarianceWouldFail :
      encode (fineAct symmetry state)
      ≡ reducedAct symmetry (encode state) → ⊥

open SymmetryIncompatibilityWitness public

record MeasurementDiscriminator
    {Fine Action Observation : Set}
    (rom : ConsumerRelativeReduction Fine Action Observation)
    (left right : Fine) : Set₁ where
  constructor measurementDiscriminator
  field
    Measurement : Set
    measure : Fine → Measurement
    currentlyCollapsed : encode rom left ≡ encode rom right
    measurementSeparates : measure left ≡ measure right → ⊥

open MeasurementDiscriminator public

record EvidenceRefinement (Fine : Set) : Set₁ where
  constructor evidenceRefinement
  field
    OldEvidence : Fine → Set
    Measurement : Set
    measure : Fine → Measurement
    observed : Measurement

  RefinedEvidence : Fine → Set
  RefinedEvidence state = OldEvidence state × (measure state ≡ observed)

open EvidenceRefinement public

refinedEvidenceDescendsToOldEvidence :
  ∀ {Fine} (refinement : EvidenceRefinement Fine) {state} →
  RefinedEvidence refinement state → OldEvidence refinement state
refinedEvidenceDescendsToOldEvidence refinement = proj₁

record MechanisticEquifinalityWitness
    {Fine Action Observation : Set}
    (rom : ConsumerRelativeReduction Fine Action Observation) : Set₁ where
  constructor mechanisticEquifinalityWitness
  field
    Mechanism : Set
    mechanism : Fine → Mechanism
    left right : Fine
    sameConsumerCode : encode rom left ≡ encode rom right
    differentMechanism : mechanism left ≡ mechanism right → ⊥

open MechanisticEquifinalityWitness public

record InterventionCompatibleReduction
    {Fine Action Observation : Set}
    (rom : ConsumerRelativeReduction Fine Action Observation) : Set₁ where
  constructor interventionCompatibleReduction
  field
    Intervention : Set
    fineIntervene : Intervention → Fine → Fine
    reducedIntervene : Intervention → Reduced rom → Reduced rom
    interventionCommutes :
      (intervention : Intervention) (state : Fine) →
      encode rom (fineIntervene intervention state)
      ≡ reducedIntervene intervention (encode rom state)

open InterventionCompatibleReduction public

interventionConsumerPreserved :
  ∀ {Fine Action Observation}
    {rom : ConsumerRelativeReduction Fine Action Observation} →
  (compatible : InterventionCompatibleReduction rom) →
  (intervention : Intervention compatible) →
  (state : Fine) →
  fineObserve rom (fineIntervene compatible intervention state)
  ≡ reducedObserve rom
      (reducedIntervene compatible intervention (encode rom state))
interventionConsumerPreserved {rom = rom} compatible intervention state =
  trans
    (observationFactors rom (fineIntervene compatible intervention state))
    (cong (reducedObserve rom)
      (interventionCommutes compatible intervention state))

record HistorySensitiveFutureWitness
    {Fine Action Observation : Set}
    (fineStep : Action → Fine → Fine)
    (observe : Fine → Observation) : Set where
  constructor historySensitiveFutureWitness
  field
    left right : Fine
    sameCurrentObservation : observe left ≡ observe right
    separatingAction : Action
    futureSeparates :
      observe (fineStep separatingAction left)
      ≡ observe (fineStep separatingAction right) → ⊥

open HistorySensitiveFutureWitness public

record FidelityEscalationWitness
    {Fine Action LowObservation HighObservation : Set}
    (low : ConsumerRelativeReduction Fine Action LowObservation)
    (high : ConsumerRelativeReduction Fine Action HighObservation) : Set where
  constructor fidelityEscalationWitness
  field
    left right : Fine
    lowCollapses : encode low left ≡ encode low right
    highSeparates : encode high left ≡ encode high right → ⊥

open FidelityEscalationWitness public

------------------------------------------------------------------------
-- Falsification surface inspired by the repo's broader proof-search discipline:
-- a candidate compression is rejected by one collision whose declared future
-- consumer separates.  No global metric or statistical threshold is needed.
------------------------------------------------------------------------

record CandidateReductionFailure
    {Fine Action Observation CandidateCode : Set}
    (fineStep : Action → Fine → Fine)
    (observe : Fine → Observation)
    (candidate : Fine → CandidateCode) : Set where
  constructor candidateReductionFailure
  field
    left right : Fine
    candidateCollides : candidate left ≡ candidate right
    separatingTrace : List Action
    futureConsumerSeparates :
      observe (run fineStep separatingTrace left)
      ≡ observe (run fineStep separatingTrace right) → ⊥

open CandidateReductionFailure public

ScaleSafeReduction : Set → Set → Set → Set₁
ScaleSafeReduction = ConsumerRelativeReduction
