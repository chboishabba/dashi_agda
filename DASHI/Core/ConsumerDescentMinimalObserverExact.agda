module DASHI.Core.ConsumerDescentMinimalObserverExact where

------------------------------------------------------------------------
-- TOP-DOWN CONSUMER DESCENT / MINIMAL SUFFICIENCY
--
-- A public/coarse observation is sufficient for a declared consumer exactly
-- when equal coarse observations force equal consumer outcomes.  This is the
-- kernel/fibre formulation of descent.  On a sectioned projection, that
-- condition is equivalent to construction of an explicit factor map.
--
-- The canonical consumer observer is itself least informative among observers
-- sufficient for that consumer, in DASHI's information order: every sufficient
-- observer refines the consumer observer.  This is deterministic,
-- consumer-indexed minimality; it is not a statistical likelihood theorem and
-- does not promote the consumer into a world-complete ontology.
--
-- SOURCE / METHOD CALIBRATION
--
-- David Blackwell, "Equivalent Comparisons of Experiments",
-- Annals of Mathematical Statistics 24(2), 1953, 265--272.
-- DOI: 10.1214/aoms/1177729032.
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977.
-- DOI: 10.1145/512950.512973.
--
-- E. L. Lehmann and George Casella,
-- "Theory of Point Estimation", 2nd ed., Springer, 1998.
-- DOI: 10.1007/b98854.
--
-- Lehmann--Casella is calibration for the classical minimal-sufficiency
-- vocabulary only.  The constructive theorem below is deterministic and
-- consumer-indexed; it does not import likelihoods, probability families, or
-- almost-everywhere identification.
--
-- DASHI already uses Blackwell/Cousot in
-- MinimalSufficientObservationGovernanceExact.  The finite constructive proofs
-- below are local and require no probabilistic assumptions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned

record FactorsThrough
    {State Surface Outcome : Set}
    (observe : State → Surface)
    (consumer : State → Outcome) : Set₁ where
  constructor factorsThrough
  field
    factor : Surface → Outcome
    factorizes : (state : State) → consumer state ≡ factor (observe state)

open FactorsThrough public

FibreConstantFor :
  ∀ {State Surface Outcome : Set} →
  (State → Surface) → (State → Outcome) → Set
FibreConstantFor observe consumer =
  ∀ left right → observe left ≡ observe right → consumer left ≡ consumer right

ConsumerSufficient :
  ∀ {State Surface Outcome : Set} →
  (State → Surface) → (State → Outcome) → Set
ConsumerSufficient observe consumer = Observer.Refines consumer observe

factorsThroughImpliesFibreConstant :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  FactorsThrough observe consumer → FibreConstantFor observe consumer
factorsThroughImpliesFibreConstant factorization left right sameSurface =
  trans
    (factorizes factorization left)
    (trans
      (cong (factor factorization) sameSurface)
      (sym (factorizes factorization right)))

fibreConstantIsConsumerSufficient :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  FibreConstantFor observe consumer → ConsumerSufficient observe consumer
fibreConstantIsConsumerSufficient constant = constant

consumerSufficientIsFibreConstant :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  ConsumerSufficient observe consumer → FibreConstantFor observe consumer
consumerSufficientIsFibreConstant sufficient = sufficient

sectionedFibreConstantFactors :
  ∀ {State Surface Outcome : Set}
    (projection : Sectioned.SectionedProjection State Surface)
    (consumer : State → Outcome) →
  FibreConstantFor (Sectioned.project projection) consumer →
  FactorsThrough (Sectioned.project projection) consumer
sectionedFibreConstantFactors projection consumer constant =
  factorsThrough
    (Sectioned.representativeObservable projection consumer)
    (λ state →
      Sectioned.fibreConstantObservableReconstructsFromSection
        projection consumer constant state)

record LogicalIff (A B : Set) : Set where
  constructor logicalIff
  field
    forward : A → B
    backward : B → A

open LogicalIff public

sectionedDescentIffFibreConstant :
  ∀ {State Surface Outcome : Set}
    (projection : Sectioned.SectionedProjection State Surface)
    (consumer : State → Outcome) →
  LogicalIff
    (FactorsThrough (Sectioned.project projection) consumer)
    (FibreConstantFor (Sectioned.project projection) consumer)
sectionedDescentIffFibreConstant projection consumer =
  logicalIff
    factorsThroughImpliesFibreConstant
    (sectionedFibreConstantFactors projection consumer)

consumerObserverIsSufficient :
  ∀ {State Outcome : Set}
    (consumer : State → Outcome) →
  ConsumerSufficient consumer consumer
consumerObserverIsSufficient consumer left right same = same

record LeastSufficientConsumerObserver
    {State Outcome : Set}
    (consumer : State → Outcome) : Set₁ where
  constructor leastSufficientConsumerObserver
  field
    selfSufficient : ConsumerSufficient consumer consumer
    belowEverySufficient :
      ∀ {Surface : Set}
        (observe : State → Surface) →
      ConsumerSufficient observe consumer →
      Observer.Refines consumer observe

open LeastSufficientConsumerObserver public

canonicalConsumerObserverIsLeast :
  ∀ {State Outcome : Set}
    (consumer : State → Outcome) →
  LeastSufficientConsumerObserver consumer
canonicalConsumerObserverIsLeast consumer =
  leastSufficientConsumerObserver
    (consumerObserverIsSufficient consumer)
    (λ observe sufficient → sufficient)

record ConsumerNonDescentWitness
    {State Surface Outcome : Set}
    (observe : State → Surface)
    (consumer : State → Outcome) : Set where
  constructor consumerNonDescentWitness
  field
    left right : State
    sameSurface : observe left ≡ observe right
    differentOutcome : consumer left ≡ consumer right → ⊥

open ConsumerNonDescentWitness public

nonDescentWitnessBlocksSufficiency :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  ConsumerNonDescentWitness observe consumer →
  ConsumerSufficient observe consumer →
  ⊥
nonDescentWitnessBlocksSufficiency witness sufficient =
  differentOutcome witness
    (sufficient
      (left witness)
      (right witness)
      (sameSurface witness))

nonDescentWitnessBlocksFactorization :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  ConsumerNonDescentWitness observe consumer →
  FactorsThrough observe consumer →
  ⊥
nonDescentWitnessBlocksFactorization witness factorization =
  nonDescentWitnessBlocksSufficiency witness
    (fibreConstantIsConsumerSufficient
      (factorsThroughImpliesFibreConstant factorization))

record ConsumerDescentMinimalObserverBoundary : Set where
  constructor consumerDescentMinimalObserverBoundary
  field
    descentImpliesFibreConstancy : Bool
    sectionedFibreConstancyConstructsDescent : Bool
    consumerObserverIsLeastSufficient : Bool
    nonDescentWitnessBlocksConsumerSufficiency : Bool
    minimalSufficiencyMeansWorldCompleteness : Bool
    oneObserverIsBestForEveryConsumer : Bool

canonicalConsumerDescentMinimalObserverBoundary :
  ConsumerDescentMinimalObserverBoundary
canonicalConsumerDescentMinimalObserverBoundary =
  consumerDescentMinimalObserverBoundary true true true true false false
