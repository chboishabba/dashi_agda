module DASHI.Core.ConsumerIndexedResidualRefinementExact where

------------------------------------------------------------------------
-- CONSUMER-INDEXED RESIDUAL REFINEMENT
--
-- Top-down rule:
--
--   declare consumer F
--   -> test whether coarse observer O is sufficient
--   -> if not, exhibit a consumer-relevant collision
--   -> add a typed residual R
--   -> prove the joint observer (O,R) is sufficient.
--
-- The key theorem is necessity, not merely construction: EVERY observer that
-- is sufficient for F must distinguish each O-collision on which F differs.
-- Hence a useful repair is not "more data" in the abstract; it must resolve the
-- particular collision fibre relevant to the declared consumer.
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
-- The constructive collision/residual theorems below are local DASHI results;
-- the citations calibrate information-order terminology only.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer

ConsumerSufficient :
  ∀ {State Surface Outcome : Set} →
  (State → Surface) → (State → Outcome) → Set
ConsumerSufficient observe consumer = Observer.Refines consumer observe

record ConsumerRelevantCollision
    {State Surface Outcome : Set}
    (observe : State → Surface)
    (consumer : State → Outcome) : Set where
  constructor consumer-relevant-collision
  field
    left right : State
    sameSurface : observe left ≡ observe right
    differentOutcome : consumer left ≡ consumer right → ⊥

open ConsumerRelevantCollision public

coarseCollisionBlocksSufficiency :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  ConsumerRelevantCollision observe consumer →
  ConsumerSufficient observe consumer →
  ⊥
coarseCollisionBlocksSufficiency collision sufficient =
  differentOutcome collision
    (sufficient
      (left collision)
      (right collision)
      (sameSurface collision))

-- A sufficient observer must distinguish EVERY consumer-relevant collision,
-- regardless of how its carrier is represented.
everySufficientObserverSeparatesRelevantCollision :
  ∀ {State Coarse Fine Outcome : Set}
    {coarse : State → Coarse}
    {fine : State → Fine}
    {consumer : State → Outcome} →
  ConsumerRelevantCollision coarse consumer →
  ConsumerSufficient fine consumer →
  fine (left _) ≡ fine (right _) → ⊥
everySufficientObserverSeparatesRelevantCollision collision sufficient sameFine =
  differentOutcome collision
    (sufficient
      (left collision)
      (right collision)
      sameFine)

pairEquality :
  ∀ {A B : Set} {a a' : A} {b b' : B} →
  a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
pairEquality refl refl = refl

record ResidualRepair
    {State Coarse Residual Outcome : Set}
    (coarse : State → Coarse)
    (residual : State → Residual)
    (consumer : State → Outcome) : Set where
  constructor residual-repair
  field
    jointSufficient :
      ConsumerSufficient (Observer.pairObserver coarse residual) consumer

open ResidualRepair public

-- If (coarse,residual) is sufficient, the residual is forced to distinguish
-- every consumer-relevant collision that the coarse observer erased.
residualMustSeparateRelevantCollision :
  ∀ {State Coarse Residual Outcome : Set}
    {coarse : State → Coarse}
    {residual : State → Residual}
    {consumer : State → Outcome} →
  (collision : ConsumerRelevantCollision coarse consumer) →
  ResidualRepair coarse residual consumer →
  residual (left collision) ≡ residual (right collision) → ⊥
residualMustSeparateRelevantCollision collision repair sameResidual =
  differentOutcome collision
    (jointSufficient repair
      (left collision)
      (right collision)
      (pairEquality (sameSurface collision) sameResidual))

-- The same hypotheses construct an exact strict refinement witness.
consumerRelevantResidualGivesStrictRefinement :
  ∀ {State Coarse Residual Outcome : Set}
    {coarse : State → Coarse}
    {residual : State → Residual}
    {consumer : State → Outcome} →
  (collision : ConsumerRelevantCollision coarse consumer) →
  (repair : ResidualRepair coarse residual consumer) →
  Observer.StrictRefinement
    coarse
    (Observer.pairObserver coarse residual)
consumerRelevantResidualGivesStrictRefinement collision repair =
  Observer.strictPairRefinement
    _ _
    (left collision)
    (right collision)
    (sameSurface collision)
    (residualMustSeparateRelevantCollision collision repair)

-- Exact reconstruction is stronger than any one consumer requirement: a
-- separating observer is sufficient for every deterministic consumer.
separatingObserverIsSufficientForEveryConsumer :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface} →
  Observer.Separating observe →
  (consumer : State → Outcome) →
  ConsumerSufficient observe consumer
separatingObserverIsSufficientForEveryConsumer separating consumer left right same =
  cong consumer (separating left right same)

-- Two semantically distinct observer carriers may both be sufficient for the
-- same declared consumer.  This record deliberately carries no equality or
-- decoder between their surface types.
record ParallelConsumerSufficiency
    {State A B Outcome : Set}
    (leftObserver : State → A)
    (rightObserver : State → B)
    (consumer : State → Outcome) : Set where
  constructor parallel-consumer-sufficiency
  field
    leftSufficient : ConsumerSufficient leftObserver consumer
    rightSufficient : ConsumerSufficient rightObserver consumer

open ParallelConsumerSufficiency public

parallelObserversAgreeAtConsumer :
  ∀ {State A B Outcome : Set}
    {leftObserver : State → A}
    {rightObserver : State → B}
    {consumer : State → Outcome} →
  ParallelConsumerSufficiency leftObserver rightObserver consumer →
  ∀ x y →
  leftObserver x ≡ leftObserver y →
  rightObserver x ≡ rightObserver y →
  consumer x ≡ consumer y
parallelObserversAgreeAtConsumer parallel x y sameLeft sameRight =
  leftSufficient parallel x y sameLeft

record ConsumerIndexedResidualRefinementBoundary : Set where
  field
    collisionBlocksCoarseSufficiency : Bool
    everySufficientRepairMustSeparateRelevantCollision : Bool
    sufficientResidualConstructsStrictRefinement : Bool
    separatingObserverWorksForEveryConsumer : Bool
    parallelSufficiencyIdentifiesObserverCarriers : Bool
    refinementAutomaticallyMeansWorldCompleteness : Bool

canonicalConsumerIndexedResidualRefinementBoundary :
  ConsumerIndexedResidualRefinementBoundary
canonicalConsumerIndexedResidualRefinementBoundary = record
  { collisionBlocksCoarseSufficiency = true
  ; everySufficientRepairMustSeparateRelevantCollision = true
  ; sufficientResidualConstructsStrictRefinement = true
  ; separatingObserverWorksForEveryConsumer = true
  ; parallelSufficiencyIdentifiesObserverCarriers = false
  ; refinementAutomaticallyMeansWorldCompleteness = false
  }
