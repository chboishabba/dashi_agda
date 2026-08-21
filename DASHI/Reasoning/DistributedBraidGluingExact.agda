module DASHI.Reasoning.DistributedBraidGluingExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A finite distributed-gluing model for the living-braid interpretation.
--
-- Coherent sections are the even-parity configurations of three local
-- holders.  Every individual observation is non-injective: no single holder
-- determines the global section.  A cyclic role rotation acts equivariantly
-- and preserves coherence.
------------------------------------------------------------------------

data Agent : Set where
  agentA agentB agentC : Agent

data CoherentSection : Set where
  section000 : CoherentSection
  section011 : CoherentSection
  section101 : CoherentSection
  section110 : CoherentSection

observe : Agent → CoherentSection → Bool
observe agentA section000 = false
observe agentA section011 = false
observe agentA section101 = true
observe agentA section110 = true
observe agentB section000 = false
observe agentB section011 = true
observe agentB section101 = false
observe agentB section110 = true
observe agentC section000 = false
observe agentC section011 = true
observe agentC section101 = true
observe agentC section110 = false

_≠_ : {A : Set} → A → A → Set
first ≠ second = first ≡ second → ⊥

section000Not011 : section000 ≠ section011
section000Not011 ()

section000Not101 : section000 ≠ section101
section000Not101 ()

section000Not110 : section000 ≠ section110
section000Not110 ()

SingleOwnerCollision : Agent → Set
SingleOwnerCollision agent =
  Σ CoherentSection
    (λ first →
      Σ CoherentSection
        (λ second →
          (observe agent first ≡ observe agent second)
          × (first ≠ second)))

singleOwnerNonInjective :
  (agent : Agent) →
  SingleOwnerCollision agent
singleOwnerNonInjective agentA =
  section000 , (section011 , (refl , section000Not011))
singleOwnerNonInjective agentB =
  section000 , (section101 , (refl , section000Not101))
singleOwnerNonInjective agentC =
  section000 , (section110 , (refl , section000Not110))

rotateAgent : Agent → Agent
rotateAgent agentA = agentB
rotateAgent agentB = agentC
rotateAgent agentC = agentA

rotateAgentThreeTimes :
  (agent : Agent) →
  rotateAgent (rotateAgent (rotateAgent agent)) ≡ agent
rotateAgentThreeTimes agentA = refl
rotateAgentThreeTimes agentB = refl
rotateAgentThreeTimes agentC = refl

rotateSection : CoherentSection → CoherentSection
rotateSection section000 = section000
rotateSection section011 = section101
rotateSection section101 = section110
rotateSection section110 = section011

rotateSectionThreeTimes :
  (section : CoherentSection) →
  rotateSection (rotateSection (rotateSection section)) ≡ section
rotateSectionThreeTimes section000 = refl
rotateSectionThreeTimes section011 = refl
rotateSectionThreeTimes section101 = refl
rotateSectionThreeTimes section110 = refl

rotationObservationEquivariant :
  (agent : Agent) →
  (section : CoherentSection) →
  observe (rotateAgent agent) (rotateSection section)
  ≡ observe agent section
rotationObservationEquivariant agentA section000 = refl
rotationObservationEquivariant agentA section011 = refl
rotationObservationEquivariant agentA section101 = refl
rotationObservationEquivariant agentA section110 = refl
rotationObservationEquivariant agentB section000 = refl
rotationObservationEquivariant agentB section011 = refl
rotationObservationEquivariant agentB section101 = refl
rotationObservationEquivariant agentB section110 = refl
rotationObservationEquivariant agentC section000 = refl
rotationObservationEquivariant agentC section011 = refl
rotationObservationEquivariant agentC section101 = refl
rotationObservationEquivariant agentC section110 = refl

record DistributedBraid : Set₁ where
  constructor distributedBraid
  field
    Holder : Set
    GlobalSection : Set
    LocalState : Holder → Set
    localObservation :
      (holder : Holder) → GlobalSection → LocalState holder
    rotateHolder : Holder → Holder
    rotateGlobal : GlobalSection → GlobalSection
    rotateLocal :
      (holder : Holder) →
      LocalState (rotateHolder holder) → LocalState holder
    observationEquivariant :
      (holder : Holder) →
      (section : GlobalSection) →
      rotateLocal holder
        (localObservation (rotateHolder holder) (rotateGlobal section))
      ≡ localObservation holder section
    noSingleOwner :
      (holder : Holder) →
      Σ GlobalSection
        (λ first →
          Σ GlobalSection
            (λ second →
              (localObservation holder first
               ≡ localObservation holder second)
              × (first ≠ second)))

open DistributedBraid public

canonicalDistributedBraid : DistributedBraid
canonicalDistributedBraid =
  distributedBraid
    Agent
    CoherentSection
    (λ holder → Bool)
    observe
    rotateAgent
    rotateSection
    (λ holder state → state)
    rotationObservationEquivariant
    singleOwnerNonInjective

communalObjectNotRecoverableFromAnySingleHolder :
  (holder : Holder canonicalDistributedBraid) →
  Σ (GlobalSection canonicalDistributedBraid)
    (λ first →
      Σ (GlobalSection canonicalDistributedBraid)
        (λ second →
          (localObservation canonicalDistributedBraid holder first
           ≡ localObservation canonicalDistributedBraid holder second)
          × (first ≠ second)))
communalObjectNotRecoverableFromAnySingleHolder =
  noSingleOwner canonicalDistributedBraid
