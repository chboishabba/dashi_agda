module DASHI.Unified.ThreePhaseCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Topology.HelicalWeaveMappingTorusExact as Helix
import DASHI.Reasoning.DistributedBraidGluingExact as Braid
import DASHI.Physics.Closure.KleinQuarticGenerationSymmetryExact as Klein

------------------------------------------------------------------------
-- Cross-pollination without conflation.
--
-- Helical stitch phase, distributed-holder role and three-factor slot all
-- carry the same free cyclic order-three action.  Explicit mutually inverse
-- maps intertwine those actions.  This proves a shared C3 torsor shape; it does
-- not identify stitches, people or Klein-quartic factors physically.
------------------------------------------------------------------------

_≠_ : {A : Set} → A → A → Set
first ≠ second = first ≡ second → ⊥

phaseToAgent : Helix.Phase3 → Braid.Agent
phaseToAgent Helix.phase0 = Braid.agentA
phaseToAgent Helix.phase1 = Braid.agentB
phaseToAgent Helix.phase2 = Braid.agentC

agentToPhase : Braid.Agent → Helix.Phase3
agentToPhase Braid.agentA = Helix.phase0
agentToPhase Braid.agentB = Helix.phase1
agentToPhase Braid.agentC = Helix.phase2

agentAfterPhase :
  (phase : Helix.Phase3) →
  agentToPhase (phaseToAgent phase) ≡ phase
agentAfterPhase Helix.phase0 = refl
agentAfterPhase Helix.phase1 = refl
agentAfterPhase Helix.phase2 = refl

phaseAfterAgent :
  (agent : Braid.Agent) →
  phaseToAgent (agentToPhase agent) ≡ agent
phaseAfterAgent Braid.agentA = refl
phaseAfterAgent Braid.agentB = refl
phaseAfterAgent Braid.agentC = refl

phaseAgentRotationEquivariant :
  (phase : Helix.Phase3) →
  phaseToAgent (Helix.rotatePhase phase)
  ≡ Braid.rotateAgent (phaseToAgent phase)
phaseAgentRotationEquivariant Helix.phase0 = refl
phaseAgentRotationEquivariant Helix.phase1 = refl
phaseAgentRotationEquivariant Helix.phase2 = refl

phaseToFactor : Helix.Phase3 → Klein.Factor3
phaseToFactor Helix.phase0 = Klein.factorA
phaseToFactor Helix.phase1 = Klein.factorB
phaseToFactor Helix.phase2 = Klein.factorC

factorToPhase : Klein.Factor3 → Helix.Phase3
factorToPhase Klein.factorA = Helix.phase0
factorToPhase Klein.factorB = Helix.phase1
factorToPhase Klein.factorC = Helix.phase2

factorAfterPhase :
  (phase : Helix.Phase3) →
  factorToPhase (phaseToFactor phase) ≡ phase
factorAfterPhase Helix.phase0 = refl
factorAfterPhase Helix.phase1 = refl
factorAfterPhase Helix.phase2 = refl

phaseAfterFactor :
  (factor : Klein.Factor3) →
  phaseToFactor (factorToPhase factor) ≡ factor
phaseAfterFactor Klein.factorA = refl
phaseAfterFactor Klein.factorB = refl
phaseAfterFactor Klein.factorC = refl

rotateFactor : Klein.Factor3 → Klein.Factor3
rotateFactor Klein.factorA = Klein.factorB
rotateFactor Klein.factorB = Klein.factorC
rotateFactor Klein.factorC = Klein.factorA

rotateFactorThreeTimes :
  (factor : Klein.Factor3) →
  rotateFactor (rotateFactor (rotateFactor factor)) ≡ factor
rotateFactorThreeTimes Klein.factorA = refl
rotateFactorThreeTimes Klein.factorB = refl
rotateFactorThreeTimes Klein.factorC = refl

phaseFactorRotationEquivariant :
  (phase : Helix.Phase3) →
  phaseToFactor (Helix.rotatePhase phase)
  ≡ rotateFactor (phaseToFactor phase)
phaseFactorRotationEquivariant Helix.phase0 = refl
phaseFactorRotationEquivariant Helix.phase1 = refl
phaseFactorRotationEquivariant Helix.phase2 = refl

phaseRotationHasNoFixedPoint :
  (phase : Helix.Phase3) →
  Helix.rotatePhase phase ≠ phase
phaseRotationHasNoFixedPoint Helix.phase0 ()
phaseRotationHasNoFixedPoint Helix.phase1 ()
phaseRotationHasNoFixedPoint Helix.phase2 ()

agentRotationHasNoFixedPoint :
  (agent : Braid.Agent) →
  Braid.rotateAgent agent ≠ agent
agentRotationHasNoFixedPoint Braid.agentA ()
agentRotationHasNoFixedPoint Braid.agentB ()
agentRotationHasNoFixedPoint Braid.agentC ()

factorRotationHasNoFixedPoint :
  (factor : Klein.Factor3) →
  rotateFactor factor ≠ factor
factorRotationHasNoFixedPoint Klein.factorA ()
factorRotationHasNoFixedPoint Klein.factorB ()
factorRotationHasNoFixedPoint Klein.factorC ()

record FreeCyclicThreeAction : Set₁ where
  constructor freeCyclicThreeAction
  field
    Carrier : Set
    rotate : Carrier → Carrier
    orderThree :
      (value : Carrier) →
      rotate (rotate (rotate value)) ≡ value
    noFixedPoint :
      (value : Carrier) →
      rotate value ≠ value

open FreeCyclicThreeAction public

helicalPhaseC3 : FreeCyclicThreeAction
helicalPhaseC3 =
  freeCyclicThreeAction
    Helix.Phase3
    Helix.rotatePhase
    Helix.rotationHasOrderThree
    phaseRotationHasNoFixedPoint

distributedRoleC3 : FreeCyclicThreeAction
distributedRoleC3 =
  freeCyclicThreeAction
    Braid.Agent
    Braid.rotateAgent
    Braid.rotateAgentThreeTimes
    agentRotationHasNoFixedPoint

factorSlotC3 : FreeCyclicThreeAction
factorSlotC3 =
  freeCyclicThreeAction
    Klein.Factor3
    rotateFactor
    rotateFactorThreeTimes
    factorRotationHasNoFixedPoint

record ThreePhaseInterpretationBoundary : Set where
  constructor threePhaseInterpretationBoundary
  field
    phaseAgentBijectionLeft :
      (phase : Helix.Phase3) →
      agentToPhase (phaseToAgent phase) ≡ phase
    phaseAgentBijectionRight :
      (agent : Braid.Agent) →
      phaseToAgent (agentToPhase agent) ≡ agent
    phaseFactorBijectionLeft :
      (phase : Helix.Phase3) →
      factorToPhase (phaseToFactor phase) ≡ phase
    phaseFactorBijectionRight :
      (factor : Klein.Factor3) →
      phaseToFactor (factorToPhase factor) ≡ factor
    sharedC3ShapeImpliesPhysicalIdentity : Bool
    sharedC3ShapeImpliesPhysicalIdentityIsFalse :
      sharedC3ShapeImpliesPhysicalIdentity ≡ false

canonicalThreePhaseInterpretationBoundary :
  ThreePhaseInterpretationBoundary
canonicalThreePhaseInterpretationBoundary =
  threePhaseInterpretationBoundary
    agentAfterPhase
    phaseAfterAgent
    factorAfterPhase
    phaseAfterFactor
    false refl
