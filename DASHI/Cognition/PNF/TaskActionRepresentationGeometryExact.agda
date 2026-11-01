module DASHI.Cognition.PNF.TaskActionRepresentationGeometryExact where

------------------------------------------------------------------------
-- SOURCE-FACING MOTIVATION
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted.
--
-- Andrey Gromov, "Grokking modular arithmetic", arXiv:2301.02679.
-- No DOI asserted.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as Task
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as Cyclo
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

record EquivariantRepresentation (State Action Latent : Set) : Set₁ where
  constructor equivariantRepresentation
  field
    encode : State → Latent
    stateAction : Action → State → State
    latentAction : Action → Latent → Latent
    actionCommutesWithEncoding :
      (a : Action) (x : State) →
      encode (stateAction a x) ≡ latentAction a (encode x)

open EquivariantRepresentation public

record ActionIntertwiner (Action A B : Set) : Set₁ where
  constructor actionIntertwiner
  field
    map : A → B
    actionA : Action → A → A
    actionB : Action → B → B
    intertwines : (a : Action) (x : A) →
      map (actionA a x) ≡ actionB a (map x)

open ActionIntertwiner public

composeEquivariant :
  ∀ {State Action A B} →
  (R : EquivariantRepresentation State Action A) →
  (I : ActionIntertwiner Action A B) →
  ((a : Action) (x : A) → actionA I a x ≡ latentAction R a x) →
  EquivariantRepresentation State Action B
composeEquivariant R I sameAction =
  equivariantRepresentation
    (λ x → map I (encode R x))
    (stateAction R)
    (actionB I)
    proof
  where
    proof : ∀ a x →
      map I (encode R (stateAction R a x))
      ≡ actionB I a (map I (encode R x))
    proof a x
      rewrite actionCommutesWithEncoding R a x
            | sym (sameAction a (encode R x)) =
      intertwines I a (encode R x)

Phase : Set
Phase = Wheel.DepthWheelPhase

stateAdd : Phase → Phase → Phase
stateAdd = Task.phaseComposeC3

phaseLatentAction : Phase → Cyclo.Cyclotomic3 → Cyclo.Cyclotomic3
phaseLatentAction a z = Cyclo.root a Cyclo.*C z

c3CyclotomicRepresentation : EquivariantRepresentation Phase Phase Cyclo.Cyclotomic3
c3CyclotomicRepresentation =
  equivariantRepresentation Cyclo.root stateAdd phaseLatentAction Cyclo.rootCharacterHomomorphism

c3ActionBecomesCyclotomicMultiplication : (a x : Phase) →
  encode c3CyclotomicRepresentation (stateAction c3CyclotomicRepresentation a x)
  ≡ latentAction c3CyclotomicRepresentation a
      (encode c3CyclotomicRepresentation x)
c3ActionBecomesCyclotomicMultiplication =
  actionCommutesWithEncoding c3CyclotomicRepresentation

phaseOneActsByOmega :
  latentAction c3CyclotomicRepresentation Wheel.phase-1 Cyclo.oneC
  ≡ Cyclo.omega
phaseOneActsByOmega =
  sym (Cyclo.rootCharacterHomomorphism Wheel.phase-1 Wheel.phase-0)

data GeometryPrior : Set where
  denseGlobal : GeometryPrior
  translationLocal : GeometryPrior
  routedLocal : GeometryPrior
  queryDependentGraph : GeometryPrior
  taskHarmonic : GeometryPrior

record LearnedGeometryWitness : Set₁ where
  field
    State Action Latent : Set
    architecturePrior : GeometryPrior
    representation : EquivariantRepresentation State Action Latent

record NeuralGeometryAuthorityBoundary : Set where
  field
    c3TheoremImpliesAllLLMsLearnCyclicGeometry : Bool
    c3TheoremImpliesAllLLMsLearnCyclicGeometryIsFalse :
      c3TheoremImpliesAllLLMsLearnCyclicGeometry ≡ false
    fullyConnectedArchitectureForcesFourierBasis : Bool
    fullyConnectedArchitectureForcesFourierBasisIsFalse :
      fullyConnectedArchitectureForcesFourierBasis ≡ false

canonicalNeuralGeometryAuthorityBoundary : NeuralGeometryAuthorityBoundary
canonicalNeuralGeometryAuthorityBoundary = record
  { c3TheoremImpliesAllLLMsLearnCyclicGeometry = false
  ; c3TheoremImpliesAllLLMsLearnCyclicGeometryIsFalse = refl
  ; fullyConnectedArchitectureForcesFourierBasis = false
  ; fullyConnectedArchitectureForcesFourierBasisIsFalse = refl
  }
