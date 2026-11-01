module DASHI.Biology.Cell.CellViabilityKernel where

open import DASHI.Biology.Core.ContextIndexedSystem

-- A living cell is modelled as an open controlled system that remains inside an
-- admissible viability region under a declared disturbance class and resource
-- budget.  It is not an equilibrium energy minimum.
record CellViabilitySystem : Set₁ where
  field
    control : OpenControlledSystem
    budget  : OpenSystemBudget

    Viable : OpenControlledSystem.Context control →
             OpenControlledSystem.State control → Set

    ResourceSupported :
      OpenControlledSystem.Context control →
      OpenControlledSystem.State control → Set

    MetabolicSupport : Set
    MembraneSupport  : Set
    RegulatorySupport : Set

record CellViabilityWitness
  (V : CellViabilitySystem) : Set₁ where
  open CellViabilitySystem V
  open OpenControlledSystem control
  field
    context : Context
    state   : State
    correction : GoalCorrectionWitness control

    initiallyViable : Viable context state
    resourceSupported : ResourceSupported context state

    remainsViable :
      (d : Disturbance) →
      Viable context
        (step context
          (GoalCorrectionWitness.policy correction context
            (disturb d state) d)
          (disturb d state))

-- A viability kernel is the set of initial states for which an admitted policy
-- keeps the trajectory in the viability region.  The membership proof is kept
-- explicit rather than defined by persistence alone.
record ViabilityKernel
  (V : CellViabilitySystem) : Set₁ where
  open CellViabilitySystem V
  open OpenControlledSystem control
  field
    InKernel : Context → State → Set

    kernelSound :
      (c : Context) (x : State) → InKernel c x → Viable c x

    policyExists :
      (c : Context) (x : State) → InKernel c x →
      GoalCorrectionWitness control

record CellViabilityBoundary : Set₁ where
  field
    equilibriumIsNotViability : Set
    persistenceIsNotAgency    : Set
    viabilityIsNotConsciousness : Set
    cellModelIsNotClinicalAuthority : Set
