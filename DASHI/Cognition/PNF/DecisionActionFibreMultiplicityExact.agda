module DASHI.Cognition.PNF.DecisionActionFibreMultiplicityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.DecisionStateBundleDynamicsExact as Dynamics
import DASHI.Cognition.PNF.DecisionPotentialFibreExact as Potential
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision

------------------------------------------------------------------------
-- MULTIPLICITY OF THE OBSERVED-ACTION FIBRE
--
-- Across the supplied decision literatures, identical emitted behaviour can be
-- compatible with different attention, evidence history, potential/basin,
-- consideration, commitment and release states.  These are distinct fine
-- coordinates in one fibre of Bundle.observedAction.
------------------------------------------------------------------------

narrowBundle : Memory.MemoryFibre → Bundle.DecisionStateBundle
narrowBundle memory =
  record (Bundle.attendedBundle memory)
    { considerationMode = Decision.narrowConsideration }

broadBundle : Memory.MemoryFibre → Bundle.DecisionStateBundle
broadBundle memory =
  record (Bundle.attendedBundle memory)
    { considerationMode = Decision.broadConsideration }

ordinaryPotentialBundle : Memory.MemoryFibre → Bundle.DecisionStateBundle
ordinaryPotentialBundle memory =
  Dynamics.setPotentialContext Potential.ordinaryContext (Bundle.attendedBundle memory)

threatPotentialBundle : Memory.MemoryFibre → Bundle.DecisionStateBundle
threatPotentialBundle memory =
  Dynamics.setPotentialContext Potential.threatContext (Bundle.attendedBundle memory)

record ActionFibreMultiplicity (memory : Memory.MemoryFibre) : Set where
  constructor actionFibreMultiplicity
  field
    attentionCollision :
      Bundle.observedAction (Bundle.attendedBundle memory)
      ≡ Bundle.observedAction (Bundle.unattendedBundle memory)
    attentionStillDiffers :
      Bundle.attention (Bundle.attendedBundle memory)
      ≡ Bundle.attention (Bundle.unattendedBundle memory) → ⊥

    historyCollision :
      Bundle.observedAction (Dynamics.historyABBundle memory)
      ≡ Bundle.observedAction (Dynamics.historyBABundle memory)
    historyStillDiffers :
      Bundle.historyState (Dynamics.historyABBundle memory)
      ≡ Bundle.historyState (Dynamics.historyBABundle memory) → ⊥

    potentialCollision :
      Bundle.observedAction (ordinaryPotentialBundle memory)
      ≡ Bundle.observedAction (threatPotentialBundle memory)
    potentialStillDiffers :
      Bundle.potentialSurface (ordinaryPotentialBundle memory)
      ≡ Bundle.potentialSurface (threatPotentialBundle memory) → ⊥

    considerationCollision :
      Bundle.observedAction (narrowBundle memory)
      ≡ Bundle.observedAction (broadBundle memory)
    considerationStillDiffers :
      Bundle.considerationMode (narrowBundle memory)
      ≡ Bundle.considerationMode (broadBundle memory) → ⊥

    commitmentCollision :
      Bundle.observedAction (Bundle.blockedCommittedBundle memory)
      ≡ Bundle.observedAction (Bundle.uncommittedBundle memory)
    commitmentStillDiffers :
      Bundle.commitmentState (Bundle.blockedCommittedBundle memory)
      ≡ Bundle.commitmentState (Bundle.uncommittedBundle memory) → ⊥

open ActionFibreMultiplicity public

canonicalActionFibreMultiplicity :
  (memory : Memory.MemoryFibre) → ActionFibreMultiplicity memory
canonicalActionFibreMultiplicity memory = actionFibreMultiplicity
  refl
  (λ ())
  refl
  (λ ())
  refl
  (λ ())
  refl
  (λ ())
  refl
  (λ ())

------------------------------------------------------------------------
-- Boundary: behavioural equality certifies only equality in the action
-- projection.  It does not identify any of the fine coordinates above.
------------------------------------------------------------------------
