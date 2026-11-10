module DASHI.Physics.Motors.Circuit36927SwitchStateExact where

------------------------------------------------------------------------
-- Logic-level switch states, not a transistor/diode or motor model.
-- An OPEN switch has no through-switch edge in this abstraction.
-- A CLOSED switch has exactly a permitted through-switch edge.
-- External bypass wires may still connect the terminals.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

data SwitchState : Set where
  openSwitch : SwitchState
  closedSwitch : SwitchState

data ThroughSwitch : SwitchState → Set where
  closedEdge : ThroughSwitch closedSwitch

closedSwitchConducts : ThroughSwitch closedSwitch
closedSwitchConducts = closedEdge

openSwitchNoThroughEdge : ThroughSwitch openSwitch → Empty
openSwitchNoThroughEdge ()

-- A state-machine step is a permitted control action, NOT a
-- time-continuous current/voltage or arcing model.
data SwitchAction : Set where
  hold toggle : SwitchAction

nextState : SwitchAction → SwitchState → SwitchState
nextState hold s = s
nextState toggle openSwitch = closedSwitch
nextState toggle closedSwitch = openSwitch

toggleIsInvolution : (s : SwitchState) →
  nextState toggle (nextState toggle s) ≡ s
toggleIsInvolution openSwitch = refl
toggleIsInvolution closedSwitch = refl

holdPreservesState : (s : SwitchState) →
  nextState hold s ≡ s
holdPreservesState openSwitch = refl
holdPreservesState closedSwitch = refl

-- The through-switch edge must eventually be welded to the selected
-- pin-level netlist and a model of finite on-resistance, off-leakage,
-- switch loss and interruption of inductive current.
