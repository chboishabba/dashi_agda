module DASHI.Mathematics.Complexity.VirtualStandardTapeExecutionExact where

------------------------------------------------------------------------
-- CONVENTIONAL STANDARD-TM CONTROL OVER A VIRTUAL SPARSE TAPE
--
-- The finite-control transition function is unchanged.  Only tape storage is
-- replaced by:
--
--   immutable virtual base + sparse latest-write residual + absolute head.
--
-- A step therefore reads exactly one current cell, applies the ordinary
-- StandardSingleTapeMachine transition, records exactly one write, and moves
-- the absolute head by at most one.  No full input materialisation is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.VirtualTapeSparseOverlayExact as Overlay

------------------------------------------------------------------------
-- Absolute head motion.  Left of address zero is intentionally partial; the
-- guarded T+1 margin theorem is the downstream reason this case is unreachable
-- during the candidate's T-step run.
------------------------------------------------------------------------

moveHead : Local.Direction → Nat → Maybe Nat
moveHead Local.moveLeft zero = nothing
moveHead Local.moveLeft (suc address) = just address
moveHead Local.stayPut address = just address
moveHead Local.moveRight address = just (suc address)

record VirtualStandardConfiguration
    {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (base : Overlay.VirtualTapeBase Symbol) : Set where
  constructor virtual-standard-configuration
  field
    control : State
    headAddress : Nat
    residual : Overlay.WriteResidual Symbol

open VirtualStandardConfiguration public

virtualScanned :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol} →
  VirtualStandardConfiguration machine base → Maybe Symbol
virtualScanned {base = base} configuration =
  Overlay.overlayRead
    base
    (residual configuration)
    (headAddress configuration)

applyVirtualTransition :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol} →
  VirtualStandardConfiguration machine base →
  Standard.StandardTransition State Symbol →
  Nat →
  VirtualStandardConfiguration machine base
applyVirtualTransition before selected nextHead =
  virtual-standard-configuration
    (Standard.targetState selected)
    nextHead
    (Overlay.writeResidual
      (headAddress before)
      (Standard.writeSymbol selected)
      (residual before))

virtualNext :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol} →
  VirtualStandardConfiguration machine base →
  Maybe (VirtualStandardConfiguration machine base)
virtualNext {machine = machine} before
  with virtualScanned before
... | nothing = nothing
... | just scanned
  with Standard.transition machine (control before) scanned
... | nothing = nothing
... | just selected
  with moveHead (Standard.direction selected) (headAddress before)
... | nothing = nothing
... | just nextHead =
  just (applyVirtualTransition before selected nextHead)

------------------------------------------------------------------------
-- One-step resource/representation receipts.
------------------------------------------------------------------------

applyVirtualTransitionWritesCurrentCell :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (nextHead : Nat) →
  Overlay.overlayRead
      base
      (residual (applyVirtualTransition before selected nextHead))
      (headAddress before)
  ≡ just (Standard.writeSymbol selected)
applyVirtualTransitionWritesCurrentCell before selected nextHead =
  Overlay.overlayReadWritten
    _
    (residual before)
    (headAddress before)
    (Standard.writeSymbol selected)

applyVirtualTransitionControlExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (nextHead : Nat) →
  control (applyVirtualTransition before selected nextHead)
  ≡ Standard.targetState selected
applyVirtualTransitionControlExact before selected nextHead = refl

applyVirtualTransitionHeadExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (nextHead : Nat) →
  headAddress (applyVirtualTransition before selected nextHead)
  ≡ nextHead
applyVirtualTransitionHeadExact before selected nextHead = refl

applyVirtualTransitionResidualExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (nextHead : Nat) →
  residual (applyVirtualTransition before selected nextHead)
  ≡ Overlay.writeResidual
      (headAddress before)
      (Standard.writeSymbol selected)
      (residual before)
applyVirtualTransitionResidualExact before selected nextHead = refl

------------------------------------------------------------------------
-- A proof-relevant edge exposes the same read/transition/move decomposition as
-- `virtualNext`, making later finite-machine compilation obligations explicit.
------------------------------------------------------------------------

record VirtualStandardEdge
    {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before after : VirtualStandardConfiguration machine base) : Set where
  field
    scanned : Symbol
    selected : Standard.StandardTransition State Symbol
    nextHead : Nat

    readExact : virtualScanned before ≡ just scanned
    transitionExact :
      Standard.transition machine (control before) scanned ≡ just selected
    moveExact :
      moveHead (Standard.direction selected) (headAddress before)
      ≡ just nextHead
    afterExact :
      after ≡ applyVirtualTransition before selected nextHead

open VirtualStandardEdge public

virtualEdgeGivesNext :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    {before after : VirtualStandardConfiguration machine base} →
  VirtualStandardEdge before after →
  virtualNext before ≡ just after
virtualEdgeGivesNext edge
  rewrite readExact edge
        | transitionExact edge
        | moveExact edge
        | afterExact edge =
  refl

------------------------------------------------------------------------
-- ACTIVE CONSEQUENCE
--
-- This pays the semantic call-frame invariant the previous reset-style virtual
-- compiler lacked: candidate control and writes can persist across generated
-- reads.  Remaining work is representational compilation of this executable
-- state `(control, headAddress, residual)` plus the streamed base reader into
-- the SAME finite coded target machine, with an explicit polynomial clock.
------------------------------------------------------------------------
