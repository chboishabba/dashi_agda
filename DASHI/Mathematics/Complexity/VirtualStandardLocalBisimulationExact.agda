module DASHI.Mathematics.Complexity.VirtualStandardLocalBisimulationExact where

------------------------------------------------------------------------
-- LOCAL BISIMULATION: ORDINARY STANDARD STEP = PERSISTENT VIRTUAL STEP
--
-- StandardSingleTapeMachine changes only the scanned cell, finite control and
-- one neighbouring head position.  The sparse overlay therefore needs only two
-- non-interference facts: a write at h leaves h-1 and h+1 unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.VirtualTapeSparseOverlayExact as Overlay
import DASHI.Mathematics.Complexity.VirtualStandardTapeExecutionExact as Virtual

------------------------------------------------------------------------
-- Elementary successor apartness.
------------------------------------------------------------------------

sucInjective : ∀ {left right : Nat} → suc left ≡ suc right → left ≡ right
sucInjective refl = refl

selfNotSuccessor : (n : Nat) → n ≡ suc n → ⊥
selfNotSuccessor zero ()
selfNotSuccessor (suc n) equality =
  selfNotSuccessor n (sucInjective equality)

successorNotSelf : (n : Nat) → suc n ≡ n → ⊥
successorNotSelf n equality =
  selfNotSuccessor n (sym equality)
  where
    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

------------------------------------------------------------------------
-- A current-head write leaves the immediate neighbours untouched.
------------------------------------------------------------------------

leftNeighbourWriteStable :
  ∀ {Cell : Set}
    (base : Overlay.VirtualTapeBase Cell)
    (residual : Overlay.WriteResidual Cell)
    (head : Nat)
    (cell : Cell) →
  Overlay.overlayRead
      base
      (Overlay.writeResidual (suc head) cell residual)
      head
  ≡ Overlay.overlayRead base residual head
leftNeighbourWriteStable base residual head cell =
  Overlay.overlayReadOtherWrite
    base
    (selfNotSuccessor head)
    cell residual

rightNeighbourWriteStable :
  ∀ {Cell : Set}
    (base : Overlay.VirtualTapeBase Cell)
    (residual : Overlay.WriteResidual Cell)
    (head : Nat)
    (cell : Cell) →
  Overlay.overlayRead
      base
      (Overlay.writeResidual head cell residual)
      (suc head)
  ≡ Overlay.overlayRead base residual (suc head)
rightNeighbourWriteStable base residual head cell =
  Overlay.overlayReadOtherWrite
    base
    (successorNotSelf head)
    cell residual

------------------------------------------------------------------------
-- Exact scanned-symbol transport for each head direction.
------------------------------------------------------------------------

stayPutNextScannedExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : Virtual.VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol) →
  Standard.direction selected ≡ Local.stayPut →
  Virtual.virtualScanned
      (Virtual.applyVirtualTransition
        before selected (Virtual.headAddress before))
  ≡ just (Standard.writeSymbol selected)
stayPutNextScannedExact before selected directionExact =
  Virtual.applyVirtualTransitionWritesCurrentCell
    before selected (Virtual.headAddress before)

moveLeftNextScannedExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : Virtual.VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (leftAddress : Nat)
    (leftSymbol : Symbol) →
  Virtual.headAddress before ≡ suc leftAddress →
  Overlay.overlayRead
      base
      (Virtual.residual before)
      leftAddress
    ≡ just leftSymbol →
  Virtual.virtualScanned
      (Virtual.applyVirtualTransition before selected leftAddress)
  ≡ just leftSymbol
moveLeftNextScannedExact {base = base}
    before selected leftAddress leftSymbol headExact leftExact
  rewrite headExact
        | leftNeighbourWriteStable
            base
            (Virtual.residual before)
            leftAddress
            (Standard.writeSymbol selected)
        | leftExact =
  refl

moveRightNextScannedExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : Virtual.VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (rightSymbol : Symbol) →
  Overlay.overlayRead
      base
      (Virtual.residual before)
      (suc (Virtual.headAddress before))
    ≡ just rightSymbol →
  Virtual.virtualScanned
      (Virtual.applyVirtualTransition
        before selected (suc (Virtual.headAddress before)))
  ≡ just rightSymbol
moveRightNextScannedExact {base = base}
    before selected rightSymbol rightExact
  rewrite rightNeighbourWriteStable
      base
      (Virtual.residual before)
      (Virtual.headAddress before)
      (Standard.writeSymbol selected)
        | rightExact =
  refl

------------------------------------------------------------------------
-- Control transport is literally the ordinary target control in all cases.
------------------------------------------------------------------------

virtualStepControlMatchesStandard :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (before : Virtual.VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (nextHead : Nat) →
  Virtual.control (Virtual.applyVirtualTransition before selected nextHead)
  ≡ Standard.targetState selected
virtualStepControlMatchesStandard =
  Virtual.applyVirtualTransitionControlExact

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The persistent virtual representation now has the exact local bisimulation
-- data required by the ordinary split-tape machine: same selected transition,
-- same written symbol, same target control, and the same next scanned symbol for
-- stay/left/right motion.  Combined with finite-window materialisation, the
-- remaining compiler proof is bookkeeping over finite left/right lists and the
-- generator arithmetic, not a semantic gap in candidate execution.
------------------------------------------------------------------------
