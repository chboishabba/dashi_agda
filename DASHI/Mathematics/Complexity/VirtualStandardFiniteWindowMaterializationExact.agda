module DASHI.Mathematics.Complexity.VirtualStandardFiniteWindowMaterializationExact where

------------------------------------------------------------------------
-- FINITE STANDARD-TAPE MATERIALISATION OF THE PERSISTENT VIRTUAL TAPE
--
-- The compiler proof needs a concrete relation between the persistent virtual
-- representation and the ordinary split-tape StandardConfiguration.  This
-- owner supplies that relation without materialising the whole infinite tape:
-- for any chosen finite right span it materialises exactly the cells visible
-- around the current absolute head.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.VirtualTapeSparseOverlayExact as Overlay
import DASHI.Mathematics.Complexity.VirtualStandardTapeExecutionExact as Virtual

------------------------------------------------------------------------
-- Total observation of a virtual cell.  `fallback` is used only if the chosen
-- base itself is partial.  GuardedCookVirtualTapeBaseExact is total (`just` at
-- every absolute address), so the self-quotation instance never takes it.
------------------------------------------------------------------------

readOr :
  ∀ {Cell : Set} →
  Cell → Maybe Cell → Cell
readOr fallback nothing = fallback
readOr fallback (just cell) = cell

virtualCell :
  ∀ {Cell : Set} →
  Cell →
  Overlay.VirtualTapeBase Cell →
  Overlay.WriteResidual Cell →
  Nat → Cell
virtualCell fallback base residual address =
  readOr fallback (Overlay.overlayRead base residual address)

virtualCellOfJust :
  ∀ {Cell : Set}
    (fallback cell : Cell)
    (base : Overlay.VirtualTapeBase Cell)
    (residual : Overlay.WriteResidual Cell)
    (address : Nat) →
  Overlay.overlayRead base residual address ≡ just cell →
  virtualCell fallback base residual address ≡ cell
virtualCellOfJust fallback cell base residual address proof
  rewrite proof = refl

------------------------------------------------------------------------
-- Left side is nearest-first, exactly matching StandardConfiguration.left.
------------------------------------------------------------------------

leftCells :
  ∀ {Cell : Set} →
  Cell → Overlay.VirtualTapeBase Cell → Overlay.WriteResidual Cell →
  Nat → List Cell
leftCells fallback base residual zero = []
leftCells fallback base residual (suc address) =
  virtualCell fallback base residual address
  ∷ leftCells fallback base residual address

rightCells :
  ∀ {Cell : Set} →
  Cell → Overlay.VirtualTapeBase Cell → Overlay.WriteResidual Cell →
  Nat → Nat → List Cell
rightCells fallback base residual head zero = []
rightCells fallback base residual head (suc span) =
  virtualCell fallback base residual (suc head)
  ∷ rightCells fallback base residual (suc head) span

------------------------------------------------------------------------
-- Materialise one persistent virtual configuration into an ordinary split tape.
------------------------------------------------------------------------

materializeFiniteWindow :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol} →
  (fallback : Symbol) →
  Virtual.VirtualStandardConfiguration machine base →
  Nat →
  Standard.StandardConfiguration machine
materializeFiniteWindow {base = base} fallback configuration rightSpan =
  Standard.standard-configuration
    (leftCells fallback base
      (Virtual.residual configuration)
      (Virtual.headAddress configuration))
    (Virtual.control configuration)
    (virtualCell fallback base
      (Virtual.residual configuration)
      (Virtual.headAddress configuration))
    (rightCells fallback base
      (Virtual.residual configuration)
      (Virtual.headAddress configuration)
      rightSpan)

materializedControlExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (fallback : Symbol)
    (configuration : Virtual.VirtualStandardConfiguration machine base)
    (rightSpan : Nat) →
  Standard.state (materializeFiniteWindow fallback configuration rightSpan)
  ≡ Virtual.control configuration
materializedControlExact fallback configuration rightSpan = refl

materializedScannedExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (fallback scanned : Symbol)
    (configuration : Virtual.VirtualStandardConfiguration machine base)
    (rightSpan : Nat) →
  Virtual.virtualScanned configuration ≡ just scanned →
  Standard.scanned (materializeFiniteWindow fallback configuration rightSpan)
  ≡ scanned
materializedScannedExact {base = base}
    fallback scanned configuration rightSpan readExact =
  virtualCellOfJust
    fallback scanned base
    (Virtual.residual configuration)
    (Virtual.headAddress configuration)
    readExact

------------------------------------------------------------------------
-- A virtual write is visible at the same absolute address in every subsequent
-- finite materialisation.  This is the central reopening property needed for
-- candidate continuation after a generated Cook-bit read.
------------------------------------------------------------------------

materializedWrittenCellExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (fallback : Symbol)
    (before : Virtual.VirtualStandardConfiguration machine base)
    (selected : Standard.StandardTransition State Symbol)
    (nextHead : Nat) →
  virtualCell fallback base
      (Virtual.residual
        (Virtual.applyVirtualTransition before selected nextHead))
      (Virtual.headAddress before)
  ≡ Standard.writeSymbol selected
materializedWrittenCellExact {base = base}
    fallback before selected nextHead =
  virtualCellOfJust
    fallback
    (Standard.writeSymbol selected)
    base
    (Virtual.residual
      (Virtual.applyVirtualTransition before selected nextHead))
    (Virtual.headAddress before)
    (Virtual.applyVirtualTransitionWritesCurrentCell before selected nextHead)

------------------------------------------------------------------------
-- The left list contains exactly one concrete cell for every absolute address
-- strictly left of the head.  This ties head address to actual split-tape span.
------------------------------------------------------------------------

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

leftCellsLengthExact :
  ∀ {Cell : Set}
    (fallback : Cell)
    (base : Overlay.VirtualTapeBase Cell)
    (residual : Overlay.WriteResidual Cell)
    (head : Nat) →
  listLength (leftCells fallback base residual head) ≡ head
leftCellsLengthExact fallback base residual zero = refl
leftCellsLengthExact fallback base residual (suc head)
  rewrite leftCellsLengthExact fallback base residual head = refl

materializedLeftSpanExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    (fallback : Symbol)
    (configuration : Virtual.VirtualStandardConfiguration machine base)
    (rightSpan : Nat) →
  listLength
    (Standard.left (materializeFiniteWindow fallback configuration rightSpan))
  ≡ Virtual.headAddress configuration
materializedLeftSpanExact {base = base} fallback configuration rightSpan =
  leftCellsLengthExact
    fallback base
    (Virtual.residual configuration)
    (Virtual.headAddress configuration)

------------------------------------------------------------------------
-- BOUNDARY
--
-- This pays the concrete finite-window representation map.  The remaining
-- bisimulation theorem must show that, with enough right span, one ordinary
-- `standardNext` step on this materialisation equals materialisation of the
-- corresponding `VirtualStandardEdge` (with the expected span adjustment on
-- head motion).  That is now a local list equality theorem, not an undefined
-- representation problem.
------------------------------------------------------------------------
