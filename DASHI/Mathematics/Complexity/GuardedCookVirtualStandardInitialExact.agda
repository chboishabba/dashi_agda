module DASHI.Mathematics.Complexity.GuardedCookVirtualStandardInitialExact where

------------------------------------------------------------------------
-- CANONICAL INITIAL CONFIGURATION FOR STANDARD CONTROL ON GUARDED VIRTUAL COOK
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookVirtualTapeBaseExact as Base
import DASHI.Mathematics.Complexity.VirtualTapeSparseOverlayExact as Overlay
import DASHI.Mathematics.Complexity.VirtualStandardTapeExecutionExact as Virtual
import DASHI.Mathematics.Complexity.VirtualStandardTapeCostExact as Cost

------------------------------------------------------------------------
-- Empty residual and exact absolute head position T+1.
------------------------------------------------------------------------

initialVirtualConfiguration :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription) →
  Virtual.VirtualStandardConfiguration
    machine
    (Base.guardedCookVirtualBase blank zeroSymbol oneSymbol description)
initialVirtualConfiguration machine blank zeroSymbol oneSymbol description =
  Virtual.virtual-standard-configuration
    (Standard.initialState machine)
    (Base.payloadStart description)
    []

initialVirtualControlExact :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription) →
  Virtual.control
    (initialVirtualConfiguration machine blank zeroSymbol oneSymbol description)
  ≡ Standard.initialState machine
initialVirtualControlExact machine blank zeroSymbol oneSymbol description = refl

initialVirtualHeadExact :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription) →
  Virtual.headAddress
    (initialVirtualConfiguration machine blank zeroSymbol oneSymbol description)
  ≡ suc (Description.steps description)
initialVirtualHeadExact machine blank zeroSymbol oneSymbol description = refl

initialVirtualResidualEmpty :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription) →
  Virtual.residual
    (initialVirtualConfiguration machine blank zeroSymbol oneSymbol description)
  ≡ []
initialVirtualResidualEmpty machine blank zeroSymbol oneSymbol description = refl

------------------------------------------------------------------------
-- The first untouched scanned symbol is exactly streamed Cook bit zero whenever
-- that bit is in range.
------------------------------------------------------------------------

initialVirtualScannedBitZero :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription)
    (bit : Bool) →
  Semantics.queryAnswer (Description.atIndex description zero) ≡ just bit →
  Virtual.virtualScanned
    (initialVirtualConfiguration machine blank zeroSymbol oneSymbol description)
  ≡ just (Base.boolSymbol zeroSymbol oneSymbol bit)
initialVirtualScannedBitZero
    machine blank zeroSymbol oneSymbol description bit semantic =
  Base.guardedCookSemanticPayloadRead
    blank zeroSymbol oneSymbol description zero bit semantic

------------------------------------------------------------------------
-- Left-margin arithmetic for persistent virtual execution.
------------------------------------------------------------------------

virtualMoveConsumesLeftMargin :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    {before after : Virtual.VirtualStandardConfiguration machine base}
    (edge : Virtual.VirtualStandardEdge before after)
    (k : Nat) →
  suc k ≤ Virtual.headAddress before →
  k ≤ Virtual.headAddress after
virtualMoveConsumesLeftMargin {before = before} edge k margin
  with Standard.direction (Virtual.selected edge)
     | Virtual.headAddress before
     | Virtual.moveExact edge
     | Virtual.afterExact edge
... | Local.moveLeft | zero | () | afterExact
... | Local.moveLeft | suc address | refl | refl =
  NatP.≤-pred margin
... | Local.stayPut | address | refl | refl =
  NatP.≤-trans (NatP.n≤1+n k) margin
... | Local.moveRight | address | refl | refl =
  NatP.≤-trans
    (NatP.n≤1+n k)
    (NatP.≤-trans margin (NatP.n≤1+n address))

------------------------------------------------------------------------
-- Run-level margin consumption.  This is indexed directly by the number of
-- remaining virtual source edges.
------------------------------------------------------------------------

virtualRunPreservesRemainingLeftMargin :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    {steps : Nat}
    {start finish : Virtual.VirtualStandardConfiguration machine base} →
  Cost.VirtualExactRun steps start finish →
  suc steps ≤ Virtual.headAddress start →
  suc zero ≤ Virtual.headAddress finish
virtualRunPreservesRemainingLeftMargin Cost.virtualRunDone margin =
  margin
virtualRunPreservesRemainingLeftMargin
    (Cost.virtualRunStep {steps = steps} edge rest)
    margin =
  virtualRunPreservesRemainingLeftMargin
    rest
    (virtualMoveConsumesLeftMargin edge (suc steps) margin)

initialBudgetProvidesLeftMargin :
  ∀ {State Symbol : Set}
    (machine : Standard.StandardSingleTapeMachine State Symbol)
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription) →
  suc (Description.steps description)
  ≤ Virtual.headAddress
      (initialVirtualConfiguration machine blank zeroSymbol oneSymbol description)
initialBudgetProvidesLeftMargin machine blank zeroSymbol oneSymbol description =
  NatP.≤-refl _

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- An exact virtual run of T edges started from the canonical guarded virtual
-- input remains at absolute address >= 1.  The partial `moveHead` left-of-zero
-- case is therefore unreachable along a T-step candidate run once the run is
-- constructed from this initial state.
------------------------------------------------------------------------
