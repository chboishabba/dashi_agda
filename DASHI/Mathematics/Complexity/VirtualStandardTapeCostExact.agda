module DASHI.Mathematics.Complexity.VirtualStandardTapeCostExact where

------------------------------------------------------------------------
-- RESOURCE ACCOUNTING FOR PERSISTENT VIRTUAL STANDARD-TAPE EXECUTION
--
-- Each virtual standard edge contributes exactly one newest residual write.
-- Latest-write lookup scans from newest to oldest and therefore costs at most
-- the residual depth.  Starting from an empty residual, after k source edges the
-- mutable-overlay lookup cost is at most k; it cannot hide super-polynomial work.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.VirtualTapeSparseOverlayExact as Overlay
import DASHI.Mathematics.Complexity.VirtualStandardTapeExecutionExact as Virtual

------------------------------------------------------------------------
-- Residual depth and lookup work.
------------------------------------------------------------------------

residualDepth :
  ∀ {Cell : Set} →
  Overlay.WriteResidual Cell → Nat
residualDepth [] = zero
residualDepth (_ ∷ rest) = suc (residualDepth rest)

latestWriteWork :
  ∀ {Cell : Set} →
  Nat → Overlay.WriteResidual Cell → Nat
latestWriteWork requested [] = zero
latestWriteWork requested (entry ∷ rest)
  with Overlay.natEqual requested (Overlay.address entry)
... | true = suc zero
... | false = suc (latestWriteWork requested rest)

latestWriteWorkBound :
  ∀ {Cell : Set}
    (requested : Nat)
    (residual : Overlay.WriteResidual Cell) →
  latestWriteWork requested residual ≤ residualDepth residual
latestWriteWorkBound requested [] = NatP.≤-refl _
latestWriteWorkBound requested (entry ∷ rest)
  with Overlay.natEqual requested (Overlay.address entry)
... | true = NatP.s≤s NatP.z≤n
... | false =
  NatP.s≤s (latestWriteWorkBound requested rest)

writeResidualDepthExact :
  ∀ {Cell : Set}
    (requested : Nat)
    (cell : Cell)
    (residual : Overlay.WriteResidual Cell) →
  residualDepth (Overlay.writeResidual requested cell residual)
  ≡ suc (residualDepth residual)
writeResidualDepthExact requested cell residual = refl

------------------------------------------------------------------------
-- Exact virtual run carrier.
------------------------------------------------------------------------

data VirtualExactRun
    {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol} :
    Nat →
    Virtual.VirtualStandardConfiguration machine base →
    Virtual.VirtualStandardConfiguration machine base →
    Set where

  virtualRunDone :
    ∀ {configuration} →
    VirtualExactRun zero configuration configuration

  virtualRunStep :
    ∀ {steps start middle finish} →
    Virtual.VirtualStandardEdge start middle →
    VirtualExactRun steps middle finish →
    VirtualExactRun (suc steps) start finish

------------------------------------------------------------------------
-- Every edge adds exactly one residual entry.
------------------------------------------------------------------------

virtualEdgeResidualDepth :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    {before after : Virtual.VirtualStandardConfiguration machine base} →
  Virtual.VirtualStandardEdge before after →
  residualDepth (Virtual.residual after)
  ≡ suc (residualDepth (Virtual.residual before))
virtualEdgeResidualDepth edge
  rewrite Virtual.afterExact edge = refl

virtualRunResidualDepthExact :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    {steps : Nat}
    {start finish : Virtual.VirtualStandardConfiguration machine base} →
  VirtualExactRun steps start finish →
  residualDepth (Virtual.residual finish)
  ≡ residualDepth (Virtual.residual start) + steps
virtualRunResidualDepthExact virtualRunDone = refl
virtualRunResidualDepthExact
    (virtualRunStep {steps = steps} {start = start} edge rest)
  rewrite virtualRunResidualDepthExact rest
        | virtualEdgeResidualDepth edge
        | NatP.+-suc (residualDepth (Virtual.residual start)) steps =
  refl

------------------------------------------------------------------------
-- Empty-start specialization used by self-quotation simulation.
------------------------------------------------------------------------

emptyResidual : ∀ {Cell : Set} → Overlay.WriteResidual Cell
emptyResidual = []

emptyStartRunResidualDepth :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    {steps : Nat}
    {start finish : Virtual.VirtualStandardConfiguration machine base} →
  Virtual.residual start ≡ emptyResidual →
  VirtualExactRun steps start finish →
  residualDepth (Virtual.residual finish) ≡ steps
emptyStartRunResidualDepth startEmpty run
  rewrite virtualRunResidualDepthExact run
        | startEmpty =
  refl

finishLookupWorkBoundByRun :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {base : Overlay.VirtualTapeBase Symbol}
    {steps : Nat}
    {start finish : Virtual.VirtualStandardConfiguration machine base} →
  Virtual.residual start ≡ emptyResidual →
  VirtualExactRun steps start finish →
  (requested : Nat) →
  latestWriteWork requested (Virtual.residual finish) ≤ steps
finishLookupWorkBoundByRun
    {steps = steps} {finish = finish}
    startEmpty run requested =
  NatP.≤-trans
    (latestWriteWorkBound requested (Virtual.residual finish))
    equalityAsBound
  where
    depthExact : residualDepth (Virtual.residual finish) ≡ steps
    depthExact = emptyStartRunResidualDepth startEmpty run

    equalityAsBound : residualDepth (Virtual.residual finish) ≤ steps
    equalityAsBound = NatP.≤-reflexive depthExact

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The sparse residual is a polynomially tame mutable layer: one entry per source
-- edge and linear lookup in source time.  A virtual read can therefore be
-- implemented as:
--
--   scan <= k residual entries;
--   if hit, return locally;
--   if miss, invoke exactly one immutable streamed-base query.
--
-- The remaining dominant cost theorem is the streamed Cook query evaluator and
-- its compilation into the fixed coded target machine.
------------------------------------------------------------------------
