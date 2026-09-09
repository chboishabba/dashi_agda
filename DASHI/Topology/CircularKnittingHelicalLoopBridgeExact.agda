module DASHI.Topology.CircularKnittingHelicalLoopBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Topology.HelicalWeaveMappingTorusExact as Helix
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch
import DASHI.Topology.TextileStitchOperationalSemanticsExact as Operational

------------------------------------------------------------------------
-- Literal bridge between the existing helical production coordinate and the
-- operational knit-loop transition.  The two coordinates remain distinct:
-- one indexes where the circular machine is in its production orbit, while
-- the other records the loop-frontier update performed at that production
-- step.
------------------------------------------------------------------------

record CircularKnitTransition
    (before after : Stitch.StitchState) : Set where
  constructor circular-knit-transition
  field
    siteBefore : Helix.HelicalSite
    siteAfter : Helix.HelicalSite
    siteAdvancesHelically :
      siteAfter ≡ Helix.helicalStep siteBefore
    loopTransition : Operational.KnitTransition before after

open CircularKnitTransition public

canonicalCircularKnitTransition :
  ∀ {before after} →
  (site : Helix.HelicalSite) →
  Operational.KnitTransition before after →
  CircularKnitTransition before after
canonicalCircularKnitTransition site transition =
  circular-knit-transition
    site
    (Helix.helicalStep site)
    refl
    transition

circularKnitTransitionAdvancesRound :
  ∀ {before after} →
  (transition : CircularKnitTransition before after) →
  Helix.productionRound (siteAfter transition)
  ≡ suc (Helix.productionRound (siteBefore transition))
circularKnitTransitionAdvancesRound
  (circular-knit-transition (Helix.helicalSite round phase) .(Helix.helicalStep (Helix.helicalSite round phase)) refl loopTransition) =
  refl

circularKnitTransitionRotatesPhase :
  ∀ {before after} →
  (transition : CircularKnitTransition before after) →
  Helix.stitchPhase (siteAfter transition)
  ≡ Helix.rotatePhase (Helix.stitchPhase (siteBefore transition))
circularKnitTransitionRotatesPhase
  (circular-knit-transition (Helix.helicalSite round phase) .(Helix.helicalStep (Helix.helicalSite round phase)) refl loopTransition) =
  refl

------------------------------------------------------------------------
-- Three-step production trace.  The textile transitions are retained as the
-- actual operational witnesses; the helical phase/round theorem comes from the
-- already-owned mapping-torus carrier rather than being reproved in parallel.
------------------------------------------------------------------------

record CircularKnitThreeStepTrace
    (state0 state1 state2 state3 : Stitch.StitchState) : Set where
  constructor circular-knit-three-step-trace
  field
    initialSite : Helix.HelicalSite
    firstLoopStep : Operational.KnitTransition state0 state1
    secondLoopStep : Operational.KnitTransition state1 state2
    thirdLoopStep : Operational.KnitTransition state2 state3

open CircularKnitThreeStepTrace public

threeStepFinalSite :
  ∀ {state0 state1 state2 state3} →
  CircularKnitThreeStepTrace state0 state1 state2 state3 →
  Helix.HelicalSite
threeStepFinalSite trace =
  Helix.helicalThreeSteps (initialSite trace)

threeCircularKnitStepsReturnToSamePhase :
  ∀ {state0 state1 state2 state3} →
  (trace : CircularKnitThreeStepTrace state0 state1 state2 state3) →
  Helix.stitchPhase (threeStepFinalSite trace)
  ≡ Helix.stitchPhase (initialSite trace)
threeCircularKnitStepsReturnToSamePhase trace =
  Helix.threeStepsReturnToSamePhase (initialSite trace)

threeCircularKnitStepsAdvanceRoundByThree :
  ∀ {state0 state1 state2 state3} →
  (trace : CircularKnitThreeStepTrace state0 state1 state2 state3) →
  Helix.productionRound (threeStepFinalSite trace)
  ≡ 3 + Helix.productionRound (initialSite trace)
threeCircularKnitStepsAdvanceRoundByThree trace =
  Helix.threeStepsAdvanceProductionRound (initialSite trace)

------------------------------------------------------------------------
-- Boundary discipline.
--
-- This bridge proves an indexed circular-knitting construction semantics.  It
-- does not by itself derive yarn tension redistribution, needle geometry, cam
-- timing, stitch length, constitutive elasticity, contact/slip, or failure.
------------------------------------------------------------------------

data HelicalLoopBridgeDeterminesMechanicalEvolution : Set where

helicalLoopBridgeDoesNotDetermineMechanicalEvolution :
  HelicalLoopBridgeDeterminesMechanicalEvolution → ⊥
helicalLoopBridgeDoesNotDetermineMechanicalEvolution ()
