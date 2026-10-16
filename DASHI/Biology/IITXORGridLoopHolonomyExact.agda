module DASHI.Biology.IITXORGridLoopHolonomyExact where

------------------------------------------------------------------------
-- GRID LOOP HOLONOMY FROM THE ORDERED A/B SOCKET FABRIC
--
-- Every XOR-grid site already has two named input sockets.  XOR itself is
-- symmetric and therefore quotients that ordering from its output, but the
-- fabric retains it.  This owner equips the retained ordering with the exact
-- symbolic C3 chart
--
--   A -> zeta,    B -> zeta^2 = conjugate(zeta),    empty path -> 1
--
-- and multiplies those phases along a routed socket path.  Global A/B reversal
-- conjugates the path holonomy.  This is a chosen finite orientation chart on
-- the causal fabric; it is NOT by itself physical torque or a continuous gauge
-- connection.  The point is narrower: global recurrence can carry an oriented
-- loop observable even when the local XOR output is orientation-blind.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Biology.IITCausalPantsFibreGluingExact as Pants
import DASHI.Biology.IITXORGridSynthesisFabricExact as Grid

------------------------------------------------------------------------
-- 1. Socket reversal and exact C3 chart.
------------------------------------------------------------------------

swapPort : Pants.InputPort → Pants.InputPort
swapPort Pants.inputA = Pants.inputB
swapPort Pants.inputB = Pants.inputA

swapPortInvolutive : (port : Pants.InputPort) → swapPort (swapPort port) ≡ port
swapPortInvolutive Pants.inputA = refl
swapPortInvolutive Pants.inputB = refl

socketPhase : Pants.InputPort → C3.C3Phase
socketPhase Pants.inputA = Fourier.zeta
socketPhase Pants.inputB = Fourier.zetaSquared

socketSwapConjugates :
  (port : Pants.InputPort) →
  socketPhase (swapPort port) ≡ Fourier.inversePhase (socketPhase port)
socketSwapConjugates Pants.inputA = refl
socketSwapConjugates Pants.inputB = refl

------------------------------------------------------------------------
-- 2. Holonomy of a finite socket path.
------------------------------------------------------------------------

SocketPath : Set
SocketPath = List Pants.InputPort

swapSocketPath : SocketPath → SocketPath
swapSocketPath [] = []
swapSocketPath (port ∷ rest) = swapPort port ∷ swapSocketPath rest

phaseHolonomy : SocketPath → C3.C3Phase
phaseHolonomy [] = Fourier.one
phaseHolonomy (port ∷ rest) =
  C3.multiplyPhase (socketPhase port) (phaseHolonomy rest)

inverseProduct :
  (a b : C3.C3Phase) →
  C3.multiplyPhase (Fourier.inversePhase a) (Fourier.inversePhase b)
  ≡ Fourier.inversePhase (C3.multiplyPhase a b)
inverseProduct C3.phase0 C3.phase0 = refl
inverseProduct C3.phase0 C3.phase1 = refl
inverseProduct C3.phase0 C3.phase2 = refl
inverseProduct C3.phase1 C3.phase0 = refl
inverseProduct C3.phase1 C3.phase1 = refl
inverseProduct C3.phase1 C3.phase2 = refl
inverseProduct C3.phase2 C3.phase0 = refl
inverseProduct C3.phase2 C3.phase1 = refl
inverseProduct C3.phase2 C3.phase2 = refl

swapPathConjugatesHolonomy :
  (path : SocketPath) →
  phaseHolonomy (swapSocketPath path)
  ≡ Fourier.inversePhase (phaseHolonomy path)
swapPathConjugatesHolonomy [] = refl
swapPathConjugatesHolonomy (port ∷ rest)
  rewrite socketSwapConjugates port
        | swapPathConjugatesHolonomy rest =
  inverseProduct (socketPhase port) (phaseHolonomy rest)

------------------------------------------------------------------------
-- 3. Exact three-edge examples.  Uniform three-step windings close in C3;
--    mixed socket words can carry nontrivial phase.
------------------------------------------------------------------------

threeA : SocketPath
threeA = Pants.inputA ∷ Pants.inputA ∷ Pants.inputA ∷ []

threeB : SocketPath
threeB = Pants.inputB ∷ Pants.inputB ∷ Pants.inputB ∷ []

mixedAAB : SocketPath
mixedAAB = Pants.inputA ∷ Pants.inputA ∷ Pants.inputB ∷ []

mixedABB : SocketPath
mixedABB = Pants.inputA ∷ Pants.inputB ∷ Pants.inputB ∷ []

threeAHolonomyTrivial : phaseHolonomy threeA ≡ Fourier.one
threeAHolonomyTrivial = refl

threeBHolonomyTrivial : phaseHolonomy threeB ≡ Fourier.one
threeBHolonomyTrivial = refl

mixedAABHolonomy : phaseHolonomy mixedAAB ≡ Fourier.zeta
mixedAABHolonomy = refl

mixedABBHolonomy : phaseHolonomy mixedABB ≡ Fourier.zetaSquared
mixedABBHolonomy = refl

zetaNotZetaSquared : Fourier.zeta ≡ Fourier.zetaSquared → ⊥
zetaNotZetaSquared ()

mixedPathDetectsOrientationReversal :
  phaseHolonomy mixedAAB ≡ phaseHolonomy (swapSocketPath mixedAAB) → ⊥
mixedPathDetectsOrientationReversal equality = zetaNotZetaSquared equality

------------------------------------------------------------------------
-- 4. A typed three-edge routed loop consumes the same port word.  The edge
--    equalities certify that each predecessor really feeds the declared socket.
------------------------------------------------------------------------

sourceForPort :
  {Site : Set} →
  Grid.TwoInputFabric Site →
  Pants.InputPort →
  Site → Site
sourceForPort fabric Pants.inputA = Grid.inputASource fabric
sourceForPort fabric Pants.inputB = Grid.inputBSource fabric

record ThreeEdgeRoutedLoop
    {Site : Set}
    (fabric : Grid.TwoInputFabric Site) : Set where
  constructor three-edge-routed-loop
  field
    site0 site1 site2 : Site
    into1 into2 into0 : Pants.InputPort
    edge01 : sourceForPort fabric into1 site1 ≡ site0
    edge12 : sourceForPort fabric into2 site2 ≡ site1
    edge20 : sourceForPort fabric into0 site0 ≡ site2
open ThreeEdgeRoutedLoop public

loopSocketPath :
  {Site : Set} {fabric : Grid.TwoInputFabric Site} →
  ThreeEdgeRoutedLoop fabric → SocketPath
loopSocketPath loop = into1 loop ∷ into2 loop ∷ into0 loop ∷ []

loopHolonomy :
  {Site : Set} {fabric : Grid.TwoInputFabric Site} →
  ThreeEdgeRoutedLoop fabric → C3.C3Phase
loopHolonomy loop = phaseHolonomy (loopSocketPath loop)

------------------------------------------------------------------------
-- 5. XOR dynamics is still invariant under global A/B reversal.  Therefore the
--    phase chart can distinguish orientation information retained by the fabric
--    even when the Boolean transition law cannot.
------------------------------------------------------------------------

xorDynamicsIgnoresGlobalSocketSwap :
  {Site : Set} →
  (fabric : Grid.TwoInputFabric Site) →
  (state : Grid.BoolField Site) →
  (target : Site) →
  Grid.xorFabricStep (Grid.swapFabricInputs fabric) state target
  ≡ Grid.xorFabricStep fabric state target
xorDynamicsIgnoresGlobalSocketSwap = Grid.xorStepIgnoresLocalInputOrder

record GridLoopHolonomyBoundary : Set where
  constructor grid-loop-holonomy-boundary
  field
    namedSocketsCarryChosenC3Chart : Bool
    socketSwapConjugatesPhase : Bool
    pathSwapConjugatesHolonomy : Bool
    uniformThreeStepWindingsAreC3Trivial : Bool
    mixedThreeStepPathCanHaveNontrivialHolonomy : Bool
    xorOutputDetectsTheSameOrientationByItself : Bool
    socketPhaseChartIsPhysicalTorqueByDefinition : Bool
    nontrivialHolonomyRequiresPrimitiveThreeInputGate : Bool
open GridLoopHolonomyBoundary public

canonicalGridLoopHolonomyBoundary : GridLoopHolonomyBoundary
canonicalGridLoopHolonomyBoundary =
  grid-loop-holonomy-boundary
    true true true true true false false false
