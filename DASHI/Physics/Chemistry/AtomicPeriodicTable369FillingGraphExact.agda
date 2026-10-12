module DASHI.Physics.Chemistry.AtomicPeriodicTable369FillingGraphExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungPeriodPartitionExact as PP
import DASHI.Physics.Chemistry.AtomicPeriodicTable369OEISAufbauFormulaWeldExact as O

------------------------------------------------------------------------
-- Executable early filling graph.
--
-- This owner turns the already-paid structural Madelung period partition into
-- a literal directed C_N -> C_{N+1} path through the first three closures.
-- It is a structural filling graph, not an interacting-Hamiltonian theorem.
------------------------------------------------------------------------

data EarlyFillingState : Set where
  c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : EarlyFillingState
  c10 c11 c12 c13 c14 c15 c16 c17 c18 : EarlyFillingState

nextEarly : EarlyFillingState -> EarlyFillingState
nextEarly c0 = c1
nextEarly c1 = c2
nextEarly c2 = c3
nextEarly c3 = c4
nextEarly c4 = c5
nextEarly c5 = c6
nextEarly c6 = c7
nextEarly c7 = c8
nextEarly c8 = c9
nextEarly c9 = c10
nextEarly c10 = c11
nextEarly c11 = c12
nextEarly c12 = c13
nextEarly c13 = c14
nextEarly c14 = c15
nextEarly c15 = c16
nextEarly c16 = c17
nextEarly c17 = c18
nextEarly c18 = c18

electronCount : EarlyFillingState -> Nat
electronCount c0 = 0
electronCount c1 = 1
electronCount c2 = 2
electronCount c3 = 3
electronCount c4 = 4
electronCount c5 = 5
electronCount c6 = 6
electronCount c7 = 7
electronCount c8 = 8
electronCount c9 = 9
electronCount c10 = 10
electronCount c11 = 11
electronCount c12 = 12
electronCount c13 = 13
electronCount c14 = 14
electronCount c15 = 15
electronCount c16 = 16
electronCount c17 = 17
electronCount c18 = 18

------------------------------------------------------------------------
-- Observer levels.  The graph owns the path; different consumers may inspect
-- only count, current subshell block, or closure class.
------------------------------------------------------------------------

data EarlyBlock : Set where
  before1s : EarlyBlock
  block1s block2s block2p block3s block3p : EarlyBlock

blockObserver : EarlyFillingState -> EarlyBlock
blockObserver c0 = before1s
blockObserver c1 = block1s
blockObserver c2 = block1s
blockObserver c3 = block2s
blockObserver c4 = block2s
blockObserver c5 = block2p
blockObserver c6 = block2p
blockObserver c7 = block2p
blockObserver c8 = block2p
blockObserver c9 = block2p
blockObserver c10 = block2p
blockObserver c11 = block3s
blockObserver c12 = block3s
blockObserver c13 = block3p
blockObserver c14 = block3p
blockObserver c15 = block3p
blockObserver c16 = block3p
blockObserver c17 = block3p
blockObserver c18 = block3p

data ClosureClass : Set where
  openShell : ClosureClass
  heliumClosure neonClosure argonClosure : ClosureClass

closureObserver : EarlyFillingState -> ClosureClass
closureObserver c2 = heliumClosure
closureObserver c10 = neonClosure
closureObserver c18 = argonClosure
closureObserver _ = openShell

heliumClosureCount : electronCount c2 ≡ G.historicalClosureZ G.heliumLikeClosure
heliumClosureCount = refl

neonClosureCount : electronCount c10 ≡ G.historicalClosureZ G.neonLikeClosure
neonClosureCount = refl

argonClosureCount : electronCount c18 ≡ G.historicalClosureZ G.argonLikeClosure
argonClosureCount = refl

------------------------------------------------------------------------
-- Same-object period/closure coordinates already owned upstream.
------------------------------------------------------------------------

firstPeriodCapacity : PP.periodCapacity PP.period1Blocks ≡ 2
firstPeriodCapacity = refl

secondPeriodCapacity : PP.periodCapacity PP.period2Blocks ≡ 8
secondPeriodCapacity = refl

thirdPeriodCapacity : PP.periodCapacity PP.period3Blocks ≡ 8
thirdPeriodCapacity = refl

firstClosureMatchesOEIS : electronCount c2 ≡ O.aufbauClosure 1
firstClosureMatchesOEIS = refl

secondClosureMatchesOEIS : electronCount c10 ≡ O.aufbauClosure 2
secondClosureMatchesOEIS = refl

thirdClosureMatchesOEIS : electronCount c18 ≡ O.aufbauClosure 3
thirdClosureMatchesOEIS = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AtomicFillingGraphBoundary : Set where
  constructor atomicFillingGraphBoundary
  field
    directedStructuralFillingGraphPaid : Bool
    closureObserverPaid : Bool
    graphEqualsInteractingGroundStateDynamics : Bool
    graphEqualsMeasuredSpectrum : Bool
    graphDerivesOrbitalLabelsFromTernaryCardinality : Bool

canonicalAtomicFillingGraphBoundary : AtomicFillingGraphBoundary
canonicalAtomicFillingGraphBoundary =
  atomicFillingGraphBoundary true true false false false
