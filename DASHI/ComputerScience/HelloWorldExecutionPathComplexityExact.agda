module DASHI.ComputerScience.HelloWorldExecutionPathComplexityExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.ComputerScience.HelloWorldEncodedWordMachineExact as Machine

------------------------------------------------------------------------
-- HELLO WORLD AS AN ACTUAL EXECUTION-FIBRE PATH
--
-- The path contains the initial machine state and each successive state after
-- one transition, through the final halted state.  This lets different cost
-- consumers observe the same execution without collapsing them together.
------------------------------------------------------------------------

stateAt : Nat → Machine.MachineState
stateAt n = Machine.runFuel n Machine.initialState

canonicalMachinePath :
  Complexity.ExecutionFibrePath Machine.MachineState
canonicalMachinePath =
  Complexity.executionFibrePath
    (stateAt 0
    ∷ stateAt 1
    ∷ stateAt 2
    ∷ stateAt 3
    ∷ stateAt 4
    ∷ stateAt 5
    ∷ stateAt 6
    ∷ stateAt 7
    ∷ stateAt 8
    ∷ stateAt 9
    ∷ stateAt 10
    ∷ stateAt 11
    ∷ stateAt 12
    ∷ stateAt 13
    ∷ stateAt 14
    ∷ [])

canonicalPathStateCount :
  Complexity.pathStateCount canonicalMachinePath ≡ 15
canonicalPathStateCount = refl

canonicalPathTransitionCount :
  Complexity.pathTransitionCount canonicalMachinePath ≡ 14
canonicalPathTransitionCount = refl

------------------------------------------------------------------------
-- K_C(gamma): same path, different consumers.
------------------------------------------------------------------------

helloWorldTransitionComplexity : Nat
helloWorldTransitionComplexity =
  Complexity.K Complexity.transitionConsumer canonicalMachinePath

helloWorldStateVisitComplexity : Nat
helloWorldStateVisitComplexity =
  Complexity.K Complexity.stateVisitConsumer canonicalMachinePath

helloWorldPCHeadTravelComplexity : Nat
helloWorldPCHeadTravelComplexity =
  Complexity.K
    (Complexity.headTravelConsumer Machine.pc)
    canonicalMachinePath

helloWorldTransitionComplexityIsFourteen :
  helloWorldTransitionComplexity ≡ 14
helloWorldTransitionComplexityIsFourteen = refl

helloWorldStateVisitComplexityIsFifteen :
  helloWorldStateVisitComplexity ≡ 15
helloWorldStateVisitComplexityIsFifteen = refl

-- PC moves 0 -> ... -> 13 during the thirteen output instructions.  The
-- fourteenth HALT transition leaves PC at 13, so head travel is 13 although
-- transition count is 14.
helloWorldPCHeadTravelComplexityIsThirteen :
  helloWorldPCHeadTravelComplexity ≡ 13
helloWorldPCHeadTravelComplexityIsThirteen = refl

------------------------------------------------------------------------
-- Storage/register observations are also functions of the same path.
------------------------------------------------------------------------

registerCellCount : Machine.MachineState → Nat
registerCellCount state = 2

programAndDataCellCount : Machine.MachineState → Nat
programAndDataCellCount state = 27

helloWorldPeakRegisterCells : Nat
helloWorldPeakRegisterCells =
  Complexity.K
    (Complexity.peakMeasureConsumer registerCellCount)
    canonicalMachinePath

helloWorldPeakProgramAndDataCells : Nat
helloWorldPeakProgramAndDataCells =
  Complexity.K
    (Complexity.peakMeasureConsumer programAndDataCellCount)
    canonicalMachinePath

helloWorldPeakRegisterCellsIsTwo :
  helloWorldPeakRegisterCells ≡ 2
helloWorldPeakRegisterCellsIsTwo = refl

helloWorldPeakProgramAndDataCellsIsTwentySeven :
  helloWorldPeakProgramAndDataCells ≡ 27
helloWorldPeakProgramAndDataCellsIsTwentySeven = refl

record HelloWorldPathComplexityReceipt : Set where
  constructor helloWorldPathComplexityReceipt
  field
    stateVisits : Nat
    transitions : Nat
    pcHeadTravel : Nat
    peakRegisterCells : Nat
    peakProgramAndDataCells : Nat
    stateVisitsExact : stateVisits ≡ 15
    transitionsExact : transitions ≡ 14
    pcHeadTravelExact : pcHeadTravel ≡ 13
    peakRegisterCellsExact : peakRegisterCells ≡ 2
    peakProgramAndDataCellsExact : peakProgramAndDataCells ≡ 27

canonicalHelloWorldPathComplexityReceipt :
  HelloWorldPathComplexityReceipt
canonicalHelloWorldPathComplexityReceipt =
  helloWorldPathComplexityReceipt
    helloWorldStateVisitComplexity
    helloWorldTransitionComplexity
    helloWorldPCHeadTravelComplexity
    helloWorldPeakRegisterCells
    helloWorldPeakProgramAndDataCells
    helloWorldStateVisitComplexityIsFifteen
    helloWorldTransitionComplexityIsFourteen
    helloWorldPCHeadTravelComplexityIsThirteen
    helloWorldPeakRegisterCellsIsTwo
    helloWorldPeakProgramAndDataCellsIsTwentySeven

record HelloWorldPathComplexityBoundary : Set where
  constructor helloWorldPathComplexityBoundary
  field
    samePathSupportsMultipleCostConsumers : Bool
    transitionCountEqualsHeadTravel : Bool
    logicalCellCountEqualsPhysicalArea : Bool
    pathComplexityIsRepresentationIndependentByDefault : Bool

canonicalHelloWorldPathComplexityBoundary :
  HelloWorldPathComplexityBoundary
canonicalHelloWorldPathComplexityBoundary =
  helloWorldPathComplexityBoundary true false false false
