module DASHI.ComputerScience.ProgramInputSemanticNonDescentExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine

------------------------------------------------------------------------
-- PROGRAM SURFACE DOES NOT DETERMINE EXECUTION SEMANTICS WITHOUT INPUT STATE
--
-- The same countdown program is run from two different initial register files.
-- A coarse observer that sees only the Program collides, while a bounded output
-- consumer distinguishes the states.  This is an executable non-descent witness
-- using the repository's canonical ConsumerNonDescentWitness.
--
-- This is NOT Rice's theorem.  It is one concrete fibre collision showing why
-- syntax/program identity and semantic outcome must remain distinct.
------------------------------------------------------------------------

programObserver : Machine.MachineState → Machine.Program
programObserver = Machine.program

boundedOutput6 : Machine.MachineState → List Nat
boundedOutput6 state = Machine.output (Machine.runFuel 6 state)

countdown0State : Machine.MachineState
countdown0State = Machine.countdownInitialState 0

countdown1State : Machine.MachineState
countdown1State = Machine.countdownInitialState 1

sameCountdownProgram :
  programObserver countdown0State ≡ programObserver countdown1State
sameCountdownProgram = refl

countdown0BoundedOutput : boundedOutput6 countdown0State ≡ []
countdown0BoundedOutput = refl

countdown1BoundedOutput : boundedOutput6 countdown1State ≡ 1 ∷ []
countdown1BoundedOutput = refl

countdownProgramSurfaceNonDescent :
  Descent.ConsumerNonDescentWitness programObserver boundedOutput6
countdownProgramSurfaceNonDescent =
  Descent.consumerNonDescentWitness
    countdown0State
    countdown1State
    sameCountdownProgram
    different
  where
    different : boundedOutput6 countdown0State ≡ boundedOutput6 countdown1State → ⊥
    different ()

programAloneNotSufficientForBoundedOutput :
  Descent.ConsumerSufficient programObserver boundedOutput6 → ⊥
programAloneNotSufficientForBoundedOutput =
  Descent.nonDescentWitnessBlocksSufficiency countdownProgramSurfaceNonDescent

------------------------------------------------------------------------
-- The collision tells us which coordinate is absent for this witnessed pair:
-- the initial register/input state.  Pairing is a candidate refinement; this
-- module does not overclaim global semantic sufficiency for all programs.
------------------------------------------------------------------------

record ProgramInputSurface : Set where
  constructor programInputSurface
  field
    programSurface : Machine.Program
    registerSurface : Machine.RegisterFile

open ProgramInputSurface public

programAndRegisterObserver : Machine.MachineState → ProgramInputSurface
programAndRegisterObserver state =
  programInputSurface (Machine.program state) (Machine.registers state)

record ProgramSemanticNonDescentBoundary : Set where
  constructor programSemanticNonDescentBoundary
  field
    sameProgramDifferentBoundedOutputWitnessed : Bool
    programAloneSufficientForBoundedOutput : Bool
    inputRegisterCoordinateExposed : Bool
    pairedProgramInputGloballySufficientClaimed : Bool
    riceTheoremClaimedFromThisWitness : Bool

canonicalProgramSemanticNonDescentBoundary : ProgramSemanticNonDescentBoundary
canonicalProgramSemanticNonDescentBoundary =
  programSemanticNonDescentBoundary true false true false false
