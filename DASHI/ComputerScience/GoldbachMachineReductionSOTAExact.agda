module DASHI.ComputerScience.GoldbachMachineReductionSOTAExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ATTRIBUTED SURROUNDING SOTA: CERTIFIED MACHINE REDUCTIONS
--
-- External owner:
--   Maxence Faldor; Moritz Firsching / Google DeepMind
--   google-deepmind/cryptids
-- Pinned repository revision inspected by DASHI:
--   f5d4559a82df052b2297be3349eccbf58b2c5a1d
--
-- Their Lean development proves a 25 -> 21 state Goldbach Turing-machine
-- reduction, halting equivalence, and conjecture semantics.  Their public
-- runtime audit reports 339411 steps for the 21-state machine versus 170966
-- for the 25-state machine through n=40 (~1.99x), so reducing static control
-- size can increase dynamic execution cost.
--
-- This is an EXTERNAL FORMAL REDUCTION PRECEDENT.  It proves nothing about
-- Mike Dupont's FRACTRAN machines or DASHI's independent success-macro theorem.
------------------------------------------------------------------------

data ReductionSourceRole : Set where
  externalFormalReductionPrecedent : ReductionSourceRole
  localDASHIComparison : ReductionSourceRole

record MachineReductionSOTASource : Set where
  constructor machineReductionSOTASource
  field
    role : ReductionSourceRole
    owner : String
    repository : String
    revision : String
    sourceMachine : String
    reducedMachine : String
    formalScope : String
    runtimeScope : String

open MachineReductionSOTASource public

deepMindGoldbachReductionPrecedent : MachineReductionSOTASource
deepMindGoldbachReductionPrecedent =
  machineReductionSOTASource
    externalFormalReductionPrecedent
    "Maxence Faldor; Moritz Firsching / Google DeepMind"
    "google-deepmind/cryptids"
    "f5d4559a82df052b2297be3349eccbf58b2c5a1d"
    "goldbach_25: 25-state 2-symbol Turing machine"
    "goldbach_21: 21-state 2-symbol Turing machine"
    "Lean 4 kernel proofs of fewer states, candidate/reference halting equivalence, and both machines halting iff Goldbach's conjecture is false"
    "Public runtime audit through n=40: goldbach_21 = 339411 steps; goldbach_25 = 170966 steps; about 1.99x"

externalGoldbach21RuntimeSteps : Nat
externalGoldbach21RuntimeSteps = 339411

externalGoldbach25RuntimeSteps : Nat
externalGoldbach25RuntimeSteps = 170966

externalReducedStateCount : Nat
externalReducedStateCount = 21

externalReferenceStateCount : Nat
externalReferenceStateCount = 25

record GoldbachMachineReductionSOTABoundary : Set where
  constructor goldbachMachineReductionSOTABoundary
  field
    externalCertifiedStateReductionExists : Bool
    externalHaltingEquivalenceExists : Bool
    externalConjectureSemanticsExists : Bool
    externalReducedMachineCanRunLonger : Bool
    staticCompressionCanIncreaseRuntimeHasIndependentPrecedentFlag : Bool
    sameConjectureMeansSameMachine : Bool
    turingStateReductionEqualsFractranFractionReduction : Bool
    deepMindResultProvesDashiFractranReductionFlag : Bool

open GoldbachMachineReductionSOTABoundary public

canonicalGoldbachMachineReductionSOTABoundary :
  GoldbachMachineReductionSOTABoundary
canonicalGoldbachMachineReductionSOTABoundary =
  goldbachMachineReductionSOTABoundary
    true true true true true
    false false false

staticCompressionCanIncreaseRuntimeHasIndependentPrecedent : Bool
staticCompressionCanIncreaseRuntimeHasIndependentPrecedent = true

deepMindResultProvesDashiFractranReduction : Bool
deepMindResultProvesDashiFractranReduction = false
