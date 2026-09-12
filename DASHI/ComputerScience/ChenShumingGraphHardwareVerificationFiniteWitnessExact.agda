module DASHI.ComputerScience.ChenShumingGraphHardwareVerificationFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.ChenShumingGraphHardwareVerificationBidiExact as Chen

------------------------------------------------------------------------
-- FINITE RECONSTRUCTION WITNESS
--
-- This is a finite DASHI witness for the published method shape, not a claim
-- that these counts are the paper's experimental corpus or a Galaxy/Feiteng
-- processor qualification run.
------------------------------------------------------------------------

record FiniteChenVerificationWitness : Set where
  constructor finite-chen-verification-witness
  field
    sourceReference : String
    specificationNodes : Nat
    finiteStimuli : Nat
    observedSignals : Nat
    residualMismatches : Nat
    mechanismStages : List Chen.VerificationStage
    sourcePaperNumericsReproduced : Bool
    processorInstantiationPaid : Bool
    nextExactLeaf : String

open FiniteChenVerificationWitness public

finiteChenVerificationWitness : FiniteChenVerificationWitness
finiteChenVerificationWitness = finite-chen-verification-witness
  "DOI 10.1155/2018/6398616"
  3
  4
  4
  1
  (Chen.graphSpecification ∷ Chen.stimulusConstruction ∷ Chen.simulationExecution ∷
   Chen.observationExtraction ∷ Chen.specificationComparison ∷ Chen.residualClassification ∷ [])
  false
  false
  "recover source-exact graph semantics, stimulus corpus, coverage metric and mismatch oracle, then replay a paper-level finite verification case"

finiteWitnessExercisesPublishedStageOrder : Bool
finiteWitnessExercisesPublishedStageOrder = true

finiteWitnessIsPaperNumericalReplication : Bool
finiteWitnessIsPaperNumericalReplication = false

finiteWitnessPaysGalaxyProcessorDeployment : Bool
finiteWitnessPaysGalaxyProcessorDeployment = false
