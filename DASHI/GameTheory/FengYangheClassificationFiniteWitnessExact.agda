module DASHI.GameTheory.FengYangheClassificationFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.GameTheory.FengYangheMilitaryAIGameStatisticsBidiExact as F

record FiniteFengClassificationWitness : Set where
  constructor finite-feng-classification-witness
  field
    sourceReferences : String
    family : F.FengWorkFamily
    sampleCount : Nat
    attributeCount : Nat
    noisyLabelCount : Nat
    retainedAttributeCount : Nat
    predictedClassCount : Nat
    syntheticClassifier : Bool
    sourceNumericsReproduced : Bool
    warSkullSameObjectPaid : Bool
    nextExactLeaf : String

open FiniteFengClassificationWitness public

finiteFengClassificationWitness : FiniteFengClassificationWitness
finiteFengClassificationWitness = finite-feng-classification-witness
  "NUDT Press ISBN 978-7-5673-0533-5; ISBN 978-7-5673-0611-0"
  F.multiGroupBayesianClassification
  12
  6
  2
  4
  3
  true
  false
  false
  "recover source-exact Bayesian/noisy-label model equations, data and evaluation example; require separate software/document receipt before mapping the method into War Skull II"

finiteWitnessExercisesNoiseAndAttributeFiltering : Bool
finiteWitnessExercisesNoiseAndAttributeFiltering = true

finiteWitnessIsSourceClassifierReplication : Bool
finiteWitnessIsSourceClassifierReplication = false

finiteWitnessPaysWarSkullImplementation : Bool
finiteWitnessPaysWarSkullImplementation = false
