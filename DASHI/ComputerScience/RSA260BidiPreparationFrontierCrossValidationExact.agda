module DASHI.ComputerScience.RSA260BidiPreparationFrontierCrossValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiPreparationFibreSearchExact as Search
import DASHI.ComputerScience.RSA260BidiCandidateProjection256Exact as Projection256

record FrontierValidationRuntimeSource : Set where
  constructor frontier-validation-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    runtime : String
open FrontierValidationRuntimeSource public

rotate31FrontierRuntimeSource : FrontierValidationRuntimeSource
rotate31FrontierRuntimeSource = frontier-validation-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_preparation_frontier_validation.py"
  "f8dab8edffc0544156e6991efeeeb2af2f0bb643"
  "b95aa8df3731f0fea83f78adbf32450290b33688"
  "Python 3.13.5 / NumPy 2.3.5"

rotate29FrontierRuntimeSource : FrontierValidationRuntimeSource
rotate29FrontierRuntimeSource = frontier-validation-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_rotate29_frontier_validation.py"
  "2a9f3fb23f416bb04cc8f2ccfaa73276e7a6d030"
  "c36c5df385e4f7895bc74a51e7e32f4453fb1def"
  "Python 3.13.5 / NumPy 2.3.5"

record PreparationCrossSeedReceipt : Set where
  constructor preparation-cross-seed-receipt
  field
    adapter : String
    independentSeedPairs : Nat
    passedSeedPairs : Nat
    meanGeneratorDegreeNumeratorTimes1000 : Nat
    meanRelationDimensionNumeratorTimes1000 : Nat
    zeroShiftTotal : Nat
    medianMinimumKernelWeight : Nat
    minimumObservedKernelWeight : Nat
    maximumObservedMinimumKernelWeight : Nat
open PreparationCrossSeedReceipt public

affine511CrossSeed : PreparationCrossSeedReceipt
affine511CrossSeed = preparation-cross-seed-receipt
  "affine_511_1" 8 8 16875 15125 1 304 12 376

rotate31CrossSeed : PreparationCrossSeedReceipt
rotate31CrossSeed = preparation-cross-seed-receipt
  "rotate31" 8 8 16250 10250 0 78 52 100

rotate29CrossSeed : PreparationCrossSeedReceipt
rotate29CrossSeed = preparation-cross-seed-receipt
  "rotate29" 8 8 15125 9000 0 30 24 48

record Width256FrontierReceipt : Set where
  constructor width256-frontier-receipt
  field
    adapter : String
    width : Nat
    sequenceCount : Nat
    totalBlockColumns : Nat
    termsPerSequence : Nat
    totalElapsedMillisecondsApprox : Nat
    consumerTransportPassed : Bool
open Width256FrontierReceipt public

affine511Width256 : Width256FrontierReceipt
affine511Width256 = width256-frontier-receipt
  "affine_511_1" 256 2 512 4 2533 true

rotate31Width256 : Width256FrontierReceipt
rotate31Width256 = width256-frontier-receipt
  "rotate31" 256 2 512 4 2492 true

rotate29Width256 : Width256FrontierReceipt
rotate29Width256 = width256-frontier-receipt
  "rotate29" 256 2 512 4 2410 true

record RobustnessAwarePreparationPreference : Set where
  constructor robustness-aware-preparation-preference
  field
    previousPreferredAdapter : String
    preferredAdapter : String
    allFrontierSeedRunsPassed : Bool
    preferredHasLowerMeanGeneratorDegree : Bool
    preferredHasLowerMeanRelationDimension : Bool
    preferredHasNoZeroShiftFailures : Bool
    preferredHasLowerMedianMinimumKernelWeight : Bool
    width256RuntimeOrderMateriallySeparated : Bool
    exactFrontierScriptBlobExecuted : Bool
    exactDependencyClosureExecuted : Bool
    preferredTestedIsGlobalOptimum : Bool
    preferredAdapterIsProductionCADOPreparation : Bool
    historicalSameObjectIdentityPaid : Bool
open RobustnessAwarePreparationPreference public

currentRobustnessAwarePreparationPreference : RobustnessAwarePreparationPreference
currentRobustnessAwarePreparationPreference = robustness-aware-preparation-preference
  "rotate31"
  "rotate29"
  true true true true true
  false
  true
  false
  false false false

record Rotate29ImprovementReceipt : Set where
  constructor rotate29-improvement-receipt
  field
    rotate29PassesEightOfEight : Bool
    rotate31PassesEightOfEight : Bool
    rotate29MeanDegreeTimes1000 : Nat
    rotate31MeanDegreeTimes1000 : Nat
    rotate29MeanRelationDimensionTimes1000 : Nat
    rotate31MeanRelationDimensionTimes1000 : Nat
    rotate29MedianMinimumKernelWeight : Nat
    rotate31MedianMinimumKernelWeight : Nat
    rotate29Width256Passed : Bool
    rotate31Width256Passed : Bool
    preferenceChangedByCrossValidation : Bool
open Rotate29ImprovementReceipt public

currentRotate29ImprovementReceipt : Rotate29ImprovementReceipt
currentRotate29ImprovementReceipt = rotate29-improvement-receipt
  true true
  15125 16250
  9000 10250
  30 78
  true true
  true

searchBoundary : Search.PreparationFibreInterpretationBoundary
searchBoundary = Search.canonicalPreparationFibreInterpretationBoundary

projection256Boundary : Projection256.Projection256ConsumerBoundary
projection256Boundary = Projection256.canonicalProjection256ConsumerBoundary

data FrontierPreferenceImpliesGlobalOptimum : Set where
data PythonTimingImpliesProductionPerformance : Set where
data RobustPreferredAdapterImpliesProductionAdapter : Set where
data ExactScriptImpliesExactDependencyClosure : Set where
data PreviousPreferenceBecomesFalseAfterSupersession : Set where

frontierPreferenceDoesNotCreateGlobalOptimum : FrontierPreferenceImpliesGlobalOptimum → ⊥
frontierPreferenceDoesNotCreateGlobalOptimum ()

pythonTimingDoesNotCreateProductionPerformance : PythonTimingImpliesProductionPerformance → ⊥
pythonTimingDoesNotCreateProductionPerformance ()

robustPreferenceDoesNotCreateProductionAdapter : RobustPreferredAdapterImpliesProductionAdapter → ⊥
robustPreferenceDoesNotCreateProductionAdapter ()

exactScriptDoesNotCreateDependencyClosure : ExactScriptImpliesExactDependencyClosure → ⊥
exactScriptDoesNotCreateDependencyClosure ()

supersessionDoesNotRewriteHistoricalPreference : PreviousPreferenceBecomesFalseAfterSupersession → ⊥
supersessionDoesNotRewriteHistoricalPreference ()
