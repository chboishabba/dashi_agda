module DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmExecutionRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

record ThreeArmExecutionRegression : Set where
  constructor three-arm-execution-regression
  field
    sameSourceAliquotsRequired : Bool
    fixedRatioDeclaredRequired : Bool
    machinePuffProtocolRequired : Bool
    sourceResidueVectorRequired : Bool
    smokeParentVectorRequired : Bool
    thermalProductVectorRequired : Bool
    heldOutReplicatesRequired : Bool
    ratioSourceBoundedRequired : Bool
    humanUseRatioNotUniversalRequired : Bool
    directInteractionResidualRequired : Bool
    baselineRatioEvidence : String
    machineProtocolEvidence : String
open ThreeArmExecutionRegression public

requiredThreeArmExecutionRegression : ThreeArmExecutionRegression
requiredThreeArmExecutionRegression = three-arm-execution-regression
  true true true true true true true true true true
  "Hindocha et al. 2017 actual baseline cannabis:tobacco ratio 0.53:1; broad observed range retained"
  "Health Canada Intense-compatible 55 mL / 2 s / 30 s routine is an experimental comparator, not a human-topography identity"
