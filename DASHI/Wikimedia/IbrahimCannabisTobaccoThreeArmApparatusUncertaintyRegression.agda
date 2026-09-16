module DASHI.Wikimedia.IbrahimCannabisTobaccoThreeArmApparatusUncertaintyRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

record ThreeArmApparatusUncertaintyRegression : Set where
  constructor three-arm-apparatus-uncertainty-regression
  field
    exactJointGeometryRequired : Bool
    machineRegimeRequired : Bool
    hybridProvenanceMustBeExplicit : Bool
    analyteWiseUncertaintyRequired : Bool
    covarianceMustBeRetained : Bool
    lowMiddleHighRatioEscalationRequired : Bool
    centralRatioNotUniversal : Bool
    targetOwner : String
open ThreeArmApparatusUncertaintyRegression public

requiredThreeArmApparatusUncertaintyRegression : ThreeArmApparatusUncertaintyRegression
requiredThreeArmApparatusUncertaintyRegression = three-arm-apparatus-uncertainty-regression
  true true true true true true true
  "IbrahimCannabisTobaccoThreeArmApparatusUncertaintyExact"
