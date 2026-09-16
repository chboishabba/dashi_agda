module DASHI.Wikimedia.IbrahimDisposableVapeUnknownIngredientRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

record DisposableVapeUnknownIngredientRegression : Set where
  constructor disposable-vape-unknown-ingredient-regression
  field
    labelNotCompositionRequired : Bool
    targetedPanelNotChemicalUniverseRequired : Bool
    liquidNotAerosolRequired : Bool
    virginNotAgedRequired : Bool
    deviceMaterialsSeparateRequired : Bool
    reactionProductsSeparateRequired : Bool
    unidentifiedFeaturesRetainedRequired : Bool
    nonTargetedEscalationRequired : Bool
    australiaIllicitMarketLaneRequired : Bool
    primaryConsumer : String
open DisposableVapeUnknownIngredientRegression public

requiredDisposableVapeUnknownIngredientRegression : DisposableVapeUnknownIngredientRegression
requiredDisposableVapeUnknownIngredientRegression = disposable-vape-unknown-ingredient-regression
  true true true true true true true true true
  "recover the declared, identified, tentatively identified, reaction-generated, device-derived and still-unidentified chemical universe across liquid and aerosol"
