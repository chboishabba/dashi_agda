module DASHI.Culture.Cuisine.CompositionProvenanceCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Material composition, nutrition, cooking transformation, and provenance
-- are composable surfaces, but none is definitionally the dish's identity.
------------------------------------------------------------------------

data Nutrient : Set where
  energy       : Nutrient
  protein      : Nutrient
  totalFat     : Nutrient
  saturatedFat : Nutrient
  carbohydrate : Nutrient
  sugar        : Nutrient
  fibre        : Nutrient
  sodium       : Nutrient
  calcium      : Nutrient
  iron         : Nutrient
  potassium    : Nutrient
  vitaminA     : Nutrient
  vitaminC     : Nutrient
  vitaminB12   : Nutrient

record NutritionVector : Set where
  field
    amount : Nutrient → Nat
    basis  : String
    unit   : String

open NutritionVector public

data ProcessEffectKind : Set where
  retained      : ProcessEffectKind
  lost          : ProcessEffectKind
  added         : ProcessEffectKind
  concentrated  : ProcessEffectKind
  diluted       : ProcessEffectKind
  transformed   : ProcessEffectKind
  unknownEffect : ProcessEffectKind

record NutrientProcessEffect : Set where
  field
    nutrient        : Nutrient
    effectKind      : ProcessEffectKind
    beforeAmount    : Nat
    afterAmount     : Nat
    measurementNote : String

open NutrientProcessEffect public

record NutritionTransition : Set where
  field
    inputProfile  : NutritionVector
    outputProfile : NutritionVector
    effects       : List NutrientProcessEffect
    method        : String

open NutritionTransition public

data ProductionPractice : Set where
  conventional      : ProductionPractice
  organic           : ProductionPractice
  regenerative      : ProductionPractice
  agroecological    : ProductionPractice
  wildHarvested     : ProductionPractice
  intensiveAnimal   : ProductionPractice
  extensiveAnimal   : ProductionPractice
  indoorCultivation : ProductionPractice
  unknownPractice   : ProductionPractice

data ProcessingStep : Set where
  harvested   : ProcessingStep
  milled      : ProcessingStep
  fermented   : ProcessingStep
  cured       : ProcessingStep
  aged        : ProcessingStep
  smoked      : ProcessingStep
  dried       : ProcessingStep
  frozen      : ProcessingStep
  canned      : ProcessingStep
  transported : ProcessingStep

record IngredientProvenance : Set where
  field
    ingredientName      : String
    organismOrSubstrate : String
    cultivarOrBreed     : String
    producer            : String
    region              : String
    practice            : ProductionPractice
    processingChain     : List ProcessingStep
    labourReceipt       : String
    ecologicalReceipt   : String

open IngredientProvenance public

record IngredientGenealogy : Set where
  field
    ancestralCarrier         : String
    domesticationOrSelection : String
    historicalRegions        : List String
    transformations          : List ProcessingStep
    currentForm              : String
    sourceLocators           : List String

open IngredientGenealogy public

record RecipeTransition (State : Set) : Set where
  field
    beforeState           : State
    afterState            : State
    operation             : String
    tool                  : String
    timeCoordinate        : Nat
    temperatureCoordinate : Nat
    targetDescription     : String

open RecipeTransition public

data Route (State : Set) : State → State → Set where
  routeStop : {s : State} → Route State s s
  routeStep : {a b c : State} →
              (transition : RecipeTransition State) →
              beforeState transition ≡ a →
              afterState transition ≡ b →
              Route State b c →
              Route State a c

------------------------------------------------------------------------
-- Small exact nutrition arithmetic witness: composition remains explicit.
------------------------------------------------------------------------

record TwoIngredientNutrientTotal : Set where
  field
    firstAmount  : Nat
    secondAmount : Nat
    totalAmount  : Nat
    totalLaw     : totalAmount ≡ firstAmount + secondAmount

open TwoIngredientNutrientTotal public

proteinCompositionExample : TwoIngredientNutrientTotal
proteinCompositionExample = record
  { firstAmount = 7
  ; secondAmount = 5
  ; totalAmount = 12
  ; totalLaw = refl
  }
