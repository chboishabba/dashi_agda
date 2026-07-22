module DASHI.Cognition.CognitiveVacuumClassBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (length)
open import Data.Nat using (_≤_)

import DASHI.Cognition.DashiCognitiveSystem as Cognitive

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- A vacuum class is a stable observed class plus an actual multiscale
-- minimum theorem.  Stability alone does not manufacture that minimum.
------------------------------------------------------------------------

record MultiscaleDefectModel
    (system : Cognitive.DASHICognitiveSystem) : Set₁ where
  field
    scales : List Nat
    weight : Nat → Nat
    defect : Nat → Cognitive.Hidden system → Nat

open MultiscaleDefectModel public

weightedDefectAt :
  ∀ {system} →
  MultiscaleDefectModel system →
  Nat →
  Cognitive.Hidden system →
  Nat
weightedDefectAt model scale hidden =
  weight model scale * defect model scale hidden

sumDefect :
  ∀ {system} →
  MultiscaleDefectModel system →
  List Nat →
  Cognitive.Hidden system →
  Nat
sumDefect model [] hidden = 0
sumDefect model (scale ∷ rest) hidden =
  weightedDefectAt model scale hidden + sumDefect model rest hidden

totalDefect :
  ∀ {system} →
  MultiscaleDefectModel system →
  Cognitive.Hidden system →
  Nat
totalDefect model hidden = sumDefect model (scales model) hidden

record VacuumClass
    (system : Cognitive.DASHICognitiveSystem)
    (model : MultiscaleDefectModel system)
    (representative : Cognitive.Hidden system) : Set where
  field
    classStable : Cognitive.StableObservedClass system representative
    globallyMinimal :
      ∀ candidate →
      totalDefect model representative ≤ totalDefect model candidate

vacuumClassIsStable :
  ∀ {system model representative} →
  VacuumClass system model representative →
  Cognitive.StableObservedClass system representative
vacuumClassIsStable vacuum = VacuumClass.classStable vacuum

------------------------------------------------------------------------
-- Concrete counterexample: both hidden states lie in the same stable
-- observation class, but only true minimizes the literal defect.  Therefore
-- stable cognitive class does not imply vacuum class.
------------------------------------------------------------------------

booleanCognitiveSystem : Cognitive.DASHICognitiveSystem
booleanCognitiveSystem = record
  { Hidden = Bool
  ; Observable = ⊤
  ; Control = ⊤
  ; StackSymbol = ⊤
  ; observe = λ _ → tt
  ; admissibleWorld = λ _ → ⊤
  ; semanticStep = λ _ hidden _ → hidden
  ; stackStep = λ _ stack _ → stack
  ; margin = λ _ _ _ → Cognitive.positiveMargin 1
  ; grammarCost = length
  ; modelCost = 0
  ; distortion = λ _ _ → 0
  ; coarseGrain = λ _ hidden → hidden
  ; involution = λ hidden → hidden
  ; coarseObservationStable = λ _ _ → refl
  ; involutionObservationStable = λ _ → refl
  }

booleanDefectModel : MultiscaleDefectModel booleanCognitiveSystem
booleanDefectModel = record
  { scales = 0 ∷ []
  ; weight = λ _ → 1
  ; defect = λ _ hidden →
      caseBool hidden
  }
  where
  caseBool : Bool → Nat
  caseBool false = 1
  caseBool true = 0

falseClassIsStable :
  Cognitive.StableObservedClass booleanCognitiveSystem false
falseClassIsStable =
  Cognitive.canonicalStableObservedClass booleanCognitiveSystem false

trueClassIsStable :
  Cognitive.StableObservedClass booleanCognitiveSystem true
trueClassIsStable =
  Cognitive.canonicalStableObservedClass booleanCognitiveSystem true

falseDefectIsOne : totalDefect booleanDefectModel false ≡ 1
falseDefectIsOne = refl

trueDefectIsZero : totalDefect booleanDefectModel true ≡ 0
trueDefectIsZero = refl

falseStableClassIsNotVacuum :
  ¬ VacuumClass booleanCognitiveSystem booleanDefectModel false
falseStableClassIsNotVacuum vacuum with
  VacuumClass.globallyMinimal vacuum true
... | ()

trueIsVacuum : VacuumClass booleanCognitiveSystem booleanDefectModel true
trueIsVacuum = record
  { classStable = trueClassIsStable
  ; globallyMinimal = λ where
      false → Data.Nat.z≤n
      true → Data.Nat.z≤n
  }
