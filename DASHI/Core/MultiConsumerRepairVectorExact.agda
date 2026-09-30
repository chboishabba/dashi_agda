module DASHI.Core.MultiConsumerRepairVectorExact where

-- Multi-consumer modeled repair guard.
-- An improvement in one fibre cannot hide a checked regression in another;
-- unchecked consumers are preserved as an explicit epistemic state.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

data RepairOutcome : Set where
  improved preserved regressed unchecked : RepairOutcome

record ConsumerRepairResult : Set where
  constructor consumer-repair-result
  field
    consumerRef : String
    outcome : RepairOutcome
    preservationWitnessRef : String
    dischargedObligationRefs : List String
    newlyCreatedObligationRefs : List String
open ConsumerRepairResult public

data NoRegression : List ConsumerRepairResult → Set where
  none : NoRegression []
  keepImproved :
    ∀ {x xs} →
    outcome x ≡ improved →
    NoRegression xs →
    NoRegression (x ∷ xs)
  keepPreserved :
    ∀ {x xs} →
    outcome x ≡ preserved →
    NoRegression xs →
    NoRegression (x ∷ xs)
  keepUnchecked :
    ∀ {x xs} →
    outcome x ≡ unchecked →
    NoRegression xs →
    NoRegression (x ∷ xs)

data SomeImprovement : List ConsumerRepairResult → Set where
  here :
    ∀ {x xs} →
    outcome x ≡ improved →
    SomeImprovement (x ∷ xs)
  there :
    ∀ {x xs} →
    SomeImprovement xs →
    SomeImprovement (x ∷ xs)

record ReviewableRepairVector : Set where
  constructor reviewable-repair-vector
  field
    repairVectorRef : String
    results : List ConsumerRepairResult
    noCheckedRegression : NoRegression results
    atLeastOneImprovement : SomeImprovement results
    appliesExternalEdit : Set
    externalEditImpossible : appliesExternalEdit → ⊥
open ReviewableRepairVector public

uncheckedIsNotPreserved : unchecked ≡ preserved → ⊥
uncheckedIsNotPreserved ()

regressionCannotEnterNoRegression :
  ∀ {x xs} →
  outcome x ≡ regressed →
  NoRegression (x ∷ xs) →
  ⊥
regressionCannotEnterNoRegression refl ()
