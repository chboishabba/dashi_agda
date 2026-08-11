module DASHI.Cognition.PNF.SetBasedDemandPlanning where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.DirectDemandLookup using (ProbeContract)

------------------------------------------------------------------------
-- Migration 053 normalizes heterogeneous demand predicates before candidate
-- lookup.  The pure theorem covers row capacities and execution shape.  Index
-- probe behaviour remains the separate PostgreSQL ProbeContract.
------------------------------------------------------------------------

normalizedKeyRows : Nat → Nat → Nat
normalizedKeyRows zero keysPerDemand = zero
normalizedKeyRows (suc demands) keysPerDemand =
  keysPerDemand +ᶜ normalizedKeyRows demands keysPerDemand

normalizedKeyRowsClosed : ∀ demands keysPerDemand →
  normalizedKeyRows demands keysPerDemand ≡ demands *ᶜ keysPerDemand
normalizedKeyRowsClosed zero keysPerDemand = refl
normalizedKeyRowsClosed (suc demands) keysPerDemand
  rewrite normalizedKeyRowsClosed demands keysPerDemand = refl

candidateRowCapacity : Nat → Nat → Nat
candidateRowCapacity zero maximumCandidates = zero
candidateRowCapacity (suc demands) maximumCandidates =
  maximumCandidates +ᶜ candidateRowCapacity demands maximumCandidates

candidateRowCapacityClosed : ∀ demands maximumCandidates →
  candidateRowCapacity demands maximumCandidates ≡
    demands *ᶜ maximumCandidates
candidateRowCapacityClosed zero maximumCandidates = refl
candidateRowCapacityClosed (suc demands) maximumCandidates
  rewrite candidateRowCapacityClosed demands maximumCandidates = refl

data PlanningExecution : Set where
  perDemandProcedural setBasedRelational : PlanningExecution

data CandidateValidation : Set where
  perCandidateRecursive setBasedContainment : CandidateValidation

record DemandKeyBudget (keysPerDemand : Nat) : Set where
  constructor demandKeyBudget
  field
    actualKeys : Nat
    actualKeysWithinBudget : actualKeys ≤ᶜ keysPerDemand

open DemandKeyBudget public

record SetBasedPlanningCertificate
    (demands keysPerDemand maximumCandidates : Nat) : Set where
  constructor setBasedPlanningCertificate
  field
    execution : PlanningExecution
    executionIsSetBased : execution ≡ setBasedRelational
    validation : CandidateValidation
    validationIsSetBased : validation ≡ setBasedContainment
    normalizedKeyBound : Nat
    normalizedKeyBoundClosed :
      normalizedKeyBound ≡ demands *ᶜ keysPerDemand
    candidateOutputBound : Nat
    candidateOutputBoundClosed :
      candidateOutputBound ≡ demands *ᶜ maximumCandidates
    storageEngineProbe : ProbeContract

open SetBasedPlanningCertificate public

canonicalSetBasedPlanningCertificate :
  ∀ demands keysPerDemand maximumCandidates →
  ProbeContract →
  SetBasedPlanningCertificate demands keysPerDemand maximumCandidates
canonicalSetBasedPlanningCertificate
  demands keysPerDemand maximumCandidates probe =
  setBasedPlanningCertificate
    setBasedRelational
    refl
    setBasedContainment
    refl
    (demands *ᶜ keysPerDemand)
    refl
    (demands *ᶜ maximumCandidates)
    refl
    probe

proceduralLoopIsNotSetBased :
  perDemandProcedural ≡ setBasedRelational → ⊥
proceduralLoopIsNotSetBased ()

recursiveTriggerIsNotSetBasedValidation :
  perCandidateRecursive ≡ setBasedContainment → ⊥
recursiveTriggerIsNotSetBasedValidation ()

proceduralRuntimeCannotUseSetBasedCertificate :
  ∀ demands keysPerDemand maximumCandidates probe →
  perDemandProcedural ≡
    execution
      (canonicalSetBasedPlanningCertificate
        demands keysPerDemand maximumCandidates probe) → ⊥
proceduralRuntimeCannotUseSetBasedCertificate
  demands keysPerDemand maximumCandidates probe proof =
  proceduralLoopIsNotSetBased proof

recursiveRuntimeCannotUseSetBasedValidationCertificate :
  ∀ demands keysPerDemand maximumCandidates probe →
  perCandidateRecursive ≡
    validation
      (canonicalSetBasedPlanningCertificate
        demands keysPerDemand maximumCandidates probe) → ⊥
recursiveRuntimeCannotUseSetBasedValidationCertificate
  demands keysPerDemand maximumCandidates probe proof =
  recursiveTriggerIsNotSetBasedValidation proof
