module DASHI.Core.CandidateFamilyExecutionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CandidateFamilyExecutionExact as Family


data CandidateFamily : Set where family0 : CandidateFamily
data GlobalAction : Set where action0 : GlobalAction

spine : Family.CandidateFamilyExecutionSpine
spine = record
  { Family = CandidateFamily
  ; GlobalAction = GlobalAction
  ; admissibleFamily = λ family → Bool
  ; compose = λ family → action0
  ; globallyAdmissible = λ action → Bool
  }

execution : Family.AdmittedCandidateFamilyExecution spine family0
execution = Family.admitCandidateFamilyExecution true true

globalCheckSeparate : Bool
globalCheckSeparate =
  Family.CandidateFamilyExecutionBoundary.familyAdmissibilityImpliesGlobalAdmissibility
    Family.canonicalCandidateFamilyExecutionBoundary

globalCheckSeparateIsFalse : globalCheckSeparate ≡ false
globalCheckSeparateIsFalse = refl
