module DASHI.Cognition.PNF.PhysicalMutationChurnEconomyRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Cognition.PNF.ComplexityArithmetic using (_≤ᶜ_; z≤n; s≤s)
import DASHI.Cognition.PNF.PhysicalMutationChurnEconomyExact as Churn

------------------------------------------------------------------------
-- Tiny executable witness: two physical maintenance paths can be semantically
-- identical while one uses fewer state transitions. The equality is the legal
-- rewrite boundary; the mutation inequality is only the physical-economy claim.
------------------------------------------------------------------------

Projection : Set
Projection = Nat

rebuild : Nat → Projection
rebuild n = n

deltaMaintain : Nat → Projection
deltaMaintain n = n

exactMaintenance : Churn.ExactCurrentProjectionMaintenance Nat Projection
exactMaintenance = record
  { rebuild = rebuild
  ; deltaMaintain = deltaMaintain
  ; finalProjectionExact = λ input → refl
  }

before : Churn.MutationChurnReceipt
before = Churn.mutationChurnReceipt (suc (suc zero)) zero (suc zero) (suc zero)

after : Churn.MutationChurnReceipt
after = Churn.mutationChurnReceipt (suc zero) zero zero (suc zero)

one≤three : suc zero ≤ᶜ suc (suc (suc zero))
one≤three = s≤s z≤n

nonWorsening : Churn.MutationNonWorsening before after
nonWorsening = record { mutationCountNonWorse = one≤three }

candidate : Churn.ChurnOptimisationCandidate Nat Projection
candidate = record
  { exactMaintenance = exactMaintenance
  ; before = before
  ; after = after
  ; nonWorsening = nonWorsening
  }

regressionFinalProjectionExact :
  Churn.deltaMaintain exactMaintenance (suc zero)
  ≡ Churn.rebuild exactMaintenance (suc zero)
regressionFinalProjectionExact =
  Churn.deltaMaintenanceCannotChangeFinalProjection exactMaintenance (suc zero)
