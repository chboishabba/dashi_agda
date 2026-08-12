module DASHI.Crypto.AlgorithmRelativeRecoveryCostExact where

------------------------------------------------------------------------
-- ALGORITHM-RELATIVE VALUE OF INFORMATION
--
-- Cardinality shrinkage is not the same statement as computational progress.
-- An observation is useful to a particular recovery architecture only when the
-- complete local+reconciliation cost actually drops.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

record RecoveryArchitecture : Set where
  constructor recoveryArchitecture
  field
    candidateCount : Nat
    perCandidateLocalCost : Nat
    reconciliationCost : Nat

open RecoveryArchitecture public

totalRecoveryCost : RecoveryArchitecture → Nat
totalRecoveryCost architecture =
  candidateCount architecture * perCandidateLocalCost architecture
  + reconciliationCost architecture

record ObservationCostComparison : Set where
  constructor observationCostComparison
  field
    before after : RecoveryArchitecture
    candidateShrinks : candidateCount after ≤ candidateCount before

open ObservationCostComparison public

record ComputationalImprovement
    (comparison : ObservationCostComparison) : Set where
  constructor computationalImprovement
  field
    CostDrop : Nat
    dropAccounting :
      totalRecoveryCost (before comparison)
      ≡ totalRecoveryCost (after comparison) + CostDrop

open ComputationalImprovement public

------------------------------------------------------------------------
-- Exact regressions.
------------------------------------------------------------------------

beneficialBefore : RecoveryArchitecture
beneficialBefore = recoveryArchitecture 2 7 6

beneficialAfter : RecoveryArchitecture
beneficialAfter = recoveryArchitecture 1 7 6

beneficialComparison : ObservationCostComparison
beneficialComparison = observationCostComparison beneficialBefore beneficialAfter (s≤s (s≤s z≤n))

beneficialCostDrop : ComputationalImprovement beneficialComparison
beneficialCostDrop = computationalImprovement 7 refl

-- Candidate cardinality can shrink while reconciliation becomes more expensive.
-- This is the exact counterexample to "one leaked bit is automatically useful".

adverseBefore : RecoveryArchitecture
adverseBefore = recoveryArchitecture 2 1 0

adverseAfter : RecoveryArchitecture
adverseAfter = recoveryArchitecture 1 1 10

adverseComparison : ObservationCostComparison
adverseComparison = observationCostComparison adverseBefore adverseAfter (s≤s (s≤s z≤n))

candidateShrinkButCostRises :
  totalRecoveryCost adverseBefore ≡ 2
  × totalRecoveryCost adverseAfter ≡ 11
candidateShrinkButCostRises = refl , refl
  where
  open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Search-cost information measure: the theorem-bearing object is an exact
-- cost drop, not merely log-cardinality or a Shannon quantity.
------------------------------------------------------------------------

algorithmRelativeInformationGain :
  ∀ {comparison : ObservationCostComparison} →
  ComputationalImprovement comparison → Nat
algorithmRelativeInformationGain improvement = CostDrop improvement
