module DASHI.Economics.AIFinancingCohortMatchedOutcomeExperiment20261017Validation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Economics.AIFinancingCohortMatchedOutcomeExperiment20261017Exact as Cohort

matchedComparatorContractPaid : Cohort.matchedComparatorDeclared Cohort.currentCohortExperiment ≡ true
matchedComparatorContractPaid = Cohort.matchedComparatorContractPaid

mechanismIsNotOutcome : Cohort.mechanismSimilaritySelectsOutcome Cohort.currentCohortExperiment ≡ false
mechanismIsNotOutcome = Cohort.mechanismSimilarityDoesNotSelectOutcome

realisedOutcomesStillOpen : Cohort.allRealisedOutcomeCoordinatesPaid Cohort.currentCohortExperiment ≡ false
realisedOutcomesStillOpen = Cohort.realisedOutcomesRemainOpen
