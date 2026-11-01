module DASHI.Crypto.FiniteMLWEPriorScoreSearchRegressionExact where

------------------------------------------------------------------------
-- FINITE MLWE LAB: PRIOR / SCORE / SEARCH ARE DIFFERENT LAYERS
--
-- The existing 2x2 Z/5Z lab already has an additive two-row residual score.
-- Here we expose the exact consequence: score decomposition does not identify a
-- unique secret.  The public score has two distinct zero-cost candidates, and a
-- hidden-dependent observation is what finally selects one.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab
import DASHI.Crypto.AlgorithmRelativeRecoveryCostExact as Cost

row0Score : Lab.Public2 → Lab.Secret2 → Nat
row0Score t s = Lab.residualScore (Lab.e0 (Lab.candidateResidual t s))

row1Score : Lab.Public2 → Lab.Secret2 → Nat
row1Score t s = Lab.residualScore (Lab.e1 (Lab.candidateResidual t s))

scoreDecomposesByRows : ∀ t s →
  Lab.candidateScore t s ≡ row0Score t s + row1Score t s
scoreDecomposesByRows t s = refl

s01HasZeroScore : Lab.candidateScore Lab.public22 Lab.s01 ≡ 0
s01HasZeroScore = Lab.score01

s10HasZeroScore : Lab.candidateScore Lab.public22 Lab.s10 ≡ 0
s10HasZeroScore = Lab.score10

zeroScoreDoesNotIdentifyUniqueSecret : Lab.s01 ≡ Lab.s10 → ⊥
zeroScoreDoesNotIdentifyUniqueSecret = Lab.secret01NotSecret10

------------------------------------------------------------------------
-- Algorithm-relative cost on the lab's public candidate fibre.
------------------------------------------------------------------------

labBeforeObservation : Cost.RecoveryArchitecture
labBeforeObservation = Cost.recoveryArchitecture 2 5 3

labAfterObservation : Cost.RecoveryArchitecture
labAfterObservation = Cost.recoveryArchitecture 1 5 3

labObservationComparison : Cost.ObservationCostComparison
labObservationComparison =
  Cost.observationCostComparison
    labBeforeObservation
    labAfterObservation
    Cost.one≤two

labObservationSearchCostDrop : Cost.ComputationalImprovement labObservationComparison
labObservationSearchCostDrop = Cost.computationalImprovement 5 refl

labBeforeCost : Cost.totalRecoveryCost labBeforeObservation ≡ 13
labBeforeCost = refl

labAfterCost : Cost.totalRecoveryCost labAfterObservation ≡ 8
labAfterCost = refl

------------------------------------------------------------------------
-- Boundary: additive row score is a verifier decomposition, not a search
-- theorem.  Search improvement appears only after an actual candidate-fibre
-- refinement is supplied.
------------------------------------------------------------------------
