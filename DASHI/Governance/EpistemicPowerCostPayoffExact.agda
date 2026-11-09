module DASHI.Governance.EpistemicPowerCostPayoffExact where

-- DASHI finite countermodels motivated by Satta (2024), "Epistemic
-- Exhaustion and the Retention of Power". Section-level interpretation:
-- burden-shifting can raise epistemic costs and lower expected returns.
-- The finite flags below are NOT measured psychological exhaustion,
-- causal evidence, or an interpretation of all epistemic costs.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact as History

data ReviewContext : Set where
  supportedReview asymmetricReview : ReviewContext

-- Equal work *count*, unequal circumstances.
nominalTaskCount : ReviewContext → Nat
nominalTaskCount supportedReview = suc zero
nominalTaskCount asymmetricReview = suc zero

data EpistemicCost : Set where
  lowerContextCost higherContextCost : EpistemicCost

data ExpectedEpistemicReturn : Set where
  lowerExpectedReturn higherExpectedReturn : ExpectedEpistemicReturn

contextCost : ReviewContext → EpistemicCost
contextCost supportedReview = lowerContextCost
contextCost asymmetricReview = higherContextCost

contextReturn : ReviewContext → ExpectedEpistemicReturn
contextReturn supportedReview = higherExpectedReturn
contextReturn asymmetricReview = lowerExpectedReturn

record CostPayoff : Set where
  constructor cost-payoff
  field
    effortCost : EpistemicCost
    expectedReturn : ExpectedEpistemicReturn

open CostPayoff public

costPayoff : ReviewContext → CostPayoff
costPayoff context = cost-payoff (contextCost context) (contextReturn context)

sameNominalTasksDifferentContextualCost :
  INF.NonFactorabilityWitness nominalTaskCount contextCost
sameNominalTasksDifferentContextualCost =
  INF.nonFactorabilityWitness supportedReview asymmetricReview refl (λ ())

sameNominalTasksDifferentExpectedReturn :
  INF.NonFactorabilityWitness nominalTaskCount contextReturn
sameNominalTasksDifferentExpectedReturn =
  INF.nonFactorabilityWitness supportedReview asymmetricReview refl (λ ())

sameNominalTasksDifferentCostPayoff :
  INF.NonFactorabilityWitness nominalTaskCount costPayoff
sameNominalTasksDifferentCostPayoff =
  INF.nonFactorabilityWitness supportedReview asymmetricReview refl (λ ())

taskCountCannotRecoverCostPayoff :
  INF.FactorsThrough nominalTaskCount costPayoff → ⊥
taskCountCannotRecoverCostPayoff =
  INF.witnessRulesOutEveryFlatFactorisation
    sameNominalTasksDifferentCostPayoff

anyTaskCountRechartStillLosesCostPayoff :
  ∀ {Recharted : Set} (rechart : Nat → Recharted) →
  INF.FactorsThrough
    (λ context → rechart (nominalTaskCount context))
    costPayoff → ⊥
anyTaskCountRechartStillLosesCostPayoff rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart sameNominalTasksDifferentCostPayoff

-- A finite receipt of cost/return inversion, not a claim that the selected
-- high-cost context is socially oppressive or deliberately engineered.
record CostPayoffInversionWitness : Set where
  constructor cost-payoff-inversion
  field
    sameNominalWork :
      nominalTaskCount supportedReview ≡
      nominalTaskCount asymmetricReview
    supportedCost :
      contextCost supportedReview ≡ lowerContextCost
    asymmetricCost :
      contextCost asymmetricReview ≡ higherContextCost
    supportedReturn :
      contextReturn supportedReview ≡ higherExpectedReturn
    asymmetricReturn :
      contextReturn asymmetricReview ≡ lowerExpectedReturn

costPayoffInversionWitness : CostPayoffInversionWitness
costPayoffInversionWitness =
  cost-payoff-inversion refl refl refl refl refl

------------------------------------------------------------------------
-- Same observed procedural burden cannot establish malicious intention.
-- Imported from earlier negative-control owner, without requiring causal
-- intent to be a derived field of the work-count model.
------------------------------------------------------------------------

sameReviewTasksDoNotDeterminePurpose :
  INF.FactorsThrough
    History.observedTasks History.statedPurpose → ⊥
sameReviewTasksDoNotDeterminePurpose =
  INF.witnessRulesOutEveryFlatFactorisation
    History.sameTasksCannotIdentifyPurpose
