module DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto

------------------------------------------------------------------------
-- Regression surface for the generic finite requirement Pareto compiler.
-- DASHI synthesis; no external legal proposition is introduced here.
------------------------------------------------------------------------

multipleUndominatedQuestionsAreRetained :
  Pareto.paretoFrontier Pareto.toyPortfolio
  ≡ Pareto.cheapCell ∷ Pareto.highGainCell ∷ []
multipleUndominatedQuestionsAreRetained = Pareto.toyFrontierHasTwoTradeoffs

requiredButInertIsNotEligibleNow :
  Pareto.eligible? Pareto.inertButRequiredCell ≡ false
requiredButInertIsNotEligibleNow = Pareto.inertNotEligibleNow

requiredButInertRemainsRequired :
  Pareto.requiredForConsumer Pareto.inertButRequiredCell ≡ true
requiredButInertRemainsRequired = Pareto.inertStillRequired

inadmissibleHighGainCannotEnterFrontier :
  Pareto.onParetoFrontier? Pareto.toyPortfolio Pareto.inadmissibleCell ≡ false
inadmissibleHighGainCannotEnterFrontier = Pareto.inadmissibleIsOffFrontier
