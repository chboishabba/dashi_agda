module DASHI.Wikimedia.IbrahimPesticideExperimentDesignRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RED / REGRESSION SURFACE
--
-- The pesticide/cannabis/tobacco regulatory lane must consume the existing
-- DASHI experiment-design discipline rather than merely accumulating more
-- analytes or country-comparison coordinates.
--
-- Required downstream surfaces:
--   * observer collision / missing distinction;
--   * admissibility before ranking;
--   * finite candidate experiment language;
--   * Pareto ranking without implicit authority;
--   * held-out / same-object validation;
--   * cheapest adequate measurement escalation.
------------------------------------------------------------------------

record PesticideExperimentDesignRegression : Set where
  constructor pesticide-experiment-design-regression
  field
    observerCollisionRequired : Bool
    admissibilityBeforeParetoRequired : Bool
    finiteCandidateLanguageRequired : Bool
    paretoDoesNotChooseAuthorityRequired : Bool
    sameObjectValidationRequired : Bool
    cheapestAdequateExperimentRequired : Bool
    priorityZeroExperimentName : String
    priorityOneExperimentName : String
    priorityTwoExperimentName : String
open PesticideExperimentDesignRegression public

requiredPesticideExperimentDesignRegression : PesticideExperimentDesignRegression
requiredPesticideExperimentDesignRegression = pesticide-experiment-design-regression
  true true true true true true
  "same-material cannabis / tobacco / mixed-combustion transfer experiment"
  "Bt post-application harvest burden experiment"
  "jurisdiction exposure-prior refresh / surveillance comparison"
