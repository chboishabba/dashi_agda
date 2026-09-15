module DASHI.Wikimedia.IbrahimPesticideExperimentConsumerIndexedParetoRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record ConsumerIndexedParetoRegression : Set where
  constructor consumer-indexed-pareto-regression
  field
    crossConsumerDominanceForbidden : Bool
    sameConsumerComparisonRequired : Bool
    roadmapPrioritySeparatedFromScientificDominance : Bool
    metaConsumerMustBeExplicit : Bool
    preferenceDoesNotBecomeAuthority : Bool
    motivatingFalseDominance : String
open ConsumerIndexedParetoRegression public

requiredConsumerIndexedParetoRegression : ConsumerIndexedParetoRegression
requiredConsumerIndexedParetoRegression = consumer-indexed-pareto-regression
  true true true true true
  "raw synthetic axes can make co-smoke dominate Bt/glyphosate despite answering different scientific consumers"
