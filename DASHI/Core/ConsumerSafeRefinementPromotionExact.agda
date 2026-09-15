module DASHI.Core.ConsumerSafeRefinementPromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL

------------------------------------------------------------------------
-- CONSUMER-SAFE REFINEMENT PROMOTION
--
-- Domain-neutral synthesis of a pattern already instantiated in several DASHI
-- lanes:
--
--   consumer counterexample
--     -> typed local refinement repair
--     -> repaired eligibility
--     -> minimal-eligible / Pareto selection.
--
-- Application sources pay only their source-bounded premises.  This generic
-- theorem is DASHI synthesis and transfers structure, not empirical authority.
------------------------------------------------------------------------

record ConsumerSafeRefinementPromotion
    {problem : MDL.ConsumerMDLProblem}
    (costs : MDL.CostHyperfabric problem)
    (coarse fine : MDL.Model problem) : Set₁ where
  constructor consumerSafeRefinementPromotion
  field
    repair : MDL.LocalRefinementRepair problem coarse fine
    minimalSelection : MDL.MinimalEligibleDescription problem fine
    paretoSelection : MDL.ParetoAdmissible costs fine

open ConsumerSafeRefinementPromotion public

coarseEligibilityExcluded :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem} →
  ConsumerSafeRefinementPromotion costs coarse fine →
  MDL.Eligible problem coarse →
  ⊥
coarseEligibilityExcluded promotion =
  MDL.counterexampleExcludesEligibility
    (MDL.failure (repair promotion))

fineEligibleFromRepair :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem} →
  ConsumerSafeRefinementPromotion costs coarse fine →
  MDL.Eligible problem fine
fineEligibleFromRepair promotion =
  MDL.repairProvidesEligibleRefinement (repair promotion)

fineEligibleFromMinimalSelection :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem} →
  ConsumerSafeRefinementPromotion costs coarse fine →
  MDL.Eligible problem fine
fineEligibleFromMinimalSelection promotion =
  MDL.minimalDescriptionIsEligible (minimalSelection promotion)

fineEligibleFromParetoSelection :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem} →
  ConsumerSafeRefinementPromotion costs coarse fine →
  MDL.Eligible problem fine
fineEligibleFromParetoSelection promotion =
  MDL.selectedEligible (paretoSelection promotion)

record ConsumerSafeSelectionReceipt
    {problem : MDL.ConsumerMDLProblem}
    (costs : MDL.CostHyperfabric problem)
    (selected : MDL.Model problem) : Set₁ where
  constructor consumerSafeSelectionReceipt
  field
    eligible : MDL.Eligible problem selected
    minimal : MDL.MinimalEligibleDescription problem selected
    pareto : MDL.ParetoAdmissible costs selected

open ConsumerSafeSelectionReceipt public

promotionProducesSafeSelection :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem} →
  ConsumerSafeRefinementPromotion costs coarse fine →
  ConsumerSafeSelectionReceipt costs fine
promotionProducesSafeSelection promotion =
  consumerSafeSelectionReceipt
    (fineEligibleFromRepair promotion)
    (minimalSelection promotion)
    (paretoSelection promotion)

record ConsumerSafeRefinementPromotionBoundary : Set where
  constructor consumer-safe-refinement-promotion-boundary
  field
    counterexampleExcludesCoarseEligibility : Bool
    localRepairConstructsFineEligibility : Bool
    minimalSelectionRequiresEligibility : Bool
    paretoSelectionRequiresEligibility : Bool
    promotionIsConsumerIndexed : Bool
    domainSourceBecomesAuthorOfGenericTheorem : Bool
    genericPromotionCreatesEmpiricalTruth : Bool
    consumerSafeMeansWorldComplete : Bool
    paretoSelectionCreatesOperationalAuthority : Bool

canonicalConsumerSafeRefinementPromotionBoundary :
  ConsumerSafeRefinementPromotionBoundary
canonicalConsumerSafeRefinementPromotionBoundary =
  consumer-safe-refinement-promotion-boundary
    true true true true true false false false false

record PromotionAttributionFirewall : Set where
  constructor promotion-attribution-firewall
  field
    genericOwner : String
    applicationSourceRole : String
    transferRule : String

canonicalPromotionAttributionFirewall : PromotionAttributionFirewall
canonicalPromotionAttributionFirewall =
  promotion-attribution-firewall
    "DASHI generic synthesis: counterexample -> local repair -> eligible -> minimal/Pareto selection"
    "application sources pay only their source-bounded empirical/domain premises and identifiers"
    "cross-pollination transfers reusable structure only; it does not transfer authorship, truth, mechanism, empirical status, legal authority, or operational authority"
