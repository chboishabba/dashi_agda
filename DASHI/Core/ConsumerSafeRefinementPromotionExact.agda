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
-- The theorem deliberately begins *after* an application has paid its own
-- domain semantics.  A protein paper, connectome source, sensor paper, legal
-- source, or other application record may pay the local facts used to construct
-- a counterexample or adequacy receipt.  Importing those facts does not transfer
-- authorship of this generic theorem to that source, and this theorem does not
-- transfer empirical truth or authority back into the application.
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

------------------------------------------------------------------------
-- The coarse candidate is excluded by the counterexample carried by repair.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Repair itself constructs consumer eligibility for the refined model.
------------------------------------------------------------------------

fineEligibleFromRepair :
  ∀ {problem : MDL.ConsumerMDLProblem}
    {costs : MDL.CostHyperfabric problem}
    {coarse fine : MDL.Model problem} →
  ConsumerSafeRefinementPromotion costs coarse fine →
  MDL.Eligible problem fine
fineEligibleFromRepair promotion =
  MDL.repairProvidesEligibleRefinement (repair promotion)

------------------------------------------------------------------------
-- The independent selection receipts also carry eligibility.  These are kept
-- separate rather than proof-identified: agreement of selected repository
-- objects does not require proof irrelevance or collapse provenance histories.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Boundary / attribution firewall.
------------------------------------------------------------------------

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
    true
    true
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Attribution note encoded as data, not authority transfer.
------------------------------------------------------------------------

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
