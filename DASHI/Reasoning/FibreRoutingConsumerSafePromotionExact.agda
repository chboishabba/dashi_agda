module DASHI.Reasoning.FibreRoutingConsumerSafePromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerSafeRefinementPromotionExact as Promotion
import DASHI.Reasoning.FibreRoutingProjectionAdequacyCrossPollinationExact as Domain

------------------------------------------------------------------------
-- FIBRE-ROUTING INSTANTIATION OF CONSUMER-SAFE PROMOTION
--
-- The parent fibre-routing owner already carries the domain-specific hard-winner
-- overlap defect, typed hard->soft repair, and semantic adequacy receipt.  This
-- module contributes only the generic-selection instantiation required to show
-- that the DASHI promotion theorem is not AdK-specific.
--
-- Attribution firewall:
--   * Domain pays its own fibre-routing fixture and any source-bound premises;
--   * this bridge does not reattribute those premises;
--   * ConsumerSafeRefinementPromotionExact is DASHI generic synthesis;
--   * structural reuse does not create a biological mechanism claim.
------------------------------------------------------------------------

data FibreRoutingCostAxis : Set where
  retainedProjectionComplexity : FibreRoutingCostAxis

fibreRoutingCost :
  FibreRoutingCostAxis →
  Domain.FlyProjectionModel →
  Nat
fibreRoutingCost retainedProjectionComplexity model =
  Domain.projectionDescriptionLength model

fibreRoutingCostReference : FibreRoutingCostAxis → String
fibreRoutingCostReference retainedProjectionComplexity =
  "finite repository-local projection description length; ranking only after overlap-consumer adequacy"

fibreRoutingCostHyperfabric :
  MDL.CostHyperfabric Domain.flyProjectionProblem
fibreRoutingCostHyperfabric =
  MDL.costHyperfabric
    FibreRoutingCostAxis
    fibreRoutingCost
    fibreRoutingCostReference

softNoLongerThanAnyEligible :
  (candidate : Domain.FlyProjectionModel) →
  MDL.Admissible Domain.flyProjectionProblem candidate →
  MDL.ConsumerAdequate Domain.flyProjectionProblem candidate →
  MDL.descriptionLength Domain.flyProjectionProblem Domain.softOverlapModel ≤
  MDL.descriptionLength Domain.flyProjectionProblem candidate
softNoLongerThanAnyEligible Domain.hardWinnerModel admissible ()
softNoLongerThanAnyEligible Domain.softOverlapModel admissible adequate = ≤-refl

softOverlapMinimalEligible :
  MDL.MinimalEligibleDescription
    Domain.flyProjectionProblem
    Domain.softOverlapModel
softOverlapMinimalEligible =
  MDL.minimalEligibleDescription
    Domain.unit
    Domain.softOverlapAdequacyReceipt
    softNoLongerThanAnyEligible
    "soft overlap model is the only consumer-adequate member of the finite hard/soft projection family"

softNoStrictlyCheaperEligibleWitness :
  (candidate : Domain.FlyProjectionModel) →
  MDL.Eligible Domain.flyProjectionProblem candidate →
  MDL.WeaklyDominates fibreRoutingCostHyperfabric candidate Domain.softOverlapModel →
  MDL.WeaklyDominates fibreRoutingCostHyperfabric Domain.softOverlapModel candidate
softNoStrictlyCheaperEligibleWitness Domain.hardWinnerModel (admissible , ()) dominates
softNoStrictlyCheaperEligibleWitness Domain.softOverlapModel eligible dominates axis = ≤-refl

softOverlapParetoSelected :
  MDL.ParetoAdmissible
    fibreRoutingCostHyperfabric
    Domain.softOverlapModel
softOverlapParetoSelected =
  MDL.paretoAdmissible
    Domain.softRepairIsEligible
    softNoStrictlyCheaperEligibleWitness
    "soft overlap model is Pareto-selected inside the eligible overlap-consumer stratum; hard winner is excluded by its retained counterexample"

fibreRoutingConsumerSafePromotion :
  Promotion.ConsumerSafeRefinementPromotion
    fibreRoutingCostHyperfabric
    Domain.hardWinnerModel
    Domain.softOverlapModel
fibreRoutingConsumerSafePromotion =
  Promotion.consumerSafeRefinementPromotion
    Domain.hardToSoftLocalRepair
    softOverlapMinimalEligible
    softOverlapParetoSelected

hardWinnerExcludedForOverlapConsumer :
  MDL.Eligible Domain.flyProjectionProblem Domain.hardWinnerModel → ⊥
hardWinnerExcludedForOverlapConsumer =
  Promotion.coarseEligibilityExcluded fibreRoutingConsumerSafePromotion

softOverlapEligibleFromGenericPromotion :
  MDL.Eligible Domain.flyProjectionProblem Domain.softOverlapModel
softOverlapEligibleFromGenericPromotion =
  Promotion.fineEligibleFromRepair fibreRoutingConsumerSafePromotion

softOverlapSafeSelection :
  Promotion.ConsumerSafeSelectionReceipt
    fibreRoutingCostHyperfabric
    Domain.softOverlapModel
softOverlapSafeSelection =
  Promotion.promotionProducesSafeSelection fibreRoutingConsumerSafePromotion

domainBoundaryDonor : Domain.ProjectionRepairCrossPollinationBoundary
domainBoundaryDonor = Domain.canonicalProjectionRepairCrossPollinationBoundary

genericPromotionDonor : Promotion.ConsumerSafeRefinementPromotionBoundary
genericPromotionDonor = Promotion.canonicalConsumerSafeRefinementPromotionBoundary

record FibreRoutingConsumerSafePromotionBoundary : Set where
  constructor fibre-routing-consumer-safe-promotion-boundary
  field
    genericPromotionInstantiatedForOverlapRepair : Bool
    hardWinnerExcludedForOverlapConsumer : Bool
    softOverlapParetoSelected : Bool
    domainPremisesRemainAttributedToDomainOwner : Bool
    domainDonorBecomesAuthorOfGenericPromotion : Bool
    genericPromotionCreatesBiologicalMechanism : Bool
    finiteProjectionCostEqualsEmpiricalBiologicalCost : Bool
    oneRepairProvesUniversalFibreSufficiency : Bool

canonicalFibreRoutingConsumerSafePromotionBoundary :
  FibreRoutingConsumerSafePromotionBoundary
canonicalFibreRoutingConsumerSafePromotionBoundary =
  fibre-routing-consumer-safe-promotion-boundary
    true
    true
    true
    true
    false
    false
    false
    false
