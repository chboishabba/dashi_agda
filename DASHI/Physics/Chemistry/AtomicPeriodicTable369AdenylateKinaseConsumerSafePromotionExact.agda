module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConsumerSafePromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerSafeRefinementPromotionExact as Promotion
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoExact as Pareto
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverLocalRepairExact as Local
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETThirdAxisExact as Third

------------------------------------------------------------------------
-- ADK INSTANTIATION OF THE GENERIC CONSUMER-SAFE PROMOTION THEOREM
--
-- Domain attribution remains local:
--   * Li, Liu & Ji 2015 pay the source-bounded three-CV AdK description;
--   * the AdK owners pay the repository-local third-axis collision, local repair,
--     adequacy receipts, and finite observer costs;
--   * ConsumerSafeRefinementPromotionExact is DASHI generic synthesis.
--
-- Importing the source-backed AdK premise does not make the paper the author of
-- the generic theorem, and the generic theorem does not turn repository-local
-- observer costs into measured experimental optimality.
------------------------------------------------------------------------

thirdAxisCostHyperfabric : MDL.CostHyperfabric Pareto.thirdAxisProblem
thirdAxisCostHyperfabric =
  MDL.costHyperfabric
    Pareto.ObserverCostAxis
    Pareto.observerCost
    Pareto.observerCostReference

thirdAxisNoStrictlyCheaperEligibleWitness :
  (candidate : Pareto.ObserverModel) →
  MDL.Eligible Pareto.thirdAxisProblem candidate →
  MDL.WeaklyDominates thirdAxisCostHyperfabric candidate Pareto.threeAxis →
  MDL.WeaklyDominates thirdAxisCostHyperfabric Pareto.threeAxis candidate
thirdAxisNoStrictlyCheaperEligibleWitness Pareto.axisErased (admissible , ()) dominates
thirdAxisNoStrictlyCheaperEligibleWitness Pareto.lidNmpOnly (admissible , ()) dominates
thirdAxisNoStrictlyCheaperEligibleWitness Pareto.lidCoreOnly (admissible , ()) dominates
thirdAxisNoStrictlyCheaperEligibleWitness Pareto.joinedTwo (admissible , ()) dominates
thirdAxisNoStrictlyCheaperEligibleWitness Pareto.threeAxis eligible dominates axis = ≤-refl

thirdAxisParetoSelected :
  MDL.ParetoAdmissible thirdAxisCostHyperfabric Pareto.threeAxis
thirdAxisParetoSelected =
  MDL.paretoAdmissible
    Pareto.thirdAxisSelectedIsEligible
    thirdAxisNoStrictlyCheaperEligibleWitness
    "threeAxis is the only eligible observer in the finite AdK family for the declared third-axis consumer; Pareto comparison occurs only inside that eligible stratum"

adkThirdAxisConsumerSafePromotion :
  Promotion.ConsumerSafeRefinementPromotion
    thirdAxisCostHyperfabric
    Pareto.joinedTwo
    Pareto.threeAxis
adkThirdAxisConsumerSafePromotion =
  Promotion.consumerSafeRefinementPromotion
    Local.joinedTwoToThreeAxisRepair
    Pareto.thirdAxisMinimalEligible
    thirdAxisParetoSelected

coarseTwoAxisObserverExcluded :
  MDL.Eligible Pareto.thirdAxisProblem Pareto.joinedTwo → ⊥
coarseTwoAxisObserverExcluded =
  Promotion.coarseEligibilityExcluded adkThirdAxisConsumerSafePromotion

threeAxisEligibleFromGenericPromotion :
  MDL.Eligible Pareto.thirdAxisProblem Pareto.threeAxis
threeAxisEligibleFromGenericPromotion =
  Promotion.fineEligibleFromRepair adkThirdAxisConsumerSafePromotion

adkThirdAxisSafeSelection :
  Promotion.ConsumerSafeSelectionReceipt
    thirdAxisCostHyperfabric
    Pareto.threeAxis
adkThirdAxisSafeSelection =
  Promotion.promotionProducesSafeSelection adkThirdAxisConsumerSafePromotion

------------------------------------------------------------------------
-- Source donor stays source-bound to the three-CV premise.
------------------------------------------------------------------------

thirdAxisSourceDonor : Third.ThirdAxisSourceCoordinate
thirdAxisSourceDonor = Third.liLiuJi2015ThreeCvSource

genericPromotionDonor : Promotion.ConsumerSafeRefinementPromotionBoundary
genericPromotionDonor = Promotion.canonicalConsumerSafeRefinementPromotionBoundary

record AdKConsumerSafePromotionBoundary : Set where
  constructor adk-consumer-safe-promotion-boundary
  field
    genericPromotionInstantiatedForThirdAxisRepair : Bool
    coarseTwoAxisObserverExcludedForThirdAxisConsumer : Bool
    threeAxisObserverParetoSelected : Bool
    sourcePaysThreeCvAdKPremise : Bool
    liLiuJiPaysGenericPromotionTheorem : Bool
    genericPromotionProvesExperimentalOptimality : Bool
    repositoryLocalCostEqualsMeasuredAcquisitionCost : Bool
    consumerSafePromotionEqualsCompleteProteinRecovery : Bool

canonicalAdKConsumerSafePromotionBoundary : AdKConsumerSafePromotionBoundary
canonicalAdKConsumerSafePromotionBoundary =
  adk-consumer-safe-promotion-boundary
    true
    true
    true
    true
    false
    false
    false
    false
