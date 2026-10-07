module DASHI.Governance.BoloBoloFederationCostComparisonExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo

------------------------------------------------------------------------
-- BOLO'BOLO COUNTERFACTUAL FEDERATION COMPARISON.
--
-- Attribution discipline:
--   * p.m.'s source supplies the nested kana / bolo / tega design vocabulary,
--     approximate design scales, bottom-up confederal orientation and warning
--     against automatic transition success;
--   * the counterfactual transformation and cost decomposition below are
--     DASHI-derived analytical machinery, not quotations from bolo'bolo;
--   * Occupy evidence may constrain/calibrate model terms but does not by
--     itself prove that bolo'bolo is empirically superior.
------------------------------------------------------------------------

record BoloNestedArchitectureDesign : Set where
  constructor boloNestedArchitectureDesign
  field
    sourceAtlas : Bolo.BoloBoloPrimarySourceAtlas
    kanaRole : Bolo.FederatedInterpretiveRole
    boloRole : Bolo.FederatedInterpretiveRole
    tegaRole : Bolo.FederatedInterpretiveRole
    broaderRole : Bolo.FederatedInterpretiveRole

open BoloNestedArchitectureDesign public

canonicalBoloNestedArchitectureDesign : BoloNestedArchitectureDesign
canonicalBoloNestedArchitectureDesign =
  boloNestedArchitectureDesign
    Bolo.canonicalBoloBoloPrimarySourceAtlas
    (Bolo.sourceLayerInterpretation Bolo.kanaLayer)
    (Bolo.sourceLayerInterpretation Bolo.boloLayer)
    (Bolo.sourceLayerInterpretation Bolo.tegaLayer)
    (Bolo.sourceLayerInterpretation Bolo.broaderCoordinationLayer)

------------------------------------------------------------------------
-- Structural counterfactual accounting.
------------------------------------------------------------------------

record FederationTransformationAccounting : Set where
  constructor federationTransformationAccounting
  field
    globalCouplingEdges : Nat
    retainedLocalEdges : Nat
    removedGlobalEdges : Nat
    newBoundaryEdges : Nat
    newDelegationEdges : Nat
    unresolvedDependencyEdges : Nat
    exactGlobalPartition :
      globalCouplingEdges ≡ retainedLocalEdges + removedGlobalEdges

open FederationTransformationAccounting public

newFederationInterfaceEdges : FederationTransformationAccounting → Nat
newFederationInterfaceEdges accounting =
  newBoundaryEdges accounting
  + newDelegationEdges accounting
  + unresolvedDependencyEdges accounting

------------------------------------------------------------------------
-- Abstract coordination-cost decomposition.
------------------------------------------------------------------------

record CounterfactualCoordinationCostModel : Set where
  constructor counterfactualCoordinationCostModel
  field
    retainedCost : Nat
    removedGlobalCouplingCost : Nat
    boundaryOverheadCost : Nat
    delegationOverheadCost : Nat
    unresolvedDependencyOverheadCost : Nat

open CounterfactualCoordinationCostModel public

federationOverhead : CounterfactualCoordinationCostModel → Nat
federationOverhead model =
  boundaryOverheadCost model
  + delegationOverheadCost model
  + unresolvedDependencyOverheadCost model

globalCoordinationCost : CounterfactualCoordinationCostModel → Nat
globalCoordinationCost model =
  retainedCost model + removedGlobalCouplingCost model

federatedCoordinationCost : CounterfactualCoordinationCostModel → Nat
federatedCoordinationCost model =
  retainedCost model + federationOverhead model

------------------------------------------------------------------------
-- Exact win condition.
------------------------------------------------------------------------

record RemovalPaysOverhead
  (model : CounterfactualCoordinationCostModel) : Set where
  constructor removalPaysOverhead
  field
    improvementMargin : Nat
    removedPaysOverheadWithPositiveMargin :
      removedGlobalCouplingCost model
      ≡ federationOverhead model + suc improvementMargin

open RemovalPaysOverhead public

StrictCostImprovement : CounterfactualCoordinationCostModel → Set
StrictCostImprovement model =
  Σ Nat
    (λ margin →
      globalCoordinationCost model
      ≡ federatedCoordinationCost model + suc margin)

removalPaysOverheadImpliesStrictImprovement :
  ∀ {model} →
  RemovalPaysOverhead model →
  StrictCostImprovement model
removalPaysOverheadImpliesStrictImprovement {model} witness =
  improvementMargin witness
  , trans
      (cong
        (λ removed → retainedCost model + removed)
        (removedPaysOverheadWithPositiveMargin witness))
      (sym
        (+-assoc
          (retainedCost model)
          (federationOverhead model)
          (suc (improvementMargin witness))))

record BreakEvenCostWitness
  (model : CounterfactualCoordinationCostModel) : Set where
  constructor breakEvenCostWitness
  field
    removedEqualsOverhead :
      removedGlobalCouplingCost model ≡ federationOverhead model

open BreakEvenCostWitness public

------------------------------------------------------------------------
-- Linear weighted specialization.
--
-- This is the explicit candidate formula discussed in the research programme:
--
--   α ΔE  >  β B + γ D + δ U
--
-- where ΔE is removed global coupling, B is new boundary coupling, D is new
-- delegation/reportback coupling and U is unresolved dependency overhead.
-- The weights are supplied model parameters. They are not p.m.'s numbers and
-- are not inferred from the source's population scales.
------------------------------------------------------------------------

record LinearCoordinationWeights : Set where
  constructor linearCoordinationWeights
  field
    incidenceWeight : Nat
    boundaryWeight : Nat
    delegationWeight : Nat
    unresolvedWeight : Nat

open LinearCoordinationWeights public

weightedFederationOverhead :
  LinearCoordinationWeights →
  FederationTransformationAccounting →
  Nat
weightedFederationOverhead weights accounting =
  boundaryWeight weights * newBoundaryEdges accounting
  + delegationWeight weights * newDelegationEdges accounting
  + unresolvedWeight weights * unresolvedDependencyEdges accounting

linearCostModel :
  LinearCoordinationWeights →
  FederationTransformationAccounting →
  CounterfactualCoordinationCostModel
linearCostModel weights accounting =
  counterfactualCoordinationCostModel
    (incidenceWeight weights * retainedLocalEdges accounting)
    (incidenceWeight weights * removedGlobalEdges accounting)
    (boundaryWeight weights * newBoundaryEdges accounting)
    (delegationWeight weights * newDelegationEdges accounting)
    (unresolvedWeight weights * unresolvedDependencyEdges accounting)

record LinearWinCondition
  (weights : LinearCoordinationWeights)
  (accounting : FederationTransformationAccounting) : Set where
  constructor linearWinCondition
  field
    linearImprovementMargin : Nat
    exactWeightedDominance :
      incidenceWeight weights * removedGlobalEdges accounting
      ≡ weightedFederationOverhead weights accounting
        + suc linearImprovementMargin

open LinearWinCondition public

linearWinConditionPaysOverhead :
  ∀ {weights accounting} →
  LinearWinCondition weights accounting →
  RemovalPaysOverhead (linearCostModel weights accounting)
linearWinConditionPaysOverhead condition =
  removalPaysOverhead
    (linearImprovementMargin condition)
    (exactWeightedDominance condition)

linearWinConditionImpliesStrictImprovement :
  ∀ {weights accounting} →
  LinearWinCondition weights accounting →
  StrictCostImprovement (linearCostModel weights accounting)
linearWinConditionImpliesStrictImprovement condition =
  removalPaysOverheadImpliesStrictImprovement
    (linearWinConditionPaysOverhead condition)

------------------------------------------------------------------------
-- Synthetic arithmetic examples.
------------------------------------------------------------------------

syntheticCostModel : CounterfactualCoordinationCostModel
syntheticCostModel =
  counterfactualCoordinationCostModel
    40
    60
    10
    10
    5

syntheticRemovalPaysOverhead : RemovalPaysOverhead syntheticCostModel
syntheticRemovalPaysOverhead =
  removalPaysOverhead 34 refl

syntheticStrictCostImprovement : StrictCostImprovement syntheticCostModel
syntheticStrictCostImprovement =
  removalPaysOverheadImpliesStrictImprovement syntheticRemovalPaysOverhead

syntheticAccounting : FederationTransformationAccounting
syntheticAccounting =
  federationTransformationAccounting
    100
    40
    60
    10
    10
    5
    refl

syntheticUnitWeights : LinearCoordinationWeights
syntheticUnitWeights =
  linearCoordinationWeights 1 1 1 1

syntheticLinearWinCondition :
  LinearWinCondition syntheticUnitWeights syntheticAccounting
syntheticLinearWinCondition =
  linearWinCondition 34 refl

syntheticLinearStrictImprovement :
  StrictCostImprovement
    (linearCostModel syntheticUnitWeights syntheticAccounting)
syntheticLinearStrictImprovement =
  linearWinConditionImpliesStrictImprovement syntheticLinearWinCondition

------------------------------------------------------------------------
-- Attribution / empirical-promotion firewall.
------------------------------------------------------------------------

record BoloComparisonBoundary : Set where
  constructor boloComparisonBoundary
  field
    sourceArchitectureUsedAsDesignInput : Bool
    costModelQuotedFromBoloBolo : Bool
    sourcePopulationNumbersBecomeCostCoefficients : Bool
    occupyEvidenceAutomaticallyProvesBoloSuperiority : Bool
    removedGlobalCouplingMustExceedFederationOverhead : Bool
    boundaryDelegationOverheadMustBeMeasuredOrBounded : Bool
    unresolvedDependenciesMayEraseLocalityGain : Bool
    nonlinearCoordinationCostsRemainPossible : Bool
    syntheticExampleIsEmpiricalCalibration : Bool
    empiricalBoloSuperiorityEstablished : Bool

open BoloComparisonBoundary public

canonicalBoloComparisonBoundary : BoloComparisonBoundary
canonicalBoloComparisonBoundary =
  boloComparisonBoundary
    true
    false
    false
    false
    true
    true
    true
    true
    false
    false

canonicalBoloFederationCostComparisonReceipt : GenericReceipt.GenericReceipt
canonicalBoloFederationCostComparisonReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo nested-federation counterfactual cost comparison"
    "DASHI.Governance.BoloBoloFederationCostComparisonExact"
    "removalPaysOverheadImpliesStrictImprovement / linearWinConditionImpliesStrictImprovement / canonicalBoloComparisonBoundary"
    "separates p.m.'s nested kana-bolo-tega design input from DASHI-derived counterfactual accounting, proves the abstract positive-margin federation win theorem, and specializes it to the explicit candidate inequality alpha*removed-global-coupling > beta*boundary + gamma*delegation + delta*unresolved-dependency overhead"
    "the source does not supply the cost model or weights; source population numbers are not coefficients, nonlinear costs remain possible, and empirical superiority remains unpaid until model terms and weights are independently calibrated or bounded"
    "agda -i . DASHI/Governance/BoloBoloFederationCostComparisonRegression.agda"
