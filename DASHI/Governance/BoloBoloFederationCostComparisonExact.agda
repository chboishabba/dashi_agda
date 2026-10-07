module DASHI.Governance.BoloBoloFederationCostComparisonExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloPrimarySourceAtlasExact as Bolo

------------------------------------------------------------------------
-- BOLO'BOLO COUNTERFACTUAL FEDERATION COMPARISON.
--
-- p.m.'s source supplies the nested kana / bolo / tega design vocabulary,
-- approximate design scales, bottom-up confederal orientation and warning
-- against automatic transition success.  Every cost model below is DASHI-
-- derived analytical machinery, not quoted from bolo'bolo.
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

record FederationTransformationAccounting : Set where
  constructor federationTransformationAccounting
  field
    globalCouplingEdges : Nat
    retainedLocalEdges : Nat
    removedGlobalEdges : Nat
    newBoundaryEdges : Nat
    newDelegationEdges : Nat
    unresolvedDependencyEdges : Nat
    exactGlobalPartition : globalCouplingEdges ≡ retainedLocalEdges + removedGlobalEdges
open FederationTransformationAccounting public

newFederationInterfaceEdges : FederationTransformationAccounting → Nat
newFederationInterfaceEdges accounting =
  newBoundaryEdges accounting + newDelegationEdges accounting + unresolvedDependencyEdges accounting

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
  boundaryOverheadCost model + delegationOverheadCost model + unresolvedDependencyOverheadCost model

globalCoordinationCost : CounterfactualCoordinationCostModel → Nat
globalCoordinationCost model = retainedCost model + removedGlobalCouplingCost model

federatedCoordinationCost : CounterfactualCoordinationCostModel → Nat
federatedCoordinationCost model = retainedCost model + federationOverhead model

record RemovalPaysOverhead (model : CounterfactualCoordinationCostModel) : Set where
  constructor removalPaysOverhead
  field
    improvementMargin : Nat
    removedPaysOverheadWithPositiveMargin :
      removedGlobalCouplingCost model ≡ federationOverhead model + suc improvementMargin
open RemovalPaysOverhead public

StrictCostImprovement : CounterfactualCoordinationCostModel → Set
StrictCostImprovement model =
  Σ Nat (λ margin → globalCoordinationCost model ≡ federatedCoordinationCost model + suc margin)

removalPaysOverheadImpliesStrictImprovement :
  ∀ {model} → RemovalPaysOverhead model → StrictCostImprovement model
removalPaysOverheadImpliesStrictImprovement {model} witness =
  improvementMargin witness
  , trans
      (cong (λ removed → retainedCost model + removed)
        (removedPaysOverheadWithPositiveMargin witness))
      (sym (+-assoc (retainedCost model) (federationOverhead model)
        (suc (improvementMargin witness))))

record BreakEvenCostWitness (model : CounterfactualCoordinationCostModel) : Set where
  constructor breakEvenCostWitness
  field removedEqualsOverhead : removedGlobalCouplingCost model ≡ federationOverhead model
open BreakEvenCostWitness public

------------------------------------------------------------------------
-- Linear specialization: α ΔE > β B + γ D + δ U.
------------------------------------------------------------------------

record LinearCoordinationWeights : Set where
  constructor linearCoordinationWeights
  field
    incidenceWeight : Nat
    boundaryWeight : Nat
    delegationWeight : Nat
    unresolvedWeight : Nat
open LinearCoordinationWeights public

weightedFederationOverhead : LinearCoordinationWeights → FederationTransformationAccounting → Nat
weightedFederationOverhead weights accounting =
  boundaryWeight weights * newBoundaryEdges accounting
  + delegationWeight weights * newDelegationEdges accounting
  + unresolvedWeight weights * unresolvedDependencyEdges accounting

linearCostModel : LinearCoordinationWeights → FederationTransformationAccounting → CounterfactualCoordinationCostModel
linearCostModel weights accounting =
  counterfactualCoordinationCostModel
    (incidenceWeight weights * retainedLocalEdges accounting)
    (incidenceWeight weights * removedGlobalEdges accounting)
    (boundaryWeight weights * newBoundaryEdges accounting)
    (delegationWeight weights * newDelegationEdges accounting)
    (unresolvedWeight weights * unresolvedDependencyEdges accounting)

record LinearWinCondition (weights : LinearCoordinationWeights)
  (accounting : FederationTransformationAccounting) : Set where
  constructor linearWinCondition
  field
    linearImprovementMargin : Nat
    exactWeightedDominance :
      incidenceWeight weights * removedGlobalEdges accounting
      ≡ weightedFederationOverhead weights accounting + suc linearImprovementMargin
open LinearWinCondition public

linearWinConditionPaysOverhead :
  ∀ {weights accounting} → LinearWinCondition weights accounting →
  RemovalPaysOverhead (linearCostModel weights accounting)
linearWinConditionPaysOverhead condition =
  removalPaysOverhead (linearImprovementMargin condition) (exactWeightedDominance condition)

linearWinConditionImpliesStrictImprovement :
  ∀ {weights accounting} → LinearWinCondition weights accounting →
  StrictCostImprovement (linearCostModel weights accounting)
linearWinConditionImpliesStrictImprovement condition =
  removalPaysOverheadImpliesStrictImprovement (linearWinConditionPaysOverhead condition)

------------------------------------------------------------------------
-- Multi-level bolo/kana/tega specialization.
--
-- This keeps the nested interface terms separately observable instead of
-- folding all federation overhead into one boundary scalar.
------------------------------------------------------------------------

record NestedBoloCostComponents : Set where
  constructor nestedBoloCostComponents
  field
    kanaLocalRetainedCost : Nat
    removedGlobalCost : Nat
    boloInterfaceCost : Nat
    tegaInterfaceCost : Nat
    widerInterfaceCost : Nat
    nestedDelegationCost : Nat
    nestedUnresolvedDependencyCost : Nat
open NestedBoloCostComponents public

nestedFederationOverhead : NestedBoloCostComponents → Nat
nestedFederationOverhead components =
  boloInterfaceCost components
  + tegaInterfaceCost components
  + widerInterfaceCost components
  + nestedDelegationCost components
  + nestedUnresolvedDependencyCost components

nestedBoloCostModel : NestedBoloCostComponents → CounterfactualCoordinationCostModel
nestedBoloCostModel components =
  counterfactualCoordinationCostModel
    (kanaLocalRetainedCost components)
    (removedGlobalCost components)
    (boloInterfaceCost components + tegaInterfaceCost components + widerInterfaceCost components)
    (nestedDelegationCost components)
    (nestedUnresolvedDependencyCost components)

record NestedBoloWinCondition (components : NestedBoloCostComponents) : Set where
  constructor nestedBoloWinCondition
  field
    nestedImprovementMargin : Nat
    exactNestedDominance :
      removedGlobalCost components
      ≡ nestedFederationOverhead components + suc nestedImprovementMargin
open NestedBoloWinCondition public

nestedWinConditionPaysOverhead :
  ∀ {components} → NestedBoloWinCondition components →
  RemovalPaysOverhead (nestedBoloCostModel components)
nestedWinConditionPaysOverhead condition =
  removalPaysOverhead (nestedImprovementMargin condition) (exactNestedDominance condition)

nestedBoloWinConditionImpliesStrictImprovement :
  ∀ {components} → NestedBoloWinCondition components →
  StrictCostImprovement (nestedBoloCostModel components)
nestedBoloWinConditionImpliesStrictImprovement condition =
  removalPaysOverheadImpliesStrictImprovement (nestedWinConditionPaysOverhead condition)

------------------------------------------------------------------------
-- Synthetic arithmetic examples only; no empirical calibration.
------------------------------------------------------------------------

syntheticCostModel : CounterfactualCoordinationCostModel
syntheticCostModel = counterfactualCoordinationCostModel 40 60 10 10 5

syntheticRemovalPaysOverhead : RemovalPaysOverhead syntheticCostModel
syntheticRemovalPaysOverhead = removalPaysOverhead 34 refl

syntheticStrictCostImprovement : StrictCostImprovement syntheticCostModel
syntheticStrictCostImprovement = removalPaysOverheadImpliesStrictImprovement syntheticRemovalPaysOverhead

syntheticAccounting : FederationTransformationAccounting
syntheticAccounting = federationTransformationAccounting 100 40 60 10 10 5 refl

syntheticUnitWeights : LinearCoordinationWeights
syntheticUnitWeights = linearCoordinationWeights 1 1 1 1

syntheticLinearWinCondition : LinearWinCondition syntheticUnitWeights syntheticAccounting
syntheticLinearWinCondition = linearWinCondition 34 refl

syntheticLinearStrictImprovement :
  StrictCostImprovement (linearCostModel syntheticUnitWeights syntheticAccounting)
syntheticLinearStrictImprovement =
  linearWinConditionImpliesStrictImprovement syntheticLinearWinCondition

syntheticNestedComponents : NestedBoloCostComponents
syntheticNestedComponents = nestedBoloCostComponents 40 60 5 5 5 5 5

syntheticNestedWinCondition : NestedBoloWinCondition syntheticNestedComponents
syntheticNestedWinCondition = nestedBoloWinCondition 34 refl

syntheticNestedStrictImprovement : StrictCostImprovement (nestedBoloCostModel syntheticNestedComponents)
syntheticNestedStrictImprovement =
  nestedBoloWinConditionImpliesStrictImprovement syntheticNestedWinCondition

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
  boloComparisonBoundary true false false false true true true true false false

canonicalBoloFederationCostComparisonReceipt : GenericReceipt.GenericReceipt
canonicalBoloFederationCostComparisonReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo nested-federation counterfactual cost comparison"
    "DASHI.Governance.BoloBoloFederationCostComparisonExact"
    "abstract, linear and nested positive-margin win theorems / canonicalBoloComparisonBoundary"
    "separates p.m.'s nested kana-bolo-tega design input from DASHI-derived counterfactual accounting, proves the abstract positive-margin federation win theorem, specializes it to alpha*removed-global-coupling > beta*boundary + gamma*delegation + delta*unresolved overhead, and exposes bolo-, tega- and wider-interface costs separately in a nested specialization"
    "the source does not supply cost weights or coefficients; source population numbers are not coefficients, nonlinear costs remain possible, and empirical superiority remains unpaid until model terms are independently calibrated or bounded"
    "agda -i . DASHI/Governance/BoloBoloFederationCostComparisonRegression.agda"
