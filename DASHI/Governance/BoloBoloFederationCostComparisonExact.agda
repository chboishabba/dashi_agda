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
--
-- The transformation asks what happens when some participation coupling that
-- would otherwise be paid at the global layer is retained locally while a
-- smaller interface/delegation surface is introduced at federation layers.
-- Counts are externally audited coordinates, not source-authored numbers.
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
--
-- These are already-costed coordinates.  No claim is made here that one edge
-- has unit cost, that cost is linear in edge count, or that the components are
-- empirically identified.  That is deliberately left to the calibration lane.
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
--
-- `RemovalPaysOverhead` is the sharp finite-Nat condition that the cost removed
-- from the global layer exceeds all newly introduced federation overhead by a
-- positive margin.  The theorem transports that local condition into a strict
-- whole-system comparison.
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

------------------------------------------------------------------------
-- Converse diagnostic: if the federation overhead is exactly the removed
-- global cost, the model has no positive improvement margin to expose here.
-- This is a boundary classification rather than an impossibility theorem for
-- richer/nonlinear models.
------------------------------------------------------------------------

record BreakEvenCostWitness
  (model : CounterfactualCoordinationCostModel) : Set where
  constructor breakEvenCostWitness
  field
    removedEqualsOverhead :
      removedGlobalCouplingCost model ≡ federationOverhead model

open BreakEvenCostWitness public

------------------------------------------------------------------------
-- Synthetic arithmetic example.
--
-- This example tests the theorem surface only.  It is not fitted to Occupy,
-- bolo'bolo, or any empirical social system.
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
    "removalPaysOverheadImpliesStrictImprovement / canonicalBoloComparisonBoundary"
    "separates p.m.'s nested kana-bolo-tega design input from a DASHI-derived counterfactual cost decomposition and proves that removing global-coupling cost yields a strict whole-system improvement whenever it exceeds newly introduced boundary, delegation and unresolved-dependency overhead by a positive margin"
    "the source does not supply the cost model or coefficients; Occupy does not automatically validate bolo'bolo, nonlinear costs remain possible, and empirical superiority remains unpaid until the model terms are independently calibrated/identified"
    "agda -i . DASHI/Governance/BoloBoloFederationCostComparisonRegression.agda"
