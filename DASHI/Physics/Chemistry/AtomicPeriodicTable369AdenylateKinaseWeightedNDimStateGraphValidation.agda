module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as G

------------------------------------------------------------------------
-- RED/GREEN validation root for the first weighted NDim AdK state graph.
-- State identity, graph edges, pathway flux, free-energy coordinates and
-- promotion status remain separate proof obligations.
------------------------------------------------------------------------

stateRegression :
  G.AdKWeightedGraphBoundary.sixEquationStatesRetained
    G.canonicalAdKWeightedGraphBoundary
  ≡ true
  × G.AdKWeightedGraphBoundary.primaryAndAlternativeRoutesRetained
    G.canonicalAdKWeightedGraphBoundary
  ≡ true
stateRegression = refl , refl

weightRegression :
  G.primaryPathFluxNumerator G.canonicalPathWeight ≡ 57
  × G.primaryPathFluxDenominator G.canonicalPathWeight ≡ 10
  × G.AdKWeightedGraphBoundary.pathFluxWeightSourcePaid
    G.canonicalAdKWeightedGraphBoundary
  ≡ true
weightRegression = refl , refl , refl

freeEnergyRegression :
  G.gammaReferenceFreeEnergyTenthsKcal G.canonicalFreeEnergyReceipt ≡ 0
  × G.AdKWeightedGraphBoundary.twoAngleFreeEnergySurfaceSourcePaid
    G.canonicalAdKWeightedGraphBoundary
  ≡ true
  × G.AdKWeightedGraphBoundary.numericPerEdgeRatesFullyTranscribed
    G.canonicalAdKWeightedGraphBoundary
  ≡ false
freeEnergyRegression = refl , refl , refl

identityFirewallRegression :
  G.AdKWeightedGraphBoundary.figureZetaAndEquationXiSilentlyIdentified
    G.canonicalAdKWeightedGraphBoundary
  ≡ false
  × G.AdKWeightedGraphBoundary.weightedGraphProvesEquilibriumDistribution
    G.canonicalAdKWeightedGraphBoundary
  ≡ false
  × G.AdKWeightedGraphBoundary.weightedGraphProvesExperimentalMechanism
    G.canonicalAdKWeightedGraphBoundary
  ≡ false
identityFirewallRegression = refl , refl , refl
