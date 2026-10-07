module DASHI.Governance.BoloBoloIncidenceCompressionCostBridgeRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloIncidenceCompressionCostBridgeExact as Bridge
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison

kanaLowerRemovedPinned : Bridge.removedIncidenceEdges Bridge.kanaLowerReduction ≡ 5700
kanaLowerRemovedPinned = refl

kanaUpperRemovedPinned : Bridge.removedIncidenceEdges Bridge.kanaUpperReduction ≡ 11400
kanaUpperRemovedPinned = refl

tegaTenRemovedPinned : Bridge.removedIncidenceEdges Bridge.tegaTenReduction ≡ 45000
tegaTenRemovedPinned = refl

tegaTwentyRemovedPinned : Bridge.removedIncidenceEdges Bridge.tegaTwentyReduction ≡ 190000
tegaTwentyRemovedPinned = refl

bridgeDoesNotSetOverheadToZero :
  Bridge.federationOverheadSuppliedSeparately Bridge.canonicalCompressionCostBridgeBoundary ≡ true
bridgeDoesNotSetOverheadToZero = refl

edgeReductionNotCostReduction :
  Bridge.incidenceReductionAutomaticallyEqualsCoordinationCostReduction Bridge.canonicalCompressionCostBridgeBoundary ≡ false
edgeReductionNotCostReduction = refl
