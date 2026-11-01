module DASHI.Graph.DashifineTextGraphsBridgeTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Graph.DashifineTextGraphsBridge
open import DASHI.Graph.DashifineTextGraphsWindowMDL

------------------------------------------------------------------------
-- Exact canonical-fixture checks.

waypoint-count-smoke :
  waypointCount canonicalBridgeConformance ≡ 10
waypoint-count-smoke = waypointCountIs10 canonicalBridgeConformance

transition-count-smoke :
  transitionCount canonicalBridgeConformance ≡ 9
transition-count-smoke = transitionCountIs9 canonicalBridgeConformance

path-length-smoke :
  pathL1Length canonicalBridgeConformance ≡ 16
path-length-smoke = pathL1LengthIs16 canonicalBridgeConformance

weighted-sum-smoke :
  weightedSum canonicalBridgeConformance ≡ 41
weighted-sum-smoke = weightedSumIs41 canonicalBridgeConformance

------------------------------------------------------------------------
-- Transport parity checks.

sampleRow : BridgeRow
sampleRow = row 0 (state pos pos pos) three one

sample-r-transport :
  graphTransportedR (encodeNode sampleRow) ≡ resonance sampleRow
sample-r-transport = transportPreservesR sampleRow

sample-z-transport :
  graphTransportedZ (encodeNode sampleRow) ≡ selfNorm sampleRow
sample-z-transport = transportPreservesZ sampleRow

------------------------------------------------------------------------
-- Claim-governance checks.

transport-parity-nonpromotion-smoke :
  TransportParityPromotion → ⊥
transport-parity-nonpromotion-smoke = transportParityCannotPromote

window-selection-nonpromotion-smoke :
  WindowAwareWinnerPromotion → ⊥
window-selection-nonpromotion-smoke =
  windowAwareWinnerPromotionImpossibleHere

current-candidate-smoke :
  currentGlobalLiftCandidate ≡ ternaryL1Le2
current-candidate-smoke = currentCandidateIsTernaryL1Le2
