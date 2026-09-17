module DASHI.Wikimedia.IbrahimMonsterSSP14GlobalInversionOrbitWeldValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Wikimedia.IbrahimMonsterSSP14GlobalInversionOrbitWeldExact as W

------------------------------------------------------------------------
-- RED/GREEN validation surface for the explicit 14 <-> 14 weld.
------------------------------------------------------------------------

residualGlobalRoundTripRegression :
  (r : W.Residual14Index) →
  W.global14ToResidual14 (W.residual14ToGlobal14 r) ≡ r
residualGlobalRoundTripRegression = W.residualGlobalRoundTrip

globalResidualRoundTripRegression :
  (g : W.Ternary27GlobalInversionOrbit14) →
  W.residual14ToGlobal14 (W.global14ToResidual14 g) ≡ g
globalResidualRoundTripRegression = W.globalResidualRoundTrip

fullGlobalQuotientInvariantRegression :
  (p : W.Ternary27Point) →
  W.quotient27Global (W.negate27 p) ≡ W.quotient27Global p
fullGlobalQuotientInvariantRegression = W.quotient27GlobalNegationInvariant

naturalLiftCollisionRegression :
  W.naturalGlobalTarget W.residualMode09Negative
  ≡ W.naturalGlobalTarget W.residualMode09Positive
naturalLiftCollisionRegression = W.naturalMode09SignsCollide

explicitWeldMovesExceptionalLaneRegression :
  W.residual14ToGlobal14 W.residualMode09Positive ≡ W.globalOriginOrbit
explicitWeldMovesExceptionalLaneRegression = W.exceptionalLaneTargetsOrigin

weldPaidRegression :
  W.explicitResidual14Global14WeldPaid W.currentSSP14Global14WeldBoundary ≡ true
weldPaidRegression = W.explicitResidual14Global14WeldPaidIsTrue

canonicalLiftInducedRegression :
  W.explicitWeldIsCanonicalLiftInduced W.currentSSP14Global14WeldBoundary ≡ false
canonicalLiftInducedRegression = W.explicitWeldIsCanonicalLiftInducedIsFalse

monsterActionFirewallRegression :
  W.weldCreatesMonsterAction W.currentSSP14Global14WeldBoundary ≡ false
monsterActionFirewallRegression = W.weldCreatesMonsterActionIsFalse
