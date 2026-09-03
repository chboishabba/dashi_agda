module DASHI.Computation.SSSPThreeFrontierStableCarrierBridgeExact where

-- Give the existing six-state three-frontier SSSP chart a stable algorithmic
-- identity.  This is an explicit carrier equivalence between the old
-- MinTailCode and the named FrontierObservationResidual6 carrier.  It is not
-- an identification with cyclic C6 or with any unrelated six-element object.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Computation.PathfindingStableCarrierIdentityExact as Stable
import DASHI.Computation.SSSPThreeFrontierBinaryTernaryFactorExact as Factor
import DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact as F3

------------------------------------------------------------------------
-- 1. Name the ternary consumer coordinate.
------------------------------------------------------------------------

tritToFrontierObservation : Trit → Stable.FrontierObservation3
tritToFrontierObservation neg = Stable.frontierNegative
tritToFrontierObservation zer = Stable.frontierNeutral
tritToFrontierObservation pos = Stable.frontierPositive

frontierObservationToTrit : Stable.FrontierObservation3 → Trit
frontierObservationToTrit Stable.frontierNegative = neg
frontierObservationToTrit Stable.frontierNeutral = zer
frontierObservationToTrit Stable.frontierPositive = pos

tritObservationRoundTrip :
  (t : Trit) → frontierObservationToTrit (tritToFrontierObservation t) ≡ t
tritObservationRoundTrip neg = refl
tritObservationRoundTrip zer = refl
tritObservationRoundTrip pos = refl

observationTritRoundTrip :
  (o : Stable.FrontierObservation3) →
  tritToFrontierObservation (frontierObservationToTrit o) ≡ o
observationTritRoundTrip Stable.frontierNegative = refl
observationTritRoundTrip Stable.frontierNeutral = refl
observationTritRoundTrip Stable.frontierPositive = refl

------------------------------------------------------------------------
-- 2. Name the binary residual coordinate.
------------------------------------------------------------------------

tailToStableResidual : Factor.TailBit → Stable.BFSWithinLayerOrder2
tailToStableResidual Factor.forwardTail = Stable.bfsLeftThenRight
tailToStableResidual Factor.reverseTail = Stable.bfsRightThenLeft

stableResidualToTail : Stable.BFSWithinLayerOrder2 → Factor.TailBit
stableResidualToTail Stable.bfsLeftThenRight = Factor.forwardTail
stableResidualToTail Stable.bfsRightThenLeft = Factor.reverseTail

tailResidualRoundTrip :
  (t : Factor.TailBit) → stableResidualToTail (tailToStableResidual t) ≡ t
tailResidualRoundTrip Factor.forwardTail = refl
tailResidualRoundTrip Factor.reverseTail = refl

residualTailRoundTrip :
  (r : Stable.BFSWithinLayerOrder2) →
  tailToStableResidual (stableResidualToTail r) ≡ r
residualTailRoundTrip Stable.bfsLeftThenRight = refl
residualTailRoundTrip Stable.bfsRightThenLeft = refl

------------------------------------------------------------------------
-- 3. Old factor chart <-> stable named carrier.
------------------------------------------------------------------------

factorToStable : Factor.MinTailCode → Stable.FrontierObservationResidual6
factorToStable (Factor.minTailCode minimum tail) =
  Stable.frontierObservationResidual6
    (tritToFrontierObservation minimum)
    (tailToStableResidual tail)

stableToFactor : Stable.FrontierObservationResidual6 → Factor.MinTailCode
stableToFactor (Stable.frontierObservationResidual6 observation residual) =
  Factor.minTailCode
    (frontierObservationToTrit observation)
    (stableResidualToTail residual)

factorStableFromTo :
  (x : Factor.MinTailCode) → stableToFactor (factorToStable x) ≡ x
factorStableFromTo (Factor.minTailCode neg Factor.forwardTail) = refl
factorStableFromTo (Factor.minTailCode neg Factor.reverseTail) = refl
factorStableFromTo (Factor.minTailCode zer Factor.forwardTail) = refl
factorStableFromTo (Factor.minTailCode zer Factor.reverseTail) = refl
factorStableFromTo (Factor.minTailCode pos Factor.forwardTail) = refl
factorStableFromTo (Factor.minTailCode pos Factor.reverseTail) = refl

factorStableToFrom :
  (x : Stable.FrontierObservationResidual6) →
  factorToStable (stableToFactor x) ≡ x
factorStableToFrom
  (Stable.frontierObservationResidual6 Stable.frontierNegative Stable.bfsLeftThenRight) = refl
factorStableToFrom
  (Stable.frontierObservationResidual6 Stable.frontierNegative Stable.bfsRightThenLeft) = refl
factorStableToFrom
  (Stable.frontierObservationResidual6 Stable.frontierNeutral Stable.bfsLeftThenRight) = refl
factorStableToFrom
  (Stable.frontierObservationResidual6 Stable.frontierNeutral Stable.bfsRightThenLeft) = refl
factorStableToFrom
  (Stable.frontierObservationResidual6 Stable.frontierPositive Stable.bfsLeftThenRight) = refl
factorStableToFrom
  (Stable.frontierObservationResidual6 Stable.frontierPositive Stable.bfsRightThenLeft) = refl

threeFrontierFactorHasStableIdentity :
  Stable.CarrierIso Factor.MinTailCode Stable.FrontierObservationResidual6
threeFrontierFactorHasStableIdentity =
  Stable.carrierIso
    factorToStable
    stableToFactor
    factorStableFromTo
    factorStableToFrom

------------------------------------------------------------------------
-- 4. Original six linear orders also inherit the stable identity by explicit
--    composition through the existing encode/decode chart.
------------------------------------------------------------------------

linearOrderToStable : F3.LinearOrder3 → Stable.FrontierObservationResidual6
linearOrderToStable order = factorToStable (Factor.encodeOrder order)

stableToLinearOrder : Stable.FrontierObservationResidual6 → F3.LinearOrder3
stableToLinearOrder state = Factor.decodeOrder (stableToFactor state)

linearStableFromTo :
  (order : F3.LinearOrder3) →
  stableToLinearOrder (linearOrderToStable order) ≡ order
linearStableFromTo order rewrite Factor.orderRoundTrip order = refl

linearStableToFrom :
  (state : Stable.FrontierObservationResidual6) →
  linearOrderToStable (stableToLinearOrder state) ≡ state
linearStableToFrom state
  rewrite Factor.codeRoundTrip (stableToFactor state)
        | factorStableToFrom state = refl

threeFrontierLinearOrdersHaveStableIdentity :
  Stable.CarrierIso F3.LinearOrder3 Stable.FrontierObservationResidual6
threeFrontierLinearOrdersHaveStableIdentity =
  Stable.carrierIso
    linearOrderToStable
    stableToLinearOrder
    linearStableFromTo
    linearStableToFrom

record ThreeFrontierStableCarrierBoundary : Set where
  constructor threeFrontierStableCarrierBoundary
  field
    stableAlgorithmicIdentityConstructed : Bool
    stableAlgorithmicIdentityConstructedIsTrue :
      stableAlgorithmicIdentityConstructed ≡ true
    cardinalSixUsedAsIdentity : Bool
    cardinalSixUsedAsIdentityIsFalse : cardinalSixUsedAsIdentity ≡ false
    cyclicC6IdentificationClaimed : Bool
    cyclicC6IdentificationClaimedIsFalse : cyclicC6IdentificationClaimed ≡ false

canonicalThreeFrontierStableCarrierBoundary : ThreeFrontierStableCarrierBoundary
canonicalThreeFrontierStableCarrierBoundary =
  threeFrontierStableCarrierBoundary true refl false refl false refl
