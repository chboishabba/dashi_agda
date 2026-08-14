module DASHI.Crypto.CryptoRepresentationParetoExact where

------------------------------------------------------------------------
-- RATE / TRANSITION / REOPENING PARETO GEOMETRY
--
-- A scalar MDL/rate objective does not determine the geometry of an equally
-- short representation.  Blue-team representation selection therefore carries
-- rate, transition/update cost, reopening cost, and optional physical-observation
-- cost separately.  No universal scalar weighting is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_ ; z≤n; s≤s)
open import Data.Product using (_×_; _,_)

record RepresentationObjective : Set where
  constructor representationObjective
  field
    rateBits : Nat
    transitionCost : Nat
    reopenCost : Nat
    observationCost : Nat

open RepresentationObjective public

record WeaklyDominates
    (left right : RepresentationObjective) : Set where
  constructor weaklyDominates
  field
    rateNoWorse : rateBits left ≤ rateBits right
    transitionNoWorse : transitionCost left ≤ transitionCost right
    reopenNoWorse : reopenCost left ≤ reopenCost right
    observationNoWorse : observationCost left ≤ observationCost right

open WeaklyDominates public

------------------------------------------------------------------------
-- Wave4 / two-bit regression carried into crypto representation selection.
------------------------------------------------------------------------

binaryObjective : RepresentationObjective
binaryObjective = representationObjective 2 4 1 2

grayObjective : RepresentationObjective
grayObjective = representationObjective 2 3 1 2

grayWeaklyDominatesBinary : WeaklyDominates grayObjective binaryObjective
grayWeaklyDominatesBinary =
  weaklyDominates
    (s≤s (s≤s z≤n))
    (s≤s (s≤s (s≤s z≤n)))
    (s≤s z≤n)
    (s≤s (s≤s z≤n))

equalRate : rateBits grayObjective ≡ rateBits binaryObjective
equalRate = refl

grayTransitionStrictlyBetter : transitionCost grayObjective < transitionCost binaryObjective
grayTransitionStrictlyBetter = s≤s (s≤s (s≤s (s≤s z≤n)))

minimumRateDoesNotChooseUniqueGeometry :
  rateBits grayObjective ≡ rateBits binaryObjective
  × transitionCost grayObjective ≡ 3
  × transitionCost binaryObjective ≡ 4
minimumRateDoesNotChooseUniqueGeometry = refl , (refl , refl)

------------------------------------------------------------------------
-- Boundary: a Pareto carrier keeps tradeoffs explicit.  Choosing scalar
-- weights is an application/policy decision, not a theorem of the codec.
------------------------------------------------------------------------

data ObjectiveSelectionPolicy : Set where
  applicationSuppliedWeightsOrPareto : ObjectiveSelectionPolicy
