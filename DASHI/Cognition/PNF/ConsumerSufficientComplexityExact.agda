module DASHI.Cognition.PNF.ConsumerSufficientComplexityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Cognition.PNF.ComplexityArithmetic
  using (_+ᶜ_; _≤ᶜ_; ≤ᶜ-trans)

------------------------------------------------------------------------
-- Exact Kolmogorov complexity is uncomputable.  This module therefore does
-- not name any quantity K.  It formalizes the executable optimization boundary
-- used by ITIR/PNF: a concrete operational carrier may be replaced by a cheaper
-- one only when the consumer observation, residual and provenance projections
-- are all unchanged.
------------------------------------------------------------------------

record OperationalCarrierCost : Set where
  constructor operationalCost
  field
    nodes : Nat
    edges : Nat
    residuals : Nat
    encodedUnits : Nat
    boundaryDemands : Nat

open OperationalCarrierCost public

operationalDescriptionCost : OperationalCarrierCost → Nat
operationalDescriptionCost cost =
  nodes cost +ᶜ
  (edges cost +ᶜ
  (residuals cost +ᶜ
  (encodedUnits cost +ᶜ boundaryDemands cost)))

≡-trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

record ConsumerSafeCompression
  {Carrier Observation Residual Provenance : Set}
  (cost : Carrier → OperationalCarrierCost)
  (observe : Carrier → Observation)
  (residual : Carrier → Residual)
  (provenance : Carrier → Provenance)
  (source target : Carrier)
  : Set where
  field
    sameConsumerObservation : observe source ≡ observe target
    sameResidual : residual source ≡ residual target
    sameProvenance : provenance source ≡ provenance target
    nonIncreasingDescription :
      operationalDescriptionCost (cost target)
      ≤ᶜ operationalDescriptionCost (cost source)

open ConsumerSafeCompression public

composeConsumerSafeCompression :
  ∀ {Carrier Observation Residual Provenance : Set}
    {cost : Carrier → OperationalCarrierCost}
    {observe : Carrier → Observation}
    {residual : Carrier → Residual}
    {provenance : Carrier → Provenance}
    {x y z : Carrier} →
  ConsumerSafeCompression cost observe residual provenance x y →
  ConsumerSafeCompression cost observe residual provenance y z →
  ConsumerSafeCompression cost observe residual provenance x z
composeConsumerSafeCompression xy yz = record
  { sameConsumerObservation =
      ≡-trans
        (sameConsumerObservation xy)
        (sameConsumerObservation yz)
  ; sameResidual = ≡-trans (sameResidual xy) (sameResidual yz)
  ; sameProvenance = ≡-trans (sameProvenance xy) (sameProvenance yz)
  ; nonIncreasingDescription =
      ≤ᶜ-trans
        (nonIncreasingDescription yz)
        (nonIncreasingDescription xy)
  }

------------------------------------------------------------------------
-- Transition work has a separate sufficient carrier.  A compact state does
-- not imply a cheap transition if the implementation repeatedly scans inactive
-- structure.  This certificate makes the desired physical bound explicit.
------------------------------------------------------------------------

record FrontierBoundedTransition : Set where
  constructor frontierBound
  field
    activeFrontier : Nat
    touchedEdges : Nat
    measuredWork : Nat
    workBound : measuredWork ≤ᶜ (activeFrontier +ᶜ touchedEdges)

open FrontierBoundedTransition public
