module DASHI.Physics.Closure.NSTriadKNPhysicalClassWeightEnvelopes where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (sym; subst)

import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation
import DASHI.Physics.Closure.NSTriadKNPhysicalClassEncoding as Encoding

------------------------------------------------------------------------
-- Class-specific bounds are theorems about the one canonical physical weight.
-- The amplitude/phase decomposition is not treated as a second definition.
------------------------------------------------------------------------

record PhysicalClassWeightEnvelopes
    {carrier : Allocation.TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    (geometry : Allocation.Stage3GeometricPredicates retainedPolicy)
    (derivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)) : Set₁ where
  constructor physical-class-weight-envelopes
  field
    envelope :
      Allocation.ExplicitStage3Class →
      Allocation.RetainedPhysicalTriad retainedPolicy →
      Nat

    forcedTailEnvelope :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      Allocation.explicitClass allocation
        ≡ Allocation.explicitForcedTail →
      Encoding.physicalWeight derivation τ
        ≤ envelope Allocation.explicitForcedTail τ

    transitionEnvelope :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      Allocation.explicitClass allocation
        ≡ Allocation.explicitTransition →
      Encoding.physicalWeight derivation τ
        ≤ envelope Allocation.explicitTransition τ

    adversarialEnvelope :
      (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
      (allocation : Allocation.NonResidualAllocation geometry τ) →
      Allocation.explicitClass allocation
        ≡ Allocation.explicitAdversarial →
      Encoding.physicalWeight derivation τ
        ≤ envelope Allocation.explicitAdversarial τ

open PhysicalClassWeightEnvelopes public

allocatedPhysicalWeightBound :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {derivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)} →
  (bounds : PhysicalClassWeightEnvelopes geometry derivation) →
  (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
  (allocation : Allocation.NonResidualAllocation geometry τ) →
  Encoding.physicalWeight derivation τ
    ≤ envelope bounds (Allocation.explicitClass allocation) τ
allocatedPhysicalWeightBound bounds τ allocation
  with Allocation.explicitClass allocation
... | Allocation.explicitForcedTail =
      forcedTailEnvelope bounds τ allocation refl
... | Allocation.explicitTransition =
      transitionEnvelope bounds τ allocation refl
... | Allocation.explicitAdversarial =
      adversarialEnvelope bounds τ allocation refl

encodedClassWeightBound :
  ∀ {carrier N}
    {retainedPolicy : Allocation.RetainedStatePolicy carrier N}
    {geometry : Allocation.Stage3GeometricPredicates retainedPolicy}
    {derivation :
      Encoding.PhysicalWeightDerivation
        (Allocation.RetainedPhysicalTriad retainedPolicy)} →
  (representation :
    Encoding.PhysicalStage3Representation geometry derivation) →
  (bounds : PhysicalClassWeightEnvelopes geometry derivation) →
  (τ : Allocation.RetainedPhysicalTriad retainedPolicy) →
  (allocation : Allocation.NonResidualAllocation geometry τ) →
  Encoding.abstractCodeWeight representation
    (Encoding.encode representation τ allocation)
  ≤ envelope bounds (Allocation.explicitClass allocation) τ
encodedClassWeightBound representation bounds τ allocation =
  subst
    (λ value →
      value ≤ envelope bounds (Allocation.explicitClass allocation) τ)
    (sym
      (Encoding.physicalWeightPreserved
        representation τ allocation))
    (allocatedPhysicalWeightBound bounds τ allocation)

classWeightEnvelopeTransportImplemented : Bool
classWeightEnvelopeTransportImplemented = true

classWeightEnvelopeTransportImplementedIsTrue :
  classWeightEnvelopeTransportImplemented ≡ true
classWeightEnvelopeTransportImplementedIsTrue = refl

physicalClassWeightEnvelopesInhabited : Bool
physicalClassWeightEnvelopesInhabited = false

physicalClassWeightEnvelopesInhabitedIsFalse :
  physicalClassWeightEnvelopesInhabited ≡ false
physicalClassWeightEnvelopesInhabitedIsFalse = refl
