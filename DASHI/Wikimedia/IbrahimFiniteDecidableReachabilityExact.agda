module DASHI.Wikimedia.IbrahimFiniteDecidableReachabilityExact where

open import DASHI.Core.Prelude
import Data.Fin.Properties as FinP
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Wikimedia.IbrahimFinitePigeonholeProducerExact as Pigeonhole
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General
import DASHI.Wikimedia.IbrahimCycleRotationRelationExact as Rotation

------------------------------------------------------------------------
-- M2 / New DASHI constructive finite reachability decision layer.
-- Original Wikipedia First Link Network attribution: Ibrahim, Danforth
-- and Dodds, DOI 10.1016/j.jocs.2016.12.001.
--
-- This proof does NOT assume that the Node type has a decidable
-- equality. Instead the already kernel-accepted finite carrier
-- provides an injective index into Fin N, where stdlib equality is
-- decidable. The bound below is explicit: bounded reachability is
-- weaker than a complete unbounded two-way cycle-membership decision.
------------------------------------------------------------------------

finiteNodeEqualityFromCarrier :
  ∀ {Node : Set}
    (carrier : General.CompleteFiniteCarrier Node)
    (a b : Node) →
  (a ≡ b) ⊎ (a ≡ b → ⊥)
finiteNodeEqualityFromCarrier carrier a b
  with FinP._≟_
    (Pigeonhole.carrierEncode carrier a)
    (Pigeonhole.carrierEncode carrier b)
... | yes same =
  inj₁ (Pigeonhole.encodedEqualityReflectsOriginal carrier same)
... | no unequal =
  inj₂ (λ equal →
    unequal (cong (Pigeonhole.carrierEncode carrier) equal))

data ReachWithin {Node : Set}
    (next : Node → Node) (target : Node) :
    Nat → Node → Set where
  reachNow : ∀ {fuel start} →
    start ≡ target → ReachWithin next target fuel start
  reachLater : ∀ {fuel start} →
    ReachWithin next target fuel (next start) →
    ReachWithin next target (suc fuel) start

decideReachWithin :
  ∀ {Node : Set}
    (carrier : General.CompleteFiniteCarrier Node)
    (next : Node → Node)
    (target : Node) →
  (fuel : Nat) (start : Node) →
  ReachWithin next target fuel start ⊎
  (ReachWithin next target fuel start → ⊥)
decideReachWithin carrier next target zero start
  with finiteNodeEqualityFromCarrier carrier start target
... | inj₁ same = inj₁ (reachNow same)
... | inj₂ notEqual =
  inj₂ (λ { (reachNow same) → notEqual same })
decideReachWithin carrier next target (suc fuel) start
  with finiteNodeEqualityFromCarrier carrier start target
... | inj₁ same = inj₁ (reachNow same)
... | inj₂ notEqual
  with decideReachWithin carrier next target fuel (next start)
...   | inj₁ path = inj₁ (reachLater path)
...   | inj₂ noPath =
  inj₂ (λ { (reachNow same) → notEqual same
           ; (reachLater tail) → noPath tail })

boundedPathImpliesForwardRotation :
  ∀ {Node : Set} {next : Node → Node}
    {fuel : Nat} {start target : Node} →
  ReachWithin next target fuel start →
  Rotation.ForwardRotation next start target
boundedPathImpliesForwardRotation (reachNow same) =
  Rotation.forwardRotation zero same
boundedPathImpliesForwardRotation (reachLater tail)
  with boundedPathImpliesForwardRotation tail
... | Rotation.forwardRotation k path =
  Rotation.forwardRotation (suc k) path

record BoundedMutualRotation {Node : Set}
    (next : Node → Node)
    (fuel : Nat) (a b : Node) : Set where
  constructor boundedMutualRotation
  field
    toward : ReachWithin next b fuel a
    return : ReachWithin next a fuel b
open BoundedMutualRotation public

decideBoundedMutualRotation :
  ∀ {Node : Set}
    (carrier : General.CompleteFiniteCarrier Node)
    (next : Node → Node) →
  (fuel : Nat) (a b : Node) →
  BoundedMutualRotation next fuel a b ⊎
  (BoundedMutualRotation next fuel a b → ⊥)
decideBoundedMutualRotation carrier next fuel a b
  with decideReachWithin carrier next b fuel a
... | inj₂ noToward =
  inj₂ (λ pair → noToward (toward pair))
... | inj₁ yesToward
  with decideReachWithin carrier next a fuel b
...   | inj₁ yesReturn =
  inj₁ (boundedMutualRotation yesToward yesReturn)
...   | inj₂ noReturn =
  inj₂ (λ pair → noReturn (return pair))

boundedMutualRotationIsSound :
  ∀ {Node : Set} {next : Node → Node}
    {fuel : Nat} {a b : Node} →
  BoundedMutualRotation next fuel a b →
  Rotation.MutualOrbitRotation next a b
boundedMutualRotationIsSound pair =
  Rotation.mutualOrbitRotation
    (boundedPathImpliesForwardRotation (toward pair))
    (boundedPathImpliesForwardRotation (return pair))

-- M2 open remainder: prove that chosen fuel is COMPLETE for every
-- mutual rotation in a finite total graph (bounded ≤|allNodes| search),
-- not merely that a successful bounded witness is sound. Do not infer
-- this from a name equality or from a downloaded Wiki page title.
