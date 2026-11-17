module DASHI.Mathematics.Topology.AlexanderHornedSpinVOAFactorFunctorExact where

------------------------------------------------------------------------
-- 360 -> 180: A STRICT SAME-STATE FINITE VOA REFINEMENT.
--
-- Let D=2I and E=A5 with p:D->E surjective group morphism.
-- Existing actor: Omega_D=C3 x D, Omega_E=C3 x E.
-- Existing commutative rational vertex mode lives pointwise on
-- (Omega -> Q), not on a merely isomorphic replacement object.
--
-- Pullback f |-> f o (id_C3 x p) embeds the 180-dimensional
-- A5-coordinate VOA in the 360-dimensional 2I-coordinate VOA.
-- It preserves ALL vertex modes and intertwines
-- (D^3 rtimes C3) -> (E^3 rtimes C3).
--
-- This is a rigorous functor for any ACTUAL surjective factor
-- group map, with all its equality laws supplied as proofs.
-- The literal finite 2I->A5 group map is exhaustively constructed
-- in scripts/alexander_horned_spin_icosahedral_bridge.py,
-- but is NOT yet an Agda 120-element factor instance.
--
-- No inference of Monster 3B identity or true geometric pi1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteVOAActorExact as Actor
import DASHI.Mathematics.Topology.AlexanderHornedC3VOAModeLiftExact as Mode
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Triple
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3

record SurjectiveFiniteFactorMap : Set₂ where
  field
    Source : Actor.ActorFactorGroup
    Target : Actor.ActorFactorGroup

    factor : Actor.Carrier Source → Actor.Carrier Target
    factorUnit :
      factor (Actor.unit Source) ≡ Actor.unit Target
    factorProduct : ∀ a b →
      factor (Actor.multiply Source a b)
        ≡ Actor.multiply Target (factor a) (factor b)

    preimage : (b : Actor.Carrier Target) →
      Σ (Actor.Carrier Source) (λ a → factor a ≡ b)

open SurjectiveFiniteFactorMap public

factorTriple : (P : SurjectiveFiniteFactorMap) →
  Triple.Triple (Actor.Carrier (Source P)) →
  Triple.Triple (Actor.Carrier (Target P))
factorTriple P (Triple.xyz a b c) =
  Triple.xyz (factor P a) (factor P b) (factor P c)

factorActor : (P : SurjectiveFiniteFactorMap) →
  Actor.Actor (Source P) → Actor.Actor (Target P)
factorActor P (Actor.actor q phase) =
  Actor.actor (factorTriple P q) phase

factorSlot : (P : SurjectiveFiniteFactorMap) →
  Actor.Slot (Source P) → Actor.Slot (Target P)
factorSlot P (Actor.slot sector a) =
  Actor.slot sector (factor P a)

-- There are 3 x 3=9 phase/sector cases. In each case the
-- statement is exactly multiplication preservation.
factorActorCoordinateNaturality :
  (P : SurjectiveFiniteFactorMap) →
  ∀ g x →
  factorSlot P (Actor.coordinateAction (Source P) g x)
  ≡ Actor.coordinateAction (Target P)
      (factorActor P g) (factorSlot P x)
factorActorCoordinateNaturality P (Actor.actor q C3.c0) (Actor.slot C3.c0 a) =
  cong (Actor.slot C3.c0) (factorProduct P (Actor.at (Source P) q C3.c0) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c0) (Actor.slot C3.c1 a) =
  cong (Actor.slot C3.c1) (factorProduct P (Actor.at (Source P) q C3.c1) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c0) (Actor.slot C3.c2 a) =
  cong (Actor.slot C3.c2) (factorProduct P (Actor.at (Source P) q C3.c2) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c1) (Actor.slot C3.c0 a) =
  cong (Actor.slot C3.c1) (factorProduct P (Actor.at (Source P) q C3.c1) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c1) (Actor.slot C3.c1 a) =
  cong (Actor.slot C3.c2) (factorProduct P (Actor.at (Source P) q C3.c2) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c1) (Actor.slot C3.c2 a) =
  cong (Actor.slot C3.c0) (factorProduct P (Actor.at (Source P) q C3.c0) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c2) (Actor.slot C3.c0 a) =
  cong (Actor.slot C3.c2) (factorProduct P (Actor.at (Source P) q C3.c2) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c2) (Actor.slot C3.c1 a) =
  cong (Actor.slot C3.c0) (factorProduct P (Actor.at (Source P) q C3.c0) a)
factorActorCoordinateNaturality P (Actor.actor q C3.c2) (Actor.slot C3.c2 a) =
  cong (Actor.slot C3.c1) (factorProduct P (Actor.at (Source P) q C3.c1) a)

pullbackRationalState :
  (P : SurjectiveFiniteFactorMap) →
  Mode.RationalState (Target P) → Mode.RationalState (Source P)
pullbackRationalState P f x = f (factorSlot P x)

pullbackPreservesEveryVertexMode :
  (P : SurjectiveFiniteFactorMap) →
  ∀ f g n x →
  pullbackRationalState P (Mode.vertexMode (Target P) f n g) x
    ≡ Mode.vertexMode (Source P)
         (pullbackRationalState P f) n
         (pullbackRationalState P g) x
pullbackPreservesEveryVertexMode P f g n x = refl

pullbackIntertwinesActorAction :
  (P : SurjectiveFiniteFactorMap) →
  ∀ actor f x →
  pullbackRationalState P
    (Actor.rightAct (Target P) (factorActor P actor) f) x
    ≡ Actor.rightAct (Source P) actor
      (pullbackRationalState P f) x
pullbackIntertwinesActorAction P actor f x =
  cong f (sym (factorActorCoordinateNaturality P actor x))

-- Injectivity is proved at the OBSERVATION/POINTWISE level;
-- no functional extensionality is postulated.
pullbackReflectsPointwiseEquality :
  (P : SurjectiveFiniteFactorMap) →
  ∀ f g →
  (∀ x → pullbackRationalState P f x
      ≡ pullbackRationalState P g x) →
  ∀ y → f y ≡ g y
pullbackReflectsPointwiseEquality P f g agree
    (Actor.slot sector b)
  with preimage P b
... | a , factorAIsB =
  trans
    (sym (cong (λ z → f (Actor.slot sector z)) factorAIsB))
    (trans
      (agree (Actor.slot sector a))
      (cong (λ z → g (Actor.slot sector z)) factorAIsB))

-- When P is concrete 2I->A5, the spin sign lies in its kernel;
-- pullback is proper, with dimension 180 in dimension 360.
-- The BIDI module provides the lost-sign witness.
