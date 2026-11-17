module DASHI.Mathematics.Topology.AlexanderHornedNonabelianRegularPadicReuseExact where

------------------------------------------------------------------------
-- THE EXISTING FINITE HORN/VOA ACTOR IS ALREADY A FAITHFUL
-- REGULAR COORDINATE ACTION OF ITS FINITE NONABELIAN FACTOR.
--
-- SOURCE:
--  AlexanderHornedC3FiniteVOAActorExact (actual coordinate action);
--  AlexanderHornedC3VOAModeLiftExact (same rational vertex modes);
--  Foundations.PolyhedralRegularRepresentationShiftExact (A5 j-scan);
--  Representation theory: Serre; standard regular representation.
--
-- Here the coordinate action's faithfulness on one sector is proved,
-- using only a genuine RIGHT unit law for the selected group factor.
-- This is a carrier identity, not a representation-label receipt.
--
-- The subsequent permutation matrices exist over every coefficient
-- field, including Q_p. A literal Q_p field/GL_n library instance
-- is not claimed by the source-written Agda theorem.
-- Trivial pro-p completion does NOT rule out nonabelian finite
-- image permutation representations in GL_n(Q_p).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteVOAActorExact as Actor
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Triple
import DASHI.Mathematics.Topology.AlexanderHornedC3VOAModeLiftExact as Modes
import DASHI.Foundations.PolyhedralRegularRepresentationShiftExact as Regular

oneSectorFactorActor :
  (D : Actor.ActorFactorGroup) →
  Actor.Carrier D → Actor.Actor D
oneSectorFactorActor D g =
  Actor.actor
    (Triple.xyz g (Actor.unit D) (Actor.unit D))
    C3.c0

rightUnitSlot :
  (D : Actor.ActorFactorGroup) →
  (rightIdentity : ∀ g →
    Actor.multiply D g (Actor.unit D) ≡ g) →
  ∀ g →
  Actor.coordinateAction D (oneSectorFactorActor D g)
    (Actor.slot C3.c0 (Actor.unit D))
    ≡ Actor.slot C3.c0 g
rightUnitSlot D rightIdentity g =
  cong (Actor.slot C3.c0) (rightIdentity g)

regularSectorActionSeparatesAnyTwoFactors :
  (D : Actor.ActorFactorGroup) →
  (rightIdentity : ∀ g →
    Actor.multiply D g (Actor.unit D) ≡ g) →
  ∀ g h →
  Actor.coordinateAction D (oneSectorFactorActor D g)
    (Actor.slot C3.c0 (Actor.unit D))
  ≡
  Actor.coordinateAction D (oneSectorFactorActor D h)
    (Actor.slot C3.c0 (Actor.unit D))
  → g ≡ h
regularSectorActionSeparatesAnyTwoFactors D rightIdentity g h same =
  trans (sym (rightIdentity g))
    (trans (cong Actor.coordinate same) (rightIdentity h))

-- The pointwise VOA modes are also equivariant under EACH selected
-- finite factor actor. This is real reuse of the finite state owner,
-- not another regular-representation carrier.
sameVertexModesIntertwineRegularFactor :
  (D : Actor.ActorFactorGroup) →
  ∀ factor (f g : Modes.RationalState D) n x →
  Actor.rightAct D (oneSectorFactorActor D factor)
    (Modes.vertexMode D f n g) x
  ≡ Modes.vertexMode D
      (Actor.rightAct D (oneSectorFactorActor D factor) f) n
      (Actor.rightAct D (oneSectorFactorActor D factor) g) x
sameVertexModesIntertwineRegularFactor D factor =
  Modes.allVertexModesIntertwineRightAction D
    (oneSectorFactorActor D factor)

-- Existing A5 regular-character source: dimension 60, no
-- invented representation values.
oldIcosahedralRegularDimensionReused :
  Regular.rotationGroupOrder Regular.rotationalIcosahedral ≡ 60
oldIcosahedralRegularDimensionReused = refl

-- For a concrete finite group of order 60 this action has 60
-- distinct coordinates PER factor. The 3-sector permutation actor
-- thus has 180 coordinates. Matrix entries 0 and 1 work over Q_p
-- for every p; the group map's kernel back in G is still nontrivial.
