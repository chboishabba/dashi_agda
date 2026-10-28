module DASHI.Mathematics.Topology.AlexanderHornedA5C3RestrictionWeldExact where

------------------------------------------------------------------------
-- TWO C3s, ONE FINITE VOA ACTOR:
--
--   C3_int  <= A5 by a specified order-three element (3-cycle)
--   C3_ext  acts by permuting three horn/VOA coordinate sectors.
--
-- These are different cyclic actions. Their diagonal/internal and
-- sector/external lifts commute in A5^3 rtimes C3, yielding C3 x C3
-- provided the internal order-three element is nonidentity.
--
-- EXISTING SOURCE OWNER:
--  Foundations.PolyhedralFiniteRestrictionInstancesExact
--  Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact
--  Foundations.IcosahedralSO3RestrictionJ0To35Exact
-- Those authors own the SO3(j) -> A5 -> C3 restriction spectrum.
--
-- NEW CONTRIBUTION:
--  Connect the exact cyclic probe with a GENERIC ACTUAL ORDER-THREE
--  ELEMENT of the existing finite nonabelian VOA actor's factor
--  group. Prove C3_int commutes with C3_ext on THE SAME Slot state
--  coordinates. No second, invented VOA carrier.
--
-- No nontrivial group morphism A5 -> C3 exists (A5 perfect).
-- Restriction goes along C3 -> A5, NOT the reverse map.
-- This module does not instantiate finite A5 multiplication in Agda,
-- prove the actual horned 3-manifold pi1 is the abstract group,
-- or identify the finite c=0 VOA with the moonshine VOA V-natural.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Triple
import DASHI.Foundations.PolyhedralFiniteRestrictionInstancesExact as Poly
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed
import DASHI.Foundations.SU2SO3IrrepDimensionExact as SO3
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteVOAActorExact as Actor
import DASHI.Mathematics.Topology.AlexanderHornedC3VOAModeLiftExact as Modes

-- Prove that the correct previous A5/C3 owner is being consumed:
-- the icosahedral fixed-space probe is exactly the shared axial C3
-- formula for EVERY j in the existing finite angular-momentum scan.
existingA5C3FixedSpaceIsSharedFormula :
  (j : SO3.AngularMomentum0To35) →
  Poly.icosahedralFixedDimension j Poly.icosahedralC3
    ≡ Fixed.fixedDimension j Fixed.C3Probe
existingA5C3FixedSpaceIsSharedFormula j = refl

existingC3CharacterAverageReused :
  (j : SO3.AngularMomentum0To35) →
  (+ 3) *ℤ (+ (Poly.icosahedralFixedDimension j Poly.icosahedralC3))
    ≡ (+ (SO3.jDimension j))
      +ℤ ((+ 2) *ℤ Fixed.thirdTurnCharacter (SO3.jNat j))
existingC3CharacterAverageReused j =
  Fixed.c3CharacterAverageExact j

-- The supplied factor must be a genuine group and a genuine
-- order-three element. No dimension or icosahedral LABEL is
-- permitted to inhabit this record without these laws.
record InternalC3Element (D : Actor.ActorFactorGroup) : Set where
  field
    element : Actor.Carrier D
    rightIdentity : ∀ a →
      Actor.multiply D a (Actor.unit D) ≡ a
    orderThree : Actor.multiply D
       (Actor.multiply D element element) element
        ≡ Actor.unit D
    nonIdentity : element ≡ Actor.unit D → ⊥

open InternalC3Element public

internalActor :
  (D : Actor.ActorFactorGroup) →
  InternalC3Element D → Actor.Actor D
internalActor D selected =
  Actor.actor
    (Triple.xyz (element selected)
      (element selected) (element selected))
    C3.c0

-- The same selected A5-element (after actual A5 instantiation) must
-- act at all three horn sectors. Sector rotation leaves it diagonal.
internalExternalCommuteOnSlot :
  (D : Actor.ActorFactorGroup) →
  (selected : InternalC3Element D) →
  (x : Actor.Slot D) →
  Actor.coordinateAction D (internalActor D selected)
    (Actor.coordinateAction D (Actor.pureRotation D) x)
  ≡
  Actor.coordinateAction D (Actor.pureRotation D)
    (Actor.coordinateAction D (internalActor D selected) x)
internalExternalCommuteOnSlot D selected (Actor.slot C3.c0 a) =
  cong (Actor.slot C3.c1)
    (trans
      (cong (Actor.multiply D (element selected))
        (Actor.leftIdentity D a))
      (sym (Actor.leftIdentity D
        (Actor.multiply D (element selected) a))))
internalExternalCommuteOnSlot D selected (Actor.slot C3.c1 a) =
  cong (Actor.slot C3.c2)
    (trans
      (cong (Actor.multiply D (element selected))
        (Actor.leftIdentity D a))
      (sym (Actor.leftIdentity D
        (Actor.multiply D (element selected) a))))
internalExternalCommuteOnSlot D selected (Actor.slot C3.c2 a) =
  cong (Actor.slot C3.c0)
    (trans
      (cong (Actor.multiply D (element selected))
        (Actor.leftIdentity D a))
      (sym (Actor.leftIdentity D
        (Actor.multiply D (element selected) a))))

-- More than numerical coincidence: the internal generator has
-- actual order three on all coordinates, by the group multiplication
-- and its supplied order-three witness.
cubeElementActs : (D : Actor.ActorFactorGroup) →
  (selected : InternalC3Element D) → ∀ a →
  Actor.multiply D (element selected)
    (Actor.multiply D (element selected)
      (Actor.multiply D (element selected) a))
    ≡ a
cubeElementActs D selected a =
  trans
    (cong (Actor.multiply D (element selected))
      (sym (Actor.associative D
        (element selected) (element selected) a)))
    (trans
      (sym (Actor.associative D
        (element selected)
        (Actor.multiply D (element selected) (element selected)) a))
      (trans
        (cong (λ b → Actor.multiply D b a)
          (sym (Actor.associative D
            (element selected) (element selected) (element selected))))
        (trans
          (cong (λ b → Actor.multiply D b a) (orderThree selected))
          (Actor.leftIdentity D a))))

internalPeriodThreeOnSlot :
  (D : Actor.ActorFactorGroup) →
  (selected : InternalC3Element D) →
  (x : Actor.Slot D) →
  Actor.coordinateAction D (internalActor D selected)
    (Actor.coordinateAction D (internalActor D selected)
      (Actor.coordinateAction D (internalActor D selected) x))
    ≡ x
internalPeriodThreeOnSlot D selected (Actor.slot C3.c0 a) =
  cong (Actor.slot C3.c0) (cubeElementActs D selected a)
internalPeriodThreeOnSlot D selected (Actor.slot C3.c1 a) =
  cong (Actor.slot C3.c1) (cubeElementActs D selected a)
internalPeriodThreeOnSlot D selected (Actor.slot C3.c2 a) =
  cong (Actor.slot C3.c2) (cubeElementActs D selected a)

internalMovesIdentitySlot :
  (D : Actor.ActorFactorGroup) →
  (selected : InternalC3Element D) →
  Actor.coordinateAction D (internalActor D selected)
    (Actor.slot C3.c0 (Actor.unit D))
  ≡ Actor.slot C3.c0 (Actor.unit D) → ⊥
internalMovesIdentitySlot D selected impossible =
  nonIdentity selected
    (trans
      (sym (rightIdentity selected (element selected)))
      (cong Actor.coordinate
        impossible))

externalMovesIdentitySlot :
  (D : Actor.ActorFactorGroup) →
  Actor.coordinateAction D (Actor.pureRotation D)
    (Actor.slot C3.c0 (Actor.unit D))
  ≡ Actor.slot C3.c0 (Actor.unit D) → ⊥
externalMovesIdentitySlot D ()

-- Distinguishes the two cyclic actors by which coordinate they move.
-- Neither is a quotient character of perfect A5.

------------------------------------------------------------------------
-- SAME VOA STATE CONSUMER.  The two commuting order-three actions
-- preserve all pointwise rational vertex modes, not merely an
-- unrelated coordinate group action.  No function extensionality.
------------------------------------------------------------------------

internalExternalCommuteOnRationalStates :
  (D : Actor.ActorFactorGroup) →
  (selected : InternalC3Element D) →
  (f : Modes.RationalState D) → ∀ x →
  Actor.rightAct D (internalActor D selected)
    (Actor.rightAct D (Actor.pureRotation D) f) x
  ≡
  Actor.rightAct D (Actor.pureRotation D)
    (Actor.rightAct D (internalActor D selected) f) x
internalExternalCommuteOnRationalStates D selected f x =
  cong f (sym (internalExternalCommuteOnSlot D selected x))

internalIntertwinesAllVertexModes :
  (D : Actor.ActorFactorGroup) →
  (selected : InternalC3Element D) →
  ∀ (f g : Modes.RationalState D) n x →
  Actor.rightAct D (internalActor D selected)
    (Modes.vertexMode D f n g) x
  ≡
  Modes.vertexMode D
    (Actor.rightAct D (internalActor D selected) f) n
    (Actor.rightAct D (internalActor D selected) g) x
internalIntertwinesAllVertexModes D selected =
  Modes.allVertexModesIntertwineRightAction D
    (internalActor D selected)

externalIntertwinesAllVertexModes :
  (D : Actor.ActorFactorGroup) →
  ∀ (f g : Modes.RationalState D) n x →
  Actor.rightAct D (Actor.pureRotation D)
    (Modes.vertexMode D f n g) x
  ≡
  Modes.vertexMode D
    (Actor.rightAct D (Actor.pureRotation D) f) n
    (Actor.rightAct D (Actor.pureRotation D) g) x
externalIntertwinesAllVertexModes D =
  Modes.allVertexModesIntertwineRightAction D
    (Actor.pureRotation D)
