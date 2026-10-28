module DASHI.Mathematics.Topology.AlexanderHornedC3FiniteVOAActorExact where

------------------------------------------------------------------------
-- FINITE NONABELIAN QUOTIENT ACTOR FOR THE HORNED C3 PROGRAM.
--
-- Mathematically specialise A to A5, with three independent factors.
-- The group Q=A^3 ⋊ C3 acts on three regular A-address blocks:
--
--   (u,k) . (i,a) = (k+i, u_(k+i) a).
--
-- The group law is (u,k)(v,l)=(u * beta^k(v), k+l),
-- beta(v)_i=v_(i-1). This module proves the ACTION COMPOSITION
-- for arbitrary group A, using its actual associative/identity laws,
-- not an opaque VOAGroupAction.actionComposition : Set.
--
-- Pullback gives a RIGHT action on the coordinate algebra
-- Functions(C3 x A,K), preserving pointwise multiplication and 1.
-- A LEFT action is obtained by pullback through the group inverse.
-- For A=A5, this is the underlying function algebra of the
-- finite-dimensional c=0 commutative vertex operator algebra
-- C^(C3 x A5), a VOA with all states in weight zero.
--
-- BOUNDARY: a finite target group A5 is not constructed in this
-- module; a finite Python permutation audit independently checks
-- the A5 instance. No exact G -> A5^3 map, full VOA Jacobi axiom,
-- actual geometric exterior pi1, Monster/3B action or kernel
-- certification is produced *by this module alone*.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Triple

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record ActorFactorGroup : Set₁ where
  field
    Carrier : Set
    unit : Carrier
    multiply : Carrier → Carrier → Carrier
    leftIdentity : ∀ a → multiply unit a ≡ a
    associative : ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)

open ActorFactorGroup public

record Slot (D : ActorFactorGroup) : Set where
  constructor slot
  field
    sector : C3.C3
    coordinate : Carrier D

open Slot public

at : (D : ActorFactorGroup) →
  Triple.Triple (Carrier D) → C3.C3 → Carrier D
at D q C3.c0 = Triple.first q
at D q C3.c1 = Triple.second q
at D q C3.c2 = Triple.third q

multiplyTriple : (D : ActorFactorGroup) →
  Triple.Triple (Carrier D) → Triple.Triple (Carrier D) →
  Triple.Triple (Carrier D)
multiplyTriple D q p = Triple.xyz
  (multiply D (at D q C3.c0) (at D p C3.c0))
  (multiply D (at D q C3.c1) (at D p C3.c1))
  (multiply D (at D q C3.c2) (at D p C3.c2))

shift : (D : ActorFactorGroup) → C3.C3 →
  Triple.Triple (Carrier D) → Triple.Triple (Carrier D)
shift D C3.c0 p = p
shift D C3.c1 p = Triple.xyz
  (at D p C3.c2) (at D p C3.c0) (at D p C3.c1)
shift D C3.c2 p = Triple.xyz
  (at D p C3.c1) (at D p C3.c2) (at D p C3.c0)

record Actor (D : ActorFactorGroup) : Set where
  constructor actor
  field
    triple : Triple.Triple (Carrier D)
    phase : C3.C3

open Actor public

identityActor : (D : ActorFactorGroup) → Actor D
identityActor D = actor (Triple.xyz (unit D) (unit D) (unit D)) C3.c0

compose : (D : ActorFactorGroup) → Actor D → Actor D → Actor D
compose D (actor q k) (actor p l) =
  actor (multiplyTriple D q (shift D k p)) (C3._∙_ k l)

coordinateAction : (D : ActorFactorGroup) →
  Actor D → Slot D → Slot D
coordinateAction D (actor q k) (slot i a) =
  slot (C3._∙_ k i)
    (multiply D (at D q (C3._∙_ k i)) a)

coordinateIdentity : (D : ActorFactorGroup) → ∀ x →
  coordinateAction D (identityActor D) x ≡ x
coordinateIdentity D (slot C3.c0 a) =
  cong (slot C3.c0) (leftIdentity D a)
coordinateIdentity D (slot C3.c1 a) =
  cong (slot C3.c1) (leftIdentity D a)
coordinateIdentity D (slot C3.c2 a) =
  cong (slot C3.c2) (leftIdentity D a)

coordinateActionComposition : (D : ActorFactorGroup) →
  ∀ g h x →
  coordinateAction D (compose D g h) x
    ≡ coordinateAction D g (coordinateAction D h x)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c0) (slot C3.c0 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c0) (slot C3.c1 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c0) (slot C3.c2 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c1) (slot C3.c0 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c1) (slot C3.c1 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c1) (slot C3.c2 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c2) (slot C3.c0 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c2) (slot C3.c1 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c0) (actor p C3.c2) (slot C3.c2 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c0) (slot C3.c0 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c0) (slot C3.c1 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c0) (slot C3.c2 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c1) (slot C3.c0 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c1) (slot C3.c1 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c1) (slot C3.c2 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c2) (slot C3.c0 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c2) (slot C3.c1 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c1) (actor p C3.c2) (slot C3.c2 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c0) (slot C3.c0 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c0) (slot C3.c1 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c0) (slot C3.c2 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c1) (slot C3.c0 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c1) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c1) (slot C3.c1 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c1) (slot C3.c2 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c2) (slot C3.c0 a) =
  cong (slot C3.c1)
    (associative D (at D q C3.c1) (at D p C3.c2) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c2) (slot C3.c1 a) =
  cong (slot C3.c2)
    (associative D (at D q C3.c2) (at D p C3.c0) a)
coordinateActionComposition D (actor q C3.c2) (actor p C3.c2) (slot C3.c2 a) =
  cong (slot C3.c0)
    (associative D (at D q C3.c0) (at D p C3.c1) a)


-- A right action on the coordinate function algebra; pullback
-- reverses composition, which the following lemma states exactly.
State : (D : ActorFactorGroup) → (K : Set) → Set
State D K = Slot D → K

rightAct : (D : ActorFactorGroup) → {K : Set} →
  Actor D → State D K → State D K
rightAct D g f x = f (coordinateAction D g x)

rightActIdentity : (D : ActorFactorGroup) →
  {K : Set} → (f : State D K) → ∀ x →
  rightAct D (identityActor D) f x ≡ f x
rightActIdentity D f x = cong f (coordinateIdentity D x)

rightActComposition : (D : ActorFactorGroup) →
  {K : Set} → ∀ g h (f : State D K) x →
  rightAct D (compose D g h) f x
    ≡ rightAct D h (rightAct D g f) x
rightActComposition D g h f x =
  cong f (coordinateActionComposition D g h x)

pointwiseProduct : (D : ActorFactorGroup) → {K : Set} →
  (K → K → K) → State D K → State D K → State D K
pointwiseProduct D op f g x = op (f x) (g x)

constant : (D : ActorFactorGroup) → {K : Set} → K → State D K
constant D k _ = k

rightActPreservesPointwiseProduct : (D : ActorFactorGroup) →
  {K : Set} → (op : K → K → K) → ∀ g f h x →
  rightAct D g (pointwiseProduct D op f h) x
  ≡ pointwiseProduct D op (rightAct D g f) (rightAct D g h) x
rightActPreservesPointwiseProduct D op g f h x = refl

rightActPreservesConstant : (D : ActorFactorGroup) →
  {K : Set} → (k : K) → ∀ g x →
  rightAct D g (constant D k) x ≡ constant D k x
rightActPreservesConstant D k g x = refl

-- Order-three sector permutation is nontrivial on coordinates.
pureRotation : (D : ActorFactorGroup) → Actor D
pureRotation D = actor
  (Triple.xyz (unit D) (unit D) (unit D)) C3.c1

pureRotationMovesFirstSector : (D : ActorFactorGroup) →
  coordinateAction D (pureRotation D) (slot C3.c0 (unit D))
    ≢ slot C3.c0 (unit D)
pureRotationMovesFirstSector D ()
