module DASHI.Physics.Motors.SmithFilsingerLocalCausalADEReachExact where

-- F13: STRONG dynamic finite graph-dependency cone.
-- Reuse canonical sameID and two-coordinate LocalPrimitive/applyStages.
-- Unlike the earlier "never touched" frame, a touched, formerly zero
-- coordinate can become nonzero ONLY after one of its own input
-- coordinates was already reachable.
--
-- Every primitive needs explicit zero/zero -> zero receipts.
-- Nonzero external current is admitted ONLY as an initially sourced
-- coordinate. An unaccounted later current cannot be represented by
-- a zero-preserving primitive and must receive its own source marker.
--
-- Pure mathematical support, NOT a physical continuum Maxwell speed.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed
import DASHI.Physics.Motors.SmithFilsingerLocalCausalADEFrameExact as Frame

data Absurd : Set where

Not : Set → Set
Not P = P → Absurd

data Or (P Q : Set) : Set where
  orLeft : P → Or P Q
  orRight : Q → Or P Q

-- The update owner supplies this evidence for the actual two-coordinate
-- Cayley operator. It is not inferred from a chosen "reachability" set.
record ZeroPreserving {A : Set} (z : A)
  (p : Frame.LocalPrimitive A) : Set where
  field
    firstZero : Frame.LocalPrimitive.firstValue p z z ≡ z
    secondZero : Frame.LocalPrimitive.secondValue p z z ≡ z

record GuardedPrimitive (A : Set) (z : A) : Set where
  constructor guardedPrimitive
  field
    primitive : Frame.LocalPrimitive A
    preservesZero : ZeroPreserving z primitive

-- A step is a complete two-coordinate dependency transfer:
-- - if k is touched, only the PREVIOUS reachability of the two
--   endpoint coordinates can justify nonzero output;
-- - if k is untouched, its previous reachability remains unchanged.
-- Crucially there is no blanket expansion merely because a cell was
-- *mentioned* by the update.
reachStep :
  ∀ {A : Set} → Frame.LocalPrimitive A →
  (Nat → Set) → Nat → Set
reachStep p R k with
    Indexed.sameID k (Frame.LocalPrimitive.firstID p)
  | Indexed.sameID k (Frame.LocalPrimitive.secondID p)
... | true | _ =
  Or (R (Frame.LocalPrimitive.firstID p))
     (R (Frame.LocalPrimitive.secondID p))
... | false | true =
  Or (R (Frame.LocalPrimitive.firstID p))
     (R (Frame.LocalPrimitive.secondID p))
... | false | false = R k

-- A source-free state is supported by R if it vanishes at every
-- coordinate for which there is NO prior source-to-coordinate path.
OutsideZero :
  ∀ {A : Set} → A → Frame.State A → (Nat → Set) → Set
OutsideZero z s R = (k : Nat) → Not (R k) → s k ≡ z

-- This is the key nonvacuous one-stage preservation theorem.
-- For a touched output, the absence of both endpoint dependency
-- certificates forces both input values to be zero. The primitive
-- zero-preserving proof then forces the output to remain zero.
oneStepOutsideZero :
  ∀ {A : Set} (z : A) (g : GuardedPrimitive A z)
  (s : Frame.State A) (R : Nat → Set) →
  OutsideZero z s R →
  OutsideZero z
    (Frame.applyPrimitive (GuardedPrimitive.primitive g) s)
    (reachStep (GuardedPrimitive.primitive g) R)
oneStepOutsideZero z g s R initial k notReach with
    Indexed.sameID k (Frame.LocalPrimitive.firstID p)
  | Indexed.sameID k (Frame.LocalPrimitive.secondID p)
... | true | _ =
  trans
    (cong₂ (Frame.LocalPrimitive.firstValue p)
      (initial (Frame.LocalPrimitive.firstID p)
        (λ r → notReach (orLeft r)))
      (initial (Frame.LocalPrimitive.secondID p)
        (λ r → notReach (orRight r))))
    (ZeroPreserving.firstZero (GuardedPrimitive.preservesZero g))
... | false | true =
  trans
    (cong₂ (Frame.LocalPrimitive.secondValue p)
      (initial (Frame.LocalPrimitive.firstID p)
        (λ r → notReach (orLeft r)))
      (initial (Frame.LocalPrimitive.secondID p)
        (λ r → notReach (orRight r))))
    (ZeroPreserving.secondZero (GuardedPrimitive.preservesZero g))
... | false | false = initial k notReach
  where
    p = GuardedPrimitive.primitive g

guardedStages :
  ∀ {A : Set} {z : A} →
  List (GuardedPrimitive A z) → Frame.State A → Frame.State A
guardedStages [] s = s
guardedStages (g ∷ gs) s =
  guardedStages gs
    (Frame.applyPrimitive (GuardedPrimitive.primitive g) s)

reachStages :
  ∀ {A : Set} {z : A} →
  List (GuardedPrimitive A z) → (Nat → Set) → Nat → Set
reachStages [] R = R
reachStages (g ∷ gs) R =
  reachStages gs (reachStep (GuardedPrimitive.primitive g) R)

-- All-N dynamic cone: no nonzero response outside the EXACT evolving
-- source-reachable coordinate set for arbitrary noncommuting stage lists.
noSignalOutsideDynamicCone :
  ∀ {A : Set} (z : A)
  (gs : List (GuardedPrimitive A z))
  (s : Frame.State A) (R : Nat → Set) →
  OutsideZero z s R →
  OutsideZero z (guardedStages gs s) (reachStages gs R)
noSignalOutsideDynamicCone z [] s R initially = initially
noSignalOutsideDynamicCone z (g ∷ gs) s R initially =
  noSignalOutsideDynamicCone z gs
    (Frame.applyPrimitive (GuardedPrimitive.primitive g) s)
    (reachStep (GuardedPrimitive.primitive g) R)
    (oneStepOutsideZero z g s R initially)

-- This theorem does not claim a physical Maxwell front. In particular,
-- a macro step containing N sequential edges can cross N edges at
-- the *same named* macro-step. Propagation speed requires independent
-- physical distance and duration, with true Maxwell material causality.
