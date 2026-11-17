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

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
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
    Indexed.sameID k (Frame.LocalPrimitive.firstID (GuardedPrimitive.primitive g))
  | Indexed.sameID k (Frame.LocalPrimitive.secondID (GuardedPrimitive.primitive g))
... | true | _ =
  trans
    (cong₂ (Frame.LocalPrimitive.firstValue (GuardedPrimitive.primitive g))
      (initial (Frame.LocalPrimitive.firstID (GuardedPrimitive.primitive g))
        (λ r → notReach (orLeft r)))
      (initial (Frame.LocalPrimitive.secondID (GuardedPrimitive.primitive g))
        (λ r → notReach (orRight r))))
    (ZeroPreserving.firstZero (GuardedPrimitive.preservesZero g))
... | false | true =
  trans
    (cong₂ (Frame.LocalPrimitive.secondValue (GuardedPrimitive.primitive g))
      (initial (Frame.LocalPrimitive.firstID (GuardedPrimitive.primitive g))
        (λ r → notReach (orLeft r)))
      (initial (Frame.LocalPrimitive.secondID (GuardedPrimitive.primitive g))
        (λ r → notReach (orRight r))))
    (ZeroPreserving.secondZero (GuardedPrimitive.preservesZero g))
... | false | false = initial k notReach
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

-- Real source events are NOT zero-preserving. Their own cell is a
-- new root even when no prior signal reaches it. A source label alone
-- never certifies that its work came from the Sun–Earth environment.
data SourceOwner : Set where
  naturalSource : SourceOwner
  controllerSource : SourceOwner

data LocalEvent (A : Set) (z : A) : Set where
  propagate : GuardedPrimitive A z → LocalEvent A z
  injectAt : SourceOwner → Nat → (A → A) → LocalEvent A z

data Ticket : Set where
  ticket : Ticket

absurdElim : ∀ {X : Set} → Absurd → X
absurdElim ()

applyInjection :
  ∀ {A : Set} → Nat → (A → A) → Frame.State A → Frame.State A
applyInjection sourceID change s k with Indexed.sameID k sourceID
... | true = change (s k)
... | false = s k

-- At the source coordinate the reachability type is inhabited
-- unconditionally; everywhere else it stays precisely the old type.
seedReach : Nat → (Nat → Set) → Nat → Set
seedReach sourceID R k with Indexed.sameID k sourceID
... | true = Ticket
... | false = R k

injectionOutsideZero :
  ∀ {A : Set} (z : A) (sourceID : Nat) (change : A → A)
  (s : Frame.State A) (R : Nat → Set) →
  OutsideZero z s R →
  OutsideZero z (applyInjection sourceID change s)
    (seedReach sourceID R)
injectionOutsideZero z sourceID change s R initial k outside with
    Indexed.sameID k sourceID
... | true = absurdElim (outside ticket)
... | false = initial k outside

runEvent :
  ∀ {A : Set} {z : A} →
  LocalEvent A z → Frame.State A → Frame.State A
runEvent (propagate g) s =
  Frame.applyPrimitive (GuardedPrimitive.primitive g) s
runEvent (injectAt owner sourceID change) s =
  applyInjection sourceID change s

reachEvent :
  ∀ {A : Set} {z : A} →
  LocalEvent A z → (Nat → Set) → Nat → Set
reachEvent (propagate g) R =
  reachStep (GuardedPrimitive.primitive g) R
reachEvent (injectAt owner sourceID change) R =
  seedReach sourceID R

eventOutsideZero :
  ∀ {A : Set} (z : A) (event : LocalEvent A z)
  (s : Frame.State A) (R : Nat → Set) →
  OutsideZero z s R →
  OutsideZero z (runEvent event s) (reachEvent event R)
eventOutsideZero z (propagate g) s R initial =
  oneStepOutsideZero z g s R initial
eventOutsideZero z (injectAt owner sourceID change) s R initial =
  injectionOutsideZero z sourceID change s R initial

runEvents :
  ∀ {A : Set} {z : A} →
  List (LocalEvent A z) → Frame.State A → Frame.State A
runEvents [] s = s
runEvents (event ∷ events) s =
  runEvents events (runEvent event s)

reachEvents :
  ∀ {A : Set} {z : A} →
  List (LocalEvent A z) → (Nat → Set) → Nat → Set
reachEvents [] R = R
reachEvents (event ∷ events) R =
  reachEvents events (reachEvent event R)

-- Strong all-N result: any finite interleaving of ordinary local
-- propagation, natural-source injections and controller injections
-- has no nonzero response outside its EXACT dynamic dependency set.
-- This prevents the prior source-seeding bug in an Agda theorem,
-- conditional on real zero-preserving primitive receipts.
noSignalOutsideInterleavedSourceCone :
  ∀ {A : Set} (z : A)
  (events : List (LocalEvent A z))
  (s : Frame.State A) (R : Nat → Set) →
  OutsideZero z s R →
  OutsideZero z (runEvents events s) (reachEvents events R)
noSignalOutsideInterleavedSourceCone z [] s R initially = initially
noSignalOutsideInterleavedSourceCone z (event ∷ events) s R initially =
  noSignalOutsideInterleavedSourceCone z events
    (runEvent event s) (reachEvent event R)
    (eventOutsideZero z event s R initially)

-- Nonvacuous native Agda fixture: an additive two-coordinate
-- primitive has an actual (not postulated) zero-preservation receipt.
-- It is an interface sanity witness, not a Maxwell Cayley discretization.
additivePrimitive : Frame.LocalPrimitive Nat
additivePrimitive =
  Frame.localPrimitive zero (suc zero) _+_ _+_

additiveZeroPreserving : ZeroPreserving zero additivePrimitive
additiveZeroPreserving =
  record { firstZero = refl ; secondZero = refl }

additiveGuarded : GuardedPrimitive Nat zero
additiveGuarded =
  guardedPrimitive additivePrimitive additiveZeroPreserving

-- This theorem does not claim a physical Maxwell front. In particular,
-- a macro step containing N sequential edges can cross N edges at
-- the *same named* macro-step. Propagation speed requires independent
-- physical distance and duration, with true Maxwell material causality.
