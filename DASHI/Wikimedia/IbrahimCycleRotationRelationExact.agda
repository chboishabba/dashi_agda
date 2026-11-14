module DASHI.Wikimedia.IbrahimCycleRotationRelationExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit

------------------------------------------------------------------------
-- NEW DASHI mathematical consequences of Ibrahim-style deterministic
-- first-link orbits. Original first-link study: Mark Ibrahim,
-- Christopher M. Danforth and Peter Sheridan Dodds (2017),
-- DOI: 10.1016/j.jocs.2016.12.001.
--
-- Intrinsic orbit rotation is deliberately stronger than equality of
-- certificates' arbitrary chosen representatives. This module proves
-- sound rotation witnesses in the original Node -> Node carrier.
-- Full automatic canonical cycle uniqueness remains a separate gate.
------------------------------------------------------------------------

-- Two certificates of the SAME start, with entry times differing by k,
-- must name representatives related by exactly k forward graph edges.
laterEntryIsForwardRotation :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  (earlier later : Orbit.EventualCycle next start) →
  (offset : Nat) →
  Orbit.entryHops later ≡ Orbit.entryHops earlier + offset →
  Orbit.iterate next offset (Orbit.representative earlier) ≡
    Orbit.representative later
laterEntryIsForwardRotation {next = next} {start = start}
    earlier later offset laterEntry =
  trans
    (sym (cong (Orbit.iterate next offset) (Orbit.entered earlier)))
    (trans
      (sym (Orbit.iterateAppend next
        (Orbit.entryHops earlier) offset start))
      (trans
        (cong (λ time → Orbit.iterate next time start)
          (sym laterEntry))
        (Orbit.entered later)))

-- An explicit rotation witness is verified against the original edge
-- transition function, NOT merely an equality of QID/title projections.
record ForwardRotation {Node : Set}
  (next : Node → Node) (from to : Node) : Set where
  constructor forwardRotation
  field
    offset : Nat
    turns : Orbit.iterate next offset from ≡ to
open ForwardRotation public

entryOrderCreatesForwardRotation :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  (earlier later : Orbit.EventualCycle next start) →
  (offset : Nat) →
  Orbit.entryHops later ≡ Orbit.entryHops earlier + offset →
  ForwardRotation next
    (Orbit.representative earlier) (Orbit.representative later)
entryOrderCreatesForwardRotation earlier later offset order =
  forwardRotation offset
    (laterEntryIsForwardRotation earlier later offset order)

forwardRotationTransitive :
  ∀ {Node : Set} {next : Node → Node}
    {a b c : Node} →
  ForwardRotation next a b →
  ForwardRotation next b c →
  ForwardRotation next a c
forwardRotationTransitive {next = next}
  {a = a} (forwardRotation first firstEquals)
  (forwardRotation second secondEquals) =
  forwardRotation (first + second)
    (trans
      (Orbit.iterateAppend next first second a)
      (trans
        (cong (Orbit.iterate next second) firstEquals)
        secondEquals))

-- A bounded offset within a known period is a *true* rotation:
-- a -> b and b -> a, not just common representative labels.
cycleRotationHasReturn :
  ∀ {Node : Set} {next : Node → Node}
    (from to : Node) (offset remaining : Nat) →
  Orbit.iterate next offset from ≡ to →
  Orbit.iterate next (offset + remaining) from ≡ from →
  Orbit.iterate next remaining to ≡ from
cycleRotationHasReturn {next = next} from to offset remaining
    rotated closed =
  trans
    (sym (cong (Orbit.iterate next remaining) rotated))
    (trans
      (sym (Orbit.iterateAppend next offset remaining from))
      closed)

record MutualOrbitRotation {Node : Set}
  (next : Node → Node) (a b : Node) : Set where
  constructor mutualOrbitRotation
  field
    forward : ForwardRotation next a b
    backward : ForwardRotation next b a
open MutualOrbitRotation public

knownPeriodMakesMutualRotation :
  ∀ {Node : Set} {next : Node → Node}
    {a b : Node} →
  (offset remaining : Nat) →
  Orbit.iterate next offset a ≡ b →
  Orbit.iterate next (offset + remaining) a ≡ a →
  MutualOrbitRotation next a b
knownPeriodMakesMutualRotation {next = next} {a = a} {b = b}
    offset remaining rotates closes =
  mutualOrbitRotation
    (forwardRotation offset rotates)
    (forwardRotation remaining
      (cycleRotationHasReturn a b offset remaining rotates closes))

-- The known-period premise prevents an erroneous converse for a
-- transient path leading into a cycle. A QID collision, title equality
-- or fabricated source record cannot instantiate it.
