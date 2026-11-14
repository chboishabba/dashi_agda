module DASHI.Wikimedia.IbrahimPartialFirstLinkSemanticsExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit

------------------------------------------------------------------------
-- NEW DASHI typed partial-first-link semantics, preserving the three
-- independent source observations of the reference Python checker:
-- a qualifying known target, a genuine eligible-link dead end, and a
-- link into an unresolved/missing source. No unknown is silently
-- converted into an absorbing graph self-loop or a signed-zero trit.
--
-- Original first-link methodology: Ibrahim, Danforth, Dodds (2017),
-- DOI 10.1016/j.jocs.2016.12.001. This source is a new DASHI proof
-- adapter, not a claim of author-code/wikitext parser equality.
------------------------------------------------------------------------

data FirstLinkSelection (Node Outside : Set) : Set where
  knownTarget : Node → FirstLinkSelection Node Outside
  explicitDeadEnd : FirstLinkSelection Node Outside
  unresolvedTarget : Outside → FirstLinkSelection Node Outside

data PartialObservation (Node Outside : Set) : Set where
  visiting : Node → PartialObservation Node Outside
  stoppedAt : Node → PartialObservation Node Outside
  missingTarget : Outside → PartialObservation Node Outside

advancePartial :
  ∀ {Node Outside : Set} →
  (select : Node → FirstLinkSelection Node Outside) →
  PartialObservation Node Outside →
  PartialObservation Node Outside
advancePartial select (visiting node) with select node
... | knownTarget next = visiting next
... | explicitDeadEnd = stoppedAt node
... | unresolvedTarget target = missingTarget target
advancePartial select (stoppedAt node) = stoppedAt node
advancePartial select (missingTarget target) = missingTarget target

partialIterate :
  ∀ {Node Outside : Set} →
  (select : Node → FirstLinkSelection Node Outside) →
  Nat → PartialObservation Node Outside →
  PartialObservation Node Outside
partialIterate select zero current = current
partialIterate select (suc n) current =
  partialIterate select n (advancePartial select current)

missingTargetNotDeadEnd :
  ∀ {Node Outside : Set} {node : Node} {target : Outside} →
  stoppedAt node ≡ missingTarget target → ⊥
missingTargetNotDeadEnd ()

activeNotMissingTarget :
  ∀ {Node Outside : Set} {node : Node} {target : Outside} →
  visiting node ≡ missingTarget target → ⊥
activeNotMissingTarget ()

activeNotDeadEnd :
  ∀ {Node Outside : Set} {node other : Node} →
  visiting node ≡ stoppedAt other → ⊥
activeNotDeadEnd ()

partialDeadEndAbsorbs :
  ∀ {Node Outside : Set}
    (select : Node → FirstLinkSelection Node Outside)
    (n : Nat) (node : Node) →
  partialIterate select n (stoppedAt node) ≡ stoppedAt node
partialDeadEndAbsorbs select zero node = refl
partialDeadEndAbsorbs select (suc n) node =
  partialDeadEndAbsorbs select n node

partialUnresolvedAbsorbs :
  ∀ {Node Outside : Set}
    (select : Node → FirstLinkSelection Node Outside)
    (n : Nat) (target : Outside) →
  partialIterate select n (missingTarget target) ≡ missingTarget target
partialUnresolvedAbsorbs select zero target = refl
partialUnresolvedAbsorbs select (suc n) target =
  partialUnresolvedAbsorbs select n target

totalAsPartialSelection :
  ∀ {Node Outside : Set} →
  (next : Node → Node) →
  Node → FirstLinkSelection Node Outside
totalAsPartialSelection next node = knownTarget (next node)

totalGraphEmbeddedIntoPartial :
  ∀ {Node Outside : Set} (next : Node → Node)
    (n : Nat) (start : Node) →
  partialIterate (totalAsPartialSelection {Outside = Outside} next)
    n (visiting start) ≡ visiting (Orbit.iterate next n start)
totalGraphEmbeddedIntoPartial next zero start = refl
totalGraphEmbeddedIntoPartial next (suc n) start =
  totalGraphEmbeddedIntoPartial next n (next start)

totalGraphCannotCreateMissingTarget :
  ∀ {Node Outside : Set} (next : Node → Node)
    (n : Nat) (start : Node) (target : Outside) →
  partialIterate (totalAsPartialSelection next)
    n (visiting start) ≡ missingTarget target → ⊥
totalGraphCannotCreateMissingTarget next n start target false =
  activeNotMissingTarget
    (trans (sym (totalGraphEmbeddedIntoPartial next n start)) false)

totalGraphCannotCreateDeadEnd :
  ∀ {Node Outside : Set} (next : Node → Node)
    (n : Nat) (start stop : Node) →
  partialIterate (totalAsPartialSelection {Outside = Outside} next)
    n (visiting start) ≡ stoppedAt stop → ⊥
totalGraphCannotCreateDeadEnd next n start stop false =
  activeNotDeadEnd
    (trans (sym (totalGraphEmbeddedIntoPartial next n start)) false)

-- A typed first-link observation remains a navigation projection.
-- Source/QID identity, parser legitimacy, human repair authority and
-- physical shard acceptance do not follow from these constructors.
