module DASHI.Wikimedia.IbrahimFiniteLoopErasureAndWireNormalFormExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit
import DASHI.Wikimedia.IbrahimCycleRotationRelationExact as Rotation
import DASHI.Wikimedia.IbrahimFiniteTraceCheckerWeldExact as Trace

------------------------------------------------------------------------
-- M2a / M4a: explicit genuine-edge loop erasure and FIRST-REPEAT
-- canonical normal-form witness. Original research provenance:
-- Ibrahim, Danforth, Dodds (2017), DOI 10.1016/j.jocs.2016.12.001.
--
-- These are mathematical typed/semantic witnesses. A JSON byte decoder
-- or the original Wikipedia link selector is NOT proven by this module.
-- Kernel acceptance required on the changed exact source head.
------------------------------------------------------------------------

-- Given an actual repeated node at two different orbit positions,
-- remove that positive-gap subwalk and retain the same end vertex.
-- No node identity or edge is inferred from a Wikidata QID/title.
finitePathLoopErasure :
  ∀ {Node : Set} →
  (next : Node → Node)
  (prefix gap suffix : Nat) (start target : Node) →
  Orbit.iterate next prefix start ≡
    Orbit.iterate next (prefix + suc gap) start →
  Orbit.iterate next ((prefix + suc gap) + suffix) start ≡ target →
  Rotation.ForwardRotation next start target
finitePathLoopErasure next prefix gap suffix start target repeat end =
  Rotation.forwardRotation (prefix + suffix)
    (trans
      (Orbit.iterateAppend next prefix suffix start)
      (trans
        (cong (Orbit.iterate next suffix) repeat)
        (trans
          (sym (Orbit.iterateAppend next (prefix + suc gap)
            suffix start))
          end)))

-- Canonical first-repeat format: a positive repeated edge cycle,
-- with all *earlier* in-carrier orbit observations distinct.
-- This is intentionally narrower than arbitrary CheckedEdgePath.
record TypedFirstRepeatNormalForm {Node : Set}
    (next : Node → Node) (start : Node) : Set where
  constructor typedFirstRepeatNormalForm
  field
    entryHops periodTail : Nat
    repeatedNode : Node
    entryPath :
      Trace.CheckedEdgePath next entryHops start repeatedNode
    positiveReturn :
      Trace.CheckedEdgePath next (suc periodTail)
        repeatedNode repeatedNode
    noEarlierRepeat :
      (i j : Nat) →
      i < j →
      j < (entryHops + suc periodTail) →
      Orbit.iterate next i start ≡ Orbit.iterate next j start →
      ⊥
open TypedFirstRepeatNormalForm public

-- M4a: semantics of a TYPED strict first-repeat normal form refine the
-- original graph's checked-edge-path and accepted cycle contracts.
-- A Python checker that parses JSON into this dependent type remains a
-- separate source-language implementation/refinement obligation.
verifiedNormalFormYieldsCheckedEdgePath :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  TypedFirstRepeatNormalForm next start →
  Trace.AcceptedCycleTrace next start
verifiedNormalFormYieldsCheckedEdgePath wire =
  Trace.acceptedCycleTrace
    (entryHops wire)
    (periodTail wire)
    (repeatedNode wire)
    (entryPath wire)
    (positiveReturn wire)

verifiedNormalFormYieldsEventualCycle :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  TypedFirstRepeatNormalForm next start →
  Orbit.EventualCycle next start
verifiedNormalFormYieldsEventualCycle wire =
  Trace.acceptedTraceImpliesEventualCycle
    (verifiedNormalFormYieldsCheckedEdgePath wire)

verifiedNormalFormPreservesFirstRepeat :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  (wire : TypedFirstRepeatNormalForm next start) →
  (i j : Nat) → i < j →
  j < (entryHops wire + suc (periodTail wire)) →
  Orbit.iterate next i start ≡ Orbit.iterate next j start →
  ⊥
verifiedNormalFormPreservesFirstRepeat wire =
  noEarlierRepeat wire

-- Remaining, strictly distinct targets:
-- M2b: deduce an explicit fuel bound from a complete finite carrier.
-- M2c: eliminate the cycle-membership oracle with complete bounded search.
-- M2d: instantiate order-dependent canonical root choice without oracle.
-- M4b/c: prove typed wire parser completeness and Python/JSON refinement.
-- Historical Wikimedia oldid/link-selector and original bin/source
-- authentication remain empirical gates, never axioms of this module.
