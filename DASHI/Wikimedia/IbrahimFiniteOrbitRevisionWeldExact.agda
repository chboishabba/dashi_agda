module DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN
import DASHI.Wikimedia.IbrahimFirstLinkPhilosophyCoreBasinDeweyQidExact as Core

------------------------------------------------------------------------
-- IBRAHIM FLN: CERTIFIED FINITE ORBITS AND REVISION SENSITIVITY
--
-- Original first-link/traversal-funnel methodology:
-- M. Ibrahim, C. M. Danforth, P. S. Dodds (2017),
-- "Connecting every bit of knowledge: The structure of Wikipedia's
-- First Link Network", Journal of Computational Science 19, 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001.
--
-- The proofs below are new DASHI graph lemmas. The source does not
-- assert them as verbatim theorems. The historical seven-cycle fixture
-- is attributed to the author's basins notebook (see Core).
--
-- This module does NOT prove corpus finiteness, parser correctness,
-- exhaustive cycle enumeration, exact historical dump identity, or
-- equivalence to the original traversal-funnel implementation.
------------------------------------------------------------------------

iterate : ∀ {Node : Set} → (Node → Node) → Nat → Node → Node
iterate next zero start = start
iterate next (suc n) start = iterate next n (next start)

iterateZero : ∀ {Node : Set} (next : Node → Node) (v : Node) →
  iterate next zero v ≡ v
iterateZero next v = refl

iterateSuccessor : ∀ {Node : Set} (next : Node → Node)
  (n : Nat) (v : Node) →
  iterate next (suc n) v ≡ iterate next n (next v)
iterateSuccessor next n v = refl

------------------------------------------------------------------------
-- A prefix certificate witnesses equality of the actual outgoing
-- edges visited on the OLD orbit, not equality of page titles/QIDs,
-- and not equality of the entire two graph versions.
------------------------------------------------------------------------

data StablePrefix {Node : Set}
  (old new : Node → Node) : Nat → Node → Set where
  stableZero : ∀ {v} → StablePrefix old new zero v
  stableStep : ∀ {n v} →
    old v ≡ new v →
    StablePrefix old new n (old v) →
    StablePrefix old new (suc n) v

stablePrefixIterate :
  ∀ {Node : Set} {old new : Node → Node} {n : Nat} {v : Node} →
  StablePrefix old new n v →
  iterate old n v ≡ iterate new n v
stablePrefixIterate stableZero = refl
stablePrefixIterate {new = new} {n = suc n}
  (stableStep same rest) =
  trans (stablePrefixIterate rest)
        (cong (iterate new n) same)

------------------------------------------------------------------------
-- A change set may contain many vertices; every nonchanged vertex
-- must have a genuinely equal outgoing link. No Boolean flag suffices.
------------------------------------------------------------------------

record TypedRevisionDelta (Node : Set) : Set₁ where
  constructor typedRevisionDelta
  field
    oldLink newLink : Node → Node
    changedAt : Node → Set
    unchangedHasEqualLink :
      ∀ {v} → (changedAt v → ⊥) → oldLink v ≡ newLink v
open TypedRevisionDelta public

data AvoidsEditedVertices {Node : Set}
  (old : Node → Node) (changed : Node → Set) :
  Nat → Node → Set where
  avoidsZero : ∀ {v} → AvoidsEditedVertices old changed zero v
  avoidsStep : ∀ {n v} →
    (changed v → ⊥) →
    AvoidsEditedVertices old changed n (old v) →
    AvoidsEditedVertices old changed (suc n) v

avoidanceImpliesStable :
  ∀ {Node : Set} (delta : TypedRevisionDelta Node)
    {n : Nat} {v : Node} →
  AvoidsEditedVertices (oldLink delta) (changedAt delta) n v →
  StablePrefix (oldLink delta) (newLink delta) n v
avoidanceImpliesStable delta avoidsZero = stableZero
avoidanceImpliesStable delta (avoidsStep unedited tail) =
  stableStep (unchangedHasEqualLink delta unedited)
             (avoidanceImpliesStable delta tail)

unchangedOldOrbitPreservesResult :
  ∀ {Node : Set} (delta : TypedRevisionDelta Node)
    {n : Nat} {v : Node} →
  AvoidsEditedVertices (oldLink delta) (changedAt delta) n v →
  iterate (oldLink delta) n v ≡ iterate (newLink delta) n v
unchangedOldOrbitPreservesResult delta avoids =
  stablePrefixIterate (avoidanceImpliesStable delta avoids)

-- Constructive contrapositive: a changed endpoint after n steps
-- entails that no certificate of avoiding edits along the old n-step
-- path can exist. No classical decidability assumption is inserted.
changedResultRequiresOldEditedReachability :
  ∀ {Node : Set} (delta : TypedRevisionDelta Node)
    {n : Nat} {v : Node} →
  (iterate (oldLink delta) n v ≡
   iterate (newLink delta) n v → ⊥) →
  AvoidsEditedVertices (oldLink delta) (changedAt delta) n v → ⊥
changedResultRequiresOldEditedReachability delta difference avoids =
  difference (unchangedOldOrbitPreservesResult delta avoids)

------------------------------------------------------------------------
-- Constructive revision-impact witness, when edited-node membership is
-- decidable. Unlike merely negating avoidance, this produces a
-- concrete old-orbit path to a changed outgoing edge.
-- It remains a finite n-step theorem, not a terminal-census equivalence.
------------------------------------------------------------------------

data OldOrbitHitsEdit {Node : Set}
  (old : Node → Node) (changed : Node → Set) :
  Nat → Node → Set where
  editAtCurrent : ∀ {n v} →
    changed v → OldOrbitHitsEdit old changed (suc n) v
  editFurtherAlong : ∀ {n v} →
    OldOrbitHitsEdit old changed n (old v) →
    OldOrbitHitsEdit old changed (suc n) v

oldOrbitHitOrAvoid :
  ∀ {Node : Set}
    (delta : TypedRevisionDelta Node)
    {n : Nat} {v : Node} →
  ((node : Node) → changedAt delta node ⊎
    (changedAt delta node → ⊥)) →
  OldOrbitHitsEdit (oldLink delta) (changedAt delta) n v
  ⊎
  AvoidsEditedVertices (oldLink delta) (changedAt delta) n v
oldOrbitHitOrAvoid delta {zero} {v} decide = inj₂ avoidsZero
oldOrbitHitOrAvoid delta {suc n} {v} decide with decide v
... | inj₁ edited = inj₁ (editAtCurrent edited)
... | inj₂ unchanged with oldOrbitHitOrAvoid delta {n} {oldLink delta v} decide
...   | inj₁ hit = inj₁ (editFurtherAlong hit)
...   | inj₂ avoids = inj₂ (avoidsStep unchanged avoids)

changedResultWitnessesOldEditedPath :
  ∀ {Node : Set}
    (delta : TypedRevisionDelta Node)
    {n : Nat} {v : Node} →
  ((node : Node) → changedAt delta node ⊎
    (changedAt delta node → ⊥)) →
  (iterate (oldLink delta) n v ≡
   iterate (newLink delta) n v → ⊥) →
  OldOrbitHitsEdit (oldLink delta) (changedAt delta) n v
changedResultWitnessesOldEditedPath delta decide different
  with oldOrbitHitOrAvoid delta decide
... | inj₁ hit = hit
... | inj₂ avoids =
  ⊥-elim
    (different (unchangedOldOrbitPreservesResult delta avoids))

------------------------------------------------------------------------
-- Positive-period eventual-cycle receipts. A zero-length "cycle"
-- is impossible by construction: period = suc periodTail.
-- These are certified observations, NOT a claim that all nodes have
-- already been enumerated in the historical corpus.
------------------------------------------------------------------------

record EventualCycle {Node : Set}
  (next : Node → Node) (start : Node) : Set where
  constructor eventualCycle
  field
    entryHops periodTail : Nat
    representative : Node
    entered :
      iterate next entryHops start ≡ representative
    closed :
      iterate next (suc periodTail) representative ≡ representative
open EventualCycle public

transportEventualCycle :
  ∀ {Node : Set} {old new : Node → Node} {start : Node} →
  (certificate : EventualCycle old start) →
  StablePrefix old new (entryHops certificate) start →
  StablePrefix old new (suc (periodTail certificate))
    (representative certificate) →
  EventualCycle new start
transportEventualCycle certificate entryStable cycleStable =
  eventualCycle
    (entryHops certificate)
    (periodTail certificate)
    (representative certificate)
    (trans (sym (stablePrefixIterate entryStable))
           (entered certificate))
    (trans (sym (stablePrefixIterate cycleStable))
           (closed certificate))

------------------------------------------------------------------------
-- End-to-end finite revision transport: if the old entry prefix and
-- one full certified cycle avoid every changed outgoing link, the
-- old eventual-cycle certificate remains valid for the new version.
-- The representative and positive period are preserved as data.
------------------------------------------------------------------------

oldOrbitAvoidsEditsPreservesCycleCertificate :
  ∀ {Node : Set} (delta : TypedRevisionDelta Node)
    {start : Node} →
  (certificate : EventualCycle (oldLink delta) start) →
  AvoidsEditedVertices (oldLink delta) (changedAt delta)
    (entryHops certificate) start →
  AvoidsEditedVertices (oldLink delta) (changedAt delta)
    (suc (periodTail certificate)) (representative certificate) →
  EventualCycle (newLink delta) start
oldOrbitAvoidsEditsPreservesCycleCertificate delta certificate
    entryAvoid cycleAvoid =
  transportEventualCycle certificate
    (avoidanceImpliesStable delta entryAvoid)
    (avoidanceImpliesStable delta cycleAvoid)

------------------------------------------------------------------------
-- Generic orbit concatenation and positive-period repetitions.
-- Unlike a data-only figure witness, these laws quantify over ANY
-- total first-link graph and any supplied concrete eventual-cycle
-- certificate. They do not construct such a certificate from a raw
-- finite corpus; that algorithm-to-kernel weld remains P2 OPEN.
------------------------------------------------------------------------

iterateAppend :
  ∀ {Node : Set} (next : Node → Node)
    (m n : Nat) (start : Node) →
  iterate next (m + n) start ≡
  iterate next n (iterate next m start)
iterateAppend next zero n start = refl
iterateAppend next (suc m) n start =
  iterateAppend next m n (next start)

positiveCycleRepeats :
  ∀ {Node : Set} (next : Node → Node)
    (period : Nat) (representative : Node) →
  iterate next period representative ≡ representative →
  (k : Nat) →
  iterate next (k * period) representative ≡ representative
positiveCycleRepeats next period representative closed zero = refl
positiveCycleRepeats next period representative closed (suc k) =
  trans (iterateAppend next period (k * period) representative)
    (trans
      (cong (iterate next (k * period)) closed)
      (positiveCycleRepeats next period representative closed k))

eventualCycleReturnsAfterEveryPeriodMultiple :
  ∀ {Node : Set} {next : Node → Node}
    {start : Node} →
  (certificate : EventualCycle next start) →
  (k : Nat) →
  iterate next
    (entryHops certificate + (k * suc (periodTail certificate)))
    start ≡ representative certificate
eventualCycleReturnsAfterEveryPeriodMultiple {next = next}
  {start = start} certificate k =
  trans
    (iterateAppend next
      (entryHops certificate)
      (k * suc (periodTail certificate))
      start)
    (trans
      (cong (iterate next (k * suc (periodTail certificate)))
        (entered certificate))
      (positiveCycleRepeats next (suc (periodTail certificate))
        (representative certificate) (closed certificate) k))

------------------------------------------------------------------------
-- Connection to the canonical revision-indexed FLN owner. A snapshot
-- label is not silently identified with a corpus or a parser run.
------------------------------------------------------------------------

revisionGraphIterate :
  ∀ {Node : Set} →
  FLN.RevisionIndexedFirstLinkGraph Node →
  Nat → Node → Node
revisionGraphIterate graph = iterate (FLN.firstLink graph)

revisionIndexedOrbitStable :
  ∀ {Node : Set}
    (before after : FLN.RevisionIndexedFirstLinkGraph Node)
    {n : Nat} {v : Node} →
  StablePrefix (FLN.firstLink before) (FLN.firstLink after) n v →
  revisionGraphIterate before n v ≡
  revisionGraphIterate after n v
revisionIndexedOrbitStable before after witness =
  stablePrefixIterate witness

------------------------------------------------------------------------
-- Historical local fixture, source-owned by Core. The executable
-- seven-node map encodes only the exact historical core described
-- by the notebook. The full 4.7M-node graph is NOT reconstructed.
------------------------------------------------------------------------

historicalCoreNext : Core.CoreNode → Core.CoreNode
historicalCoreNext Core.awareness = Core.conscious
historicalCoreNext Core.conscious = Core.consciousness
historicalCoreNext Core.consciousness = Core.qualityPhilosophy
historicalCoreNext Core.qualityPhilosophy = Core.philosophy
historicalCoreNext Core.philosophy = Core.reality
historicalCoreNext Core.reality = Core.existence
historicalCoreNext Core.existence = Core.awareness

historicalCorePeriodSeven :
  iterate historicalCoreNext 7 Core.awareness ≡ Core.awareness
historicalCorePeriodSeven = refl

historicalCoreCycleCertificate :
  EventualCycle historicalCoreNext Core.awareness
historicalCoreCycleCertificate =
  eventualCycle 0 6 Core.awareness refl historicalCorePeriodSeven

historicalEdgeAwareness :
  Core.target Core.awarenessToConscious ≡
  historicalCoreNext (Core.source Core.awarenessToConscious)
historicalEdgeAwareness = refl

historicalEdgeClosure :
  Core.target Core.existenceToAwareness ≡
  historicalCoreNext (Core.source Core.existenceToAwareness)
historicalEdgeClosure = refl

------------------------------------------------------------------------
-- No-promotion constraints are preserved by ownership, not guessed
-- from the source-facing Boolean "paid" fields.
------------------------------------------------------------------------

data LocalCycleProofIsFullCorpusReproduction : Set where
data LinkAgreementIsSemanticEquivalence : Set where
data RevisionReachabilityGrantsSourceAuthority : Set where

localCycleDoesNotReproduceCorpus :
  LocalCycleProofIsFullCorpusReproduction → ⊥
localCycleDoesNotReproduceCorpus ()

linkAgreementDoesNotCreateSemanticEquivalence :
  LinkAgreementIsSemanticEquivalence → ⊥
linkAgreementDoesNotCreateSemanticEquivalence ()

revisionReachabilityDoesNotCreateSourceAuthority :
  RevisionReachabilityGrantsSourceAuthority → ⊥
revisionReachabilityDoesNotCreateSourceAuthority ()
