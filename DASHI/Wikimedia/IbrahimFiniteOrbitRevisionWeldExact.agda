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
