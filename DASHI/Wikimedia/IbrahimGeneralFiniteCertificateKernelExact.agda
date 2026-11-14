module DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit

------------------------------------------------------------------------
-- IBRAHIM FIRST-LINK GENERAL FINITE CERTIFICATE KERNEL
--
-- Original first-link methodology and historical empirical attribution:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's
-- First Link Network", Journal of Computational Science 19 (2017),
-- 21-30, DOI: 10.1016/j.jocs.2016.12.001.
--
-- These are NEW DASHI mathematical proofs on a deterministic first-link
-- carrier. The producer supplies collisions for every starting node;
-- completeness of this evidence is explicit, NOT inferred from a title
-- list. A general pigeonhole producer from finite enumeration alone
-- and the kernel/independent-Python-checker ABI remain OPEN.
------------------------------------------------------------------------

record OrbitRepeat {Node : Set}
    (next : Node → Node) (start : Node) : Set where
  constructor orbitRepeat
  field
    entryHops periodTail : Nat
    repeatedVertex :
      Orbit.iterate next (entryHops + suc periodTail) start
      ≡ Orbit.iterate next entryHops start
open OrbitRepeat public

collisionToEventualCycle :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  OrbitRepeat next start → Orbit.EventualCycle next start
collisionToEventualCycle {next = next} {start = start} collision =
  Orbit.eventualCycle
    (entryHops collision)
    (periodTail collision)
    (Orbit.iterate next (entryHops collision) start)
    refl
    (trans
      (sym (Orbit.iterateAppend next
        (entryHops collision) (suc (periodTail collision)) start))
      (repeatedVertex collision))

eventualCycleToCollision :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  Orbit.EventualCycle next start → OrbitRepeat next start
eventualCycleToCollision {next = next} {start = start} certificate =
  orbitRepeat
    (Orbit.entryHops certificate)
    (Orbit.periodTail certificate)
    (trans
      (Orbit.iterateAppend next
        (Orbit.entryHops certificate)
        (suc (Orbit.periodTail certificate)) start)
      (trans
        (cong (Orbit.iterate next (suc (Orbit.periodTail certificate)))
          (Orbit.entered certificate))
        (trans
          (Orbit.closed certificate)
          (sym (Orbit.entered certificate)))))

------------------------------------------------------------------------
-- Exactly the declared carrier, not all of historical Wikipedia.
------------------------------------------------------------------------

data Listed {Node : Set} (node : Node) : List Node → Set where
  listedHere : ∀ {xs} → Listed node (node ∷ xs)
  listedThere : ∀ {other xs} →
    Listed node xs → Listed node (other ∷ xs)

record CompleteFiniteCarrier (Node : Set) : Set₁ where
  constructor completeFiniteCarrier
  field
    allNodes : List Node
    covers : (node : Node) → Listed node allNodes
open CompleteFiniteCarrier public

record FiniteOrbitRepeatCertificate
    {Node : Set} (next : Node → Node) : Set where
  constructor finiteOrbitRepeatCertificate
  field
    everyStartRepeats : (node : Node) → OrbitRepeat next node
open FiniteOrbitRepeatCertificate public

record VerifiedFiniteFirstLinkCensus
    {Node : Set} (next : Node → Node) : Set₁ where
  constructor verifiedFiniteFirstLinkCensus
  field
    sourceCarrier : CompleteFiniteCarrier Node
    eventCycle : (node : Node) → Orbit.EventualCycle next node
open VerifiedFiniteFirstLinkCensus public

finiteFirstLinkOrbitClassifies :
  ∀ {Node : Set} (next : Node → Node) →
  CompleteFiniteCarrier Node →
  FiniteOrbitRepeatCertificate next →
  VerifiedFiniteFirstLinkCensus next
finiteFirstLinkOrbitClassifies next carrier collisions =
  verifiedFiniteFirstLinkCensus carrier
    (λ node → collisionToEventualCycle
      (everyStartRepeats collisions node))

terminalCensusMatchesCertificate :
  ∀ {Node : Set} {next : Node → Node} →
  (census : VerifiedFiniteFirstLinkCensus next) →
  (node : Node) →
  Orbit.iterate next
    (Orbit.entryHops (eventCycle census node)) node
  ≡ Orbit.representative (eventCycle census node)
terminalCensusMatchesCertificate census node =
  Orbit.entered (eventCycle census node)

-- This equality of selected representatives is an equivalence relation.
-- It is NOT yet cycle-rotation uniqueness: different valid certificates
-- may select different vertices of one cycle.
SameRepresentativeBasin :
  ∀ {Node : Set} {next : Node → Node} →
  VerifiedFiniteFirstLinkCensus next → Node → Node → Set
SameRepresentativeBasin census a b =
  Orbit.representative (eventCycle census a) ≡
  Orbit.representative (eventCycle census b)

sameBasinReflexive :
  ∀ {Node : Set} {next : Node → Node}
    (census : VerifiedFiniteFirstLinkCensus next) →
  (node : Node) → SameRepresentativeBasin census node node
sameBasinReflexive census node = refl

sameBasinSymmetric :
  ∀ {Node : Set} {next : Node → Node}
    (census : VerifiedFiniteFirstLinkCensus next)
    {a b : Node} →
  SameRepresentativeBasin census a b →
  SameRepresentativeBasin census b a
sameBasinSymmetric census = sym

sameBasinTransitive :
  ∀ {Node : Set} {next : Node → Node}
    (census : VerifiedFiniteFirstLinkCensus next)
    {a b c : Node} →
  SameRepresentativeBasin census a b →
  SameRepresentativeBasin census b c →
  SameRepresentativeBasin census a c
sameBasinTransitive census = trans

terminalBasinsPartition :
  ∀ {Node : Set} {next : Node → Node}
    (census : VerifiedFiniteFirstLinkCensus next)
    (node : Node) →
  Σ Node (λ representative →
    Orbit.representative (eventCycle census node) ≡ representative)
terminalBasinsPartition census node =
  Orbit.representative (eventCycle census node) , refl

------------------------------------------------------------------------
-- An old-source reverse closure is a concrete reachability predicate.
-- Excluding this closure preserves ALL finite orbit depths and every
-- declared pointwise consumer. The changed-node predicate need not be
-- decidable for this direction.
------------------------------------------------------------------------

data OldReverseDirtyCone {Node : Set}
  (old : Node → Node) (changed : Node → Set) : Node → Set where
  editedHere : ∀ {node} →
    changed node → OldReverseDirtyCone old changed node
  predecessorOfDirty : ∀ {node} →
    OldReverseDirtyCone old changed (old node) →
    OldReverseDirtyCone old changed node

oldOrbitHitImpliesDirtyCone :
  ∀ {Node : Set}
    (delta : Orbit.TypedRevisionDelta Node)
    {n : Nat} {node : Node} →
  Orbit.OldOrbitHitsEdit
    (Orbit.oldLink delta) (Orbit.changedAt delta) n node →
  OldReverseDirtyCone (Orbit.oldLink delta) (Orbit.changedAt delta) node
oldOrbitHitImpliesDirtyCone delta (Orbit.editAtCurrent edited) =
  editedHere edited
oldOrbitHitImpliesDirtyCone delta (Orbit.editFurtherAlong hit) =
  predecessorOfDirty (oldOrbitHitImpliesDirtyCone delta hit)

outsideConeAvoidsEveryFinitePrefix :
  ∀ {Node : Set} (delta : Orbit.TypedRevisionDelta Node)
    {node : Node} →
  (OldReverseDirtyCone (Orbit.oldLink delta) (Orbit.changedAt delta) node → ⊥) →
  (n : Nat) →
  Orbit.AvoidsEditedVertices
    (Orbit.oldLink delta) (Orbit.changedAt delta) n node
outsideConeAvoidsEveryFinitePrefix delta outside zero =
  Orbit.avoidsZero
outsideConeAvoidsEveryFinitePrefix delta outside (suc n) =
  Orbit.avoidsStep
    (λ edit → outside (editedHere edit))
    (outsideConeAvoidsEveryFinitePrefix delta
      (λ nextDirty → outside (predecessorOfDirty nextDirty)) n)

oldReverseClosureContainsAllChangedOrbitResults :
  ∀ {Node : Set} (delta : Orbit.TypedRevisionDelta Node)
    {node : Node} →
  ((vertex : Node) →
    Orbit.changedAt delta vertex ⊎
    (Orbit.changedAt delta vertex → ⊥)) →
  (n : Nat) →
  (Orbit.iterate (Orbit.oldLink delta) n node
    ≡ Orbit.iterate (Orbit.newLink delta) n node → ⊥) →
  OldReverseDirtyCone (Orbit.oldLink delta) (Orbit.changedAt delta) node
oldReverseClosureContainsAllChangedOrbitResults delta {node}
    decide n difference
  with Orbit.oldOrbitHitOrAvoid delta {n} {node} decide
... | inj₁ hit = oldOrbitHitImpliesDirtyCone delta hit
... | inj₂ avoids =
  ⊥-elim (difference
    (Orbit.unchangedOldOrbitPreservesResult delta avoids))

queryProjectionInvariantOutsideDirtyCone :
  ∀ {Node Outcome : Set}
    (delta : Orbit.TypedRevisionDelta Node)
    (consumer : Node → Outcome) →
  {node : Node} →
  (OldReverseDirtyCone (Orbit.oldLink delta) (Orbit.changedAt delta) node → ⊥) →
  (n : Nat) →
  consumer (Orbit.iterate (Orbit.oldLink delta) n node) ≡
  consumer (Orbit.iterate (Orbit.newLink delta) n node)
queryProjectionInvariantOutsideDirtyCone delta consumer outside n =
  cong consumer
    (Orbit.unchangedOldOrbitPreservesResult delta
      (outsideConeAvoidsEveryFinitePrefix delta outside n))

------------------------------------------------------------------------
-- Nothing here creates source authority, Wikipedia page-identity
-- transport, author-parser parity or a historical data reconstruction.
------------------------------------------------------------------------

data GraphCertificateCreatesWikipediaAuthority : Set where

certificateDoesNotCreateWikipediaAuthority :
  GraphCertificateCreatesWikipediaAuthority → ⊥
certificateDoesNotCreateWikipediaAuthority ()
