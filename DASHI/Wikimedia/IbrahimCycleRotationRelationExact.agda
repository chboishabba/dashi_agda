module DASHI.Wikimedia.IbrahimCycleRotationRelationExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General

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


------------------------------------------------------------------------
-- A2a-A2e: GENERAL uniqueness of eventual cycles up to original-graph
-- rotation. Unlike the earlier ordered-entry lemma, NO comparison,
-- period decomposition or rotation witness is passed by the caller.
------------------------------------------------------------------------

mutualOrbitRotationReflexive :
  ∀ {Node : Set} {next : Node → Node} {a : Node} →
  MutualOrbitRotation next a a
mutualOrbitRotationReflexive =
  mutualOrbitRotation (forwardRotation zero refl)
    (forwardRotation zero refl)

mutualOrbitRotationSym :
  ∀ {Node : Set} {next : Node → Node} {a b : Node} →
  MutualOrbitRotation next a b → MutualOrbitRotation next b a
mutualOrbitRotationSym (mutualOrbitRotation fwd bwd) =
  mutualOrbitRotation bwd fwd

mutualOrbitRotationTransitive :
  ∀ {Node : Set} {next : Node → Node} {a b c : Node} →
  MutualOrbitRotation next a b →
  MutualOrbitRotation next b c →
  MutualOrbitRotation next a c
mutualOrbitRotationTransitive
  (mutualOrbitRotation ab ba) (mutualOrbitRotation bc cb) =
  mutualOrbitRotation
    (forwardRotationTransitive ab bc)
    (forwardRotationTransitive cb ba)

periodicPointEveryOffsetIsMutualRotation :
  ∀ {Node : Set} (next : Node → Node) →
  (periodTail : Nat) (point : Node) →
  Orbit.iterate next (suc periodTail) point ≡ point →
  (k : Nat) →
  MutualOrbitRotation next point (Orbit.iterate next k point)
periodicPointEveryOffsetIsMutualRotation next tail point closes k =
  mutualOrbitRotation
    (forwardRotation k refl)
    (forwardRotation (k * tail)
      (trans
        (sym (Orbit.iterateAppend next k (k * tail) point))
        (trans
          (cong (λ index → Orbit.iterate next index point)
            (sym (*-suc k tail)))
          (Orbit.positiveCycleRepeats next (suc tail) point
            closes k))))

earlierEntryGivesMutualRotation :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  (first second : Orbit.EventualCycle next start) →
  Orbit.entryHops first ≤ Orbit.entryHops second →
  MutualOrbitRotation next
    (Orbit.representative first) (Orbit.representative second)
earlierEntryGivesMutualRotation {next = next} first second ordered =
  subst
    (λ target → MutualOrbitRotation next
      (Orbit.representative first) target)
    (laterEntryIsForwardRotation first second
      (Orbit.entryHops second ∸ Orbit.entryHops first)
      (sym (m+[n∸m]≡n ordered)))
    (periodicPointEveryOffsetIsMutualRotation next
      (Orbit.periodTail first)
      (Orbit.representative first)
      (Orbit.closed first)
      (Orbit.entryHops second ∸ Orbit.entryHops first))

terminalCycleUniqueUpToRotation :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  (first second : Orbit.EventualCycle next start) →
  MutualOrbitRotation next
    (Orbit.representative first) (Orbit.representative second)
terminalCycleUniqueUpToRotation first second
  with ≤-total (Orbit.entryHops first) (Orbit.entryHops second)
... | inj₁ first≤second =
  earlierEntryGivesMutualRotation first second first≤second
... | inj₂ second≤first =
  mutualOrbitRotationSym
    (earlierEntryGivesMutualRotation second first second≤first)

------------------------------------------------------------------------
-- A2f: canonical roots are UNIQUE whenever a least-root certificate
-- is provided for a total antisymmetric ordering. Finding such a root
-- algorithmically from the finite carrier is a DISTINCT producer gate.
------------------------------------------------------------------------

record CanonicalCycleRoot {Node : Set}
    (next : Node → Node)
    (order : Node → Node → Set)
    (start : Node) : Set where
  constructor canonicalCycleRoot
  field
    root : Node
    onCycle : MutualOrbitRotation next start root
    minimal : (other : Node) →
      MutualOrbitRotation next start other → order root other

canonicalCycleRepresentativeUnique :
  ∀ {Node : Set} {next : Node → Node} {start : Node}
    {order : Node → Node → Set} →
  (antisymmetric : ∀ {a b} → order a b → order b a → a ≡ b) →
  (first second : Orbit.EventualCycle next start) →
  (firstRoot : CanonicalCycleRoot next order
    (Orbit.representative first)) →
  (secondRoot : CanonicalCycleRoot next order
    (Orbit.representative second)) →
  CanonicalCycleRoot.root firstRoot ≡
    CanonicalCycleRoot.root secondRoot
canonicalCycleRepresentativeUnique antisymmetric first second
    firstRoot secondRoot =
  antisymmetric
    (CanonicalCycleRoot.minimal firstRoot
      (CanonicalCycleRoot.root secondRoot)
      (mutualOrbitRotationTransitive
        (terminalCycleUniqueUpToRotation first second)
        (CanonicalCycleRoot.onCycle secondRoot)))
    (CanonicalCycleRoot.minimal secondRoot
      (CanonicalCycleRoot.root firstRoot)
      (mutualOrbitRotationTransitive
        (mutualOrbitRotationSym
          (terminalCycleUniqueUpToRotation first second))
        (CanonicalCycleRoot.onCycle firstRoot)))

------------------------------------------------------------------------
-- A2g: intrinsic basin membership is mutual orbit reachability of
-- terminal representatives, NOT arbitrary selected-label equality.
------------------------------------------------------------------------

IntrinsicTerminalSameBasin :
  ∀ {Node : Set} {next : Node → Node} →
  General.VerifiedFiniteFirstLinkCensus next → Node → Node → Set
IntrinsicTerminalSameBasin {next = next} census a b =
  MutualOrbitRotation next
    (Orbit.representative (General.eventCycle census a))
    (Orbit.representative (General.eventCycle census b))

terminalBasinsPartitionByCycle :
  ∀ {Node : Set} {next : Node → Node} →
  (census : General.VerifiedFiniteFirstLinkCensus next) →
  General.BasinEquivalence Node (IntrinsicTerminalSameBasin census)
terminalBasinsPartitionByCycle census =
  General.basinEquivalence
    (λ node → mutualOrbitRotationReflexive)
    mutualOrbitRotationSym
    mutualOrbitRotationTransitive

terminalBasinIndependentOfCertificateChoice :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  (first second : Orbit.EventualCycle next start) →
  MutualOrbitRotation next
    (Orbit.representative first)
    (Orbit.representative second)
terminalBasinIndependentOfCertificateChoice =
  terminalCycleUniqueUpToRotation

-- Everything above concerns total deterministic graph orbits only.
-- Neither Wikipedia source provenance nor canonical-root EXISTENCE is
-- created by the intrinsic rotation-equivalence proof.
