module DASHI.Wikimedia.IbrahimFinitePartialGlobalTrichotomyExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General
import DASHI.Wikimedia.IbrahimFinitePigeonholeProducerExact as Pigeonhole
import DASHI.Wikimedia.IbrahimPartialFirstLinkSemanticsExact as Partial

------------------------------------------------------------------------
-- M3 constructive finite partial-FLN global classification.
--
-- Original first-link research: Ibrahim, Danforth, Dodds (2017),
-- DOI 10.1016/j.jocs.2016.12.001.
-- New DASHI mathematics: totalise temporarily only to *find* a
-- pigeonhole horizon, then check genuine Partial observations.
-- A dead-end and an unresolved target are NEVER asserted to be
-- graph cycles, and the Outside type need not be finite.
--
-- SOURCE-WRITTEN: Agda kernel acceptance at this new head is required.
------------------------------------------------------------------------

totalisedSelection :
  ∀ {Node Outside : Set} →
  (fallback : Node) →
  Partial.FirstLinkSelection Node Outside → Node
totalisedSelection fallback (Partial.knownTarget next) = next
totalisedSelection fallback Partial.explicitDeadEnd = fallback
totalisedSelection fallback (Partial.unresolvedTarget _) = fallback

totalisedNext :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (fallback : Node) → Node → Node
totalisedNext select fallback node =
  totalisedSelection fallback (select node)

knownAdvance :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (node next : Node) →
  select node ≡ Partial.knownTarget next →
  Partial.advancePartial select (Partial.visiting node) ≡
    Partial.visiting next
knownAdvance select node next same rewrite same = refl

deadAdvance :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (node : Node) →
  select node ≡ Partial.explicitDeadEnd →
  Partial.advancePartial select (Partial.visiting node) ≡
    Partial.stoppedAt node
deadAdvance select node same rewrite same = refl

outsideAdvance :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (node : Node) (target : Outside) →
  select node ≡ Partial.unresolvedTarget target →
  Partial.advancePartial select (Partial.visiting node) ≡
    Partial.missingTarget target
outsideAdvance select node target same rewrite same = refl

visitingInjective :
  ∀ {Node Outside : Set} {a b : Node} →
  Partial.visiting {Outside = Outside} a ≡ Partial.visiting b →
  a ≡ b
visitingInjective refl = refl

-- Crucial simulation is ONE-WAY: only paths that remain visiting
-- simulate the totalised graph. The converse would promote terminal
-- fallbacks to real source edges, which is false.
continuingMatchesTotal :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (fallback : Node) (n : Nat) (start finish : Node) →
  Partial.partialIterate select n (Partial.visiting start) ≡
    Partial.visiting finish →
  Orbit.iterate (totalisedNext select fallback) n start ≡ finish
continuingMatchesTotal select fallback zero start finish visited =
  visitingInjective visited
continuingMatchesTotal {Outside = Outside}
  select fallback (suc n) start finish visited
  with select start
... | Partial.knownTarget next =
  continuingMatchesTotal select fallback n next finish visited
... | Partial.explicitDeadEnd =
  ⊥-elim
    (Partial.activeNotDeadEnd {Outside = Outside}
      (trans
        (sym visited)
        (Partial.partialDeadEndAbsorbs select n start)))
... | Partial.unresolvedTarget target =
  ⊥-elim
    (Partial.activeNotMissingTarget
      (trans
        (sym visited)
        (Partial.partialUnresolvedAbsorbs select n target)))

-- If an observation is still visiting at depth prefix+extra, it was
-- also visiting at prefix: terminal observations absorb.
continuingPrefix :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (prefix extra : Nat) (start finish : Node) →
  Partial.partialIterate select (prefix + extra)
    (Partial.visiting start) ≡ Partial.visiting finish →
  Σ Node (λ at →
    Partial.partialIterate select prefix (Partial.visiting start) ≡
      Partial.visiting at)
continuingPrefix {Outside = Outside}
    select prefix extra start finish visited
  with Partial.partialAtEveryFiniteDepth select prefix start
... | Partial.stillVisiting point already = point , already
... | Partial.reachedDeadEnd stopped terminal =
  ⊥-elim
    (Partial.activeNotDeadEnd {Outside = Outside}
      (trans (sym visited)
        (Partial.partialDeadEndPersistsAfterDiscovery
          select prefix extra start stopped terminal)))
... | Partial.reachedUnresolved target terminal =
  ⊥-elim
    (Partial.activeNotMissingTarget
      (trans (sym visited)
        (Partial.partialUnresolvedPersistsAfterDiscovery
          select prefix extra start target terminal)))

-- Unlike a mere three-way observation at one depth, this outcome
-- carries an explicit terminal witness or POSITIVE-GAP repeat of
-- genuine in-carrier visiting states.
data FinitePartialOutcome {Node Outside : Set}
    (select : Node → Partial.FirstLinkSelection Node Outside)
    (start : Node) : Set where
  foundDeadEnd : (depth : Nat) (node : Node) →
    Partial.partialIterate select depth (Partial.visiting start) ≡
      Partial.stoppedAt node →
    FinitePartialOutcome select start
  foundUnresolved : (depth : Nat) (target : Outside) →
    Partial.partialIterate select depth (Partial.visiting start) ≡
      Partial.missingTarget target →
    FinitePartialOutcome select start
  foundPositiveCycle : (entry tail : Nat) (point : Node) →
    Partial.partialIterate select entry (Partial.visiting start) ≡
      Partial.visiting point →
    Partial.partialIterate select (entry + suc tail)
      (Partial.visiting start) ≡ Partial.visiting point →
    FinitePartialOutcome select start

classifyFromTotalRepeat :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (start : Node) →
  General.OrbitRepeat (totalisedNext select start) start →
  FinitePartialOutcome select start
classifyFromTotalRepeat {Outside = Outside} select start repeat
  with Partial.partialAtEveryFiniteDepth select
    (General.entryHops repeat + suc (General.periodTail repeat)) start
... | Partial.reachedDeadEnd stop stopped =
  foundDeadEnd
    (General.entryHops repeat + suc (General.periodTail repeat))
    stop stopped
... | Partial.reachedUnresolved target missing =
  foundUnresolved
    (General.entryHops repeat + suc (General.periodTail repeat))
    target missing
... | Partial.stillVisiting end visited
  with continuingPrefix select (General.entryHops repeat)
    (suc (General.periodTail repeat)) start end visited
...   | entryNode , atEntry =
  foundPositiveCycle
    (General.entryHops repeat) (General.periodTail repeat)
    entryNode atEntry
    (trans visited
      (cong (Partial.visiting {Outside = Outside})
        (trans
          (sym
            (continuingMatchesTotal select start
              (General.entryHops repeat + suc (General.periodTail repeat))
              start end visited))
          (trans
            (General.repeatedVertex repeat)
            (continuingMatchesTotal select start
              (General.entryHops repeat) start entryNode atEntry)))))

finitePartialFLNClassifiesOrTerminates :
  ∀ {Node Outside : Set} →
  (select : Node → Partial.FirstLinkSelection Node Outside) →
  (carrier : General.CompleteFiniteCarrier Node) →
  (start : Node) →
  FinitePartialOutcome select start
finitePartialFLNClassifiesOrTerminates select carrier start =
  classifyFromTotalRepeat select start
    (Pigeonhole.finiteCarrierImpliesEveryStartRepeats
      (totalisedNext select start) carrier start)

-- The use of totalisedNext is an internal constructive search bound,
-- NOT a proof that original terminal observations are self-loops.
-- Publication-original MediaWiki parser, pinned revisions, QIDs and
-- published Zelph source bytes require separate physical evidence.
