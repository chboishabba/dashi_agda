module DASHI.Mathematics.Topology.ExoticAmbientLinkingNoGoExact where

------------------------------------------------------------------------
-- SAME-ADDRESS / DIFFERENT-EMBEDDING NO-GO.
--
-- Existing source: AlexanderHornedC3FiniteStageExact (PR #1244).
-- Source distinction: symbolic horn addresses alone do not determine
-- ambient 3-space linking, Fox-Artin wildness or Lakes-of-Wada boundary.
-- We prove the elementary information-loss theorem for an explicitly
-- marked finite comparison pair.  The marks are DATA, NOT geometric
-- embeddings. A geometric tame/wild realisation is a separate obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn

record AmbientMarkedAddress : Set where
  constructor marked
  field
    symbolic : Horn.HornAddress
    linkedMarker : Bool

open AmbientMarkedAddress public

canonicalAddress : Horn.HornAddress
canonicalAddress = Horn.address C3.c0 []

unlinkedMarked linkedMarked : AmbientMarkedAddress
unlinkedMarked = marked canonicalAddress false
linkedMarked   = marked canonicalAddress true

sameSymbolicAddress :
  symbolic unlinkedMarked ≡ symbolic linkedMarked
sameSymbolicAddress = refl

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

-- A classifier using ONLY the horn address cannot reproduce the
-- independently supplied linking bit on all ambient-marked entries.
noUniversalAddressOnlyLinkingClassifier :
  (classify : Horn.HornAddress → Bool) →
  ((entry : AmbientMarkedAddress) →
    classify (symbolic entry) ≡ linkedMarker entry) → ⊥
noUniversalAddressOnlyLinkingClassifier classify matches =
  falseNotTrue
    (trans (sym (matches unlinkedMarked)) (matches linkedMarked))

-- The positive remedy is to keep the embedding information typed as
-- separate data; this accessor does NOT prove any knot/link invariant.
markedClassifier : AmbientMarkedAddress → Bool
markedClassifier = linkedMarker

markedClassifierDetectsUnlinked :
  markedClassifier unlinkedMarked ≡ false
markedClassifierDetectsUnlinked = refl

markedClassifierDetectsLinked :
  markedClassifier linkedMarked ≡ true
markedClassifierDetectsLinked = refl


------------------------------------------------------------------------
-- CROSS-POLLINATION FROM LATEST ANIMALEXIC PR #1259:
-- Reuse EXISTING generic query-indexed projection adequacy and
-- recharting-no-go, instead of a second factorisation calculus.
--
-- Blackwell (1953): information comparison conceptual precedent;
-- Crenshaw (1991): situated-information non-factorability motivation;
-- original mathematical query-indexed implementation: DASHI.
-- NONE of these authors is credited with a theorem about a concrete
-- Fox--Artin or Alexander embedded object.
------------------------------------------------------------------------

data AddressQuery : Set where
  askSectorC0 : AddressQuery
  askLinkedMarker : AddressQuery

sectorIsC0 : Horn.HornAddress → Bool
sectorIsC0 (Horn.address C3.c0 _) = true
sectorIsC0 (Horn.address C3.c1 _) = false
sectorIsC0 (Horn.address C3.c2 _) = false

ambientAnswer : AddressQuery → AmbientMarkedAddress → Bool
ambientAnswer askSectorC0 entry = sectorIsC0 (symbolic entry)
ambientAnswer askLinkedMarker entry = linkedMarker entry

ambientSemantics :
  Adequacy.QuerySemantics AmbientMarkedAddress AddressQuery Bool
ambientSemantics = Adequacy.querySemantics ambientAnswer

-- The address IS sufficient for the question about its own sector.
sectorQueryAdequate :
  Adequacy.AdequateFor symbolic ambientSemantics askSectorC0
sectorQueryAdequate = Adequacy.factorsForQuery
  {project = symbolic}
  {semantics = ambientSemantics}
  {query = askSectorC0}
  sectorIsC0
  (λ entry → refl)

-- The very same address loses the INDEPENDENT linked-marker query.
linkQuestionWitness :
  Adequacy.QueryAdequacyDefect symbolic ambientSemantics askLinkedMarker
linkQuestionWitness = Adequacy.queryAdequacyDefect
  {project = symbolic}
  {semantics = ambientSemantics}
  {query = askLinkedMarker}
  unlinkedMarked linkedMarked refl falseNotTrue

linkQuestionCannotFactor :
  Adequacy.AdequateFor symbolic ambientSemantics askLinkedMarker → ⊥
linkQuestionCannotFactor =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    {project = symbolic}
    {semantics = ambientSemantics}
    {query = askLinkedMarker}
    linkQuestionWitness

-- Much STRONGER than testing a fixed address classifier: no possible
-- downstream relabelling, encoding or weighting of the same coarse
-- symbolic address can reconstruct independent marker information.
linkCannotBeRecoveredByAnyAddressRechart :
  ∀ {Recharted : Set} (rechart : Horn.HornAddress → Recharted) →
  NonFactor.FactorsThrough
    (λ entry → rechart (symbolic entry))
    linkedMarker → ⊥
linkCannotBeRecoveredByAnyAddressRechart rechart =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    rechart linkQuestionWitness
