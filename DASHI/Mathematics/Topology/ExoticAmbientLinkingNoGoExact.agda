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
