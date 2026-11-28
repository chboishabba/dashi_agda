module DASHI.Cognition.PNF.X369CommutingHistorySeparatorExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Geometry-forward collision: commuting semantic actions do NOT imply
-- history-annotated consumer equivalence. Arbitrary suffixes are retained.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F
import DASHI.Cognition.PNF.X369ConstructiveConsumerSplitExact as Split

module Witness {Semantic : Set}
  (action : Split.Literal → Semantic → Semantic)
  (abCommute : (z : Semantic) →
    action Split.b (action Split.a z) ≡
    action Split.a (action Split.b z)) where

  run : List Split.Literal → Semantic → Semantic
  run [] z = z
  run (u ∷ us) z = run us (action u z)

  semanticCollision : (suffix : List Split.Literal) (z : Semantic) →
    run (Split.a ∷ Split.b ∷ suffix) z ≡
    run (Split.b ∷ Split.a ∷ suffix) z
  semanticCollision suffix z =
    F.cong (run suffix) (abCommute z)

  memoryA : (suffix : List Split.Literal) →
    Split.runLatch (Split.a ∷ Split.b ∷ suffix) Split.unset ≡ Split.firstA
  memoryA = Split.abPrefix

  memoryB : (suffix : List Split.Literal) →
    Split.runLatch (Split.b ∷ Split.a ∷ suffix) Split.unset ≡ Split.firstB
  memoryB = Split.baPrefix

  -- Any observer that sees only the endpoint necessarily identifies the
  -- commuting pair. An observer that retains the initial literal cannot.
  cannotFactorFirstThroughEndpoint :
    (suffix : List Split.Literal) (z : Semantic) →
    (read : Semantic → Split.Latch) →
    ((word : List Split.Literal) →
      read (run word z) ≡ Split.runLatch word Split.unset) → ⊥
  cannotFactorFirstThroughEndpoint suffix z read exact =
    Split.distinct
      (F.trans (F.sym (exact (Split.a ∷ Split.b ∷ suffix)))
        (F.trans (F.cong read (semanticCollision suffix z))
          (exact (Split.b ∷ Split.a ∷ suffix))))
