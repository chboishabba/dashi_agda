module DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact where

------------------------------------------------------------------------
-- UNIVERSAL SOURCE-ONLY finite Karp PARTITION -> weighted MAX CUT graph.
-- INPUT: a Vec ℤ n. NO access to any Boolean cut witness.
--
-- For each head x and remaining y, emit one ordered off-diagonal edge
-- with signed integer weight x*y (unscaled); later source-owned
-- scaleEdgeListFour changes it to 4*x*y, and threshold T².
-- The recursive construction emits exactly the upper triangle by
-- 0-first head/tail split. Fin constructors encode vertex indices
-- and each edge carries its own off-diagonal impossibility proof.
--
-- E20 still requires a SAME-OBJECT theorem identifying its cut score
-- with the old Cut.completeGraphCut over zip(weights,labels), plus
-- unique orientation/pair coverage and binary machine-time bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; map)

import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedGraphScaleAndAppendExact as Scale

-- The Fin.suc constructor is injective, unlike an arbitrary graph
-- quotient. This transports the NO-LOOP proof under vertex lifting.
finSuccessorInjective :
  ∀ {n} {i j : Fin.Fin n} →
  Fin.suc i ≡ Fin.suc j → i ≡ j
finSuccessorInjective refl = refl

promoteTailEdge :
  ∀ {n} →
  Cut.SignedUndirectedEdge n →
  Cut.SignedUndirectedEdge (suc n)
promoteTailEdge e =
  Cut.edge
    (Fin.suc (Cut.first e))
    (Fin.suc (Cut.second e))
    (λ equal →
      Cut.offDiagonal e (finSuccessorInjective equal))
    (Cut.weight e)

-- A head-edge destination is always Fin.suc i, never the head's 0.
-- We increment its tail index when a new head-tail vertex is inserted.
promoteHeadEdge :
  ∀ {n} →
  Cut.SignedUndirectedEdge (suc n) →
  Cut.SignedUndirectedEdge (suc (suc n))
promoteHeadEdge e =
  Cut.edge Fin.zero (Fin.suc (Cut.second e)) (λ ())
    (Cut.weight e)

headPairs :
  ∀ {n} → ℤ → Vec.Vec ℤ n →
  List (Cut.SignedUndirectedEdge (suc n))
headPairs x Vec.[] = []
headPairs {suc n} x (y Vec.∷ ys) =
  Cut.edge Fin.zero (Fin.suc Fin.zero) (λ ()) (x * y)
  ∷ map promoteHeadEdge (headPairs x ys)

-- Graph construction depends *only* on signed source weights.
-- This construction is total for empty/singleton vectors too.
completePairEdges :
  ∀ {n} → Vec.Vec ℤ n →
  List (Cut.SignedUndirectedEdge n)
completePairEdges Vec.[] = []
completePairEdges (x Vec.∷ xs) =
  headPairs x xs ++ map promoteTailEdge (completePairEdges xs)

completeScaledPairEdges :
  ∀ {n} → Vec.Vec ℤ n →
  List (Cut.SignedUndirectedEdge n)
completeScaledPairEdges source =
  Scale.scaleEdgeListFour (completePairEdges source)

headPairsEmpty : (x : ℤ) →
  headPairs x Vec.[] ≡ []
headPairsEmpty x = refl

completePairEdgesEmpty :
  completePairEdges Vec.[] ≡ []
completePairEdgesEmpty = refl

completePairEdgesSingleton : (x : ℤ) →
  completePairEdges (x Vec.∷ Vec.[]) ≡ []
completePairEdgesSingleton x = refl


------------------------------------------------------------------------
-- Exactly n(n-1)/2 emitted edges (structural upper-triangle count).
-- This is independent of the binary cut assignment and edge weights.
------------------------------------------------------------------------

headPairCount :
  ∀ {n} (x : ℤ) (rest : Vec.Vec ℤ n) →
  Data.List.Base.length (headPairs x rest) ≡ n
headPairCount x Vec.[] = refl
headPairCount x (y Vec.∷ ys)
  rewrite ListP.length-map promoteHeadEdge (headPairs x ys)
        | headPairCount x ys = refl

triangularPairCount : Nat → Nat
triangularPairCount zero = zero
triangularPairCount (suc n) = n + triangularPairCount n

completePairCount :
  ∀ {n} (source : Vec.Vec ℤ n) →
  Data.List.Base.length (completePairEdges source) ≡
  triangularPairCount n
completePairCount Vec.[] = refl
completePairCount (x Vec.∷ xs)
  rewrite ListP.length-++ (headPairs x xs)
      (map promoteTailEdge (completePairEdges xs))
        | ListP.length-map promoteTailEdge (completePairEdges xs)
        | headPairCount x xs
        | completePairCount xs = refl
