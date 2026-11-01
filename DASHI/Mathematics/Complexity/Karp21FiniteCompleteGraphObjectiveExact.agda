module DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphObjectiveExact where

------------------------------------------------------------------------
-- E20 UNIVERSAL MISSING SAME-OBJECT GRAPH WELD.
--
-- The source is a Vec ℤ n, not a selected witness; the graph is
-- constructed without reading any Boolean bit. For every Vec Bool n,
-- the score of the UNIQUE recursively enumerated upper-triangular
-- signed finite edge list equals Cut.completeGraphCut on the source's
-- position-preserving annotated List (ℤ × Bool).
--
-- Earlier owners: Karp (1972); Karp21PartitionCutQuadraticExact
-- (triangular symbolic source objective); Karp21FiniteCompleteGraphGenerator
-- (Fin n actual graph); Karp21SignedGraphScaleAndAppendExact (list laws).
-- This still requires checked Agda acceptance, unique-pair proof beyond
-- triangular count, fully packed graph Word and polynomial clock.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21PartitionCutQuadraticExact as Partition
import DASHI.Mathematics.Complexity.Karp21SignedGraphScaleAndAppendExact as Scale

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; solve)

annotateVec :
  ∀ {n} → Vec.Vec ℤ n → Vec.Vec Bool n → List (ℤ × Bool)
annotateVec Vec.[] Vec.[] = []
annotateVec (x Vec.∷ xs) (side Vec.∷ rest) =
  (x , side) ∷ annotateVec xs rest

-- All typed head links are indexed by the *tail* vertices only.
headLinkCutScore :
  ∀ {n} →
  List (Gen.HeadLink n) → Bool → Vec.Vec Bool n → ℤ
headLinkCutScore [] first labels = + 0
headLinkCutScore (edge ∷ es) first labels
  with Cut.differentLabels first (Vec.lookup labels (Gen.target edge))
... | true =
  Gen.signedWeight edge + headLinkCutScore es first labels
... | false = headLinkCutScore es first labels

-- Inserting an irrelevant new vertex at the front of the remaining
-- tail shifts every head-link index but does NOT change its cut value.
headLinkCutShift :
  ∀ {n} (es : List (Gen.HeadLink n))
    (head inserted : Bool) (tail : Vec.Vec Bool n) →
  headLinkCutScore (map Gen.promoteHeadLink es)
    head (inserted Vec.∷ tail) ≡
  headLinkCutScore es head tail
headLinkCutShift [] head inserted tail = refl
headLinkCutShift (edge ∷ es) head inserted tail
  with Cut.differentLabels head (Vec.lookup tail (Gen.target edge))
... | true =
  cong (λ value → Gen.signedWeight edge + value)
    (headLinkCutShift es head inserted tail)
... | false =
  headLinkCutShift es head inserted tail

headLinkCutMatchesHistoricalCross :
  ∀ {n} (headValue : ℤ) (tail : Vec.Vec ℤ n)
    (headSide : Bool) (labels : Vec.Vec Bool n) →
  headLinkCutScore (Gen.headLinks headValue tail) headSide labels ≡
  Partition.crossWith headValue headSide (annotateVec tail labels)
headLinkCutMatchesHistoricalCross headValue Vec.[] headSide Vec.[] = refl
headLinkCutMatchesHistoricalCross
  headValue (x Vec.∷ xs) true (true Vec.∷ labels) =
  trans
    (headLinkCutShift
      (Gen.headLinks headValue xs) true true labels)
    (headLinkCutMatchesHistoricalCross
      headValue xs true labels)
headLinkCutMatchesHistoricalCross
  headValue (x Vec.∷ xs) true (false Vec.∷ labels) =
  cong (λ tailScore → (headValue * x) + tailScore)
    (trans
      (headLinkCutShift
        (Gen.headLinks headValue xs) true false labels)
      (headLinkCutMatchesHistoricalCross
        headValue xs true labels))
headLinkCutMatchesHistoricalCross
  headValue (x Vec.∷ xs) false (true Vec.∷ labels) =
  cong (λ tailScore → (headValue * x) + tailScore)
    (trans
      (headLinkCutShift
        (Gen.headLinks headValue xs) false true labels)
      (headLinkCutMatchesHistoricalCross
        headValue xs false labels))
headLinkCutMatchesHistoricalCross
  headValue (x Vec.∷ xs) false (false Vec.∷ labels) =
  trans
    (headLinkCutShift
      (Gen.headLinks headValue xs) false false labels)
    (headLinkCutMatchesHistoricalCross
      headValue xs false labels)

zeroPlus : (x : ℤ) → (+ 0) + x ≡ x
zeroPlus x =
  RingZ.solve 1 (λ v → (Κ (+ 0) ⊕ v , v)) refl x

-- Emit head edges as literal off-diagonal graph edges. One Fin lookup
-- equality, independent of any selected label.
emitHeadLinksScore :
  ∀ {n} (links : List (Gen.HeadLink n))
    (head : Bool) (tail : Vec.Vec Bool n) →
  Cut.edgeListCutValue (map Gen.emitHeadLink links)
    (head Vec.∷ tail) ≡
  headLinkCutScore links head tail
emitHeadLinksScore [] head tail = refl
emitHeadLinksScore (link ∷ links) head tail
  with Cut.differentLabels head (Vec.lookup tail (Gen.target link))
... | true =
  cong (λ value → Gen.signedWeight link + value)
    (emitHeadLinksScore links head tail)
... | false =
  trans
    (cong (λ value → (+ 0) + value)
      (emitHeadLinksScore links head tail))
    (zeroPlus (headLinkCutScore links head tail))

headPairsScoreMatchesHistoricalCross :
  ∀ {n} (x : ℤ) (tail : Vec.Vec ℤ n)
    (head : Bool) (bits : Vec.Vec Bool n) →
  Cut.edgeListCutValue (Gen.headPairs x tail)
    (head Vec.∷ bits) ≡
  Partition.crossWith x head (annotateVec tail bits)
headPairsScoreMatchesHistoricalCross x tail head bits =
  trans
    (emitHeadLinksScore (Gen.headLinks x tail) head bits)
    (headLinkCutMatchesHistoricalCross x tail head bits)

tailGraphPromotionPreservesCut :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n))
    (head : Bool) (tail : Vec.Vec Bool n) →
  Cut.edgeListCutValue (map Gen.promoteTailEdge edges)
    (head Vec.∷ tail) ≡
  Cut.edgeListCutValue edges tail
tailGraphPromotionPreservesCut [] head tail = refl
tailGraphPromotionPreservesCut (e ∷ es) head tail =
  cong₂ _+_ refl
    (tailGraphPromotionPreservesCut es head tail)

-- MAIN EXACT E20 FINITE GRAPH / HISTORICAL OBJECTIVE IFF SEAM.
-- Every input and EVERY bit witness, with signs/duplicates/empty n.
e20CompleteGraphToWeightedCutEdgeListIff :
  ∀ {n} (values : Vec.Vec ℤ n)
    (labels : Vec.Vec Bool n) →
  Cut.edgeListCutValue (Gen.completePairEdges values) labels ≡
  Partition.completeGraphCut (annotateVec values labels)
e20CompleteGraphToWeightedCutEdgeListIff Vec.[] Vec.[] = refl
e20CompleteGraphToWeightedCutEdgeListIff
  (x Vec.∷ xs) (bit Vec.∷ bits) =
  trans
    (Scale.edgeListCutAppend
      (Gen.headPairs x xs)
      (map Gen.promoteTailEdge (Gen.completePairEdges xs))
      (bit Vec.∷ bits))
    (cong₂ _+_
      (headPairsScoreMatchesHistoricalCross x xs bit bits)
      (trans
        (tailGraphPromotionPreservesCut
          (Gen.completePairEdges xs) bit bits)
        (e20CompleteGraphToWeightedCutEdgeListIff xs bits)))

-- The E20 target graph has exactly the scaled weighted cut that
-- appears in the earlier signed Partition reduction, now on Fin n
-- indexed edges with no witness-dependent construction.
e20ScaledIndexedGraphExactCut :
  ∀ {n} (values : Vec.Vec ℤ n)
    (labels : Vec.Vec Bool n) →
  Cut.edgeListCutValue
    (Gen.completeScaledPairEdges values) labels ≡
  (+ 4) *
    Partition.completeGraphCut (annotateVec values labels)
e20ScaledIndexedGraphExactCut values labels =
  trans
    (Scale.scaleEdgeListFourCut (Gen.completePairEdges values) labels)
    (cong (λ score → (+ 4) * score)
      (e20CompleteGraphToWeightedCutEdgeListIff values labels))
