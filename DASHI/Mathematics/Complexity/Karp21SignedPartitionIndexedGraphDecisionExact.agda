module DASHI.Mathematics.Complexity.Karp21SignedPartitionIndexedGraphDecisionExact where

------------------------------------------------------------------------
-- E20: SOURCE LIST → SAME-OBJECT INDEXED GRAPH DECISION.
--
-- The Karp source list is the canonical finite input; its Boolean
-- selection is a dependent list witness. Compile both into Vec carriers
-- WITHOUT choosing a witness during graph construction. Then weld the
-- indexed graph cut to the original completeGraphCut expression and
-- transport the existential yes-iff. This closes the gap between typed
-- "algebraic target" and the actual finite weighted edge-list carrier.
--
-- Binary Word serialization, malformed input and real machine clock
-- remain unproved obligations. Source: Karp 1972 + DASHI #1445 owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

import Data.Vec.Base as Vec
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Integer.Base as Int
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21PartitionCutQuadraticExact as Quadratic
import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact as Source
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphObjectiveExact as Exact
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut

vectorOfList : (parts : List ℤ) → Vec.Vec ℤ (length parts)
vectorOfList [] = Vec.[]
vectorOfList (x ∷ xs) = x Vec.∷ vectorOfList xs

labelsOfSelection :
  (parts : List ℤ) →
  Source.Selection parts →
  Vec.Vec Bool (length parts)
labelsOfSelection [] tt = Vec.[]
labelsOfSelection (x ∷ xs) (bit , tail) =
  bit Vec.∷ labelsOfSelection xs tail

annotatedListIsSameObject :
  (parts : List ℤ)
  (choice : Source.Selection parts) →
  Exact.annotateVec
    (vectorOfList parts)
    (labelsOfSelection parts choice) ≡
  Source.annotate parts choice
annotatedListIsSameObject [] tt = refl
annotatedListIsSameObject (x ∷ xs) (bit , tail) =
  cong (λ remainder → (x , bit) ∷ remainder)
    (annotatedListIsSameObject xs tail)

-- The graph target is computed from parts alone; the cut labels only
-- enter its verifier, never its deterministic complete-edge map.
indexedSignedGraphCutSourceScore :
  (parts : List ℤ)
  (choice : Source.Selection parts) →
  Cut.edgeListCutValue
    (Gen.completeScaledPairEdges (vectorOfList parts))
    (labelsOfSelection parts choice) ≡
  (+ 4) * Quadratic.completeGraphCut
    (Source.annotate parts choice)
indexedSignedGraphCutSourceScore parts choice =
  trans
    (Exact.e20ScaledIndexedGraphExactCut
      (vectorOfList parts)
      (labelsOfSelection parts choice))
    (cong (λ score → (+ 4) * score)
      (annotatedListIsSameObject parts choice))

-- THIS is the actual indexed finite weighted graph threshold predicate.
IndexedScaledCutYES : List ℤ → Set
IndexedScaledCutYES parts =
  Σ (Source.Selection parts)
    (λ choice →
      Int._≤_
        (Source.sourceTotal parts * Source.sourceTotal parts)
        (Cut.edgeListCutValue
          (Gen.completeScaledPairEdges (vectorOfList parts))
          (labelsOfSelection parts choice)))

algebraicToIndexedCutYES :
  (parts : List ℤ) →
  Source.ScaledCutYES parts → IndexedScaledCutYES parts
algebraicToIndexedCutYES parts (choice , accepted) =
  choice ,
    subst
      (λ score →
        Int._≤_ (Source.sourceTotal parts * Source.sourceTotal parts)
          score)
      (sym (indexedSignedGraphCutSourceScore parts choice))
      accepted

indexedCutToAlgebraicYES :
  (parts : List ℤ) →
  IndexedScaledCutYES parts → Source.ScaledCutYES parts
indexedCutToAlgebraicYES parts (choice , accepted) =
  choice ,
    subst
      (λ score →
        Int._≤_ (Source.sourceTotal parts * Source.sourceTotal parts)
          score)
      (indexedSignedGraphCutSourceScore parts choice)
      accepted

karpPartitionActualIndexedGraphYESIff :
  (parts : List ℤ) →
  PR.Iff (Source.PartitionYES parts) (IndexedScaledCutYES parts)
karpPartitionActualIndexedGraphYESIff parts =
  PR.iffTransitive
    (Source.signedPartitionScaledCutInstanceIff parts)
    (PR.iff
      (algebraicToIndexedCutYES parts)
      (indexedCutToAlgebraicYES parts))

-- Guarded positive-threshold Karp target, including T=0 exceptional
-- instance. In the nonzero case its representation is the actual
-- finite graph; the unit-YES case is a fixed two-node edge with W=1.
IndexedPositiveTargetAccepts : Source.PositiveCutTarget → Set
IndexedPositiveTargetAccepts Source.unitEdgeYesPositive = ⊤
IndexedPositiveTargetAccepts (Source.scaledCompletePositive parts _) =
  IndexedScaledCutYES parts

sourcePartitionToIndexedPositiveTarget :
  (parts : List ℤ) → Source.PositiveCutTarget
sourcePartitionToIndexedPositiveTarget =
  Source.totalPartitionToPositiveCut

sourcePartitionIndexedPositiveTargetIff :
  (parts : List ℤ) →
  PR.Iff
    (Source.PartitionYES parts)
    (IndexedPositiveTargetAccepts
      (sourcePartitionToIndexedPositiveTarget parts))
sourcePartitionIndexedPositiveTargetIff parts
  with Int._≟_ (Source.sourceTotal parts) (+ 0)
... | yes zeroSum =
  PR.iff (λ _ → tt) (λ _ → Source.zeroTotalPartitionYES parts zeroSum)
... | no notZero =
  karpPartitionActualIndexedGraphYESIff parts
