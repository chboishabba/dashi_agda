module DASHI.Mathematics.Complexity.Karp21SignedGraphScaleAndAppendExact where

------------------------------------------------------------------------
-- Original: Richard M. Karp (1972), weighted MAX CUT.
-- DASHI formal exact finite-graph algebra:
--
--  (A) CUT(E ++ F, bits) = CUT(E,bits) + CUT(F,bits).
--  (B) CUT(map (w ↦ 4w) E,bits) = 4 CUT(E,bits).
--  (C) CUT(map (w ↦ 4w) E,bits) = LaplacianQuadratic(E,bits)
--      for ±1 spins, *including signed negative and zero weights*.
--
-- This removes a concrete E20 signed-scaling semantic duplication: all
-- three statements are about the SAME finite indexed undirected edge list
-- and the SAME Vec Bool n label certificate. It does NOT produce a
-- source PARTITION vector -> canonical distinct unordered graph pairs,
-- target Word serializer, or machine-polynomial bit-cost proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import Data.Vec.Base as Vec
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact as Lap

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; solve)

edgeListCutAppend :
  ∀ {n : Nat}
    (first second : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  Cut.edgeListCutValue (first ++ second) labels ≡
  Cut.edgeListCutValue first labels +
  Cut.edgeListCutValue second labels
edgeListCutAppend [] second labels =
  sym
    (RingZ.solve 1
      (λ x → (Κ (+ 0) ⊕ x , x))
      refl (Cut.edgeListCutValue second labels))
edgeListCutAppend (e ∷ es) second labels =
  trans
    (cong (λ remainder → Cut.edgeContribution e labels + remainder)
      (edgeListCutAppend es second labels))
    (RingZ.solve 3
      (λ head tail rest →
        (head ⊕ (tail ⊕ rest)
        , (head ⊕ tail) ⊕ rest))
      refl
      (Cut.edgeContribution e labels)
      (Cut.edgeListCutValue es labels)
      (Cut.edgeListCutValue second labels))

scaleEdgeWeightFour :
  ∀ {n : Nat} →
  Cut.SignedUndirectedEdge n → Cut.SignedUndirectedEdge n
scaleEdgeWeightFour e =
  Cut.edge
    (Cut.first e)
    (Cut.second e)
    (Cut.offDiagonal e)
    ((+ 4) * Cut.weight e)

scaleEdgeListFour :
  ∀ {n : Nat} →
  List (Cut.SignedUndirectedEdge n) →
  List (Cut.SignedUndirectedEdge n)
scaleEdgeListFour = map scaleEdgeWeightFour

scaleEdgeFourContribution :
  ∀ {n : Nat} (e : Cut.SignedUndirectedEdge n)
    (labels : Vec.Vec Bool n) →
  Cut.edgeContribution (scaleEdgeWeightFour e) labels ≡
  (+ 4) * Cut.edgeContribution e labels
scaleEdgeFourContribution e labels
  with Cut.differentLabels
    (Vec.lookup labels (Cut.first e))
    (Vec.lookup labels (Cut.second e))
... | true = refl
... | false = sym Lap.fourTimesZeroIsZero

scaleEdgeListFourCut :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  Cut.edgeListCutValue (scaleEdgeListFour edges) labels ≡
  (+ 4) * Cut.edgeListCutValue edges labels
scaleEdgeListFourCut [] labels =
  sym Lap.fourTimesZeroIsZero
scaleEdgeListFourCut (e ∷ es) labels =
  trans
    (cong₂ _+_
      (scaleEdgeFourContribution e labels)
      (scaleEdgeListFourCut es labels))
    (sym (Lap.fourDistributesOverSum
      (Cut.edgeContribution e labels)
      (Cut.edgeListCutValue es labels)))

scaledSignedGraphCutEqualsSpinQuadratic :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  Cut.edgeListCutValue (scaleEdgeListFour edges) labels ≡
  Lap.signedLaplacianQuadratic edges labels
scaledSignedGraphCutEqualsSpinQuadratic edges labels =
  trans
    (scaleEdgeListFourCut edges labels)
    (Lap.karpCutEqualsSignedLaplacianQuadratic edges labels)
