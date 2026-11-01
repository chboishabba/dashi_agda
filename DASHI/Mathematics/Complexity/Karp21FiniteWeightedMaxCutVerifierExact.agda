module DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact where

------------------------------------------------------------------------
-- Original: Richard M. Karp (1972), MAX CUT and its positive W.
--
-- DASHI: a *literal*, finite, signed-integer weighted edge-list verifier
-- with a finite Boolean selection certificate and an executable Bool
-- threshold check. Its proof is bidirectional for every finite input.
--
-- This is the SEMANTIC/verifier part of N21 InNP. The independent
-- polynomial tape-clock, binary parser, canonical serialization, and
-- duplicate-edge/symmetry constraints remain exact outstanding lemmas.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool.Base using (T)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
import Data.Integer.Base as Int
open Int using (ℤ; +_; _+_)
import Data.Integer.Properties as IntP
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (refl)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as E20

record SignedUndirectedEdge (n : Nat) : Set where
  constructor edge
  field
    first second : Fin.Fin n
    offDiagonal : first ≡ second → ⊥
    weight : ℤ

open SignedUndirectedEdge public

record WeightedCutGraph (n : Nat) : Set where
  constructor graph
  field
    edges : List (SignedUndirectedEdge n)
    threshold : ℤ
    thresholdPositive : E20.PositiveThreshold threshold

open WeightedCutGraph public

differentLabels : Bool → Bool → Bool
differentLabels true true = false
differentLabels false false = false
differentLabels true false = true
differentLabels false true = true

edgeContribution :
  ∀ {n} →
  SignedUndirectedEdge n →
  Vec.Vec Bool n → ℤ
edgeContribution e labels with
  differentLabels
    (Vec.lookup labels (first e))
    (Vec.lookup labels (second e))
... | true = weight e
... | false = + 0

edgeListCutValue :
  ∀ {n} →
  List (SignedUndirectedEdge n) →
  Vec.Vec Bool n →
  ℤ
edgeListCutValue [] labels = + 0
edgeListCutValue (e ∷ es) labels =
  edgeContribution e labels + edgeListCutValue es labels

cutValue :
  ∀ {n} →
  WeightedCutGraph n → Vec.Vec Bool n → ℤ
cutValue g labels = edgeListCutValue (edges g) labels

-- Decidable threshold check on binary-friendly signed integer values.
-- This *does not* assert polynomial time without a machine semantics.
verifyWeightedMaxCut :
  ∀ {n} →
  WeightedCutGraph n → Vec.Vec Bool n → Bool
verifyWeightedMaxCut g labels =
  Int._≤ᵇ_ (threshold g) (cutValue g labels)

AcceptedCut :
  ∀ {n} →
  WeightedCutGraph n → Vec.Vec Bool n → Set
AcceptedCut g labels =
  Int._≤_ (threshold g) (cutValue g labels)

weightedMaxCutVerifierSound :
  ∀ {n}
    (g : WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  T (verifyWeightedMaxCut g labels) →
  AcceptedCut g labels
weightedMaxCutVerifierSound g labels observed =
  IntP.≤ᵇ⇒≤ observed

weightedMaxCutVerifierComplete :
  ∀ {n}
    (g : WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  AcceptedCut g labels →
  T (verifyWeightedMaxCut g labels)
weightedMaxCutVerifierComplete g labels proof =
  IntP.≤⇒≤ᵇ proof

karpFiniteWeightedMaxCutVerifierIff :
  ∀ {n}
    (g : WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  PR.Iff
    (T (verifyWeightedMaxCut g labels))
    (AcceptedCut g labels)
karpFiniteWeightedMaxCutVerifierIff g labels =
  PR.iff
    (weightedMaxCutVerifierSound g labels)
    (weightedMaxCutVerifierComplete g labels)
