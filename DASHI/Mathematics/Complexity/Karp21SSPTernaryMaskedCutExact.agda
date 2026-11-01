module DASHI.Mathematics.Complexity.Karp21SSPTernaryMaskedCutExact where

------------------------------------------------------------------------
-- TERNARY PNF / SSP / MAX CUT BIDI, with explicit domain separation.
--
-- Reuse golden DASHI.Foundations.SSPTritCarrier {-1,0,+1}.
-- This is a *new partial-cut/graph-mask functional*, not Karp's
-- original binary MAX CUT decision language. For arbitrary signed
-- edge weights, (x_i-x_j)^2 has the three levels 0/1/4.
--
-- Separate induced ACTIVE edges from boundary BLEED edges:
--   Q_ternary(E,x) = Q_induced(E,x) + Q_bleed(E,x).
-- Zero-zero edges contribute 0; active-zero edges contribute 1*w,
-- and active opposing edges contribute 4*w.
--
-- In particular a zero vertex does NOT simply "drop out" from Q:
-- the source original graph contains the bleed contribution unless
-- its boundary edges are explicitly deleted. No claim of equality
-- to dual-Cheeger/signless 1-Laplacian is made.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import Data.Vec.Base as Vec
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact as Spin

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; solve)

tritValue : SSP.SSPTrit → ℤ
tritValue SSP.sspNegOne = - (+ 1)
tritValue SSP.sspZero = + 0
tritValue SSP.sspPosOne = + 1

tritActive : SSP.SSPTrit → Bool
tritActive SSP.sspNegOne = true
tritActive SSP.sspZero = false
tritActive SSP.sspPosOne = true

ternaryGapSquare : SSP.SSPTrit → SSP.SSPTrit → ℤ
ternaryGapSquare a b =
  (tritValue a - tritValue b) *
  (tritValue a - tritValue b)

ternaryEqualGapIsZero :
  (a : SSP.SSPTrit) → ternaryGapSquare a a ≡ + 0
ternaryEqualGapIsZero SSP.sspNegOne = refl
ternaryEqualGapIsZero SSP.sspZero = refl
ternaryEqualGapIsZero SSP.sspPosOne = refl

ternaryZeroPositiveGapIsOne :
  ternaryGapSquare SSP.sspZero SSP.sspPosOne ≡ + 1
ternaryZeroPositiveGapIsOne = refl

ternaryNegativeZeroGapIsOne :
  ternaryGapSquare SSP.sspNegOne SSP.sspZero ≡ + 1
ternaryNegativeZeroGapIsOne = refl

ternaryOppositeGapIsFour :
  ternaryGapSquare SSP.sspNegOne SSP.sspPosOne ≡ + 4
ternaryOppositeGapIsFour = refl

ternaryEnergyEdge :
  ℤ → SSP.SSPTrit → SSP.SSPTrit → ℤ
ternaryEnergyEdge weight a b =
  weight * ternaryGapSquare a b

-- Active-active energy: this is the literal induced-subgraph energy.
-- All boundary and zero-zero edges are excluded.
inducedEnergyEdge :
  ℤ → SSP.SSPTrit → SSP.SSPTrit → ℤ
inducedEnergyEdge w SSP.sspNegOne SSP.sspNegOne =
  ternaryEnergyEdge w SSP.sspNegOne SSP.sspNegOne
inducedEnergyEdge w SSP.sspNegOne SSP.sspPosOne =
  ternaryEnergyEdge w SSP.sspNegOne SSP.sspPosOne
inducedEnergyEdge w SSP.sspPosOne SSP.sspNegOne =
  ternaryEnergyEdge w SSP.sspPosOne SSP.sspNegOne
inducedEnergyEdge w SSP.sspPosOne SSP.sspPosOne =
  ternaryEnergyEdge w SSP.sspPosOne SSP.sspPosOne
inducedEnergyEdge w _ _ = + 0

-- Exactly one neutral endpoint: this is the bleed/excluded-boundary
-- contribution, not a regular binary cut edge.
bleedEnergyEdge :
  ℤ → SSP.SSPTrit → SSP.SSPTrit → ℤ
bleedEnergyEdge w SSP.sspNegOne SSP.sspZero =
  ternaryEnergyEdge w SSP.sspNegOne SSP.sspZero
bleedEnergyEdge w SSP.sspZero SSP.sspNegOne =
  ternaryEnergyEdge w SSP.sspZero SSP.sspNegOne
bleedEnergyEdge w SSP.sspPosOne SSP.sspZero =
  ternaryEnergyEdge w SSP.sspPosOne SSP.sspZero
bleedEnergyEdge w SSP.sspZero SSP.sspPosOne =
  ternaryEnergyEdge w SSP.sspZero SSP.sspPosOne
bleedEnergyEdge w _ _ = + 0

rightZero : (z : ℤ) → z ≡ z + (+ 0)
rightZero z =
  RingZ.solve 1 (λ x → (x , x ⊕ Κ (+ 0))) refl z

leftZero : (z : ℤ) → z ≡ (+ 0) + z
leftZero z =
  RingZ.solve 1 (λ x → (x , Κ (+ 0) ⊕ x)) refl z

-- All nine SSP trit pairs, with no double counting of bleed edges.
ternaryInducedBleedEdge :
  (w : ℤ) (a b : SSP.SSPTrit) →
  ternaryEnergyEdge w a b ≡
  inducedEnergyEdge w a b + bleedEnergyEdge w a b
ternaryInducedBleedEdge w SSP.sspNegOne SSP.sspNegOne =
  rightZero (ternaryEnergyEdge w SSP.sspNegOne SSP.sspNegOne)
ternaryInducedBleedEdge w SSP.sspNegOne SSP.sspZero =
  leftZero (ternaryEnergyEdge w SSP.sspNegOne SSP.sspZero)
ternaryInducedBleedEdge w SSP.sspNegOne SSP.sspPosOne =
  rightZero (ternaryEnergyEdge w SSP.sspNegOne SSP.sspPosOne)
ternaryInducedBleedEdge w SSP.sspZero SSP.sspNegOne =
  leftZero (ternaryEnergyEdge w SSP.sspZero SSP.sspNegOne)
ternaryInducedBleedEdge w SSP.sspZero SSP.sspZero = refl
ternaryInducedBleedEdge w SSP.sspZero SSP.sspPosOne =
  leftZero (ternaryEnergyEdge w SSP.sspZero SSP.sspPosOne)
ternaryInducedBleedEdge w SSP.sspPosOne SSP.sspNegOne =
  rightZero (ternaryEnergyEdge w SSP.sspPosOne SSP.sspNegOne)
ternaryInducedBleedEdge w SSP.sspPosOne SSP.sspZero =
  leftZero (ternaryEnergyEdge w SSP.sspPosOne SSP.sspZero)
ternaryInducedBleedEdge w SSP.sspPosOne SSP.sspPosOne =
  rightZero (ternaryEnergyEdge w SSP.sspPosOne SSP.sspPosOne)

ternaryEnergy :
  ∀ {n : Nat} →
  List (Cut.SignedUndirectedEdge n) →
  Vec.Vec SSP.SSPTrit n → ℤ
ternaryEnergy [] labels = + 0
ternaryEnergy (e ∷ es) labels =
  ternaryEnergyEdge (Cut.weight e)
    (Vec.lookup labels (Cut.first e))
    (Vec.lookup labels (Cut.second e))
  + ternaryEnergy es labels

inducedEnergy :
  ∀ {n : Nat} →
  List (Cut.SignedUndirectedEdge n) →
  Vec.Vec SSP.SSPTrit n → ℤ
inducedEnergy [] labels = + 0
inducedEnergy (e ∷ es) labels =
  inducedEnergyEdge (Cut.weight e)
    (Vec.lookup labels (Cut.first e))
    (Vec.lookup labels (Cut.second e))
  + inducedEnergy es labels

bleedEnergy :
  ∀ {n : Nat} →
  List (Cut.SignedUndirectedEdge n) →
  Vec.Vec SSP.SSPTrit n → ℤ
bleedEnergy [] labels = + 0
bleedEnergy (e ∷ es) labels =
  bleedEnergyEdge (Cut.weight e)
    (Vec.lookup labels (Cut.first e))
    (Vec.lookup labels (Cut.second e))
  + bleedEnergy es labels

associateTernaryTerms : (a b c d : ℤ) →
  (a + b) + (c + d) ≡ (a + c) + (b + d)
associateTernaryTerms a b c d =
  RingZ.solve 4
    (λ a b c d →
      ((a ⊕ b) ⊕ (c ⊕ d)
       , (a ⊕ c) ⊕ (b ⊕ d)))
    refl a b c d

-- Universal exact active/neutral split for ANY signed weighted edge
-- list, no graph-index conversion, no "don't care" leakage assumption.
ternaryEnergyExactlyInducedPlusBleed :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec SSP.SSPTrit n) →
  ternaryEnergy edges labels ≡
  inducedEnergy edges labels + bleedEnergy edges labels
ternaryEnergyExactlyInducedPlusBleed [] labels = refl
ternaryEnergyExactlyInducedPlusBleed (e ∷ es) labels =
  trans
    (cong₂ _+_
      (ternaryInducedBleedEdge (Cut.weight e)
        (Vec.lookup labels (Cut.first e))
        (Vec.lookup labels (Cut.second e)))
      (ternaryEnergyExactlyInducedPlusBleed es labels))
    (associateTernaryTerms
      (inducedEnergyEdge (Cut.weight e)
        (Vec.lookup labels (Cut.first e))
        (Vec.lookup labels (Cut.second e)))
      (bleedEnergyEdge (Cut.weight e)
        (Vec.lookup labels (Cut.first e))
        (Vec.lookup labels (Cut.second e)))
      (inducedEnergy es labels)
      (bleedEnergy es labels))

boolToSSPTrit : Bool → SSP.SSPTrit
boolToSSPTrit true = SSP.sspPosOne
boolToSSPTrit false = SSP.sspNegOne

binaryToSSPTritLabels :
  ∀ {n} → Vec.Vec Bool n → Vec.Vec SSP.SSPTrit n
binaryToSSPTritLabels Vec.[] = Vec.[]
binaryToSSPTritLabels (bit Vec.∷ tail) =
  boolToSSPTrit bit Vec.∷ binaryToSSPTritLabels tail

binaryTernaryEdgeQuadratic :
  (w : ℤ) (a b : Bool) →
  ternaryEnergyEdge w (boolToSSPTrit a) (boolToSSPTrit b) ≡
  w * Spin.spinGapSquare a b
binaryTernaryEdgeQuadratic w true true = refl
binaryTernaryEdgeQuadratic w true false = refl
binaryTernaryEdgeQuadratic w false true = refl
binaryTernaryEdgeQuadratic w false false = refl

binaryTernaryEdgeListSpecialization :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  ternaryEnergy edges (binaryToSSPTritLabels labels) ≡
  Spin.signedLaplacianQuadratic edges labels
binaryTernaryEdgeListSpecialization [] labels = refl
binaryTernaryEdgeListSpecialization (e ∷ es) labels =
  cong₂ _+_
    (binaryTernaryEdgeQuadratic (Cut.weight e)
      (Vec.lookup labels (Cut.first e))
      (Vec.lookup labels (Cut.second e)))
    (binaryTernaryEdgeListSpecialization es labels)
