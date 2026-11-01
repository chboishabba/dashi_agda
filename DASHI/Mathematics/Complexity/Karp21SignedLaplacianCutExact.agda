module DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact where

------------------------------------------------------------------------
-- ORIGINAL AUTHORITY: Richard M. Karp (1972), weighted MAX CUT.
-- Mathematical identity: for spins s_i in {-1,+1},
--      4 CUT = sum_(undirected edges ij) w_ij (s_i - s_j)^2.
--
-- DASHI CONTRIBUTION:
-- Reuse the *existing* literal signed-weight edge-list witness verifier
-- from Karp21FiniteWeightedMaxCutVerifierExact, not an AO/eigen summary.
-- Prove the exact combinatorial-to-quadratic same-object bridge on that
-- very edge list, including negative edge weights.
--
-- Signed Laplacian Q is NOT assumed positive semidefinite; a negative
-- Karp edge destroys the unrestricted Rayleigh/min-eigenvalue shortcut.
-- The spectral/eigen, AO Pareto and provenance work may propose witnesses
-- or algorithmic priorities; no eigenvalue bound or PTAS or NP-hardness
-- conclusion follows merely from this algebra.
--
-- Provenance of reuse: DASHI/Interop/PNFSpectralFieldGraph.agda
-- (signed residual graph is an *evidence class*, not a Karp instance);
-- DASHI #1415/#1416 world/sub-eigen and hierarchical Pareto boundaries;
-- DASHI #1438 graph-colouring weighted-cut instance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

spin : Bool → ℤ
spin true = + 1
spin false = -[1+ 0 ]

-- Keep the signed integer `w` throughout, including w < 0.
spinGapSquare : Bool → Bool → ℤ
spinGapSquare a b =
  (spin a - spin b) * (spin a - spin b)

bitCutWeight : ℤ → Bool → Bool → ℤ
bitCutWeight w true true = + 0
bitCutWeight w false false = + 0
bitCutWeight w true false = w
bitCutWeight w false true = w

spinGapTrueTrue : spinGapSquare true true ≡ + 0
spinGapTrueTrue = refl

spinGapFalseFalse : spinGapSquare false false ≡ + 0
spinGapFalseFalse = refl

spinGapTrueFalse : spinGapSquare true false ≡ + 4
spinGapTrueFalse = refl

spinGapFalseTrue : spinGapSquare false true ≡ + 4
spinGapFalseTrue = refl

-- The four Boolean cases are exhaustive, including signed w.
fourCutEqualsSpinQuadratic :
  (weight : ℤ) (a b : Bool) →
  (+ 4) * bitCutWeight weight a b ≡
  weight * spinGapSquare a b
fourCutEqualsSpinQuadratic weight true true =
  RingZ.solve 1
    (λ w → (Κ (+ 4) ⊗ Κ (+ 0) , w ⊗ Κ (+ 0)))
    refl weight
fourCutEqualsSpinQuadratic weight true false =
  RingZ.solve 1
    (λ w → (Κ (+ 4) ⊗ w , w ⊗ Κ (+ 4)))
    refl weight
fourCutEqualsSpinQuadratic weight false true =
  RingZ.solve 1
    (λ w → (Κ (+ 4) ⊗ w , w ⊗ Κ (+ 4)))
    refl weight
fourCutEqualsSpinQuadratic weight false false =
  RingZ.solve 1
    (λ w → (Κ (+ 4) ⊗ Κ (+ 0) , w ⊗ Κ (+ 0)))
    refl weight

edgeSpinQuadratic :
  ∀ {n : Nat} →
  Cut.SignedUndirectedEdge n →
  Vec.Vec Bool n → ℤ
edgeSpinQuadratic e labels =
  Cut.weight e *
    spinGapSquare
      (Vec.lookup labels (Cut.first e))
      (Vec.lookup labels (Cut.second e))

edgeContributionMatchesBitCut :
  ∀ {n : Nat} (e : Cut.SignedUndirectedEdge n)
    (labels : Vec.Vec Bool n) →
  Cut.edgeContribution e labels ≡
  bitCutWeight (Cut.weight e)
    (Vec.lookup labels (Cut.first e))
    (Vec.lookup labels (Cut.second e))
edgeContributionMatchesBitCut e labels
  with Vec.lookup labels (Cut.first e)
     | Vec.lookup labels (Cut.second e)
... | true | true = refl
... | true | false = refl
... | false | true = refl
... | false | false = refl

edgeCutEqualsSpinQuadratic :
  ∀ {n : Nat} (e : Cut.SignedUndirectedEdge n)
    (labels : Vec.Vec Bool n) →
  (+ 4) * Cut.edgeContribution e labels ≡
  edgeSpinQuadratic e labels
edgeCutEqualsSpinQuadratic e labels =
  trans
    (cong (λ w → (+ 4) * w)
      (edgeContributionMatchesBitCut e labels))
    (fourCutEqualsSpinQuadratic
      (Cut.weight e)
      (Vec.lookup labels (Cut.first e))
      (Vec.lookup labels (Cut.second e)))

signedLaplacianQuadratic :
  ∀ {n : Nat} →
  List (Cut.SignedUndirectedEdge n) →
  Vec.Vec Bool n → ℤ
signedLaplacianQuadratic [] labels = + 0
signedLaplacianQuadratic (e ∷ es) labels =
  edgeSpinQuadratic e labels + signedLaplacianQuadratic es labels

fourDistributesOverSum : (x y : ℤ) →
  (+ 4) * (x + y) ≡ (+ 4) * x + (+ 4) * y
fourDistributesOverSum x y =
  RingZ.solve 2
    (λ x y →
      (Κ (+ 4) ⊗ (x ⊕ y)
      , (Κ (+ 4) ⊗ x) ⊕ (Κ (+ 4) ⊗ y)))
    refl x y

fourTimesZeroIsZero : (+ 4) * (+ 0) ≡ + 0
fourTimesZeroIsZero = refl

-- THIS is the exact interface to a signed finite graph spectral
-- quadratic: identical edge list, signed weights and vertex labels.
karpCutEqualsSignedLaplacianQuadratic :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  (+ 4) * Cut.edgeListCutValue edges labels ≡
  signedLaplacianQuadratic edges labels
karpCutEqualsSignedLaplacianQuadratic [] labels =
  fourTimesZeroIsZero
karpCutEqualsSignedLaplacianQuadratic (e ∷ es) labels =
  trans
    (fourDistributesOverSum
      (Cut.edgeContribution e labels)
      (Cut.edgeListCutValue es labels))
    (cong₂ _+_
      (edgeCutEqualsSpinQuadratic e labels)
      (karpCutEqualsSignedLaplacianQuadratic es labels))
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)

-- A concrete counterexample to assuming the signed graph quadratic is
-- PSD. One crossing edge of signed weight -1 produces Q = -4.
negativeEdge : Cut.SignedUndirectedEdge 2
negativeEdge = Cut.edge Fin.zero (Fin.suc Fin.zero)
  (λ ()) (-[1+ 0 ])

negativeEdgeLabels : Vec.Vec Bool 2
negativeEdgeLabels = true Vec.∷ false Vec.∷ Vec.[]

negativeEdgeSignedQuadratic :
  signedLaplacianQuadratic
    (negativeEdge ∷ [])
    negativeEdgeLabels
  ≡ -[1+ 3 ]
negativeEdgeSignedQuadratic = refl
