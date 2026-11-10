module DASHI.Information.PNFFiniteRankNullityBridgeExact where

-- Exact bridge from a same-source centred panel to the *general*
-- finite-dimensional rank-nullity law. The source-specific linear maps,
-- their linearity and the factorisation equality are all constructed.
-- The generic field-level dimension/rank theorem is kept an explicit
-- separate authority. There is no Set-valued proof placeholder.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; suc)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_≤_)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCentredRankFactorisationExact as Factor
import DASHI.Information.PNFCentredLinearRankExact as Linear
open import Relation.Binary.PropositionalEquality using (sym)

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

-- Explicit finite linear maps over precisely the selected scalar owner.
record FiniteLinearMap
  (K : Ring.ExactOrderedCommutativeRing)
  (domain codomain : Nat) : Set where
  field
    apply : (Fin domain → SOf K) → Fin codomain → SOf K
    additive :
      (u v : Fin domain → SOf K) → (r : Fin codomain) →
      apply (Factor.pointwiseAdd K u v) r
      ≡ Factor.pointwiseAdd K (apply u) (apply v) r
    homogeneous :
      (c : SOf K) → (v : Fin domain → SOf K) →
      (r : Fin codomain) →
      apply (Factor.pointwiseScale K c v) r
      ≡ Factor.pointwiseScale K c (apply v) r

open FiniteLinearMap public

centeredLinearMap :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  FiniteLinearMap K p (suc k)
centeredLinearMap K M = record
  { apply = Linear.centeredAction K M
  ; additive = Linear.centredActionPreservesAddition K M
  ; homogeneous = Linear.centredActionPreservesScaling K M
  }

tailLinearMap :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  FiniteLinearMap K p k
tailLinearMap K M = record
  { apply = Linear.tailAction K M
  ; additive = Linear.tailActionPreservesAddition K M
  ; homogeneous = Linear.tailActionPreservesScaling K M
  }

reconstructLinearMap :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k : Nat} →
  FiniteLinearMap K k (suc k)
reconstructLinearMap K = record
  { apply = Factor.reconstructZeroSum K
  ; additive = Factor.reconstructPreservesAddition K
  ; homogeneous = Factor.reconstructPreservesScaling K
  }

-- A generic finite-dimensional theorem is NOT derived merely from the
-- weaker exact ordered-ring laws. A genuine field/dimension owner must
-- instantiate these two laws, rather than bury them in 'Set' placeholders.
record FiniteFieldRankNullityOwner
  (K : Ring.ExactOrderedCommutativeRing) : Set₁ where
  field
    rank : {p n : Nat} → FiniteLinearMap K p n → Nat
    nullity : {p n : Nat} → FiniteLinearMap K p n → Nat
    factorRankBound :
      {k p n : Nat} →
      (T : FiniteLinearMap K p n) →
      (A : FiniteLinearMap K p k) →
      (B : FiniteLinearMap K k n) →
      ((v : Fin p → SOf K) → (i : Fin n) →
        apply T v i ≡ apply B (apply A v) i) →
      rank T ≤ k
    rankNullity :
      {p n : Nat} →
      (T : FiniteLinearMap K p n) →
      (rank T + nullity T) ≡ p

open FiniteFieldRankNullityOwner public

centeredMatrixRankAtMostNMinusOne :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : FiniteFieldRankNullityOwner K) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  rank O (centeredLinearMap K M) ≤ k
centeredMatrixRankAtMostNMinusOne K O M =
  factorRankBound O
    (centeredLinearMap K M)
    (tailLinearMap K M)
    (reconstructLinearMap K)
    (λ v r → sym (Linear.centredActionFactorsThroughTail K M v r))

centeredMatrixRankNullity :
  (K : Ring.ExactOrderedCommutativeRing) →
  (O : FiniteFieldRankNullityOwner K) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  (rank O (centeredLinearMap K M)
    + nullity O (centeredLinearMap K M)) ≡ p
centeredMatrixRankNullity K O M =
  rankNullity O (centeredLinearMap K M)
