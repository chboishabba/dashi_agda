module DASHI.Information.PNFCentredRankFactorisationExact where

-- The centred n-observation matrix (n = suc k) factors, column by
-- column, through k scalar coordinates. This is a constructive
-- finite-rank *factorisation*, not a disguised assertion about a
-- spectral decomposition or a probabilistic null.
--
-- The proof reuses the canonical exact source mean and its zero-sum
-- first-row identity. No independent rank axiom is introduced.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Ring
import DASHI.Information.PNFFiniteCovarianceEconomicsExact as Matrix
import DASHI.Information.PNFCentredCovarianceExact as Centre
import DASHI.Information.PNFSampleMeanExact as Mean
import DASHI.Information.PNFCentredRankDependencyExact as Dependency

private
  SOf : Ring.ExactOrderedCommutativeRing → Set
  SOf K = Scalar.Scalar (Ring.orderedScalar K)

-- A canonical extension of a k-vector to a zero-sum (k+1)-vector.
-- Unlike a generic finite-rank receipt, this is a concrete formula.
reconstructZeroSum :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k : Nat} →
  (Fin k → SOf K) →
  Fin (suc k) → SOf K
reconstructZeroSum K tail zero =
  Scalar.neg (Ring.orderedScalar K)
    (Ring.sumFin (Ring.orderedScalar K) tail)
reconstructZeroSum K tail (suc r) = tail r

-- The selected source matrix is not replaced; the reduction merely
-- stores its last k rows. The first row is provably reconstructible.
centeredTail :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  Fin p → Fin k → SOf K
centeredTail K M i r =
  Matrix.entry (Centre.centredMatrix K (Mean.source M)) (suc r) i

centeredColumnExactReconstruction :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  (i : Fin p) → (r : Fin (suc k)) →
  reconstructZeroSum K (centeredTail K M i) r
    ≡ Matrix.entry (Centre.centredMatrix K (Mean.source M)) r i
centeredColumnExactReconstruction K M i zero =
  sym (Dependency.centredFirstRowDeterminedByRemainingRows K M i)
centeredColumnExactReconstruction K M i (suc r) = refl


-- Linear structure of the zero-sum decoder. These laws matter:
-- without them any opaque encoding could masquerade as a 'rank bound'.
pointwiseAdd :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k : Nat} →
  (a b : Fin k → SOf K) → Fin k → SOf K
pointwiseAdd K a b i =
  Scalar._+_ (Ring.orderedScalar K) (a i) (b i)

pointwiseScale :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k : Nat} →
  SOf K → (Fin k → SOf K) → Fin k → SOf K
pointwiseScale K c a i =
  Scalar._*_ (Ring.orderedScalar K) c (a i)

reconstructPreservesAddition :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k : Nat} →
  (a b : Fin k → SOf K) → (r : Fin (suc k)) →
  reconstructZeroSum K (pointwiseAdd K a b) r
  ≡ pointwiseAdd K (reconstructZeroSum K a)
      (reconstructZeroSum K b) r
reconstructPreservesAddition K a b zero =
  trans
    (cong (Scalar.neg (Ring.orderedScalar K))
      (Ring.sumFinAdd K a b))
    (Ring.negDistributesOverAddition K
      (Ring.sumFin (Ring.orderedScalar K) a)
      (Ring.sumFin (Ring.orderedScalar K) b))
reconstructPreservesAddition K a b (suc r) = refl

negativeOfProductMovesRight :
  (K : Ring.ExactOrderedCommutativeRing) →
  (c x : SOf K) →
  Scalar.neg (Ring.orderedScalar K)
    (Scalar._*_ (Ring.orderedScalar K) c x)
  ≡ Scalar._*_ (Ring.orderedScalar K)
      c (Scalar.neg (Ring.orderedScalar K) x)
negativeOfProductMovesRight K c x =
  sym
    (trans
      (Ring.mulCommutative K c (Scalar.neg (Ring.orderedScalar K) x))
      (trans
        (Ring.negMultiplicationLeft K x c)
        (cong (Scalar.neg (Ring.orderedScalar K))
          (Ring.mulCommutative K x c))))

reconstructPreservesScaling :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k : Nat} →
  (c : SOf K) → (a : Fin k → SOf K) →
  (r : Fin (suc k)) →
  reconstructZeroSum K (pointwiseScale K c a) r
  ≡ pointwiseScale K c (reconstructZeroSum K a) r
reconstructPreservesScaling K c a zero =
  trans
    (cong (Scalar.neg (Ring.orderedScalar K))
      (Ring.sumFinMulLeft K c a))
    (negativeOfProductMovesRight K c
      (Ring.sumFin (Ring.orderedScalar K) a))
reconstructPreservesScaling K c a (suc r) = refl

-- A rank-at-most-k *factorisation witness*, rather than an unproved
-- inequality about an opaque Nat-valued rank function.
record ColumnFactorisationThrough
  (K : Ring.ExactOrderedCommutativeRing)
  (k n p : Nat)
  (X : Matrix.FiniteMatrix K n p) : Set where
  field
    encode : Fin p → Fin k → SOf K
    decode : (Fin k → SOf K) → Fin n → SOf K
    reconstruct :
      (i : Fin p) → (r : Fin n) →
      decode (encode i) r ≡ Matrix.entry X r i
    decodeAdditive :
      (a b : Fin k → SOf K) → (r : Fin n) →
      decode (pointwiseAdd K a b) r ≡
        pointwiseAdd K (decode a) (decode b) r
    decodeHomogeneous :
      (c : SOf K) → (a : Fin k → SOf K) → (r : Fin n) →
      decode (pointwiseScale K c a) r ≡
        pointwiseScale K c (decode a) r

-- The original centred matrix's column map has a literal factorisation
-- through the vector space of k-vectors (k = n - 1).
centeredMatrixFactorsThroughNMinusOne :
  (K : Ring.ExactOrderedCommutativeRing) →
  {k p : Nat} →
  (M : Mean.ActualFiniteMean K (suc k) p) →
  ColumnFactorisationThrough K k (suc k) p
    (Centre.centredMatrix K (Mean.source M))
centeredMatrixFactorsThroughNMinusOne K M = record
  { encode = centeredTail K M
  ; decode = reconstructZeroSum K
  ; reconstruct = centeredColumnExactReconstruction K M
  ; decodeAdditive = reconstructPreservesAddition K
  ; decodeHomogeneous = reconstructPreservesScaling K
  }

-- ReconstructZeroSum is linear as soon as the source's additive group
-- laws are paid; the coefficient-level identity above already proves
-- the rank compression without hiding a rank theorem in a Set field.
