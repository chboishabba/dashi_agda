module DASHI.Analysis.RiemannAristotleFiniteNearOrderedPairGramDebtExact where

------------------------------------------------------------------------
-- G2 / EXACT FINITE ORDERED-PAIR GRAM-DEBT EXPANSION
--
-- Bidi purpose:
--
-- Forward: G1 already gives the literal finite three-coordinate post-Schur
-- carrier and the exact finite Gram telescope.
--
-- Backward: the Schur-margin consumer needs only a signed upper bound on the
-- finite Gram debt.  Therefore expose that debt as the explicit pair covariance
-- sum, with no absolute values and no cardinality majorant.
--
-- For cells v_0,...,v_{n-1}, exact polarization gives
--
--   GramDebt = 2 * sum_{i<j} <v_i,v_j>.
--
-- Since the real dot product is symmetric, this is the same scalar as
--
--   sum_{i != j} <v_i,v_j>.
--
-- This file proves the first identity over any exact additive carrier carrying
-- a symmetric, right-additive dot product.  No zeta-specific estimate occurs
-- here; the only remaining mathematics is the sign/size of the resulting
-- finite covariance sum.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Analysis.RiemannAristotleLiteralPostSchurFiniteGramWeldExact as G1

record RHPostSchurDotStructure : Set₁ where
  constructor rh-post-schur-dot-structure
  field
    gramStructure : G1.RHPostSchurGramStructure

    dot :
      G1.RHPostSchurCell (G1.Scalar gramStructure) →
      G1.RHPostSchurCell (G1.Scalar gramStructure) →
      G1.Scalar gramStructure

    dotSymmetric : ∀ u v → dot u v ≡ dot v u

    dotZeroRight : ∀ u →
      dot u (G1.zeroCell gramStructure) ≡ G1.zeroScalar gramStructure

    dotAddRight : ∀ u v w →
      dot u (G1.addCell gramStructure v w)
      ≡ G1.addScalar gramStructure (dot u v) (dot u w)

    signedCrossIsDoubleDot : ∀ u v →
      G1.signedCrossIncrement gramStructure u v
      ≡ G1.addScalar gramStructure (dot u v) (dot u v)

open RHPostSchurDotStructure public

Cell : RHPostSchurDotStructure → Set
Cell D = G1.RHPostSchurCell (G1.Scalar (gramStructure D))

Scalar : RHPostSchurDotStructure → Set
Scalar D = G1.Scalar (gramStructure D)

zero : (D : RHPostSchurDotStructure) → Scalar D
zero D = G1.zeroScalar (gramStructure D)

_+D_ : {D : RHPostSchurDotStructure} → Scalar D → Scalar D → Scalar D
_+D_ {D} = G1.addScalar (gramStructure D)

double : (D : RHPostSchurDotStructure) → Scalar D → Scalar D
double D x = x +D x

sumDot :
  (D : RHPostSchurDotStructure) →
  Cell D → List (Cell D) → Scalar D
sumDot D u [] = zero D
sumDot D u (v ∷ vs) = dot D u v +D sumDot D u vs

-- One copy for each unordered pair i<j.
unorderedPairDotSum :
  (D : RHPostSchurDotStructure) →
  List (Cell D) → Scalar D
unorderedPairDotSum D [] = zero D
unorderedPairDotSum D (u ∷ us) =
  sumDot D u us +D unorderedPairDotSum D us

-- Ordered-pair covariance scalar.  Symmetry means each unordered pair appears
-- twice, once as (i,j) and once as (j,i).
orderedPairDotSum :
  (D : RHPostSchurDotStructure) →
  List (Cell D) → Scalar D
orderedPairDotSum D cells = double D (unorderedPairDotSum D cells)

addZeroRight :
  (D : RHPostSchurDotStructure) →
  (x : Scalar D) → x +D zero D ≡ x
addZeroRight D x =
  trans
    (G1.addComm (gramStructure D) x (zero D))
    (G1.addZeroLeft (gramStructure D) x)

sumDotAgainstSum :
  (D : RHPostSchurDotStructure) →
  (u : Cell D) →
  (cells : List (Cell D)) →
  dot D u (G1.rhSumCells (gramStructure D) cells)
  ≡ sumDot D u cells
sumDotAgainstSum D u [] =
  dotZeroRight D u
sumDotAgainstSum D u (v ∷ vs)
  rewrite dotAddRight D u v (G1.rhSumCells (gramStructure D) vs)
        | sumDotAgainstSum D u vs = refl

-- Elementary commutative-monoid identity:
--   2a + 2b = 2(a+b).
doubleAdd :
  (D : RHPostSchurDotStructure) →
  (a b : Scalar D) →
  double D a +D double D b ≡ double D (a +D b)
doubleAdd D a b =
  trans
    (sym (G1.addAssoc S a a (double D b)))
    (trans
      (cong (G1.addScalar S a)
        (G1.addAssoc S a b b))
      (trans
        (cong (G1.addScalar S a)
          (cong (λ x → x +D b) (G1.addComm S a b)))
        (trans
          (cong (G1.addScalar S a)
            (sym (G1.addAssoc S b a b)))
          (G1.addAssoc S a b (a +D b)))))
  where
    S = gramStructure D

rhGramDebtIsOrderedPairCovariance :
  (D : RHPostSchurDotStructure) →
  (cells : List (Cell D)) →
  G1.rhGramDebt (gramStructure D) cells
  ≡ orderedPairDotSum D cells
rhGramDebtIsOrderedPairCovariance D [] =
  sym (G1.addZeroLeft (gramStructure D) (zero D))
rhGramDebtIsOrderedPairCovariance D (u ∷ us)
  rewrite signedCrossIsDoubleDot D u (G1.rhSumCells (gramStructure D) us)
        | sumDotAgainstSum D u us
        | rhGramDebtIsOrderedPairCovariance D us =
  doubleAdd D (sumDot D u us) (unorderedPairDotSum D us)

record G2OrderedPairBoundary : Set where
  constructor g2-ordered-pair-boundary
  field
    finiteGramDebtExpandedToOrderedPairCovariance : Bool
    finiteGramDebtExpandedToOrderedPairCovarianceIsTrue :
      finiteGramDebtExpandedToOrderedPairCovariance ≡ true

    absoluteValuesInsertedInPairExpansion : Bool
    absoluteValuesInsertedInPairExpansionIsFalse :
      absoluteValuesInsertedInPairExpansion ≡ false

    signedOrderedPairCovarianceEstimateClosed : Bool
    signedOrderedPairCovarianceEstimateClosedIsFalse :
      signedOrderedPairCovarianceEstimateClosed ≡ false

canonicalG2OrderedPairBoundary : G2OrderedPairBoundary
canonicalG2OrderedPairBoundary =
  g2-ordered-pair-boundary true refl false refl false refl
