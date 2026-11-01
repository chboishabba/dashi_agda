module DASHI.Mathematics.Complexity.Karp21ExactHittingTransposeExact where

------------------------------------------------------------------------
-- SOURCE: Karp (1972), pp. 95, 99, EXACT COVER -> HITTING SET.
-- DOI: 10.1007/978-1-4684-2001-2_9.
-- IMPORTANT: Karp's 1972 HITTING SET means exactly ONE selected
-- index from every transposed family member, not ordinary >=1 hitting.
-- DASHI: constructive same-witness incidence transpose theorem only.
-- Binary finite family encoding and machine cost remain unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ; _×_)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

-- A chosen indexed subfamily has exactly one member containing every
-- element: coverage plus pairwise uniqueness. This is the proof-bearing
-- form rather than a Boolean flag claiming exactness.
record ExactlyOneIndexed
    {Element Index : Set}
    (contains : Index → Element → Bool)
    (selected : Index → Bool) : Set where
  field
    covered : (element : Element) →
      Σ Index (λ index →
        selected index ≡ true × contains index element ≡ true)

    unique : ∀ element left right →
      selected left ≡ true →
      selected right ≡ true →
      contains left element ≡ true →
      contains right element ≡ true →
      left ≡ right

ExactCover :
  ∀ {Element Index : Set} →
  (Index → Element → Bool) → (Index → Bool) → Set
ExactCover contains selected = ExactlyOneIndexed contains selected

ExactHitting :
  ∀ {Element Index : Set} →
  (Element → Index → Bool) → (Index → Bool) → Set
ExactHitting transpose selected =
  ExactlyOneIndexed (λ index element → transpose element index) selected

transposeIncidence :
  ∀ {Element Index : Set} →
  (Index → Element → Bool) → Element → Index → Bool
transposeIncidence contains element index = contains index element

karpExactCoverHittingWitnessIff :
  ∀ {Element Index : Set}
    (contains : Index → Element → Bool)
    (selected : Index → Bool) →
  PR.Iff
    (ExactCover contains selected)
    (ExactHitting (transposeIncidence contains) selected)
karpExactCoverHittingWitnessIff contains selected =
  PR.iff (λ witness → witness) (λ witness → witness)
