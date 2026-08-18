module DASHI.Foundations.BalancedTernaryNineZeroFibreCountExact where

------------------------------------------------------------------------
-- EXACT EXECUTABLE ZERO-FIBRE COUNT FOR NINE BALANCED-TERNARY COORDINATES
--
-- For one coordinate {-1,0,+1}, the Laurent generating polynomial is
--
--   x^-1 + 1 + x.
--
-- For n labelled coordinates, the coefficient row of
--
--   (x^-1 + 1 + x)^n
--
-- counts words by aggregate sum from -n through +n.  Rather than inserting the
-- ninth central trinomial coefficient as a receipt, this file computes the
-- coefficient row by literal convolution with [1,1,1].
--
-- The Base369 interaction/appraisal carrier has exactly nine labelled ternary
-- coordinates (27^3 = 3^9), so the middle coefficient at n=9 is the exact
-- cardinality of the scalar aggregate-zero fibre for the flattened carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Data.List.Base using (List; []; _∷_)

-- Convolution by [1,1,1].  prev1/prev2 carry the two preceding coefficients,
-- making every output coefficient a_j + a_{j-1} + a_{j-2} with zero padding.
convolveTernary : Nat → Nat → List Nat → List Nat
convolveTernary prev1 prev2 [] =
  (prev1 + prev2) ∷ prev1 ∷ []
convolveTernary prev1 prev2 (current ∷ rest) =
  (current + prev1 + prev2) ∷
  convolveTernary current prev1 rest

ternaryStep : List Nat → List Nat
ternaryStep = convolveTernary 0 0

row0 : List Nat
row0 = 1 ∷ []

row1 row2 row3 row4 row5 row6 row7 row8 row9 : List Nat
row1 = ternaryStep row0
row2 = ternaryStep row1
row3 = ternaryStep row2
row4 = ternaryStep row3
row5 = ternaryStep row4
row6 = ternaryStep row5
row7 = ternaryStep row6
row8 = ternaryStep row7
row9 = ternaryStep row8

ninthCoefficientRowExact :
  row9 ≡
    1 ∷ 9 ∷ 45 ∷ 156 ∷ 414 ∷ 882 ∷ 1554 ∷ 2304 ∷ 2907 ∷
    3139 ∷
    2907 ∷ 2304 ∷ 1554 ∷ 882 ∷ 414 ∷ 156 ∷ 45 ∷ 9 ∷ 1 ∷ []
ninthCoefficientRowExact = refl

-- The tenth list entry is the coefficient of aggregate sum zero, because the
-- row ranges from -9 through +9.
middle9 : List Nat → Nat
middle9
  (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ centre ∷ rest) = centre
middle9 _ = 0

aggregateZeroFibreCount : Nat
aggregateZeroFibreCount = middle9 row9

aggregateZeroFibreCountIs3139 : aggregateZeroFibreCount ≡ 3139
aggregateZeroFibreCountIs3139 = refl

-- Sanity check: summing the complete coefficient row recovers 3^9 = 19683.
sumList : List Nat → Nat
sumList [] = 0
sumList (x ∷ xs) = x + sumList xs

ninthCoefficientRowTotalIs19683 : sumList row9 ≡ 19683
ninthCoefficientRowTotalIs19683 = refl

record BalancedTernaryNineZeroFibreBoundary : Set where
  field
    aggregateZeroFibreIsSingleton : Bool
    aggregateZeroCanContainInternalOpposition : Bool
    exactZeroFibreCountComputedByConvolution : Bool
    coefficientRowRecoversWholeThreePowerNineCarrier : Bool

canonicalBalancedTernaryNineZeroFibreBoundary :
  BalancedTernaryNineZeroFibreBoundary
canonicalBalancedTernaryNineZeroFibreBoundary = record
  { aggregateZeroFibreIsSingleton = false
  ; aggregateZeroCanContainInternalOpposition = true
  ; exactZeroFibreCountComputedByConvolution = true
  ; coefficientRowRecoversWholeThreePowerNineCarrier = true
  }
