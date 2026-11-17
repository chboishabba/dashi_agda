module DASHI.Physics.Gravity.KSW668F8WarpWeightedSBP2CommutatorExact where

------------------------------------------------------------------------
-- XXXVIII: exact weighted normal SBP2 FACE/commutator from ORIGINAL
-- AdS5 z^-3 energy (normal grid z_i=b+i*dy).
--
-- Normal_order=3 derivative uses forward/backward endpoint and
-- centered interior. With H=dy diag(1/2,1,...,1,1/2) and weights
-- w_i=z_i^-3 >0, for arbitrary node samples x_i,
--
--   Sum_i H_i w_i x_i (D_y x)_i
--    = [w_N x_N^2-w_0 x_0^2]/2
--      + Sum_(i=0..N-1) (w_i-w_(i+1)) x_i x_(i+1) /2 .
--
-- The second term is a BULK weight-derivative commutator and is
-- indefinite without additional trace/norm estimates. Thus a
-- boundary-only source cap is NOT sufficient for z^-3 stability.
--
-- This module proves face and arbitrary-list finite rational
-- algebra, not the analytic w(z)=z^-3 derivative bounds, moving
-- Jacobian control, higher-Sobolev trace or Agda kernel acceptance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

half : ℚ
half = (+ 1) / 2

record NormalNode : Set where
  constructor node
  field
    weight sample : ℚ
open NormalNode

weightedEndpointSquare : NormalNode → ℚ
weightedEndpointSquare n = weight n * sample n * sample n

weightedPair : NormalNode → NormalNode → ℚ
weightedPair left right =
  half * (weight left * sample left + weight right * sample right)
    * (sample right + - sample left)

weightCrossCommutator : NormalNode → NormalNode → ℚ
weightCrossCommutator left right =
  half * (weight left + - weight right)
    * sample left * sample right

weightedPairDecomposition :
  (left right : NormalNode) →
  weightedPair left right
    ≡ half * (weightedEndpointSquare right
                + - weightedEndpointSquare left)
      + weightCrossCommutator left right
weightedPairDecomposition left right = solve []

weightedSBP2FaceSum : List NormalNode → ℚ
weightedSBP2FaceSum (x ∷ y ∷ xs) =
  weightedPair x y + weightedSBP2FaceSum (y ∷ xs)
weightedSBP2FaceSum _ = 0ℚ

weightCommutatorSum : List NormalNode → ℚ
weightCommutatorSum (x ∷ y ∷ xs) =
  weightCrossCommutator x y + weightCommutatorSum (y ∷ xs)
weightCommutatorSum _ = 0ℚ

firstWeightedSquare : List NormalNode → ℚ
firstWeightedSquare [] = 0ℚ
firstWeightedSquare (x ∷ _) = weightedEndpointSquare x

lastWeightedSquare : List NormalNode → ℚ
lastWeightedSquare [] = 0ℚ
lastWeightedSquare (x ∷ []) = weightedEndpointSquare x
lastWeightedSquare (x ∷ y ∷ xs) = lastWeightedSquare (y ∷ xs)

originalWarpWeightedFiniteSBP2 :
  (xs : List NormalNode) →
  weightedSBP2FaceSum xs
  ≡ half * (lastWeightedSquare xs
              + - firstWeightedSquare xs)
      + weightCommutatorSum xs
originalWarpWeightedFiniteSBP2 [] = solve []
originalWarpWeightedFiniteSBP2 (x ∷ []) = solve []
originalWarpWeightedFiniteSBP2 (x ∷ y ∷ xs)
  rewrite originalWarpWeightedFiniteSBP2 (y ∷ xs)
    | weightedPairDecomposition x y = solve []

-- The commutator sign is indefinite even for descending positive
-- weights, e.g. wL=2, wR=1. Positive samples: +1/2.
descendingWarpPositiveCross :
  weightCrossCommutator
    (node ((+ 2) / 1) 1ℚ)
    (node 1ℚ 1ℚ)
  ≡ (+ 1) / 2
descendingWarpPositiveCross = solve []

-- The SAME descending positive weights with opposite-sign samples
-- give -1/2. No generic global dissipation follows from wL>wR.
descendingWarpNegativeCross :
  weightCrossCommutator
    (node ((+ 2) / 1) 1ℚ)
    (node 1ℚ (- 1ℚ))
  ≡ - ((+ 1) / 2)
descendingWarpNegativeCross = solve []
