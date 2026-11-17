{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDyadicCharacterPairCancellationExact where

------------------------------------------------------------------------
-- YM.REAL: finite additive cancellation for dyadic Fourier blocks.
--
-- For N=2^s and k=2^t u (u odd), write r=2^(s-t-1).
-- The primitive dyadic character satisfies
--   z^(k(j+r)) = -z^(kj).
-- Pairing adjacent length-r blocks reduces the Fourier sum to the
-- finite cancellation theorem here. The proof below is a genuine
-- structural induction, not a field providing a Fourier theorem.
--
-- The remaining ORIGINAL-SOURCE implementation is to inhabit the
-- shift identity and reindex the actual Fin N enumeration for
-- primitive Bishop dyadic roots. This module does not construct them,
-- all-degree quadrature nodes, or the Bishop Haar integral.
--
-- Attribution: Fejer/Stroud; existing DASHI finite group characters;
-- Bishop/Bridges, Murray/Csimma, Wilson/Balaban.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)

module _
  {Scalar : Set}
  (zero : Scalar)
  (_add_ : Scalar → Scalar → Scalar)
  (negate : Scalar → Scalar)
  (addInverseRight : ∀ x → (x add (negate x)) ≡ zero)
  (addZeroZero : (zero add zero) ≡ zero)
  where

  -- A block consists of actual Fourier values and their shifted
  -- opposite phases. There are no free measure or zero-sum fields.
  adjacentOppositeBlockSum : List Scalar → Scalar
  adjacentOppositeBlockSum [] = zero
  adjacentOppositeBlockSum (value ∷ rest) =
    (value add (negate value)) add adjacentOppositeBlockSum rest

  adjacentOppositeBlockSumZero :
    ∀ values → adjacentOppositeBlockSum values ≡ zero
  adjacentOppositeBlockSumZero [] = refl
  adjacentOppositeBlockSumZero (value ∷ rest)
    rewrite addInverseRight value
          | adjacentOppositeBlockSumZero rest
    = addZeroZero

  -- The same theorem holds when the second phase is independently
  -- computed, provided its equality to the actual shifted inverse
  -- is proved by a source character/power identity.
  shiftedBlockSum :
    (values : List Scalar) →
    (Scalar → Scalar) → Scalar
  shiftedBlockSum [] shift = zero
  shiftedBlockSum (value ∷ rest) shift =
    (value add (shift value)) add shiftedBlockSum rest shift

  shiftedBlockSumIfOpposite :
    (values : List Scalar) (shift : Scalar → Scalar) →
    (∀ value → shift value ≡ negate value) →
    shiftedBlockSum values shift ≡ zero
  shiftedBlockSumIfOpposite [] shift identity = refl
  shiftedBlockSumIfOpposite (value ∷ rest) shift identity
    rewrite identity value
          | addInverseRight value
          | shiftedBlockSumIfOpposite rest shift identity
    = addZeroZero
