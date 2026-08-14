module DASHI.Crypto.FiniteMLWEListDecodingGeometryExact where

------------------------------------------------------------------------
-- FINITE MLWE AS A LIST-DECODING PROBLEM
--
-- Cross-pollination with coding theory: for a public noisy-linear instance,
-- define the decoding list at score threshold tau by
--
--   L(t,tau) = { s' : Score(t-A*s') <= tau }.
--
-- The existing 2x2 Z/5 laboratory has candidate scores 2,0,0,2.  Therefore
-- threshold 0 and threshold 1 both give an exact list of size two, while
-- threshold 2 admits all four candidates.  This makes the candidate fibre a
-- literal finite list-decoding object and separates uniqueness from small-list
-- and full-list regimes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab

liveCount : List Bool → Nat
liveCount [] = 0
liveCount (false ∷ xs) = liveCount xs
liveCount (true ∷ xs) = suc (liveCount xs)

threshold0Mask : List Bool
threshold0Mask = false ∷ true ∷ true ∷ false ∷ []

threshold1Mask : List Bool
threshold1Mask = false ∷ true ∷ true ∷ false ∷ []

threshold2Mask : List Bool
threshold2Mask = true ∷ true ∷ true ∷ true ∷ []

threshold0ListSize : liveCount threshold0Mask ≡ 2
threshold0ListSize = refl

threshold1ListSize : liveCount threshold1Mask ≡ 2
threshold1ListSize = refl

threshold2ListSize : liveCount threshold2Mask ≡ 4
threshold2ListSize = refl

scoresAreTwoZeroZeroTwo :
  Lab.candidateScore Lab.public22 Lab.s00 ≡ 2
scoresAreTwoZeroZeroTwo = Lab.score00

score01Zero : Lab.candidateScore Lab.public22 Lab.s01 ≡ 0
score01Zero = Lab.score01

score10Zero : Lab.candidateScore Lab.public22 Lab.s10 ≡ 0
score10Zero = Lab.score10

score11Two : Lab.candidateScore Lab.public22 Lab.s11 ≡ 2
score11Two = Lab.score11

data DecodingRegime : Set where
  uniqueDecoding smallListDecoding fullList : DecodingRegime

regimeAt0 : DecodingRegime
regimeAt0 = smallListDecoding

regimeAt1 : DecodingRegime
regimeAt1 = smallListDecoding

regimeAt2 : DecodingRegime
regimeAt2 = fullList

record FiniteListProfile : Set where
  constructor finiteListProfile
  field
    sizeAt0 sizeAt1 sizeAt2 : Nat
    size0Is2 : sizeAt0 ≡ 2
    size1Is2 : sizeAt1 ≡ 2
    size2Is4 : sizeAt2 ≡ 4

open FiniteListProfile public

public22ListProfile : FiniteListProfile
public22ListProfile = finiteListProfile 2 2 4 refl refl refl

------------------------------------------------------------------------
-- Boundary: a small decoding list is not yet cheap recovery.  Reconciliation,
-- representation transition geometry, and observation acquisition cost remain
-- separate work coordinates in the blue-team architecture.
------------------------------------------------------------------------
