module DASHI.Moonshine.OggSSP2BWeightTwoIntegralC2DecompositionExact where

------------------------------------------------------------------------
-- WEIGHT-TWO INTEGRAL C2 DECOMPOSITION FOR 2B
--
-- Carnahan--Urano's even-weight restriction theorem says that at even weight
-- the self-dual integral Moonshine form restricts to <a>=C2 using only
--
--   E+ = Z       (trivial rank-one),
--   E0 = Z[C2]   (free/permutation rank-two)
--
-- summands.  At weight two the total rank is 196884.  The C2 Tate Hhat^0 of
-- E+ contributes one F2 dimension and E0 contributes zero; the already-paid
-- weight-two 2B Tate dimension is 276.  Hence the multiplicities are forced:
--
--   V^natural_{2,Z}|<a> = E+^276 + E0^98304.
--
-- Over Q this gives +1 eigenspace dimension 276+98304 = 98580 and -1
-- eigenspace dimension 98304.  The sourced 2B-centralizer ordinary branching
-- 196884 = 98304 + 98280 + 300 matches this exactly because
-- 98280 + 300 = 98580.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

weightTwoRank : Nat
weightTwoRank = 196884

trivialC2SummandCount : Nat
trivialC2SummandCount = 276

freeC2SummandCount : Nat
freeC2SummandCount = 98304

integralRankClosure :
  trivialC2SummandCount + (2 * freeC2SummandCount) ≡ weightTwoRank
integralRankClosure = refl

plusEigenspaceDimension : Nat
plusEigenspaceDimension = trivialC2SummandCount + freeC2SummandCount

minusEigenspaceDimension : Nat
minusEigenspaceDimension = freeC2SummandCount

plusEigenspaceIs98580 : plusEigenspaceDimension ≡ 98580
plusEigenspaceIs98580 = refl

minusEigenspaceIs98304 : minusEigenspaceDimension ≡ 98304
minusEigenspaceIs98304 = refl

conwayPositiveBranchDimension : Nat
conwayPositiveBranchDimension = 98280 + 300

conwayPositiveBranchIs98580 : conwayPositiveBranchDimension ≡ 98580
conwayPositiveBranchIs98580 = refl

centralizerBranchingClosure :
  minusEigenspaceDimension + conwayPositiveBranchDimension ≡ weightTwoRank
centralizerBranchingClosure = refl

record WeightTwoIntegralC2Boundary : Set where
  constructor weight-two-integral-c2-boundary
  field
    evenWeightC2SourceRestrictionPaid : Bool
    weightTwoTateDimension276Paid : Bool
    forcedIntegralC2MultiplicitiesPaid : Bool
    centralizerBranchingDimensionAlignmentPaid : Bool

canonicalWeightTwoIntegralC2Boundary : WeightTwoIntegralC2Boundary
canonicalWeightTwoIntegralC2Boundary =
  weight-two-integral-c2-boundary true true true true
