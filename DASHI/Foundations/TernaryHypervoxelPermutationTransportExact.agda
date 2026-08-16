module DASHI.Foundations.TernaryHypervoxelPermutationTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Volodymyr Nekrashevych,
-- "Self-Similar Groups", Mathematical Surveys and Monographs 117,
-- American Mathematical Society, 2005.
-- DOI: 10.1090/surv/117.
--
-- DASHI CONTRIBUTION
--
-- Transport the exact six coordinate permutations of the ternary carrier
-- through the repository's existing recursive hypervoxel push/pop geometry.
--
--   push = address-refine
--   pop  = coarsen
--
-- Permutation transport is defined recursively on every Axis3 coordinate in
-- every AxisBlock and every address. It commutes exactly with push, pop,
-- fine-block recovery and prefix/suffix address join. The inverse permutation
-- undoes the transport at every depth.
--
-- This is the diagonal local S3 action on the existing ternary address tree.
-- The repository's independent finite wreath witness remains the source for
-- the stronger "local transforms + coarse-index permutation" pattern; this
-- module does not silently identify the diagonal action with the full rooted
-- tree automorphism group.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import Base369 as Base
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3
import DASHI.Physics.Common.FiniteWreathRefinementExact as Wreath

axisToTri : Hyper.Axis3 → Base.TriTruth
axisToTri Hyper.axis-low = Base.tri-low
axisToTri Hyper.axis-mid = Base.tri-mid
axisToTri Hyper.axis-high = Base.tri-high

triToAxis : Base.TriTruth → Hyper.Axis3
triToAxis Base.tri-low = Hyper.axis-low
triToAxis Base.tri-mid = Hyper.axis-mid
triToAxis Base.tri-high = Hyper.axis-high

axisRoundTrip :
  (axis : Hyper.Axis3) →
  triToAxis (axisToTri axis) ≡ axis
axisRoundTrip Hyper.axis-low = refl
axisRoundTrip Hyper.axis-mid = refl
axisRoundTrip Hyper.axis-high = refl

triRoundTrip :
  (value : Base.TriTruth) →
  axisToTri (triToAxis value) ≡ value
triRoundTrip Base.tri-low = refl
triRoundTrip Base.tri-mid = refl
triRoundTrip Base.tri-high = refl

permuteAxis :
  S3.TriPermutation → Hyper.Axis3 → Hyper.Axis3
permuteAxis permutation axis =
  triToAxis (S3.applyPermutation permutation (axisToTri axis))

permuteAxisInverseLeft :
  (permutation : S3.TriPermutation) →
  (axis : Hyper.Axis3) →
  permuteAxis (S3.inversePermutation permutation)
    (permuteAxis permutation axis)
  ≡ axis
permuteAxisInverseLeft S3.permIdentity Hyper.axis-low = refl
permuteAxisInverseLeft S3.permIdentity Hyper.axis-mid = refl
permuteAxisInverseLeft S3.permIdentity Hyper.axis-high = refl
permuteAxisInverseLeft S3.permRotate Hyper.axis-low = refl
permuteAxisInverseLeft S3.permRotate Hyper.axis-mid = refl
permuteAxisInverseLeft S3.permRotate Hyper.axis-high = refl
permuteAxisInverseLeft S3.permRotate2 Hyper.axis-low = refl
permuteAxisInverseLeft S3.permRotate2 Hyper.axis-mid = refl
permuteAxisInverseLeft S3.permRotate2 Hyper.axis-high = refl
permuteAxisInverseLeft S3.permSwapLowMid Hyper.axis-low = refl
permuteAxisInverseLeft S3.permSwapLowMid Hyper.axis-mid = refl
permuteAxisInverseLeft S3.permSwapLowMid Hyper.axis-high = refl
permuteAxisInverseLeft S3.permSwapLowHigh Hyper.axis-low = refl
permuteAxisInverseLeft S3.permSwapLowHigh Hyper.axis-mid = refl
permuteAxisInverseLeft S3.permSwapLowHigh Hyper.axis-high = refl
permuteAxisInverseLeft S3.permSwapMidHigh Hyper.axis-low = refl
permuteAxisInverseLeft S3.permSwapMidHigh Hyper.axis-mid = refl
permuteAxisInverseLeft S3.permSwapMidHigh Hyper.axis-high = refl

permuteBlock :
  ∀ {rank : Nat} →
  S3.TriPermutation →
  Hyper.AxisBlock rank →
  Hyper.AxisBlock rank
permuteBlock {rank = zero} permutation Hyper.block-root =
  Hyper.block-root
permuteBlock {rank = suc rank} permutation
  (Hyper.block-cons axis rest) =
  Hyper.block-cons
    (permuteAxis permutation axis)
    (permuteBlock permutation rest)

permuteBlockInverseLeft :
  ∀ {rank : Nat} →
  (permutation : S3.TriPermutation) →
  (block : Hyper.AxisBlock rank) →
  permuteBlock (S3.inversePermutation permutation)
    (permuteBlock permutation block)
  ≡ block
permuteBlockInverseLeft {rank = zero} permutation Hyper.block-root = refl
permuteBlockInverseLeft {rank = suc rank} permutation
  (Hyper.block-cons axis rest)
  rewrite permuteAxisInverseLeft permutation axis
        | permuteBlockInverseLeft permutation rest = refl

permuteAddress :
  ∀ {rank depth : Nat} →
  S3.TriPermutation →
  Hyper.TernaryAddress rank depth →
  Hyper.TernaryAddress rank depth
permuteAddress permutation Hyper.address-root =
  Hyper.address-root
permuteAddress permutation (Hyper.address-refine parent child) =
  Hyper.address-refine
    (permuteAddress permutation parent)
    (permuteBlock permutation child)

permuteAddressInverseLeft :
  ∀ {rank depth : Nat} →
  (permutation : S3.TriPermutation) →
  (address : Hyper.TernaryAddress rank depth) →
  permuteAddress (S3.inversePermutation permutation)
    (permuteAddress permutation address)
  ≡ address
permuteAddressInverseLeft permutation Hyper.address-root = refl
permuteAddressInverseLeft permutation
  (Hyper.address-refine parent child)
  rewrite permuteAddressInverseLeft permutation parent
        | permuteBlockInverseLeft permutation child = refl

------------------------------------------------------------------------
-- Push/pop and child recovery commute with the local permutation.
------------------------------------------------------------------------

permuteRefine :
  ∀ {rank depth : Nat}
    (permutation : S3.TriPermutation)
    (parent : Hyper.TernaryAddress rank depth)
    (child : Hyper.AxisBlock rank) →
  permuteAddress permutation (Hyper.address-refine parent child)
  ≡
  Hyper.address-refine
    (permuteAddress permutation parent)
    (permuteBlock permutation child)
permuteRefine permutation parent child = refl

coarsenPermute :
  ∀ {rank depth : Nat}
    (permutation : S3.TriPermutation)
    (address : Hyper.TernaryAddress rank (suc depth)) →
  Hyper.coarsen (permuteAddress permutation address)
  ≡
  permuteAddress permutation (Hyper.coarsen address)
coarsenPermute permutation (Hyper.address-refine parent child) = refl

fineBlockPermute :
  ∀ {rank depth : Nat}
    (permutation : S3.TriPermutation)
    (address : Hyper.TernaryAddress rank (suc depth)) →
  Hyper.fineBlock (permuteAddress permutation address)
  ≡
  permuteBlock permutation (Hyper.fineBlock address)
fineBlockPermute permutation (Hyper.address-refine parent child) = refl

------------------------------------------------------------------------
-- Prefix/suffix joins are equivariant as well.
------------------------------------------------------------------------

permuteSuffix :
  ∀ {rank depth : Nat} →
  S3.TriPermutation →
  Hyper.AddressSuffix rank depth →
  Hyper.AddressSuffix rank depth
permuteSuffix permutation Hyper.suffix-root =
  Hyper.suffix-root
permuteSuffix permutation (Hyper.suffix-refine suffix child) =
  Hyper.suffix-refine
    (permuteSuffix permutation suffix)
    (permuteBlock permutation child)

joinPermute :
  ∀ {rank coarseDepth fineDepth : Nat}
    (permutation : S3.TriPermutation)
    (parent : Hyper.TernaryAddress rank coarseDepth)
    (suffix : Hyper.AddressSuffix rank fineDepth) →
  permuteAddress permutation (Hyper.joinAddress parent suffix)
  ≡
  Hyper.joinAddress
    (permuteAddress permutation parent)
    (permuteSuffix permutation suffix)
joinPermute permutation parent Hyper.suffix-root = refl
joinPermute permutation parent
  (Hyper.suffix-refine suffix child)
  rewrite joinPermute permutation parent suffix = refl

------------------------------------------------------------------------
-- Reuse the existing finite wreath witness rather than inventing a parallel
-- "wreath" vocabulary.
------------------------------------------------------------------------

existingFiniteWreathBoundary : Wreath.WreathRefinementBoundary
existingFiniteWreathBoundary = Wreath.canonicalWreathRefinementBoundary

record HypervoxelPermutationTransportBoundary : Set where
  field
    localS3TransportConstructed : Bool
    localS3TransportConstructedIsTrue :
      localS3TransportConstructed ≡ true

    pushPopEquivarianceConstructed : Bool
    pushPopEquivarianceConstructedIsTrue :
      pushPopEquivarianceConstructed ≡ true

    existingWreathSurfaceReused : Bool
    existingWreathSurfaceReusedIsTrue :
      existingWreathSurfaceReused ≡ true

    diagonalActionIdentifiedWithFullWreathAutomorphismGroup : Bool
    diagonalActionIdentifiedWithFullWreathAutomorphismGroupIsFalse :
      diagonalActionIdentifiedWithFullWreathAutomorphismGroup ≡ false

canonicalHypervoxelPermutationTransportBoundary :
  HypervoxelPermutationTransportBoundary
canonicalHypervoxelPermutationTransportBoundary =
  record
    { localS3TransportConstructed = true
    ; localS3TransportConstructedIsTrue = refl
    ; pushPopEquivarianceConstructed = true
    ; pushPopEquivarianceConstructedIsTrue = refl
    ; existingWreathSurfaceReused = true
    ; existingWreathSurfaceReusedIsTrue = refl
    ; diagonalActionIdentifiedWithFullWreathAutomorphismGroup = false
    ; diagonalActionIdentifiedWithFullWreathAutomorphismGroupIsFalse = refl
    }
