module DASHI.Reasoning.AlbertF4FiniteWeylMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- FINITE E6 -> F4 / 1+26 CROSS-PROVER RECEIPTS
--
-- Companion Lean PR #52 source-writes the finite producers summarized here:
--
-- * E6 diagram fold generators s1, s3, s0*s5, s2*s4;
-- * exact generated image order 1152;
-- * F4 Coxeter/Cartan signature;
-- * two disjoint 24-root Weyl orbits, total 48 roots;
-- * the 24 nonzero restricted E6 minuscule weights are the F4 short-root orbit;
-- * the remaining three E6 weights restrict to folded zero;
-- * those three lines carry the full S3 permutation image;
-- * their all-ones line is fixed, while the sum-zero plane is 2-dimensional;
-- * hence the finite W(F4) model pays 27 = 1 + (24 + 2) = 1 + 26;
-- * the canonical non-diagonal T5 240 is not invariant under the independently
--   paid E6 action, blocking that natural same-action E8 recognition route.
--
-- These are Lean-source producer receipts here.  No Lean theorem is silently
-- imported as an Agda kernel theorem.
------------------------------------------------------------------------

record FoldedF4WeylReceipt : Set₁ where
  field
    FoldGenerator : Set
    FoldedWeight : Set
    act : FoldGenerator → FoldedWeight → FoldedWeight

    generatedImageOrder : Nat
    generatedImageOrderIs1152Receipt : Set
    coxeterTypeF4Receipt : Set
    explicitF4CartanReceipt : Set

    ShortRoot LongRoot : Set
    shortRootCount24Receipt : Set
    longRootCount24Receipt : Set
    rootsDisjointReceipt : Set
    rootCount48Receipt : Set
open FoldedF4WeylReceipt public

record MinusculeRestrictionReceipt
  (F : FoldedF4WeylReceipt) : Set₁ where
  field
    E6MinusculeWeight : Set
    restrictWeight : E6MinusculeWeight → FoldedWeight F
    Nonzero24 Zero3 : Set

    split24Plus3Receipt : Set
    nonzeroRestrictionsPairwiseDistinctReceipt : Set
    nonzeroRestrictionsEqualShortRootsReceipt : Set
    zeroThreeRestrictToZeroReceipt : Set
open MinusculeRestrictionReceipt public

record FiniteOnePlus26Receipt
  {F : FoldedF4WeylReceipt}
  (R : MinusculeRestrictionReceipt F) : Set₁ where
  field
    CoordinateModule27 : Set
    FixedLine1 : Set
    TraceKernel26 : Set

    zeroThreePermutationImageIsS3Receipt : Set
    allOnesLineFixedReceipt : Set
    sumZeroPlaneDimension2Receipt : Set
    shortRootPartDimension24Receipt : Set
    traceKernelDimension26Receipt : Set
    directSplitOnePlus26Receipt : Set
    foldedActionPreservesTraceKernelReceipt : Set
open FiniteOnePlus26Receipt public

record LinearAlbertTransportReceipt : Set₁ where
  field
    AlbertCarrier27 : Set
    MinusculeCoordinateModule27 : Set
    linearEquivalenceReceipt : Set
    twentySevenDistinctTransportedLinesReceipt : Set
    conjugatedE6LinearActionReceipt : Set
    jordanProductCompatibilityReceipt : Set
    cubicNormCompatibilityReceipt : Set
open LinearAlbertTransportReceipt public

record TernaryLinearBasisWeldReceipt : Set₁ where
  field
    Ternary27 NonOrigin26 Traceless26 : Set
    literalOrigin : Ternary27
    nonOriginCount26Receipt : Set
    originPlus26SplitReceipt : Set
    nonOriginIndexesTracelessBasisReceipt : Set
    f4ActionCompatibilityReceipt : Set
    jordanCubicCompatibilityReceipt : Set
open TernaryLinearBasisWeldReceipt public

record NaturalT5Relative240NoGoReceipt : Set₁ where
  field
    Relative240 : Set
    E6Generator : Set
    existingAction : E6Generator → Set → Set
    relativeCount240Receipt : Set
    explicitEscapeWitnessReceipt : Set
    naturalE6InvarianceRefutedReceipt : Set
    naturalRestrictedActionImpossibleReceipt : Set
open NaturalT5Relative240NoGoReceipt public

record FiniteAlbertF4Boundary : Set where
  constructor finite-albert-f4-boundary
  field
    leanFoldedWeylOrder1152SourceWritten : Bool
    leanF4CartanSourceWritten : Bool
    leanF4RootSet48SourceWritten : Bool
    leanMinuscule24ShortPlusZero3SourceWritten : Bool
    leanZeroTripleS3SourceWritten : Bool
    leanFiniteOnePlus26SourceWritten : Bool
    leanMinusculeCoordinateModule27SourceWritten : Bool
    leanLinearAlbertTransportSourceWritten : Bool
    leanTernaryOriginPlus26BasisTransportSourceWritten : Bool
    leanNaturalRelative240E6NoGoSourceWritten : Bool

    agdaFoldedWeylKernelPaidHere : Bool
    agdaFiniteOnePlus26KernelPaidHere : Bool
    actualAlbertProductCompatibilityPaid : Bool
    actualAlbertUnitIdentificationPaid : Bool
    actualF4AutomorphismGroupRecognitionPaid : Bool
    alternativeTernary240RecognitionPaid : Bool
open FiniteAlbertF4Boundary public

canonicalFiniteAlbertF4Boundary : FiniteAlbertF4Boundary
canonicalFiniteAlbertF4Boundary = finite-albert-f4-boundary
  true true true true true true true true true true
  false false false false false false

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data FiniteWeylF4CreatesAlbertAutomorphismGroup : Set where
data LinearAlbertTransportCreatesJordanCompatibility : Set where
data NaturalRelative240NoGoBlocksAllPossible240Actions : Set where

finiteWeylDoesNotCreateAlbertAutomorphismGroup :
  FiniteWeylF4CreatesAlbertAutomorphismGroup → {A : Set} → A
finiteWeylDoesNotCreateAlbertAutomorphismGroup ()

linearTransportDoesNotCreateJordanCompatibility :
  LinearAlbertTransportCreatesJordanCompatibility → {A : Set} → A
linearTransportDoesNotCreateJordanCompatibility ()

naturalRelative240NoGoIsNotUniversal :
  NaturalRelative240NoGoBlocksAllPossible240Actions → {A : Set} → A
naturalRelative240NoGoIsNotUniversal ()
