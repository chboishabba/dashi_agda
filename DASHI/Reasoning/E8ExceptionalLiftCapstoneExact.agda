module DASHI.Reasoning.E8ExceptionalLiftCapstoneExact where

------------------------------------------------------------------------
-- E6 -> E8 EXCEPTIONAL-LIFT CAPSTONE RECEIPT
--
-- DASHI CONTRIBUTION
--
-- The Lean finite producer now source-writes a literal E8 branching with:
--   240 = 72 + 6 + 6 * 27,
-- a same-object/action E6 sector, six E6-stable transitive mixed 27 fibres,
-- and Schlaefli relation geometry on each selected 27-fibre.
--
-- This Agda owner types that exact promotion surface without importing an
-- unobserved Lean kernel result as an Agda theorem.  Full ternary-240 and
-- Albert/minuscule-27 same-action recognition remain independent receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.E6F3GeneratedGroupClosureExact as Group
import DASHI.Foundations.E6F3ExteriorSquareRecognitionExact as E6

record E8BranchingLedger : Set where
  constructor e8-branching-ledger
  field
    totalRoots : Nat
    e6SectorRoots : Nat
    a2SectorRoots : Nat
    mixedWeightFibres : Nat
    rootsPerMixedFibre : Nat

    totalRootsIs240 : totalRoots ≡ 240
    e6SectorRootsIs72 : e6SectorRoots ≡ 72
    a2SectorRootsIs6 : a2SectorRoots ≡ 6
    mixedWeightFibresIs6 : mixedWeightFibres ≡ 6
    rootsPerMixedFibreIs27 : rootsPerMixedFibre ≡ 27
open E8BranchingLedger public

record Mixed27RelationReceipt : Set₁ where
  field
    Carrier27 : Set
    Actor : Set
    act : Actor → Carrier27 → Carrier27
    related : Carrier27 → Carrier27 → Set

    cardinality27 : Set
    actionTransitive : Set
    actionPreservesRelation : Set

    schlafliDegree16 : Set
    schlafliAdjacentCommon10 : Set
    schlafliNonAdjacentCommon8 : Set
    orthogonalDegree10 : Set
    orthogonalAdjacentCommon1 : Set
    orthogonalNonAdjacentCommon5 : Set
open Mixed27RelationReceipt public

record LiteralE8ExceptionalLiftReceipt : Set₁ where
  field
    generatedE6Image : Group.GeneratedE6ImageReceipt
    e6Model : E6.E6Mod3QuadraticModel
    branching : E8BranchingLedger

    e6SectorSameObjectActionReceipt : Set
    a2RootsPointwiseFixedByE6Receipt : Set

    plus0 plus1 plus2 : Mixed27RelationReceipt
    minus0 minus1 minus2 : Mixed27RelationReceipt

    sixFibresPairwiseWeightDistinguished : Set
    sixFibresExhaustMixed162 : Set
open LiteralE8ExceptionalLiftReceipt public

record FullTernary240Recognition
  (L : LiteralE8ExceptionalLiftReceipt) : Set₁ where
  field
    Ternary240 : Set
    LiteralE8Root : Set
    Actor : Set
    ternaryAction : Actor → Ternary240 → Ternary240
    e8Action : Actor → LiteralE8Root → LiteralE8Root
    equiv240 : Ternary240 → LiteralE8Root
    inverse240 : LiteralE8Root → Ternary240
    leftInverse : Set
    rightInverse : Set
    actionIntertwines : Set
open FullTernary240Recognition public

record Albert27Recognition
  (M : Mixed27RelationReceipt) : Set₁ where
  field
    AlbertCarrier27 : Set
    AlbertActor : Set
    albertAction : AlbertActor → AlbertCarrier27 → AlbertCarrier27
    albertRelation : AlbertCarrier27 → AlbertCarrier27 → Set
    sameObjectBijectionReceipt : Set
    actionIntertwinerReceipt : Set
    relationIntertwinerReceipt : Set
open Albert27Recognition public

record ExceptionalLiftBoundary : Set where
  constructor exceptional-lift-boundary
  field
    e6SectorSameObjectActionReceiptTyped : Bool
    a2FixedSectorReceiptTyped : Bool
    sixMixed27FibresTyped : Bool
    sixMixed27TransitivityReceiptsTyped : Bool
    schlafli27RecognitionReceiptTyped : Bool
    e8Branching72Plus6PlusSix27Typed : Bool

    leanExceptionalLiftProducerSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaLiteralE8EnumerationKernelPaidHere : Bool

    fullTernary240SameActionRecognitionPaid : Bool
    albert27SameActionRecognitionPaid : Bool
    cardinalityAlonePromotesEitherRecognition : Bool
open ExceptionalLiftBoundary public

canonicalExceptionalLiftBoundary : ExceptionalLiftBoundary
canonicalExceptionalLiftBoundary =
  exceptional-lift-boundary
    true true true true true true
    true false false
    false false false
