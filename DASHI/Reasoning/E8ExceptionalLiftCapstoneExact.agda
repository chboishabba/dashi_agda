module DASHI.Reasoning.E8ExceptionalLiftCapstoneExact where

------------------------------------------------------------------------
-- E6 -> E8 EXCEPTIONAL-LIFT CAPSTONE RECEIPT
--
-- DASHI CONTRIBUTION
--
-- The companion Lean finite producer now source-writes a literal E8 branching
-- with 240 = 72 + 6 + 6 * 27, exact E6 action on the 72-sector, six transitive
-- mixed 27 fibres, Schlaefli relation geometry, a concrete same-object
-- recognition of one mixed fibre with an E6 minuscule 27 weight orbit, and an
-- explicit A5 six-object action closing to all 720 permutations.
--
-- The existing Agda Ternary27Point now additionally has a literal two-sided
-- absolute six-face 6+15+6 chart.  Companion Lean source checks that the
-- induced non-Cayley relation is SRG(27,16,10,8) and agrees pointwise with the
-- E6 minuscule relation.
--
-- This Agda owner types those promotion surfaces without importing an
-- unobserved Lean kernel result as an Agda theorem.  E6 minuscule/relation
-- recognition is kept distinct from an independently derived E6 action on the
-- pre-existing hyperfabric operations and from Albert/Jordan algebra
-- recognition: product, unit, cubic norm and F4 automorphisms remain extra data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.E6F3GeneratedGroupClosureExact as Group
import DASHI.Foundations.E6F3ExteriorSquareRecognitionExact as E6
import DASHI.Reasoning.Ternary27HyperformSchlafliRecognitionExact as T27

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

------------------------------------------------------------------------
-- E6 MINUSCULE 27: SAME OBJECT / ACTION / RELATION RECEIPT
------------------------------------------------------------------------

record E6Minuscule27SameObjectReceipt
  (M : Mixed27RelationReceipt) : Set₁ where
  field
    WeightCarrier27 : Set
    E6Actor : Set
    weightAction : E6Actor → WeightCarrier27 → WeightCarrier27
    invariantWeightRelation : WeightCarrier27 → WeightCarrier27 → Set

    sameObjectBijectionReceipt : Set
    actionIntertwinerReceipt : Set
    relationIntertwinerReceipt : Set
open E6Minuscule27SameObjectReceipt public

------------------------------------------------------------------------
-- ALBERT/JORDAN LAYER: STRICTLY STRONGER THAN MINUSCULE WEIGHT GEOMETRY
------------------------------------------------------------------------

record Albert27AlgebraRecognition
  {M : Mixed27RelationReceipt}
  (R : E6Minuscule27SameObjectReceipt M) : Set₁ where
  field
    JordanCarrier27 : Set
    jordanProduct : JordanCarrier27 → JordanCarrier27 → JordanCarrier27
    jordanUnit : JordanCarrier27
    cubicNorm : JordanCarrier27 → Set
    F4Actor : Set
    f4Action : F4Actor → JordanCarrier27 → JordanCarrier27

    underlyingCarrierMatchesMinusculeReceipt : Set
    jordanIdentitiesReceipt : Set
    unitReceipt : Set
    cubicNormCompatibilityReceipt : Set
    f4AutomorphismReceipt : Set
open Albert27AlgebraRecognition public

record ExceptionalLiftBoundary : Set where
  constructor exceptional-lift-boundary
  field
    e6SectorSameObjectActionReceiptTyped : Bool
    a2FixedSectorReceiptTyped : Bool
    sixMixed27FibresTyped : Bool
    sixMixed27TransitivityReceiptsTyped : Bool
    schlafli27RecognitionReceiptTyped : Bool
    e8Branching72Plus6PlusSix27Typed : Bool

    minuscule27SameObjectReceiptTyped : Bool
    minuscule27ActionIntertwinerReceiptTyped : Bool
    minuscule27RelationIntertwinerReceiptTyped : Bool

    typedTernary27SixPlusFifteenPlusSixChartPaidInAgda : Bool
    typedTernary27SchlafliLeanProducerSourceWritten : Bool
    typedTernary27MinusculeRelationLeanProducerSourceWritten : Bool
    a5SixObjectS6LeanProducerSourceWritten : Bool
    independentRawTernary27E6ActionPaid : Bool
    selectedQ2StabilizerA5SameObjectPaid : Bool

    albert27AlgebraReceiptTyped : Bool

    leanExceptionalLiftProducerSourceWritten : Bool
    leanMinuscule27ProducerSourceWritten : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaLiteralE8EnumerationKernelPaidHere : Bool
    agdaMinuscule27SameObjectKernelPaidHere : Bool

    fullTernary240SameActionRecognitionPaid : Bool
    albert27AlgebraRecognitionPaid : Bool
    cardinalityAlonePromotesEitherRecognition : Bool
open ExceptionalLiftBoundary public

canonicalExceptionalLiftBoundary : ExceptionalLiftBoundary
canonicalExceptionalLiftBoundary =
  exceptional-lift-boundary
    true true true true true true
    true true true
    true true true true false false
    true
    true true false false false
    false false false
