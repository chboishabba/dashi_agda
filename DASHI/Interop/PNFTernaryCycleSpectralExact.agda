module DASHI.Interop.PNFTernaryCycleSpectralExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Fan R. K. Chung,
-- "Spectral Graph Theory", CBMS Regional Conference Series in Mathematics 92,
-- American Mathematical Society, 1997.
-- DOI: 10.1090/cbms/092.
--
-- DASHI CONTRIBUTION
--
-- The existing canonical PNF contradiction 2-cell has three 0-cell witnesses
-- and a triangular 1-cell boundary.  Forgetting the signed/typed edge weights
-- gives the ordinary three-cycle C3 (= K3).  This module computes its
-- unnormalised integer Laplacian exactly:
--
--   constants                -> eigenvalue 0
--   every integer zero-sum field -> eigenvalue 3.
--
-- The theorem is attached to the existing PNF triangle witnesses, and agrees
-- numerically with the already-recorded Z/3 cycle gap in
-- FiniteCarrierSpectralGapZ7Receipt.  It does NOT identify the unsigned C3
-- operator with the full signed-residual PNF Delta0 operator; that comparison
-- remains an explicit future weighted/signed adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Interop.PNFHodgeResidualTopology as Hodge
import DASHI.Physics.Closure.FiniteCarrierSpectralGapZ7Receipt as Z7

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

------------------------------------------------------------------------
-- The three vertices are tied directly to the canonical PNF 2-cell boundary.
------------------------------------------------------------------------

data TriangleVertex : Set where
  vertex0 vertex1 vertex2 : TriangleVertex

pnfVertexRef : TriangleVertex → Hodge.PNFZeroCellRef
pnfVertexRef vertex0 = Hodge.zeroCellRef Hodge.canonicalZeroCell0
pnfVertexRef vertex1 = Hodge.zeroCellRef Hodge.canonicalZeroCell1
pnfVertexRef vertex2 = Hodge.zeroCellRef Hodge.canonicalZeroCell2

canonicalTriangleVertexRefs : List Hodge.PNFZeroCellRef
canonicalTriangleVertexRefs =
  pnfVertexRef vertex0
  ∷ pnfVertexRef vertex1
  ∷ pnfVertexRef vertex2
  ∷ []

triangleVerticesMatchExistingCycleFeature :
  canonicalTriangleVertexRefs
  ≡ Hodge.featureWitness0Cells Hodge.canonicalCycleFeature
triangleVerticesMatchExistingCycleFeature = refl

triangleTwoCellIsContradictionCell :
  Hodge.twoCellKind Hodge.canonicalContradictionTwoCell
  ≡ Hodge.contradictionTriangle2Cell
triangleTwoCellIsContradictionCell = refl

------------------------------------------------------------------------
-- Integer-valued fields and the unnormalised C3 graph Laplacian.
------------------------------------------------------------------------

record TriangleField : Set where
  constructor triangleField
  field
    value0 value1 value2 : ℤ

open TriangleField public

zeroField : TriangleField
zeroField = triangleField (+ 0) (+ 0) (+ 0)

constantField : ℤ → TriangleField
constantField value = triangleField value value value

scaleField : ℤ → TriangleField → TriangleField
scaleField scalar field =
  triangleField
    (scalar * value0 field)
    (scalar * value1 field)
    (scalar * value2 field)

cycleLaplacian : TriangleField → TriangleField
cycleLaplacian field =
  triangleField
    (((+ 2) * value0 field) - value1 field - value2 field)
    (((+ 2) * value1 field) - value2 field - value0 field)
    (((+ 2) * value2 field) - value0 field - value1 field)

fieldExtensional :
  (left right : TriangleField) →
  value0 left ≡ value0 right →
  value1 left ≡ value1 right →
  value2 left ≡ value2 right →
  left ≡ right
fieldExtensional
  (triangleField left0 left1 left2)
  (triangleField right0 right1 right2)
  refl refl refl = refl

constantKernel :
  (value : ℤ) →
  cycleLaplacian (constantField value) ≡ zeroField
constantKernel value =
  fieldExtensional
    (cycleLaplacian (constantField value))
    zeroField
    (RingZ.solve 1
      (λ x →
        ( ((Κ (+ 2) ⊗ x) ⊕ (⊝ x)) ⊕ (⊝ x)
        , Κ (+ 0)))
      refl value)
    (RingZ.solve 1
      (λ x →
        ( ((Κ (+ 2) ⊗ x) ⊕ (⊝ x)) ⊕ (⊝ x)
        , Κ (+ 0)))
      refl value)
    (RingZ.solve 1
      (λ x →
        ( ((Κ (+ 2) ⊗ x) ⊕ (⊝ x)) ⊕ (⊝ x)
        , Κ (+ 0)))
      refl value)

------------------------------------------------------------------------
-- A parameterization of the full integer zero-sum sector.
------------------------------------------------------------------------

zeroSumField : ℤ → ℤ → TriangleField
zeroSumField u v =
  triangleField
    (u + v)
    (- u)
    (- v)

fieldSum : TriangleField → ℤ
fieldSum field = value0 field + value1 field + value2 field

zeroSumFieldReallySumsToZero :
  (u v : ℤ) →
  fieldSum (zeroSumField u v) ≡ + 0
zeroSumFieldReallySumsToZero u v =
  RingZ.solve 2
    (λ u v →
      ( ((u ⊕ v) ⊕ (⊝ u)) ⊕ (⊝ v)
      , Κ (+ 0)))
    refl u v

zeroSumFieldEigenvalueThree :
  (u v : ℤ) →
  cycleLaplacian (zeroSumField u v)
  ≡ scaleField (+ 3) (zeroSumField u v)
zeroSumFieldEigenvalueThree u v =
  fieldExtensional
    (cycleLaplacian (zeroSumField u v))
    (scaleField (+ 3) (zeroSumField u v))
    (RingZ.solve 2
      (λ u v →
        ( ((Κ (+ 2) ⊗ (u ⊕ v)) ⊕ u) ⊕ v
        , Κ (+ 3) ⊗ (u ⊕ v)))
      refl u v)
    (RingZ.solve 2
      (λ u v →
        ( ((Κ (+ 2) ⊗ (⊝ u)) ⊕ v) ⊕ (⊝ (u ⊕ v))
        , Κ (+ 3) ⊗ (⊝ u)))
      refl u v)
    (RingZ.solve 2
      (λ u v →
        ( ((Κ (+ 2) ⊗ (⊝ v)) ⊕ (⊝ (u ⊕ v))) ⊕ u
        , Κ (+ 3) ⊗ (⊝ v)))
      refl u v)

firstCoordinateFromZeroSum :
  (a b c : ℤ) →
  a + b + c ≡ + 0 →
  a ≡ (- b) + (- c)
firstCoordinateFromZeroSum a b c sumIsZero =
  trans
    (RingZ.solve 3
      (λ a b c →
        ( a
        , ((((a ⊕ b) ⊕ c) ⊕ (⊝ b)) ⊕ (⊝ c))))
      refl a b c)
    (trans
      (cong (λ z → (z + (- b)) + (- c)) sumIsZero)
      (RingZ.solve 2
        (λ b c →
          ( ((Κ (+ 0) ⊕ (⊝ b)) ⊕ (⊝ c))
          , (⊝ b) ⊕ (⊝ c)))
        refl b c))

zeroSumRepresentation :
  (field : TriangleField) →
  fieldSum field ≡ + 0 →
  field
  ≡ zeroSumField (- value1 field) (- value2 field)
zeroSumRepresentation (triangleField a b c) sumIsZero =
  fieldExtensional
    (triangleField a b c)
    (zeroSumField (- b) (- c))
    (firstCoordinateFromZeroSum a b c sumIsZero)
    (RingZ.solve 1
      (λ b → (b , ⊝ (⊝ b)))
      refl b)
    (RingZ.solve 1
      (λ c → (c , ⊝ (⊝ c)))
      refl c)

zeroSumSectorEigenvalueThree :
  (field : TriangleField) →
  fieldSum field ≡ + 0 →
  cycleLaplacian field ≡ scaleField (+ 3) field
zeroSumSectorEigenvalueThree field sumIsZero
  rewrite zeroSumRepresentation field sumIsZero =
  zeroSumFieldEigenvalueThree
    (- value1 field)
    (- value2 field)

------------------------------------------------------------------------
-- The existing finite Z/3 cycle-gap receipt carries the same gap value.
------------------------------------------------------------------------

existingFiniteZ3CycleGapIsThree :
  Z7.z3CycleGap Z7.canonicalFiniteCarrierSpectralGapZ7Receipt ≡ 3
existingFiniteZ3CycleGapIsThree =
  Z7.z3CycleGapIsThree Z7.canonicalFiniteCarrierSpectralGapZ7Receipt

pnfDeltaZeroIsImplementableLayer :
  Hodge.laplacianBoundaryLayer Hodge.Δ0
  ≡ Hodge.signedGraphLaplacian0Implementable
pnfDeltaZeroIsImplementableLayer = refl

record PNFTernaryCycleSpectralBoundary : Set where
  field
    unsignedTriangleSpectrumConstructed : Bool
    unsignedTriangleSpectrumConstructedIsTrue :
      unsignedTriangleSpectrumConstructed ≡ true

    zeroSumEigenvalueIsThree : Bool
    zeroSumEigenvalueIsThreeIsTrue :
      zeroSumEigenvalueIsThree ≡ true

    existingZ3GapReceiptAgreesNumerically : Bool
    existingZ3GapReceiptAgreesNumericallyIsTrue :
      existingZ3GapReceiptAgreesNumerically ≡ true

    unsignedCycleIdentifiedWithFullSignedResidualDelta0 : Bool
    unsignedCycleIdentifiedWithFullSignedResidualDelta0IsFalse :
      unsignedCycleIdentifiedWithFullSignedResidualDelta0 ≡ false

    finiteGapPromotedToContinuumPhysics : Bool
    finiteGapPromotedToContinuumPhysicsIsFalse :
      finiteGapPromotedToContinuumPhysics ≡ false

canonicalPNFTernaryCycleSpectralBoundary :
  PNFTernaryCycleSpectralBoundary
canonicalPNFTernaryCycleSpectralBoundary =
  record
    { unsignedTriangleSpectrumConstructed = true
    ; unsignedTriangleSpectrumConstructedIsTrue = refl
    ; zeroSumEigenvalueIsThree = true
    ; zeroSumEigenvalueIsThreeIsTrue = refl
    ; existingZ3GapReceiptAgreesNumerically = true
    ; existingZ3GapReceiptAgreesNumericallyIsTrue = refl
    ; unsignedCycleIdentifiedWithFullSignedResidualDelta0 = false
    ; unsignedCycleIdentifiedWithFullSignedResidualDelta0IsFalse = refl
    ; finiteGapPromotedToContinuumPhysics = false
    ; finiteGapPromotedToContinuumPhysicsIsFalse = refl
    }
