module DASHI.Physics.YangMills.BalabanClayNormingFamilyOperatorBoundExact where

------------------------------------------------------------------------
-- SOURCE AUDIT
--
-- Mir Faizal and Arshid Shabir,
-- "Reflection-positive renormalization and the persistence of the mass gap
-- in lattice SU(N) Yang-Mills: Part (2)", International Journal of Geometric
-- Methods in Modern Physics 23 (2026).
-- DOI: 10.1142/S0219887826501136.
--
-- DASHI CONTRIBUTION
--
-- Approximate factorisation on a chosen observable family does not imply an
-- operator-norm estimate unless that family is norming and the estimate extends
-- continuously to the completed Hilbert space.  This module gives both the
-- exact required adapter and a finite countermodel showing why a non-norming
-- test family is insufficient.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data Empty : Set where

record NormingFamilyBridge
    (Operator Test Bound : Set) : Set₁ where
  field
    TestEstimate : Operator → Test → Bound → Set
    OperatorNormAtMost : Operator → Bound → Set
    testFamilyIsNorming : ∀ operator bound →
      (∀ test → TestEstimate operator test bound) →
      OperatorNormAtMost operator bound

open NormingFamilyBridge public

pointwiseNormingBoundsGiveOperatorNorm :
  ∀ {Operator Test Bound}
    (bridge : NormingFamilyBridge Operator Test Bound)
    operator bound →
  (∀ test → TestEstimate bridge operator test bound) →
  OperatorNormAtMost bridge operator bound
pointwiseNormingBoundsGiveOperatorNorm bridge operator bound pointwise =
  testFamilyIsNorming bridge operator bound pointwise

------------------------------------------------------------------------
-- Closed countermodel: one tested direction misses an uncontrolled direction.
------------------------------------------------------------------------

data ThreeVector : Set where
  zeroVector testedVector hiddenVector : ThreeVector

data SingletonTest : Set where
  onlyTest : SingletonTest

badOperator : ThreeVector → ThreeVector
badOperator zeroVector = zeroVector
badOperator testedVector = zeroVector
badOperator hiddenVector = hiddenVector

vectorNorm : ThreeVector → Nat
vectorNorm zeroVector = zero
vectorNorm testedVector = suc zero
vectorNorm hiddenVector = suc zero

infix 4 _≤ᴺ_
data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ᴺ n
  suc≤suc : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

testedDirectionBoundedByZero :
  vectorNorm (badOperator testedVector) ≤ᴺ zero
testedDirectionBoundedByZero = zero≤

oneNotBelowZero : suc zero ≤ᴺ zero → Empty
oneNotBelowZero ()

badOperatorNotGloballyBoundedByZero :
  (∀ vector → vectorNorm (badOperator vector) ≤ᴺ zero) → Empty
badOperatorNotGloballyBoundedByZero globalBound =
  oneNotBelowZero (globalBound hiddenVector)

record NonNormingTestCountermodel : Set where
  field
    pointwiseTestBound :
      vectorNorm (badOperator testedVector) ≤ᴺ zero
    globalZeroBoundImpossible :
      (∀ vector → vectorNorm (badOperator vector) ≤ᴺ zero) → Empty

oneObservableDoesNotControlOperatorNorm : NonNormingTestCountermodel
oneObservableDoesNotControlOperatorNorm = record
  { pointwiseTestBound = testedDirectionBoundedByZero
  ; globalZeroBoundImpossible = badOperatorNotGloballyBoundedByZero
  }

normingFamilyBridgeLevel : ProofLevel
normingFamilyBridgeLevel = machineChecked

nonNormingFamilyCountermodelLevel : ProofLevel
nonNormingFamilyCountermodelLevel = machineChecked
