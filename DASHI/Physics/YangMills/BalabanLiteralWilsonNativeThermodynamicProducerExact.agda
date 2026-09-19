{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonNativeThermodynamicProducerExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
open import Data.Product.Base using (Σ; _,_)
open import Function.Base using (id)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonCylinderBoundDataExact as Bounds

------------------------------------------------------------------------
-- NATIVE LITERAL-WILSON T5 PRODUCER
--
-- The observable carrier is the actual rational-SU(2) Wilson function space.
-- Pointwise multiplication is therefore the T5 multiplication by definition,
-- and "bounded observable" means existence of an explicit quantitative
-- majorant.  This is upstream of PhysicalMeasureConvergenceData, so S2b/S2c
-- are constructional facts rather than freely supplied downstream welds.
------------------------------------------------------------------------

QuantitativelyBounded :
  ∀ {n} → Wilson.RationalWilsonObservable n → Set
QuantitativelyBounded observable =
  Σ ℚ (λ majorant → Bounds.QuantitativeBound observable majorant)

quantitativeBoundIsBoundedObservable :
  ∀ {n} {observable : Wilson.RationalWilsonObservable n} majorant →
  Bounds.QuantitativeBound observable majorant →
  QuantitativelyBounded observable
quantitativeBoundIsBoundedObservable majorant proof = majorant , proof

record NativeWilsonOSOperationsInputs
    (Measure : Set) (n : Nat) : Set₁ where
  field
    reflectObservable :
      Wilson.RationalWilsonObservable n →
      Wilson.RationalWilsonObservable n
    expectation :
      Measure → Wilson.RationalWilsonObservable n → ℚ

open NativeWilsonOSOperationsInputs public

nativeWilsonOSOperations :
  ∀ {Measure n} →
  NativeWilsonOSOperationsInputs Measure n →
  Gram.PhysicalOSOperations
    Measure (Wilson.RationalWilsonObservable n) ℚ
nativeWilsonOSOperations inputs = record
  { Gram.PhysicalOSOperations.zero = 0ℚ
  ; Gram.PhysicalOSOperations.add = _+_
  ; Gram.PhysicalOSOperations.multiply = _*_
  ; Gram.PhysicalOSOperations.conjugate = id
  ; Gram.PhysicalOSOperations.reflectObservable = reflectObservable inputs
  ; Gram.PhysicalOSOperations.multiplyObservable = Wilson.multiplyObservable
  ; Gram.PhysicalOSOperations.expectation = expectation inputs
  }

nativeMultiplyIsLiteralWilsonMultiply :
  ∀ {Measure n} (inputs : NativeWilsonOSOperationsInputs Measure n)
    left right →
  Gram.multiplyObservable (nativeWilsonOSOperations inputs) left right
  ≡ Wilson.multiplyObservable left right
nativeMultiplyIsLiteralWilsonMultiply inputs left right = refl

record NativeWilsonThermodynamicInputs
    (Measure : Set) (n : Nat)
    (operationsInputs : NativeWilsonOSOperationsInputs Measure n)
    : Set₁ where
  private
    Observable = Wilson.RationalWilsonObservable n
    operations = nativeWilsonOSOperations operationsInputs
  field
    scalarConvergence :
      Gram.ScalarConvergenceAlgebra ℚ
        (Gram.zero operations)
        (Gram.add operations)
        (Gram.multiply operations)

    finiteVolumeMeasure : Nat → Nat → Measure
    thermodynamicMeasure : Nat → Measure
    continuumMeasure : Measure
    diagonalVolume : Nat → Nat

    LocalGaugeInvariant RenormalizedObservable : Observable → Set

    finiteVolumePairTail : ∀ cutoff left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      T5.TailControlledConvergence ℚ
        (Gram.Converges scalarConvergence)
        (λ volume →
          Gram.expectation operations (finiteVolumeMeasure cutoff volume)
            (Wilson.multiplyObservable
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations (thermodynamicMeasure cutoff)
          (Wilson.multiplyObservable
            (Gram.reflectObservable operations left) right))

    continuumPairTail : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      T5.TailControlledConvergence ℚ
        (Gram.Converges scalarConvergence)
        (λ cutoff →
          Gram.expectation operations (thermodynamicMeasure cutoff)
            (Wilson.multiplyObservable
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations continuumMeasure
          (Wilson.multiplyObservable
            (Gram.reflectObservable operations left) right))

    diagonalPairTail : ∀ left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      T5.TailControlledConvergence ℚ
        (Gram.Converges scalarConvergence)
        (λ cutoff →
          Gram.expectation operations
            (finiteVolumeMeasure cutoff (diagonalVolume cutoff))
            (Wilson.multiplyObservable
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations continuumMeasure
          (Wilson.multiplyObservable
            (Gram.reflectObservable operations left) right))

    renormalizedDiagonalPairTail : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      T5.TailControlledConvergence ℚ
        (Gram.Converges scalarConvergence)
        (λ cutoff →
          Gram.expectation operations
            (finiteVolumeMeasure cutoff (diagonalVolume cutoff))
            (Wilson.multiplyObservable
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations continuumMeasure
          (Wilson.multiplyObservable
            (Gram.reflectObservable operations left) right))

open NativeWilsonThermodynamicInputs public

nativeWilsonThermodynamicData :
  ∀ {Measure n}
    {operationsInputs : NativeWilsonOSOperationsInputs Measure n} →
  NativeWilsonThermodynamicInputs Measure n operationsInputs →
  T5.PhysicalThermodynamicClusterData
    Measure (Wilson.RationalWilsonObservable n) ℚ
nativeWilsonThermodynamicData
    {operationsInputs = operationsInputs} inputs = record
  { T5.PhysicalThermodynamicClusterData.operations =
      nativeWilsonOSOperations operationsInputs
  ; T5.PhysicalThermodynamicClusterData.scalarConvergence =
      scalarConvergence inputs
  ; T5.PhysicalThermodynamicClusterData.finiteVolumeMeasure =
      finiteVolumeMeasure inputs
  ; T5.PhysicalThermodynamicClusterData.thermodynamicMeasure =
      thermodynamicMeasure inputs
  ; T5.PhysicalThermodynamicClusterData.continuumMeasure =
      continuumMeasure inputs
  ; T5.PhysicalThermodynamicClusterData.diagonalVolume =
      diagonalVolume inputs
  ; T5.PhysicalThermodynamicClusterData.LocalGaugeInvariant =
      LocalGaugeInvariant inputs
  ; T5.PhysicalThermodynamicClusterData.RenormalizedObservable =
      RenormalizedObservable inputs
  ; T5.PhysicalThermodynamicClusterData.BoundedObservable =
      QuantitativelyBounded
  ; T5.PhysicalThermodynamicClusterData.finiteVolumePairTail =
      finiteVolumePairTail inputs
  ; T5.PhysicalThermodynamicClusterData.continuumPairTail =
      continuumPairTail inputs
  ; T5.PhysicalThermodynamicClusterData.diagonalPairTail =
      diagonalPairTail inputs
  ; T5.PhysicalThermodynamicClusterData.renormalizedDiagonalPairTail =
      renormalizedDiagonalPairTail inputs
  }

nativeWilsonBoundedObservableIsQuantitative :
  ∀ {Measure n}
    {operationsInputs : NativeWilsonOSOperationsInputs Measure n}
    (inputs : NativeWilsonThermodynamicInputs Measure n operationsInputs)
    observable →
  T5.BoundedObservable (nativeWilsonThermodynamicData inputs) observable
  ≡ QuantitativelyBounded observable
nativeWilsonBoundedObservableIsQuantitative inputs observable = refl

literalPathIsNativeBounded :
  ∀ {Measure n}
    {operationsInputs : NativeWilsonOSOperationsInputs Measure n}
    (inputs : NativeWilsonThermodynamicInputs Measure n operationsInputs)
    (path : Wilson.RationalWilsonPath n) →
  T5.BoundedObservable (nativeWilsonThermodynamicData inputs)
    (Wilson.literalWilsonPathObservable path)
literalPathIsNativeBounded inputs path =
  quantitativeBoundIsBoundedObservable 1ℚ
    (Bounds.quantitativeWilsonPathBound path)

identityIsNativeBounded :
  ∀ {Measure n}
    {operationsInputs : NativeWilsonOSOperationsInputs Measure n}
    (inputs : NativeWilsonThermodynamicInputs Measure n operationsInputs) →
  T5.BoundedObservable (nativeWilsonThermodynamicData inputs)
    Wilson.oneObservable
identityIsNativeBounded inputs =
  quantitativeBoundIsBoundedObservable 1ℚ Bounds.quantitativeOneBound

nativeWilsonThermodynamicCompilerLevel : ProofLevel
nativeWilsonThermodynamicCompilerLevel = machineChecked
