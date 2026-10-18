{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonNativePhysicalMeasureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Preferred
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonCylinderBoundDataExact as Bounds
import DASHI.Physics.YangMills.BalabanLiteralWilsonNativeThermodynamicProducerExact as Native

------------------------------------------------------------------------
-- NATIVE WILSON ALGEBRA ALL THE WAY TO PhysicalMeasureConvergenceData.
------------------------------------------------------------------------

record NativeWilsonPreferredPhysicalMeasureInputs
    (Measure : Set) (n : Nat)
    (operationsInputs : Native.NativeWilsonOSOperationsInputs Measure n)
    : Set₁ where
  field
    thermodynamicInputs :
      Native.NativeWilsonThermodynamicInputs Measure n operationsInputs

    preferredExpectationInputs :
      Preferred.PreferredDiagonalExpectationProducerInputs
        Measure (Wilson.RationalWilsonObservable n) ℚ
        (Native.nativeWilsonThermodynamicData thermodynamicInputs)

open NativeWilsonPreferredPhysicalMeasureInputs public

nativeWilsonExpectationProducer :
  ∀ {Measure n operationsInputs} →
  NativeWilsonPreferredPhysicalMeasureInputs Measure n operationsInputs →
  T5.PhysicalExpectationProducerData
    Measure (Wilson.RationalWilsonObservable n) ℚ
nativeWilsonExpectationProducer inputs =
  Preferred.compilePreferredDiagonalExpectationProducer
    (preferredExpectationInputs inputs)

nativeWilsonPhysicalMeasureData :
  ∀ {Measure n operationsInputs} →
  NativeWilsonPreferredPhysicalMeasureInputs Measure n operationsInputs →
  Gram.PhysicalMeasureConvergenceData
    Measure (Wilson.RationalWilsonObservable n) ℚ
nativeWilsonPhysicalMeasureData inputs =
  T5.physicalMeasureConvergenceDataFromProducer
    (nativeWilsonExpectationProducer inputs)

nativePhysicalMeasureMultiplyIsWilsonMultiply :
  ∀ {Measure n operationsInputs}
    (inputs :
      NativeWilsonPreferredPhysicalMeasureInputs Measure n operationsInputs)
    left right →
  Gram.multiplyObservable
    (Gram.operations (nativeWilsonPhysicalMeasureData inputs))
    left right
  ≡ Wilson.multiplyObservable left right
nativePhysicalMeasureMultiplyIsWilsonMultiply inputs left right = refl

nativePhysicalMeasureBoundedIsQuantitative :
  ∀ {Measure n operationsInputs}
    (inputs :
      NativeWilsonPreferredPhysicalMeasureInputs Measure n operationsInputs)
    observable →
  Gram.BoundedObservable (nativeWilsonPhysicalMeasureData inputs) observable
  ≡ Native.QuantitativelyBounded observable
nativePhysicalMeasureBoundedIsQuantitative inputs observable = refl

quantitativeBoundIsNativePhysicalBounded :
  ∀ {Measure n operationsInputs}
    (inputs :
      NativeWilsonPreferredPhysicalMeasureInputs Measure n operationsInputs)
    observable majorant →
  Bounds.QuantitativeBound observable majorant →
  Gram.BoundedObservable (nativeWilsonPhysicalMeasureData inputs) observable
quantitativeBoundIsNativePhysicalBounded inputs observable majorant proof =
  Native.quantitativeBoundIsBoundedObservable majorant proof

finiteWilsonCylinderIsNativePhysicalBounded :
  ∀ {Measure n operationsInputs}
    (inputs :
      NativeWilsonPreferredPhysicalMeasureInputs Measure n operationsInputs)
    paths →
  Gram.BoundedObservable (nativeWilsonPhysicalMeasureData inputs)
    (T5.productLoopObservable
      Bounds.literalRationalSU2WilsonCylinderBounds paths)
finiteWilsonCylinderIsNativePhysicalBounded inputs paths =
  quantitativeBoundIsNativePhysicalBounded inputs _
    (T5.productLoopBound Bounds.literalRationalSU2WilsonCylinderBounds paths)
    (Bounds.finiteLiteralWilsonCylinderBound paths)

nativeWilsonMeasureAlgebraAttachmentLevel : ProofLevel
nativeWilsonMeasureAlgebraAttachmentLevel = machineChecked
