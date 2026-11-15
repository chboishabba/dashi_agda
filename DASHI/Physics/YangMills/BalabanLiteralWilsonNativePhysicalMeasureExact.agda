{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonNativePhysicalMeasureExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Preferred
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonCylinderBoundDataExact as Bounds
import DASHI.Physics.YangMills.BalabanLiteralWilsonNativeThermodynamicProducerExact as Native
import DASHI.Physics.YangMills.BalabanClayT5MarkedPreferredExpectationRound445Exact as R445
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP

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


------------------------------------------------------------------------
-- SOURCE-FIRST R445 -> NATIVE P2 PHYSICAL MEASURE SNOWBALL
--
-- A single, same-object marked-polymer moment closure is already compiled
-- by R444/R445 to the preferred diagonal expectation inputs. Rather than
-- manufacture a second moment source when constructing the native rational
-- Wilson measure, reuse exactly that R445 output on the SAME
-- nativeWilsonThermodynamicData family.
--
-- Source mathematics: Bałaban's cluster/RG series (CMP 116/119/122),
-- Fernández–Procacci marked-polymer criterion and the corresponding
-- published continuum literature. DASHI owns this typed composition only.
--
-- This is not a new selected bounded-observable tail estimate and not an
-- unconditional continuum YM measure. Physical R445 witnesses remain inputs.
------------------------------------------------------------------------

nativeWilsonPreferredFromMarked :
  ∀ {Measure : Set} {n : Nat}
    {operationsInputs : Native.NativeWilsonOSOperationsInputs Measure n}
    {Polymer : Set}
    {model : FP.AbstractPolymerModel Polymer}
    {marked :
      FP.MarkedActivityData Polymer (Wilson.RationalWilsonObservable n) model}
    {closure :
      Physical.MarkedMomentClosure
        Polymer (Wilson.RationalWilsonObservable n) model marked}
    (thermodynamic :
      Native.NativeWilsonThermodynamicInputs Measure n operationsInputs) →
  R445.MarkedPreferredExpectationInputs
    (Native.nativeWilsonThermodynamicData thermodynamic)
    model marked closure →
  NativeWilsonPreferredPhysicalMeasureInputs Measure n operationsInputs
nativeWilsonPreferredFromMarked thermodynamic preferred = record
  { NativeWilsonPreferredPhysicalMeasureInputs.thermodynamicInputs =
      thermodynamic
  ; NativeWilsonPreferredPhysicalMeasureInputs.preferredExpectationInputs =
      R445.asPreferredDiagonalExpectationInputs preferred
  }

nativeWilsonPhysicalMeasureFromMarked :
  ∀ {Measure : Set} {n : Nat}
    {operationsInputs : Native.NativeWilsonOSOperationsInputs Measure n}
    {Polymer : Set}
    {model : FP.AbstractPolymerModel Polymer}
    {marked :
      FP.MarkedActivityData Polymer (Wilson.RationalWilsonObservable n) model}
    {closure :
      Physical.MarkedMomentClosure
        Polymer (Wilson.RationalWilsonObservable n) model marked}
    (thermodynamic :
      Native.NativeWilsonThermodynamicInputs Measure n operationsInputs)
    (preferred : R445.MarkedPreferredExpectationInputs
      (Native.nativeWilsonThermodynamicData thermodynamic)
      model marked closure) →
  Gram.PhysicalMeasureConvergenceData
    Measure (Wilson.RationalWilsonObservable n) ℚ
nativeWilsonPhysicalMeasureFromMarked thermodynamic preferred =
  nativeWilsonPhysicalMeasureData
    (nativeWilsonPreferredFromMarked thermodynamic preferred)

nativeWilsonMarkedMomentIsNotRechosen : Bool
nativeWilsonMarkedMomentIsNotRechosen = true

nativeWilsonMarkedMomentIsNotRechosenIsTrue :
  nativeWilsonMarkedMomentIsNotRechosen ≡ true
nativeWilsonMarkedMomentIsNotRechosenIsTrue = refl

-- No exact-head Agda check is claimed for this new adapter in this session.
nativeWilsonR445MarkedPreferredCompilerLevel : ProofLevel
nativeWilsonR445MarkedPreferredCompilerLevel = conditional

nativeWilsonR445PhysicalTailInputsLevel : ProofLevel
nativeWilsonR445PhysicalTailInputsLevel =
  R445.round445BoundedTailInputsLevel
