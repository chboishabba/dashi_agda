{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralCylinderLimitPhysicalMeasureExact where

------------------------------------------------------------------------
-- LITERAL A: THE CYLINDER LIMIT FUNCTIONAL IS THE PHYSICAL MEASURE CARRIER
--
-- For the pinned physical carriers
--
--   ContinuumMeasure = PhysicalContinuumYMMeasure Observable ℚ
--
-- and that carrier is literally an expectation functional Observable → ℚ.
-- Therefore no abstract representation authority is needed merely to obtain
-- the pinned continuum-measure object: the already-proved positive normalized
-- cylinder limit functional IS the carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCylinderExpectationLimitMeasureExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

literalLimitContinuumMeasure :
  ∀ {Observable}
    (dataSet : A.CylinderExpectationLimitData Observable) →
  Physical.PhysicalContinuumYMMeasure Observable ℚ
literalLimitContinuumMeasure dataSet =
  Physical.physicalContinuumMeasure
    (A.limitExpectation dataSet)

literalLimitMeasureRepresentation :
  ∀ {Observable}
    (dataSet : A.CylinderExpectationLimitData Observable) →
  A.CylinderMeasureRepresentation
    Observable
    (Physical.PhysicalContinuumYMMeasure Observable ℚ)
    dataSet
literalLimitMeasureRepresentation dataSet = record
  { A.CylinderMeasureRepresentation.measure =
      literalLimitContinuumMeasure dataSet
  ; A.CylinderMeasureRepresentation.expectation =
      Physical.expectation
  ; A.CylinderMeasureRepresentation.represented =
      λ observable → refl
  }

literalLimitExpectationIsPhysicalExpectation :
  ∀ {Observable}
    (dataSet : A.CylinderExpectationLimitData Observable)
    observable →
  Physical.expectation
    (literalLimitContinuumMeasure dataSet)
    observable
  ≡
  A.limitExpectation dataSet observable
literalLimitExpectationIsPhysicalExpectation dataSet observable = refl

literalLimitPhysicalMeasureNormalized :
  ∀ {Observable}
    (dataSet : A.CylinderExpectationLimitData Observable) →
  Physical.expectation
    (literalLimitContinuumMeasure dataSet)
    (A.one dataSet)
  ≡ 1ℚ
literalLimitPhysicalMeasureNormalized dataSet =
  A.limitOne dataSet

literalLimitPhysicalMeasurePositive :
  ∀ {Observable}
    (dataSet : A.CylinderExpectationLimitData Observable)
    observable →
  A.Nonnegative dataSet observable →
  0ℚ ≤
    Physical.expectation
      (literalLimitContinuumMeasure dataSet)
      observable
literalLimitPhysicalMeasurePositive dataSet observable nonnegative =
  A.limitPositive dataSet observable nonnegative

literalCylinderLimitPhysicalMeasureCompilerLevel : ProofLevel
literalCylinderLimitPhysicalMeasureCompilerLevel = machineChecked

-- What remains on literal A is physical, not representational:
-- identify the finite CMP119 cylinder expectations with this dataSet and prove
-- continuum/OS/Schwinger reconstruction properties of this SAME measure.
literalCMP119CylinderLimitIdentificationLevel : ProofLevel
literalCMP119CylinderLimitIdentificationLevel = conditional

literalLimitMeasureOSReconstructionLevel : ProofLevel
literalLimitMeasureOSReconstructionLevel = conditional
