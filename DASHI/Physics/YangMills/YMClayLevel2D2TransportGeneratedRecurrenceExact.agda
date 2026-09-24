{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D2TransportGeneratedRecurrenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Transport
import DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldExact as D2

------------------------------------------------------------------------
-- D2b / CANONICAL TRANSPORT-GENERATED COEFFICIENT TRAJECTORIES
--
-- Once D2a supplies the physical CompositeRGParallelTransport, there is no need
-- to postulate two additional one-step recurrence theorems for the physical and
-- AF coefficient families.  Define both trajectories by the SAME canonical
-- transportToDepth operation.  Their one-step laws are then definitional.
--
-- The only D2b datum left is the common UV normalization of the two initial
-- operator coordinates.  All-depth equality remains the existing induction
-- theorem downstream.
------------------------------------------------------------------------

record TransportGeneratedCoefficientInputs
    (Operator : Set)
    (transport : Transport.CompositeRGParallelTransport Operator) : Set₁ where
  field
    physicalUVOperator : Operator
    asymptoticFreedomUVOperator : Operator
    sameUVNormalization :
      physicalUVOperator ≡ asymptoticFreedomUVOperator

open TransportGeneratedCoefficientInputs public

transportGeneratedRecurrence :
  ∀ {Operator}
    (transport : Transport.CompositeRGParallelTransport Operator) →
  TransportGeneratedCoefficientInputs Operator transport →
  D2.SameCompositeOperatorCoefficientRecurrence Operator transport
transportGeneratedRecurrence transport inputs = record
  { D2.SameCompositeOperatorCoefficientRecurrence.physicalOperatorCoefficient =
      λ depth →
        Transport.transportToDepth transport depth
          (physicalUVOperator inputs)
  ; D2.SameCompositeOperatorCoefficientRecurrence.asymptoticFreedomOperatorCoefficient =
      λ depth →
        Transport.transportToDepth transport depth
          (asymptoticFreedomUVOperator inputs)
  ; D2.SameCompositeOperatorCoefficientRecurrence.sameUVNormalization =
      sameUVNormalization inputs
  ; D2.SameCompositeOperatorCoefficientRecurrence.physicalUsesSameOperatorMixing =
      λ depth → refl
  ; D2.SameCompositeOperatorCoefficientRecurrence.asymptoticFreedomUsesSameOperatorMixing =
      λ depth → refl
  }

transportGeneratedCoefficientsEqualAtEveryDepth :
  ∀ {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator}
    (inputs : TransportGeneratedCoefficientInputs Operator transport) →
  ∀ depth →
  D2.physicalOperatorCoefficient
      (transportGeneratedRecurrence transport inputs) depth
  ≡ D2.asymptoticFreedomOperatorCoefficient
      (transportGeneratedRecurrence transport inputs) depth
transportGeneratedCoefficientsEqualAtEveryDepth
    {transport = transport} inputs =
  D2.operatorCoefficientsEqualAtEveryDepth
    (transportGeneratedRecurrence transport inputs)

------------------------------------------------------------------------
-- Frontier reduction.
------------------------------------------------------------------------

independentPhysicalOneStepRecurrenceProofRequired : Bool
independentPhysicalOneStepRecurrenceProofRequired = false

independentPhysicalOneStepRecurrenceProofRequiredIsFalse :
  independentPhysicalOneStepRecurrenceProofRequired ≡ false
independentPhysicalOneStepRecurrenceProofRequiredIsFalse = refl

independentAFOneStepRecurrenceProofRequired : Bool
independentAFOneStepRecurrenceProofRequired = false

independentAFOneStepRecurrenceProofRequiredIsFalse :
  independentAFOneStepRecurrenceProofRequired ≡ false
independentAFOneStepRecurrenceProofRequiredIsFalse = refl

commonUVNormalizationStillPhysical : Bool
commonUVNormalizationStillPhysical = true

commonUVNormalizationStillPhysicalIsTrue :
  commonUVNormalizationStillPhysical ≡ true
commonUVNormalizationStillPhysicalIsTrue = refl

transportGeneratedRecurrenceCompilerLevel : ProofLevel
transportGeneratedRecurrenceCompilerLevel = machineChecked

physicalCompositeTransportLevel : ProofLevel
physicalCompositeTransportLevel = Transport.physicalYMCompositeMixingLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
