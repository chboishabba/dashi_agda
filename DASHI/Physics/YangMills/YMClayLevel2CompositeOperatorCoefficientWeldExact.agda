{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Transport
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as OPE

------------------------------------------------------------------------
-- LEVEL-2 D2: USE THE EXISTING COMPOSITE-OPERATOR RG TRANSPORT DIRECTLY
--
-- The earlier D2 owner introduced an abstract RGCoordinate and a second
-- oneStepMixing-shaped interface.  The repository already has the correct
-- operator carrier:
--
--   Transport.CompositeRGParallelTransport Operator
--     with
--   Transport.oneStepMixing : Nat -> Operator -> Operator.
--
-- Therefore no second mixing-map abstraction is needed.  Once the physical
-- same-family coefficient trajectory and the AF/reference trajectory are both
-- actual Operator-valued coordinates transported by this SAME map, with the
-- SAME UV normalization, the existing OPE recurrence theorem applies literally.
------------------------------------------------------------------------

record SameCompositeOperatorCoefficientRecurrence
    (Operator : Set)
    (transport : Transport.CompositeRGParallelTransport Operator) : Set₁ where
  field
    physicalOperatorCoefficient : Nat → Operator
    asymptoticFreedomOperatorCoefficient : Nat → Operator

    sameUVNormalization :
      physicalOperatorCoefficient 0
      ≡ asymptoticFreedomOperatorCoefficient 0

    physicalUsesSameOperatorMixing :
      ∀ depth →
      physicalOperatorCoefficient (Agda.Builtin.Nat.suc depth)
      ≡ Transport.oneStepMixing transport depth
          (physicalOperatorCoefficient depth)

    asymptoticFreedomUsesSameOperatorMixing :
      ∀ depth →
      asymptoticFreedomOperatorCoefficient (Agda.Builtin.Nat.suc depth)
      ≡ Transport.oneStepMixing transport depth
          (asymptoticFreedomOperatorCoefficient depth)

open SameCompositeOperatorCoefficientRecurrence public

asCoefficientRGRecurrence :
  ∀ {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator} →
  SameCompositeOperatorCoefficientRecurrence Operator transport →
  OPE.CoefficientRGRecurrence Operator
asCoefficientRGRecurrence {transport = transport} dataSet = record
  { OPE.CoefficientRGRecurrence.oneStepMixing =
      Transport.oneStepMixing transport
  ; OPE.CoefficientRGRecurrence.physicalCoefficient =
      physicalOperatorCoefficient dataSet
  ; OPE.CoefficientRGRecurrence.asymptoticFreedomCoefficient =
      asymptoticFreedomOperatorCoefficient dataSet
  ; OPE.CoefficientRGRecurrence.sameUVNormalization =
      sameUVNormalization dataSet
  ; OPE.CoefficientRGRecurrence.physicalOneStep =
      physicalUsesSameOperatorMixing dataSet
  ; OPE.CoefficientRGRecurrence.asymptoticFreedomOneStep =
      asymptoticFreedomUsesSameOperatorMixing dataSet
  }

operatorCoefficientsEqualAtEveryDepth :
  ∀ {Operator}
    {transport : Transport.CompositeRGParallelTransport Operator}
    (dataSet : SameCompositeOperatorCoefficientRecurrence Operator transport) →
  ∀ depth →
  physicalOperatorCoefficient dataSet depth
  ≡ asymptoticFreedomOperatorCoefficient dataSet depth
operatorCoefficientsEqualAtEveryDepth dataSet =
  OPE.coefficientFamiliesEqualAtEveryDepth
    (asCoefficientRGRecurrence dataSet)

------------------------------------------------------------------------
-- Literal OPE projection from the SAME composite-operator carrier.
------------------------------------------------------------------------

record LiteralOPECoefficientProjection
    {Operator PhysicalCoefficient : Set}
    {transport : Transport.CompositeRGParallelTransport Operator}
    (dataSet : SameCompositeOperatorCoefficientRecurrence Operator transport)
    : Set₁ where
  field
    projectOPECoefficient : Operator → PhysicalCoefficient
    literalOPECoefficientAt : Nat → PhysicalCoefficient

    literalOPEIsProjectedPhysicalOperator :
      ∀ depth →
      literalOPECoefficientAt depth
      ≡ projectOPECoefficient (physicalOperatorCoefficient dataSet depth)

open LiteralOPECoefficientProjection public

literalOPECoefficientMatchesProjectedAF :
  ∀ {Operator PhysicalCoefficient}
    {transport : Transport.CompositeRGParallelTransport Operator}
    {dataSet : SameCompositeOperatorCoefficientRecurrence Operator transport} →
  (projection : LiteralOPECoefficientProjection
    {PhysicalCoefficient = PhysicalCoefficient} dataSet) →
  ∀ depth →
  literalOPECoefficientAt projection depth
  ≡ projectOPECoefficient projection
      (asymptoticFreedomOperatorCoefficient dataSet depth)
literalOPECoefficientMatchesProjectedAF {dataSet = dataSet} projection depth
  rewrite literalOPEIsProjectedPhysicalOperator projection depth =
  cong
    (projectOPECoefficient projection)
    (operatorCoefficientsEqualAtEveryDepth dataSet depth)

------------------------------------------------------------------------
-- Frontier classification.
------------------------------------------------------------------------

secondMixingMapAbstractionRequiredByD2 : Bool
secondMixingMapAbstractionRequiredByD2 = false

secondMixingMapAbstractionRequiredByD2IsFalse :
  secondMixingMapAbstractionRequiredByD2 ≡ false
secondMixingMapAbstractionRequiredByD2IsFalse = refl

globalAFTheoremRequiredByD2 : Bool
globalAFTheoremRequiredByD2 = false

globalAFTheoremRequiredByD2IsFalse :
  globalAFTheoremRequiredByD2 ≡ false
globalAFTheoremRequiredByD2IsFalse = refl

allDepthComparisonRequiredByD2 : Bool
allDepthComparisonRequiredByD2 = false

allDepthComparisonRequiredByD2IsFalse :
  allDepthComparisonRequiredByD2 ≡ false
allDepthComparisonRequiredByD2IsFalse = refl

sameCompositeOperatorTrajectoryAttachmentStillPhysical : Bool
sameCompositeOperatorTrajectoryAttachmentStillPhysical = true

sameCompositeOperatorTrajectoryAttachmentStillPhysicalIsTrue :
  sameCompositeOperatorTrajectoryAttachmentStillPhysical ≡ true
sameCompositeOperatorTrajectoryAttachmentStillPhysicalIsTrue = refl

compositeOperatorToOPERecurrenceCompilerLevel : ProofLevel
compositeOperatorToOPERecurrenceCompilerLevel = machineChecked

physicalCompositeOperatorMixingLevel : ProofLevel
physicalCompositeOperatorMixingLevel = Transport.physicalYMCompositeMixingLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
