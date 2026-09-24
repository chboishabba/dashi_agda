{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact as CommonCore

------------------------------------------------------------------------
-- F4 PHYSICAL BOUNDARY UPSTREAM OF EVOLUTION EQUALITY
--
-- The physical payment is common-core/operator data, not a prepackaged theorem
-- ymEvolution = osEvolution. StressOSCommonCoreData already compiles equality
-- of core actions plus closure identifications into equality of self-adjoint
-- generators.
--
-- sameGeneratorImpliesSameEvolution is the standard Stone/OS functional
-- calculus adapter. It consumes generator equality; it does not assume
-- evolution equality as physical input.
------------------------------------------------------------------------

record PhysicalStressOSCommonCoreWitness : Set₁ where
  field
    calculus : CommonCore.CommonCoreClosureCalculus
    Time : Set

    commonCoreData :
      CommonCore.StressOSCommonCoreData calculus

    reconstructedCoreWitness :
      CommonCore.Core calculus

    SelectedYMGeneratorOnCore : Set
    selectedYMGeneratorOnCore :
      SelectedYMGeneratorOnCore

    ReconstructedOSGeneratorOnCore : Set
    reconstructedOSGeneratorOnCore :
      ReconstructedOSGeneratorOnCore

    ymEvolution :
      Time → CommonCore.Vector calculus → CommonCore.Vector calculus
    osEvolution :
      Time → CommonCore.Vector calculus → CommonCore.Vector calculus

    sameGeneratorImpliesSameEvolution :
      CommonCore.stressOperator commonCoreData
        ≡ CommonCore.osHamiltonian commonCoreData →
      ymEvolution ≡ osEvolution

open PhysicalStressOSCommonCoreWitness public

physicalSameGenerator :
  (witness : PhysicalStressOSCommonCoreWitness) →
  CommonCore.stressOperator (commonCoreData witness)
    ≡ CommonCore.osHamiltonian (commonCoreData witness)
physicalSameGenerator witness =
  CommonCore.commonCoreWardImpliesSameGenerator
    (calculus witness)
    (commonCoreData witness)

physicalSameEvolution :
  (witness : PhysicalStressOSCommonCoreWitness) →
  ymEvolution witness ≡ osEvolution witness
physicalSameEvolution witness =
  sameGeneratorImpliesSameEvolution witness
    (physicalSameGenerator witness)

evolutionEqualityPrimitivePhysicalInput : Bool
evolutionEqualityPrimitivePhysicalInput = false

evolutionEqualityPrimitivePhysicalInputIsFalse :
  evolutionEqualityPrimitivePhysicalInput ≡ false
evolutionEqualityPrimitivePhysicalInputIsFalse = refl

commonCoreDataIsPrimitivePhysicalInput : Bool
commonCoreDataIsPrimitivePhysicalInput = true

commonCoreDataIsPrimitivePhysicalInputIsTrue :
  commonCoreDataIsPrimitivePhysicalInput ≡ true
commonCoreDataIsPrimitivePhysicalInputIsTrue = refl

commonCoreGeneratorCompilerLevel : ProofLevel
commonCoreGeneratorCompilerLevel =
  CommonCore.commonCoreClosureEqualityCompilerLevel

physicalStressOSCommonCoreLevel : ProofLevel
physicalStressOSCommonCoreLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
