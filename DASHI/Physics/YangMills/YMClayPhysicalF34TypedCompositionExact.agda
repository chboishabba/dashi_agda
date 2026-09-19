{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayPhysicalF34TypedCompositionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact as Frontier
import DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessExact as F4
import DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact as CommonCore
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery

------------------------------------------------------------------------
-- Typed F3/F4 composition after frontier reconciliation.
--
-- F3: an actual physical recovery system yields the continuum vacuum gap.
-- F4: physical common-core data yields same generator and then same evolution.
-- Neither downstream conclusion is an independent physical leaf.
------------------------------------------------------------------------

f3PhysicalVacuumGapAfterRecovery :
  (f3 : Frontier.PhysicalContinuumLimitWitness) →
  Recovery.PhysicalVacuumGapAfterRecovery (Frontier.recoverySystem f3)
f3PhysicalVacuumGapAfterRecovery f3 =
  Recovery.physicalVacuumGapAfterRecovery (Frontier.recoverySystem f3)

f4DerivedSameObject :
  (f4 : F4.PhysicalStressOSCommonCoreWitness) →
  Frontier.YMOSSameObjectWitness
    (F4.Time f4)
    (CommonCore.Vector (F4.calculus f4))
f4DerivedSameObject =
  Frontier.physicalStressOSBuildsYMOSSameObjectWitness

f4PhysicalEvolutionEquality :
  (f4 : F4.PhysicalStressOSCommonCoreWitness) →
  F4.ymEvolution f4 ≡ F4.osEvolution f4
f4PhysicalEvolutionEquality = F4.physicalSameEvolution

record PhysicalF34TypedKernel : Set₁ where
  field
    f3 : Frontier.PhysicalContinuumLimitWitness
    f4 : F4.PhysicalStressOSCommonCoreWitness

  recoveredVacuumGap :
    Recovery.PhysicalVacuumGapAfterRecovery (Frontier.recoverySystem f3)
  recoveredVacuumGap = f3PhysicalVacuumGapAfterRecovery f3

  sameGenerator :
    CommonCore.stressOperator (F4.commonCoreData f4)
      ≡ CommonCore.osHamiltonian (F4.commonCoreData f4)
  sameGenerator = F4.physicalSameGenerator f4

  sameEvolution :
    F4.ymEvolution f4 ≡ F4.osEvolution f4
  sameEvolution = f4PhysicalEvolutionEquality f4

  derivedSameObject :
    Frontier.YMOSSameObjectWitness
      (F4.Time f4)
      (CommonCore.Vector (F4.calculus f4))
  derivedSameObject = f4DerivedSameObject f4

open PhysicalF34TypedKernel public

f3RecoveryGapRequiresIndependentPayment : Bool
f3RecoveryGapRequiresIndependentPayment = false

f3RecoveryGapRequiresIndependentPaymentIsFalse :
  f3RecoveryGapRequiresIndependentPayment ≡ false
f3RecoveryGapRequiresIndependentPaymentIsFalse = refl

f4EvolutionEqualityRequiresPrimitivePhysicalAxiom : Bool
f4EvolutionEqualityRequiresPrimitivePhysicalAxiom = false

f4EvolutionEqualityRequiresPrimitivePhysicalAxiomIsFalse :
  f4EvolutionEqualityRequiresPrimitivePhysicalAxiom ≡ false
f4EvolutionEqualityRequiresPrimitivePhysicalAxiomIsFalse = refl

legacyBooleanReceiptsPayTypedPhysicalF34 : Bool
legacyBooleanReceiptsPayTypedPhysicalF34 = false

legacyBooleanReceiptsPayTypedPhysicalF34IsFalse :
  legacyBooleanReceiptsPayTypedPhysicalF34 ≡ false
legacyBooleanReceiptsPayTypedPhysicalF34IsFalse = refl

typedF34CompositionCompilerOwned : Bool
typedF34CompositionCompilerOwned = true

typedF34CompositionCompilerOwnedIsTrue :
  typedF34CompositionCompilerOwned ≡ true
typedF34CompositionCompilerOwnedIsTrue = refl

f3RecoveryGapCompilerLevel : ProofLevel
f3RecoveryGapCompilerLevel = Recovery.vacuumOrthogonalMoscoRecoveryLevel

f4PhysicalWitnessLevel : ProofLevel
f4PhysicalWitnessLevel = F4.physicalStressOSCommonCoreLevel

typedF34CompositionLevel : ProofLevel
typedF34CompositionLevel = conditional
