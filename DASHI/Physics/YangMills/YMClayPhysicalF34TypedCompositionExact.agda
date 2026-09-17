{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayPhysicalF34TypedCompositionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact as Frontier
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery

------------------------------------------------------------------------
-- TYPED F3/F4 COMPOSITION OVER THE EXISTING PHYSICAL FRONTIER
--
-- The older frontier record deliberately kept physical facts explicit, but a
-- few downstream consequences were still described as if they were additional
-- research payments.  This owner removes those duplicate leaves without
-- manufacturing any physical inhabitant.
--
-- F3 already stores an actual `VacuumOrthogonalRecoverySystem`.  Once such a
-- physical system exists, the continuum vacuum-complement lower-gap theorem is
-- compiler output of `BalabanVacuumOrthogonalMoscoRecoveryExact`.
--
-- F4 already stores the SAME-OBJECT equality
--
--     ymEvolution ≡ osEvolution.
--
-- Therefore a second equality axiom is not a legitimate residual after a
-- `YMOSSameObjectWitness` has been constructed.  Common-core/operator-domain
-- semantics remain part of constructing that physical witness; this module
-- does not infer them from receipt bits or names.
------------------------------------------------------------------------

f3PhysicalVacuumGapAfterRecovery :
  (f3 : Frontier.PhysicalContinuumLimitWitness) →
  Recovery.PhysicalVacuumGapAfterRecovery (Frontier.recoverySystem f3)
f3PhysicalVacuumGapAfterRecovery f3 =
  Recovery.physicalVacuumGapAfterRecovery (Frontier.recoverySystem f3)

f4PhysicalEvolutionEquality :
  ∀ {Time Vector} →
  (f4 : Frontier.YMOSSameObjectWitness Time Vector) →
  Frontier.ymEvolution f4 ≡ Frontier.osEvolution f4
f4PhysicalEvolutionEquality f4 = Frontier.evolutionsEqual f4

-- A compact typed bundle useful for consumers that need exactly the existing
-- F3 recovery theorem and the already-stored F4 same-evolution equality.
record PhysicalF34TypedKernel : Set₁ where
  field
    f3 : Frontier.PhysicalContinuumLimitWitness

    Time : Set
    Vector : Set
    f4 : Frontier.YMOSSameObjectWitness Time Vector

  recoveredVacuumGap :
    Recovery.PhysicalVacuumGapAfterRecovery (Frontier.recoverySystem f3)
  recoveredVacuumGap = f3PhysicalVacuumGapAfterRecovery f3

  sameEvolution :
    Frontier.ymEvolution f4 ≡ Frontier.osEvolution f4
  sameEvolution = f4PhysicalEvolutionEquality f4

open PhysicalF34TypedKernel public

------------------------------------------------------------------------
-- Proof-search bookkeeping.
------------------------------------------------------------------------

-- Once F3 contains the physical recovery system, its lower-gap consequence is
-- not another independent payment.
f3RecoveryGapRequiresIndependentPayment : Bool
f3RecoveryGapRequiresIndependentPayment = false

f3RecoveryGapRequiresIndependentPaymentIsFalse :
  f3RecoveryGapRequiresIndependentPayment ≡ false
f3RecoveryGapRequiresIndependentPaymentIsFalse = refl

-- Once F4 itself has been inhabited, YM=OS evolution equality is literally one
-- of its theorem-bearing fields.  Do not charge another same-object equality.
f4EvolutionEqualityRequiresAnotherSameObjectAxiom : Bool
f4EvolutionEqualityRequiresAnotherSameObjectAxiom = false

f4EvolutionEqualityRequiresAnotherSameObjectAxiomIsFalse :
  f4EvolutionEqualityRequiresAnotherSameObjectAxiom ≡ false
f4EvolutionEqualityRequiresAnotherSameObjectAxiomIsFalse = refl

-- Historical booleans/receipts cannot build either typed physical witness.
legacyBooleanReceiptsPayTypedPhysicalF34 : Bool
legacyBooleanReceiptsPayTypedPhysicalF34 = false

legacyBooleanReceiptsPayTypedPhysicalF34IsFalse :
  legacyBooleanReceiptsPayTypedPhysicalF34 ≡ false
legacyBooleanReceiptsPayTypedPhysicalF34IsFalse = refl

-- The composition functions above are explicit Agda terms.  This status refers
-- only to the compiler/composition layer, not to construction of physical F3/F4.
typedF34CompositionCompilerOwned : Bool
typedF34CompositionCompilerOwned = true

typedF34CompositionCompilerOwnedIsTrue :
  typedF34CompositionCompilerOwned ≡ true
typedF34CompositionCompilerOwnedIsTrue = refl

f3RecoveryGapCompilerLevel : ProofLevel
f3RecoveryGapCompilerLevel = Recovery.vacuumOrthogonalMoscoRecoveryLevel

-- Physical witness construction remains conditional; equality extraction is
-- definitionally/compiler-owned after the witness exists.
f4PhysicalWitnessLevel : ProofLevel
f4PhysicalWitnessLevel = conditional

typedF34CompositionLevel : ProofLevel
typedF34CompositionLevel = machineChecked
