{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact where

------------------------------------------------------------------------
-- ROUND297 / SUBGAP NONZERO MEANING BY CONSTRUCTION
--
-- `BalabanClayT5OSReconstructionCyclicityExact` deliberately keeps an abstract
-- `NonzeroVectorWitness` and then asks for a physical interpretation into the
-- cyclicity carrier's actual `NonzeroVector`.  For the canonical spectral
-- contradiction that extra semantic layer is unnecessary: define a subgap mode
-- to carry the actual reconstructed vector and its actual nonzero witness on the
-- SAME cyclicity carrier.
--
-- This does not prove positive-time cyclicity, existence of a subgap mode, or
-- spectral energy semantics.  It only prevents a hypothetical subgap mode from
-- being represented by an unrelated nonzero token.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic

record ActualNonzeroSubgapFamily
    {Observable Energy Vector : Set}
    (cyclicity : Cyclic.PositiveTimeVacuumCyclicity Observable Vector) : Set₁ where
  field
    SubgapMode : Energy → Set
    modeVector : ∀ energy → SubgapMode energy → Vector
    modeVectorActuallyNonzero : ∀ energy mode →
      Cyclic.NonzeroVector cyclicity (modeVector energy mode)

open ActualNonzeroSubgapFamily public

asReconstructedSubgapVectors :
  ∀ {Observable Energy Vector}
    {cyclicity : Cyclic.PositiveTimeVacuumCyclicity Observable Vector} →
  ActualNonzeroSubgapFamily cyclicity →
  Cyclic.ReconstructedSubgapVectors Energy Vector
asReconstructedSubgapVectors family = record
  { Cyclic.ReconstructedSubgapVectors.SubgapMode = SubgapMode family
  ; Cyclic.ReconstructedSubgapVectors.modeVector = modeVector family
  ; Cyclic.ReconstructedSubgapVectors.NonzeroVectorWitness =
      λ energy mode →
        Cyclic.NonzeroVector _ (modeVector family energy mode)
  ; Cyclic.ReconstructedSubgapVectors.modeVectorNonzero =
      modeVectorActuallyNonzero family
  }

nonzeroMeaningByConstruction :
  ∀ {Observable Energy Vector}
    {cyclicity : Cyclic.PositiveTimeVacuumCyclicity Observable Vector}
    (family : ActualNonzeroSubgapFamily cyclicity) →
  Cyclic.CyclicSubgapVectorMeaning cyclicity
    (asReconstructedSubgapVectors family)
nonzeroMeaningByConstruction family = record
  { Cyclic.CyclicSubgapVectorMeaning.nonzeroMeaning =
      λ energy mode witness → witness
  }

modeObservableFromActualNonzeroFamily :
  ∀ {Observable Energy Vector}
    {cyclicity : Cyclic.PositiveTimeVacuumCyclicity Observable Vector}
    (family : ActualNonzeroSubgapFamily cyclicity) →
  ∀ energy → SubgapMode family energy → Observable
modeObservableFromActualNonzeroFamily family =
  Cyclic.modeObservableFromCyclicity (nonzeroMeaningByConstruction family)

modeObservableOverlapsActualSubgapVector :
  ∀ {Observable Energy Vector}
    {cyclicity : Cyclic.PositiveTimeVacuumCyclicity Observable Vector}
    (family : ActualNonzeroSubgapFamily cyclicity)
    energy (mode : SubgapMode family energy) →
  Cyclic.Overlap cyclicity
    (Cyclic.vectorOfObservable cyclicity
      (modeObservableFromActualNonzeroFamily family energy mode))
    (modeVector family energy mode)
modeObservableOverlapsActualSubgapVector family =
  Cyclic.modeObservableOverlapsSubgapVector
    (nonzeroMeaningByConstruction family)

record Round297Boundary : Set where
  constructor round297-boundary
  field
    arbitraryNonzeroWitnessInterpretationPrimitive : Bool
    arbitraryNonzeroWitnessInterpretationPrimitiveIsFalse :
      arbitraryNonzeroWitnessInterpretationPrimitive ≡ false

    actualNonzeroSubgapVectorCarriedByMode : Bool
    actualNonzeroSubgapVectorCarriedByModeIsTrue :
      actualNonzeroSubgapVectorCarriedByMode ≡ true

    observableChoiceAfterCyclicityCompilerOwned : Bool
    observableChoiceAfterCyclicityCompilerOwnedIsTrue :
      observableChoiceAfterCyclicityCompilerOwned ≡ true

    positiveTimeCyclicityProvedHere : Bool
    positiveTimeCyclicityProvedHereIsFalse : positiveTimeCyclicityProvedHere ≡ false

canonicalRound297Boundary : Round297Boundary
canonicalRound297Boundary =
  round297-boundary false refl true refl true refl false refl

round297ActualNonzeroSubgapCompilerLevel : ProofLevel
round297ActualNonzeroSubgapCompilerLevel = machineChecked

round297ObservableOverlapSelectionCompilerLevel : ProofLevel
round297ObservableOverlapSelectionCompilerLevel =
  Cyclic.cyclicityToSubgapOverlapLevel

round297PhysicalPositiveTimeCyclicityLevel : ProofLevel
round297PhysicalPositiveTimeCyclicityLevel =
  Cyclic.physicalPositiveTimeCylinderCyclicityInputsLevel
