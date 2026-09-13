{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact where

------------------------------------------------------------------------
-- ROUND299 / QUANTITATIVE CYCLIC OVERLAP BY CONSTRUCTION
--
-- R297 removed one fake semantic leaf by making each hypothetical subgap mode
-- carry its actual nonzero reconstructed vector.  The next layer should obey
-- the same discipline: if positive-time cyclicity selects an observable because
-- it overlaps that vector, the selected overlap amplitude must not be represented
-- by an unrelated opaque token.
--
-- We therefore refine the cyclicity carrier with a rational overlap weight and
-- define the old `Overlap` predicate to mean exactly strict positivity of that
-- weight.  Observable choice then automatically carries a positive amplitude.
-- This does NOT prove physical positive-time cyclicity or the spectral theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297

record QuantitativePositiveTimeVacuumCyclicity
    (Observable Vector : Set) : Set₁ where
  field
    vacuum : Vector
    vectorOfObservable : Observable → Vector
    PositiveTimeObservable : Observable → Set
    NonzeroVector : Vector → Set

    overlapWeight : Vector → Vector → ℚ

    cyclicityDetectsNonzeroVector : ∀ vector →
      NonzeroVector vector →
      Σ Observable (λ observable →
        PositiveTimeObservable observable
        × (0ℚ < overlapWeight (vectorOfObservable observable) vector))

open QuantitativePositiveTimeVacuumCyclicity public

asPositiveTimeVacuumCyclicity :
  ∀ {Observable Vector} →
  QuantitativePositiveTimeVacuumCyclicity Observable Vector →
  Cyclic.PositiveTimeVacuumCyclicity Observable Vector
asPositiveTimeVacuumCyclicity quantitative = record
  { Cyclic.PositiveTimeVacuumCyclicity.vacuum = vacuum quantitative
  ; Cyclic.PositiveTimeVacuumCyclicity.vectorOfObservable =
      vectorOfObservable quantitative
  ; Cyclic.PositiveTimeVacuumCyclicity.PositiveTimeObservable =
      PositiveTimeObservable quantitative
  ; Cyclic.PositiveTimeVacuumCyclicity.NonzeroVector =
      NonzeroVector quantitative
  ; Cyclic.PositiveTimeVacuumCyclicity.Overlap =
      λ left right → 0ℚ < overlapWeight quantitative left right
  ; Cyclic.PositiveTimeVacuumCyclicity.cyclicityDetectsNonzeroVector =
      cyclicityDetectsNonzeroVector quantitative
  }

chosenObservableOverlapWeightPositive :
  ∀ {Observable Energy Vector}
    {quantitative : QuantitativePositiveTimeVacuumCyclicity Observable Vector}
    (family : R297.ActualNonzeroSubgapFamily
      (asPositiveTimeVacuumCyclicity quantitative))
    energy (mode : R297.SubgapMode family energy) →
  0ℚ < overlapWeight quantitative
    (vectorOfObservable quantitative
      (R297.modeObservableFromActualNonzeroFamily family energy mode))
    (R297.modeVector family energy mode)
chosenObservableOverlapWeightPositive family energy mode =
  R297.modeObservableOverlapsActualSubgapVector family energy mode

chosenObservableIsPositiveTime :
  ∀ {Observable Energy Vector}
    {quantitative : QuantitativePositiveTimeVacuumCyclicity Observable Vector}
    (family : R297.ActualNonzeroSubgapFamily
      (asPositiveTimeVacuumCyclicity quantitative))
    energy (mode : R297.SubgapMode family energy) →
  PositiveTimeObservable quantitative
    (R297.modeObservableFromActualNonzeroFamily family energy mode)
chosenObservableIsPositiveTime {quantitative = quantitative} family energy mode =
  Cyclic.modeObservableIsPositiveTime
    (R297.nonzeroMeaningByConstruction family) energy mode

record Round299Boundary : Set where
  constructor round299-boundary
  field
    separatePositiveOverlapAmplitudeLeaf : Bool
    separatePositiveOverlapAmplitudeLeafIsFalse :
      separatePositiveOverlapAmplitudeLeaf ≡ false

    overlapPredicateAndWeightCanDiverge : Bool
    overlapPredicateAndWeightCanDivergeIsFalse :
      overlapPredicateAndWeightCanDiverge ≡ false

    physicalPositiveTimeCyclicityProvedHere : Bool
    physicalPositiveTimeCyclicityProvedHereIsFalse :
      physicalPositiveTimeCyclicityProvedHere ≡ false

    spectralLowerBoundProvedHere : Bool
    spectralLowerBoundProvedHereIsFalse : spectralLowerBoundProvedHere ≡ false

canonicalRound299Boundary : Round299Boundary
canonicalRound299Boundary =
  round299-boundary false refl false refl false refl false refl

round299QuantitativeOverlapSelectionCompilerLevel : ProofLevel
round299QuantitativeOverlapSelectionCompilerLevel = machineChecked

-- Physical OS input: actual positive-time cyclicity on the reconstructed
-- observable/vector carrier.  R299 only strengthens its overlap representation.
round299PhysicalPositiveTimeCyclicityLevel : ProofLevel
round299PhysicalPositiveTimeCyclicityLevel =
  R297.round297PhysicalPositiveTimeCyclicityLevel
