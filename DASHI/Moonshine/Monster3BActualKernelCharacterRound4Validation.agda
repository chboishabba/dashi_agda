module DASHI.Moonshine.Monster3BActualKernelCharacterRound4Validation where

import DASHI.Moonshine.Monster3BOrbifoldLocalModuleRound4Validation
import DASHI.Moonshine.Monster3BKernelCharacterCriterionExact as Character
import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Promotion
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannMultiplicityExact as StoneCount
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Existing
import DASHI.Moonshine.Monster3BActualMultiplicityEvaluationFromRecognitionExact as Evaluation
import DASHI.Moonshine.Monster3BNormalizerCocycleCancellationExact as Cocycle
import DASHI.Moonshine.Monster3BMultiplicityCharacterSafeReconstructionExact as Safe
import DASHI.Moonshine.MoonshineOrbifoldMasslessStateRemovalExact as Gap

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)

extraspecialDegreeBudgetCloses :
  Character.extraspecialCharacterDegreeSquareSum
  ≡ Character.extraspecialOrder
extraspecialDegreeBudgetCloses =
  Character.extraspecialCharacterDegreeSquareSumIsOrder

heisenbergCharacterHasUnitNormNumerator :
  Character.heisenbergNormNumerator ≡ Character.extraspecialOrder
heisenbergCharacterHasUnitNormNumerator =
  Character.heisenbergNormNumeratorIsExtraspecialOrder

ninetyCopiesHaveActualPhaseDegree : 90 * 729 ≡ 65610
ninetyCopiesHaveActualPhaseDegree = refl

noncentralNinetyCopyTraceVanishes :
  Character.ninetyFoldModelKernelTrace Character.noncentralClass
  ≡ Character.zeroTrace
noncentralNinetyCopyTraceVanishes =
  Character.modelNoncentralTraceIsZero

stoneVonNeumannMultiplicityIsUnique :
  (multiplicity : Nat) →
  729 * multiplicity ≡ 65610 →
  multiplicity ≡ 90
stoneVonNeumannMultiplicityIsUnique =
  StoneCount.multiplicityForcedToNinety

safeNonzeroTraceRow :
  Safe.MultiplicityClassRow Safe.naturalTraceAlgebra
safeNonzeroTraceRow =
  Safe.quotientRow Safe.naturalTraceAlgebra 65610 729 90 refl

safeZeroTraceRow :
  Safe.MultiplicityClassRow Safe.naturalTraceAlgebra
safeZeroTraceRow =
  Safe.independentRow Safe.naturalTraceAlgebra 0 0 12 refl

safeClassReconstructionExample :
  Safe.sumTensorTrace Safe.naturalTraceAlgebra
    (safeNonzeroTraceRow ∷ safeZeroTraceRow ∷ [])
  ≡ Safe.sumAmbient Safe.naturalTraceAlgebra
    (safeNonzeroTraceRow ∷ safeZeroTraceRow ∷ [])
safeClassReconstructionExample =
  Safe.multiplicityCharacterReconstructsAllClasses
    Safe.naturalTraceAlgebra
    (safeNonzeroTraceRow ∷ safeZeroTraceRow ∷ [])

moonshineWeightOneIsRemoved : Gap.MoonshineWeightOne → ⊥
moonshineWeightOneIsRemoved = Gap.moonshineWeightOneEmpty

moonshineFirstExcitationGrade :
  Gap.firstPositiveExcitationGrade
    Gap.canonicalFiniteConformalExcitationProfile
  ≡ 2
moonshineFirstExcitationGrade = Gap.conformalExcitationIndexIsTwo

actualEvaluationPromotionAvailable :
  ∀ {ActualSector} →
  (recognition : Existing.ActualZetaSectorRecognition ActualSector) →
  Evaluation.ActualMultiplicityEvaluationIsomorphism ActualSector
actualEvaluationPromotionAvailable =
  Evaluation.actualMonsterMultiplicityEvaluationIsomorphism

projectiveTensorCancellationAvailable :
  (action : Cocycle.CocycleCompensatedTensorAction) →
  (n m : Cocycle.Normalizer action) →
  (h : Cocycle.Heisenberg action) →
  (s : Cocycle.Multiplicity action) →
  Cocycle.actTensor action n
    (Cocycle.actTensor action m (Cocycle.pureTensor action h s))
  ≡ Cocycle.actTensor action
      (Cocycle.compose action n m)
      (Cocycle.pureTensor action h s)
projectiveTensorCancellationAvailable =
  Cocycle.compensatedTensorActionIsHonestOnPureTensors
