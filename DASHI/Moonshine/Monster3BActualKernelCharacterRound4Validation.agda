module DASHI.Moonshine.Monster3BActualKernelCharacterRound4Validation where

import DASHI.Moonshine.Monster3BProjectorResolutionRound3Validation
import DASHI.Moonshine.Monster3BExtraspecialCharacterSignatureExact as Signature
import DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact as Promotion
import DASHI.Moonshine.Monster3BActualMultiplicityIntertwinerExact as Evaluation
import DASHI.Moonshine.Monster3BProjectiveTensorCocycleExact as Cocycle
import DASHI.Moonshine.Monster3BMultiplicityCharacterSafeReconstructionExact as Safe
import DASHI.Moonshine.MoonshineOrbifoldMasslessStateRemovalExact as Orbifold

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])

extraspecialDegreeBudgetCloses :
  Signature.extraspecialCharacterDegreeSquareSum
  ≡ Signature.extraspecialOrder
extraspecialDegreeBudgetCloses =
  Signature.extraspecialCharacterDegreeSquareSumIsOrder

heisenbergCharacterHasUnitNormNumerator :
  Signature.heisenbergNormNumerator ≡ Signature.extraspecialOrder
heisenbergCharacterHasUnitNormNumerator =
  Signature.heisenbergNormNumeratorIsExtraspecialOrder

ninetyCopiesHaveActualPhaseDegree :
  Signature.zetaSectorDegree ≡ 65610
ninetyCopiesHaveActualPhaseDegree = Signature.zetaSectorDegreeIs65610

noncentralNinetyCopyTraceVanishes :
  Signature.ninetyHeisenbergCharacter Signature.noncentralClass
  ≡ Signature.zeroTrace
noncentralNinetyCopyTraceVanishes =
  Signature.ninetyHeisenbergNoncentralValue

safeNonzeroTraceRow : Safe.MultiplicityClassRow
safeNonzeroTraceRow = Safe.quotientRow 65610 729 90 refl

safeZeroTraceRow : Safe.MultiplicityClassRow
safeZeroTraceRow = Safe.independentRow 0 0 12 refl

safeClassReconstructionExample :
  Safe.sumTensorTrace (safeNonzeroTraceRow ∷ safeZeroTraceRow ∷ [])
  ≡ Safe.sumAmbient (safeNonzeroTraceRow ∷ safeZeroTraceRow ∷ [])
safeClassReconstructionExample =
  Safe.multiplicityCharacterReconstructsAllClasses
    (safeNonzeroTraceRow ∷ safeZeroTraceRow ∷ [])

moonshineWeightOneIsRemoved : Orbifold.moonshineWeightOneDimension ≡ 0
moonshineWeightOneIsRemoved = Orbifold.moonshineWeightOneVanishes

moonshineFirstExcitationGrade : Orbifold.conformalExcitationIndex ≡ 2
moonshineFirstExcitationGrade = Orbifold.conformalExcitationIndexIsTwo

-- The cocycle cancellation and actual evaluation theorems are generic:
-- every future actual normalizer action and actual multiplicity-space map must
-- instantiate these definitions rather than introducing parallel interfaces.
projectiveTensorCancellationAvailable :
  (data : Cocycle.CompensatingProjectiveTensor) →
  Cocycle.GenuineTensorActionCertificate data
projectiveTensorCancellationAvailable = Cocycle.actualTensorNormalizerAction

actualEvaluationPromotionAvailable :
  (data : Evaluation.ActualMultiplicityEvaluationData) →
  Evaluation.ActualEvaluationEquivariantIsomorphism data
actualEvaluationPromotionAvailable =
  Evaluation.actualMonsterLocalModuleIntertwiner
