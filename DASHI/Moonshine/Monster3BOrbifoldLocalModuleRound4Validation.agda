module DASHI.Moonshine.Monster3BOrbifoldLocalModuleRound4Validation where

import DASHI.Moonshine.Monster3BProjectorResolutionRound3Validation
import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as W2
import DASHI.Moonshine.MoonshineOrbifoldMasslessStateRemovalExact as Gap
import DASHI.Moonshine.MoonshineZ3OrbifoldThreeLocalSiblingExact as Sibling
import DASHI.Moonshine.LeechWeightTwo196608BridgeExact as Old
import DASHI.Moonshine.LeechWeightTwo196608AuthorityCorrectionExact as Correction
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity
import DASHI.Moonshine.Monster3BKernelCharacterCriterionExact as Character
import DASHI.Moonshine.Monster3BNormalizerCocycleCancellationExact as Cocycle

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Data.Empty using (⊥)

publishedWeightTwoSectorSplit :
  W2.untwistedInvariantWeightTwoDimension
  + W2.twistedInvariantWeightTwoDimension
  ≡ 196884
publishedWeightTwoSectorSplit = W2.publishedOrbifoldWeightTwoSplit

publishedMonsterWeightTwoQuotient :
  W2.monsterNontrivialWeightTwoDimension ≡ 196883
publishedMonsterWeightTwoQuotient =
  W2.monsterNontrivialWeightTwoDimensionIs196883

moonshineWeightOneIsEmpty : Gap.MoonshineWeightOne → ⊥
moonshineWeightOneIsEmpty = Gap.moonshineWeightOneEmpty

firstPositiveConformalGradeIsTwo :
  Gap.firstPositiveExcitationGrade
    Gap.canonicalFiniteConformalExcitationProfile ≡ 2
firstPositiveConformalGradeIsTwo = Gap.conformalExcitationIndexIsTwo

threeLocalSiblingsHaveCommonOrigin :
  Sibling.origin Sibling.extraspecialSuzukiShape
  ≡ Sibling.origin Sibling.elementaryOmegaShape
threeLocalSiblingsHaveCommonOrigin = Sibling.siblingsShareOrbifoldOrigin

threeLocalSiblingsHaveDifferentKernels :
  Sibling.kernelGeometry Sibling.extraspecialSuzukiShape
  ≡ Sibling.kernelGeometry Sibling.elementaryOmegaShape → ⊥
threeLocalSiblingsHaveDifferentKernels = Sibling.kernelGeometriesAreDistinct

coordinateAndOrbifoldChartsOnlyShareTotal :
  Old.leechCoordinateSubtotal + Old.offDiagonalQuadraticCount
  ≡ W2.untwistedInvariantWeightTwoDimension
    + W2.twistedInvariantWeightTwoDimension
coordinateAndOrbifoldChartsOnlyShareTotal =
  Correction.bothChartsReconstructWeightTwo

modelMultiplicityEvaluationRoundTrip :
  (tensor : Multiplicity.ModelTensorBasis) →
  Multiplicity.recoverModelTensor
    (Multiplicity.evaluateModelTensor tensor)
  ≡ tensor
modelMultiplicityEvaluationRoundTrip = Multiplicity.recoverAfterEvaluate

modelKernelCharacterIsNinetyHeisenbergCopies :
  (kind : Character.ExtraspecialClassKind) →
  Character.ninetyFoldModelKernelTrace kind
  ≡ Character.scaleTrace 90 (Character.heisenbergKernelTrace kind)
modelKernelCharacterIsNinetyHeisenbergCopies =
  Character.modelTraceIsNinetyHeisenbergCopies

centralPhaseInverseIsInvolutive :
  (phase : Cocycle.Phase3) →
  Cocycle.inversePhase (Cocycle.inversePhase phase) ≡ phase
centralPhaseInverseIsInvolutive = Cocycle.phaseInverseInvolutive
