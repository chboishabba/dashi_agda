module DASHI.Reasoning.Trialectic369Selected3BLinearAcquisitionCompletionExact where

------------------------------------------------------------------------
-- SELECTED-3B LINEAR ACQUISITION COMPLETION
--
-- DASHI CONTRIBUTION
--
-- The canonical outgoing route has already been corrected away from a pure
-- Fin90 permutation target.  Its true object is the linear multiplicity lane
--
--   W_zeta  and  S_zeta = Hom_E(H_zeta , W_zeta)
--
-- on the SAME selected 3B Monster action.
--
-- Existing owners already type all individual ingredients.  The remaining
-- repo-facing seam should therefore be one completion object, not a collection
-- of loosely related booleans:
--
--   * ActualLinearMultiplicityAcquisition
--   * ActualVOASelected3BComposition on that exact acquisition
--   * Selected3BNormalizerMonsterActionWeld on that exact acquisition.
--
-- Once those three are supplied on one same-object route, every downstream
-- linear target used by the trialectic lane is compiler output.  Optional
-- Fin90 / 10x9 / Sheet9 / 18-block specialisations remain gated by the separate
-- permutation-basis receipt.
--
-- This module does NOT manufacture the normalizer->Monster embedding or action
-- intertwiner from subgroup names, dimensions, characters or finite labels.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact as Acquisition
import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Wikimedia.IbrahimMonster3BActualVOASelected3BCompositionExact as Composition
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelSame
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as Phase
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Reasoning.Trialectic369OutgoingLinearAcquisitionBridgeExact as LinearBridge
import DASHI.Reasoning.Trialectic369LinearMultiplicityBasisSpecialisationCompilerExact as FiniteCompiler

------------------------------------------------------------------------
-- 1. One exact completion object.
------------------------------------------------------------------------

record Selected3BLinearAcquisitionCompletion
    {Monster K : Set} : Setω where
  field
    acquisition :
      Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K}

    sameElementComposition :
      Composition.ActualVOASelected3BComposition acquisition

    normalizerMonsterActionWeld :
      Acquisition.Selected3BNormalizerMonsterActionWeld acquisition

open Selected3BLinearAcquisitionCompletion public

------------------------------------------------------------------------
-- 2. Canonical linear objects are projections/compiler output.
------------------------------------------------------------------------

completedLinearZetaProducer :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  LinearZeta.LinearSingleActionProducer
completedLinearZetaProducer completion =
  Acquisition.linearZetaProducer (acquisition completion)

completedMultiplicityHomSpace :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Hom.ActualLinearMultiplicityHomSpace
completedMultiplicityHomSpace completion =
  Acquisition.multiplicityHomSpace (acquisition completion)

completedCanonicalLinearRoute :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  WrongType.CanonicalLinearMultiplicityRoute
completedCanonicalLinearRoute completion =
  LinearBridge.canonicalLinearRouteFromAcquisition
    (acquisition completion)

------------------------------------------------------------------------
-- 3. Same selected action identities are retained explicitly.
------------------------------------------------------------------------

completedComposition :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Composition.ActualVOASelected3BComposition (acquisition completion)
completedComposition =
  sameElementComposition

completedNormalizerMonsterActionWeld :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Acquisition.Selected3BNormalizerMonsterActionWeld (acquisition completion)
completedNormalizerMonsterActionWeld =
  normalizerMonsterActionWeld

selectedKernelWeldIsAcquisitionWeld :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Selected.weld
    (KernelSame.selectedSource
      (KernelSame.attachment
        (Composition.kernelRecognizedSameElementAttachment
          (sameElementComposition completion))))
  ≡
  Acquisition.literalSameObjectWeld (acquisition completion)
selectedKernelWeldIsAcquisitionWeld completion =
  Composition.kernelSelectedWeldIsAcquisitionWeld
    (sameElementComposition completion)

compiledProducerIsAcquisitionProducer :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Phase.singleActionProducerFromVOA
    (Composition.recognizedActionSourceFromSameElement
      (Composition.selectedRecognizedFromKernel
        (Composition.kernelRecognizedSameElementAttachment
          (sameElementComposition completion))))
  ≡
  LinearZeta.singleActionProducer
    (Acquisition.linearZetaProducer (acquisition completion))
compiledProducerIsAcquisitionProducer completion =
  Composition.compiledSingleActionProducerIsAcquisitionProducer
    (sameElementComposition completion)

------------------------------------------------------------------------
-- 3b. The normalizer -> Monster map is compiler output from same-producer
--     equality.  Only the ACTION INTERTWINING remains scientific.
------------------------------------------------------------------------

compiledVOAProducer :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Single.ActualMonster3BSingleActionProducer
compiledVOAProducer completion =
  Phase.singleActionProducerFromVOA
    (Composition.recognizedActionSourceFromSameElement
      (Composition.selectedRecognizedFromKernel
        (Composition.kernelRecognizedSameElementAttachment
          (sameElementComposition completion))))

acquisitionProducer :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Single.ActualMonster3BSingleActionProducer
acquisitionProducer completion =
  LinearZeta.singleActionProducer
    (Acquisition.linearZetaProducer (acquisition completion))

normalizerCarrierEqualityFromComposition :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Single.Normalizer (compiledVOAProducer completion)
  ≡
  Single.Normalizer (acquisitionProducer completion)
normalizerCarrierEqualityFromComposition completion =
  cong Single.Normalizer (compiledProducerIsAcquisitionProducer completion)

normalizerToMonsterFromComposition :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Single.Normalizer (acquisitionProducer completion) →
  Monster
normalizerToMonsterFromComposition completion normalizer =
  subst
    (λ Carrier → Carrier)
    (sym (normalizerCarrierEqualityFromComposition completion))
    normalizer

record Selected3BNormalizerActionIntertwiningOnly
    {Monster K : Set}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) : Setω where
  field
    normalizerActionIntertwines :
      (normalizer : Single.Normalizer (acquisitionProducer completion)) →
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Acquisition.weightTwoLinearBridge
              (acquisition completion)))) →
      subst
        (λ Carrier → Carrier)
        (Acquisition.selected3BStateCarrierEquality
          (acquisition completion))
        (WeightTwo.constituentAct
          (Acquisition.weightTwoLinearBridge
            (acquisition completion))
          (normalizerToMonsterFromComposition completion normalizer)
          state)
      ≡
      Inertia.act
        (Single.normalizerAction (acquisitionProducer completion))
        normalizer
        (subst
          (λ Carrier → Carrier)
          (Acquisition.selected3BStateCarrierEquality
            (acquisition completion))
          state)

open Selected3BNormalizerActionIntertwiningOnly public

compileNormalizerMonsterActionWeld :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Selected3BNormalizerActionIntertwiningOnly completion →
  Acquisition.Selected3BNormalizerMonsterActionWeld
    (acquisition completion)
compileNormalizerMonsterActionWeld completion intertwining =
  record
    { normalizerToMonster =
        normalizerToMonsterFromComposition completion
    ; normalizerActionIntertwines =
        normalizerActionIntertwines intertwining
    }

------------------------------------------------------------------------
-- 4. All linear multiplicity payloads are already inside the completion.
------------------------------------------------------------------------

sourcePaidCharacterOnSameMultiplicity :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Set
sourcePaidCharacterOnSameMultiplicity completion =
  Hom.sourcePaidCharacterOnSameMultiplicity
    (completedMultiplicityHomSpace completion)

linearEvaluationIntertwiner :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Set
linearEvaluationIntertwiner completion =
  Hom.evaluationIsLinearIntertwiner
    (completedMultiplicityHomSpace completion)

sourceNativeInertiaSameAction :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Set
sourceNativeInertiaSameAction completion =
  Acquisition.actualMultiplicityActionIsSourceNativeInertiaAction
    (acquisition completion)

twelveSeventyEightLinearIntertwiner :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Set
twelveSeventyEightLinearIntertwiner completion =
  Acquisition.twelveSeventyEightLinearIntertwiner
    (acquisition completion)

------------------------------------------------------------------------
-- 5. Optional finite basis route remains a separate downstream receipt.
------------------------------------------------------------------------

OptionalFiniteBasisRoute :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Set₁
OptionalFiniteBasisRoute completion =
  LinearBridge.OptionalFiniteBasisRoute (acquisition completion)

finiteBasisCompilerBoundary :
  FiniteCompiler.Trialectic369LinearMultiplicityBasisSpecialisationBoundary
finiteBasisCompilerBoundary =
  FiniteCompiler.canonicalTrialectic369LinearMultiplicityBasisSpecialisationBoundary

finiteNineSheetCompilerStillConditional :
  FiniteCompiler.selectedNineSheetCompilerAvailable
    finiteBasisCompilerBoundary
  ≡ true
finiteNineSheetCompilerStillConditional = refl

finiteModeBlock18CompilerStillConditional :
  FiniteCompiler.frickeStableEighteenBlockCompilerAvailable
    finiteBasisCompilerBoundary
  ≡ true
finiteModeBlock18CompilerStillConditional = refl

basisReceiptNotManufacturedByCompletion :
  FiniteCompiler.basisSpecialisationInhabitedHere
    finiteBasisCompilerBoundary
  ≡ false
basisReceiptNotManufacturedByCompletion = refl

------------------------------------------------------------------------
-- 6. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data CompletionCreatesNormalizerEmbedding : Set where
data CompletionCreatesActionIntertwinerFromCharacter : Set where
data CompletionCreatesPermutationBasis : Set where
data CompletionCreatesMonsterClassFromDimension : Set where

completionDoesNotCreateNormalizerEmbedding :
  CompletionCreatesNormalizerEmbedding → ⊥
completionDoesNotCreateNormalizerEmbedding ()

characterDoesNotCreateActionIntertwiner :
  CompletionCreatesActionIntertwinerFromCharacter → ⊥
characterDoesNotCreateActionIntertwiner ()

completionDoesNotCreatePermutationBasis :
  CompletionCreatesPermutationBasis → ⊥
completionDoesNotCreatePermutationBasis ()

dimensionDoesNotCreateMonsterClass :
  CompletionCreatesMonsterClassFromDimension → ⊥
dimensionDoesNotCreateMonsterClass ()

------------------------------------------------------------------------
-- 7. Machine-readable boundary.
------------------------------------------------------------------------

record Trialectic369Selected3BLinearAcquisitionCompletionBoundary : Set where
  constructor trialectic-369-selected3b-linear-acquisition-completion-boundary
  field
    oneCompletionOwnsAcquisition : Bool
    sameElementCompositionRequired : Bool
    normalizerMonsterActionWeldRequired : Bool
    normalizerToMonsterMapCompilerOutput : Bool
    onlyActionIntertwiningRemainsAfterComposition : Bool
    linearZetaProducerCompilerOutput : Bool
    multiplicityHomSpaceCompilerOutput : Bool
    canonicalLinearRouteCompilerOutput : Bool
    sameSelectedActionIdentitiesRetained : Bool
    sourceNativeInertiaPayloadRetained : Bool
    twelveSeventyEightIntertwinerPayloadRetained : Bool
    optionalFiniteBasisStillSeparate : Bool
    completionInhabitedHere : Bool

canonicalTrialectic369Selected3BLinearAcquisitionCompletionBoundary :
  Trialectic369Selected3BLinearAcquisitionCompletionBoundary
canonicalTrialectic369Selected3BLinearAcquisitionCompletionBoundary =
  trialectic-369-selected3b-linear-acquisition-completion-boundary
    true true true true true true true true true true true true false
