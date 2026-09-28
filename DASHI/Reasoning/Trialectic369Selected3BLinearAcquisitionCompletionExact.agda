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
-- 1. Scaffold first, then full completion.
------------------------------------------------------------------------

record Selected3BLinearAcquisitionScaffold
    {Monster K : Set} : Setω where
  field
    acquisition :
      Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K}

    sameElementComposition :
      Composition.ActualVOASelected3BComposition acquisition

open Selected3BLinearAcquisitionScaffold public

record Selected3BLinearAcquisitionCompletion
    {Monster K : Set} : Setω where
  field
    scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}

    normalizerMonsterActionWeld :
      Acquisition.Selected3BNormalizerMonsterActionWeld
        (Selected3BLinearAcquisitionScaffold.acquisition scaffold)

open Selected3BLinearAcquisitionCompletion public

completionAcquisition :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Acquisition.ActualLinearMultiplicityAcquisition {Monster} {K}
completionAcquisition completion =
  Selected3BLinearAcquisitionScaffold.acquisition (scaffold completion)

completionComposition :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Composition.ActualVOASelected3BComposition (completionAcquisition completion)
completionComposition completion =
  Selected3BLinearAcquisitionScaffold.sameElementComposition (scaffold completion)

------------------------------------------------------------------------
-- 2. Canonical linear objects are projections/compiler output.
------------------------------------------------------------------------

completedLinearZetaProducer :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  LinearZeta.LinearSingleActionProducer
completedLinearZetaProducer completion =
  Acquisition.linearZetaProducer (completionAcquisition completion)

completedMultiplicityHomSpace :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Hom.ActualLinearMultiplicityHomSpace
completedMultiplicityHomSpace completion =
  Acquisition.multiplicityHomSpace (completionAcquisition completion)

completedCanonicalLinearRoute :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  WrongType.CanonicalLinearMultiplicityRoute
completedCanonicalLinearRoute completion =
  LinearBridge.canonicalLinearRouteFromAcquisition
    (completionAcquisition completion)

------------------------------------------------------------------------
-- 3. Same selected action identities are retained explicitly.
------------------------------------------------------------------------

completedComposition :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Composition.ActualVOASelected3BComposition (completionAcquisition completion)
completedComposition =
  completionComposition

completedNormalizerMonsterActionWeld :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Acquisition.Selected3BNormalizerMonsterActionWeld (completionAcquisition completion)
completedNormalizerMonsterActionWeld =
  normalizerMonsterActionWeld

selectedKernelWeldIsAcquisitionWeld :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Selected.weld
    (KernelSame.selectedSource
      (KernelSame.attachment
        (Composition.kernelRecognizedSameElementAttachment
          (completionComposition completion))))
  ≡
  Acquisition.literalSameObjectWeld (completionAcquisition completion)
selectedKernelWeldIsAcquisitionWeld completion =
  Composition.kernelSelectedWeldIsAcquisitionWeld
    (completionComposition completion)

compiledProducerIsAcquisitionProducer :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Phase.singleActionProducerFromVOA
    (Composition.recognizedActionSourceFromSameElement
      (Composition.selectedRecognizedFromKernel
        (Composition.kernelRecognizedSameElementAttachment
          (completionComposition completion))))
  ≡
  LinearZeta.singleActionProducer
    (Acquisition.linearZetaProducer (completionAcquisition completion))
compiledProducerIsAcquisitionProducer completion =
  Composition.compiledSingleActionProducerIsAcquisitionProducer
    (completionComposition completion)

------------------------------------------------------------------------
-- 3b. The normalizer -> Monster map is compiler output from the scaffold.
--     Only the ACTION INTERTWINING remains scientific.
------------------------------------------------------------------------

scaffoldCompiledVOAProducer :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Single.ActualMonster3BSingleActionProducer
scaffoldCompiledVOAProducer scaffold =
  Phase.singleActionProducerFromVOA
    (Composition.recognizedActionSourceFromSameElement
      (Composition.selectedRecognizedFromKernel
        (Composition.kernelRecognizedSameElementAttachment
          (sameElementComposition scaffold))))

scaffoldAcquisitionProducer :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Single.ActualMonster3BSingleActionProducer
scaffoldAcquisitionProducer scaffold =
  LinearZeta.singleActionProducer
    (Acquisition.linearZetaProducer (acquisition scaffold))

scaffoldProducerEquality :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  scaffoldCompiledVOAProducer scaffold
  ≡
  scaffoldAcquisitionProducer scaffold
scaffoldProducerEquality scaffold =
  Composition.compiledSingleActionProducerIsAcquisitionProducer
    (sameElementComposition scaffold)

compiledVOANormalizerIsMonster :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Single.Normalizer (scaffoldCompiledVOAProducer scaffold)
  ≡ Monster
compiledVOANormalizerIsMonster scaffold = refl

normalizerCarrierEqualityFromScaffold :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Single.Normalizer (scaffoldCompiledVOAProducer scaffold)
  ≡
  Single.Normalizer (scaffoldAcquisitionProducer scaffold)
normalizerCarrierEqualityFromScaffold scaffold =
  cong Single.Normalizer (scaffoldProducerEquality scaffold)

normalizerToMonsterFromScaffold :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Single.Normalizer (scaffoldAcquisitionProducer scaffold) →
  Monster
normalizerToMonsterFromScaffold scaffold normalizer =
  subst
    (λ Carrier → Carrier)
    (sym (normalizerCarrierEqualityFromScaffold scaffold))
    normalizer

monsterToNormalizerFromScaffold :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Monster →
  Single.Normalizer (scaffoldAcquisitionProducer scaffold)
monsterToNormalizerFromScaffold scaffold monster =
  subst
    (λ Carrier → Carrier)
    (normalizerCarrierEqualityFromScaffold scaffold)
    (subst
      (λ Carrier → Carrier)
      (sym (compiledVOANormalizerIsMonster scaffold))
      monster)

normalizerMonsterRoundTrip :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  (normalizer : Single.Normalizer (scaffoldAcquisitionProducer scaffold)) →
  monsterToNormalizerFromScaffold scaffold
    (normalizerToMonsterFromScaffold scaffold normalizer)
  ≡ normalizer
normalizerMonsterRoundTrip scaffold normalizer
  rewrite scaffoldProducerEquality scaffold = refl

monsterNormalizerRoundTrip :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  (monster : Monster) →
  normalizerToMonsterFromScaffold scaffold
    (monsterToNormalizerFromScaffold scaffold monster)
  ≡ monster
monsterNormalizerRoundTrip scaffold monster
  rewrite scaffoldProducerEquality scaffold = refl

record Selected3BNormalizerActionIntertwiningOnly
    {Monster K : Set}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) : Setω where
  field
    normalizerActionIntertwines :
      (normalizer :
        Single.Normalizer (scaffoldAcquisitionProducer scaffold)) →
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (Acquisition.weightTwoLinearBridge
              (acquisition scaffold)))) →
      subst
        (λ Carrier → Carrier)
        (Acquisition.selected3BStateCarrierEquality
          (acquisition scaffold))
        (WeightTwo.constituentAct
          (Acquisition.weightTwoLinearBridge
            (acquisition scaffold))
          (normalizerToMonsterFromScaffold scaffold normalizer)
          state)
      ≡
      Inertia.act
        (Single.normalizerAction
          (scaffoldAcquisitionProducer scaffold))
        normalizer
        (subst
          (λ Carrier → Carrier)
          (Acquisition.selected3BStateCarrierEquality
            (acquisition scaffold))
          state)

open Selected3BNormalizerActionIntertwiningOnly public

compileNormalizerMonsterActionWeld :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Selected3BNormalizerActionIntertwiningOnly scaffold →
  Acquisition.Selected3BNormalizerMonsterActionWeld
    (acquisition scaffold)
compileNormalizerMonsterActionWeld scaffold intertwining =
  record
    { normalizerToMonster =
        normalizerToMonsterFromScaffold scaffold
    ; normalizerActionIntertwines =
        normalizerActionIntertwines intertwining
    }

completeFromActionIntertwining :
  ∀ {Monster K}
    (scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}) →
  Selected3BNormalizerActionIntertwiningOnly scaffold →
  Selected3BLinearAcquisitionCompletion {Monster} {K}
completeFromActionIntertwining scaffold intertwining =
  record
    { scaffold = scaffold
    ; normalizerMonsterActionWeld =
        compileNormalizerMonsterActionWeld scaffold intertwining
    }

------------------------------------------------------------------------
-- 3c. Exact two-field recognition min-cut.
------------------------------------------------------------------------

record Selected3BLinearRecognitionMinCut
    {Monster K : Set} : Setω where
  field
    scaffold :
      Selected3BLinearAcquisitionScaffold {Monster} {K}

    actionIntertwining :
      Selected3BNormalizerActionIntertwiningOnly scaffold

open Selected3BLinearRecognitionMinCut public

minCutToCompletion :
  ∀ {Monster K} →
  Selected3BLinearRecognitionMinCut {Monster} {K} →
  Selected3BLinearAcquisitionCompletion {Monster} {K}
minCutToCompletion cut =
  completeFromActionIntertwining
    (Selected3BLinearRecognitionMinCut.scaffold cut)
    (actionIntertwining cut)

completionToMinCut :
  ∀ {Monster K} →
  (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Selected3BLinearRecognitionMinCut {Monster} {K}
completionToMinCut completion =
  record
    { scaffold = Selected3BLinearAcquisitionCompletion.scaffold completion
    ; actionIntertwining =
        record
          { normalizerActionIntertwines =
              Acquisition.normalizerActionIntertwines
                (normalizerMonsterActionWeld completion)
          }
    }

minCutCompletionRoundTrip :
  ∀ {Monster K}
    (cut : Selected3BLinearRecognitionMinCut {Monster} {K}) →
  completionToMinCut (minCutToCompletion cut) ≡ cut
minCutCompletionRoundTrip
  record { scaffold = scaffold ; actionIntertwining = intertwining } = refl

completionMinCutRoundTrip :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  minCutToCompletion (completionToMinCut completion) ≡ completion
completionMinCutRoundTrip
  record { scaffold = scaffold ; normalizerMonsterActionWeld = weld } = refl

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
    (completionAcquisition completion)

twelveSeventyEightLinearIntertwiner :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Set
twelveSeventyEightLinearIntertwiner completion =
  Acquisition.twelveSeventyEightLinearIntertwiner
    (completionAcquisition completion)

------------------------------------------------------------------------
-- 5. Optional finite basis route remains a separate downstream receipt.
------------------------------------------------------------------------

OptionalFiniteBasisRoute :
  ∀ {Monster K}
    (completion : Selected3BLinearAcquisitionCompletion {Monster} {K}) →
  Set₁
OptionalFiniteBasisRoute completion =
  LinearBridge.OptionalFiniteBasisRoute (completionAcquisition completion)

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
    scaffoldOwnsAcquisition : Bool
    scaffoldOwnsSameElementComposition : Bool
    normalizerToMonsterMapCompilerOutput : Bool
    normalizerMonsterCarrierBidiCompilerOutput : Bool
    onlyActionIntertwiningRemainsAfterScaffold : Bool
    completionCompilerOwned : Bool
    twoFieldRecognitionMinCutOwned : Bool
    minCutCompletionBidiPaid : Bool
    linearZetaProducerCompilerOutput : Bool
    multiplicityHomSpaceCompilerOutput : Bool
    canonicalLinearRouteCompilerOutput : Bool
    sourceNativeInertiaPayloadRetained : Bool
    twelveSeventyEightIntertwinerPayloadRetained : Bool
    optionalFiniteBasisStillSeparate : Bool
    scaffoldInhabitedHere : Bool
    actionIntertwiningInhabitedHere : Bool
    completionInhabitedHere : Bool

canonicalTrialectic369Selected3BLinearAcquisitionCompletionBoundary :
  Trialectic369Selected3BLinearAcquisitionCompletionBoundary
canonicalTrialectic369Selected3BLinearAcquisitionCompletionBoundary =
  trialectic-369-selected3b-linear-acquisition-completion-boundary
    true true true true true true true true true true true true true true
    false false false
