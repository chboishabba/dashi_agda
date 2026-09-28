module DASHI.Reasoning.Trialectic369CanonicalSelected3BLinearCoreExact where

------------------------------------------------------------------------
-- CANONICAL SELECTED-3B LINEAR CORE
--
-- DASHI CONTRIBUTION
--
-- The historical ActualLinearMultiplicityAcquisition is a useful provenance /
-- compatibility bundle, but it is larger than the canonical trialectic target.
--
-- The actual downstream linear route needs only one same-object core:
--
--   * a kernel-recognized selected literal 3B source;
--   * the linear 196883 constituent on that source's weight-two action;
--   * one linear W_zeta producer on the SAME compiled selected action;
--   * S_zeta = Hom_E(H_zeta,W_zeta) with evaluation/cocycle payload;
--   * the constituent carrier identified with the selected producer's State;
--   * source-native inertia and 12+78 intertwiner receipts.
--
-- From the producer equality, the selected Normalizer carrier is exactly
-- recharted with Monster.  Therefore the only remaining same-action payment is
-- one transported constituent-action intertwining equation.
--
-- No Fin90 permutation semantics, dimension argument, character equality or
-- subgroup name manufactures that equation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact as Single
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as Phase
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelSame
import DASHI.Moonshine.MonsterGradedVOASelected3BSameElementBidiExact as Selected
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as LiteralWeld
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Wikimedia.IbrahimMonster3BActualVOASelected3BCompositionExact as Composition
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Moonshine.Monster3BNormalizerCocycleCancellationExact as Cocycle

------------------------------------------------------------------------
-- 1. Minimal canonical linear core.
------------------------------------------------------------------------

record CanonicalSelected3BLinearCore
    {Monster K : Set} : Setω where
  field
    kernelRecognizedSameElementAttachment :
      KernelSame.Actual3BKernelRecognizedSameElementAttachment Monster K

    weightTwoLinearBridge :
      WeightTwo.WeightTwoLinearActionBridge
        (LiteralWeld.gradedAuthority
          (Selected.weld
            (KernelSame.selectedSource
              (KernelSame.attachment
                kernelRecognizedSameElementAttachment))))

    linearZetaProducer :
      LinearZeta.LinearSingleActionProducer

    compiledProducerIsLinearProducer :
      Phase.singleActionProducerFromVOA
        (Composition.recognizedActionSourceFromSameElement
          (Composition.selectedRecognizedFromKernel
            kernelRecognizedSameElementAttachment))
      ≡ LinearZeta.singleActionProducer linearZetaProducer

    multiplicityHomSpace :
      Hom.ActualLinearMultiplicityHomSpace

    constituentCarrierIsSelectedAmbient :
      Linear.Vector
        (WeightTwo.constituentLinearCarrier weightTwoLinearBridge)
      ≡ Linear.Vector
          (LinearZeta.ambientLinearCarrier linearZetaProducer)

    sourceNativeInertiaSameAction : Set
    twelveSeventyEightLinearIntertwiner : Set

open CanonicalSelected3BLinearCore public

------------------------------------------------------------------------
-- 2. Selected producer and exact State-carrier equality.
------------------------------------------------------------------------

compiledVOAProducer :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  Single.ActualMonster3BSingleActionProducer
compiledVOAProducer core =
  Phase.singleActionProducerFromVOA
    (Composition.recognizedActionSourceFromSameElement
      (Composition.selectedRecognizedFromKernel
        (kernelRecognizedSameElementAttachment core)))

linearProducer :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  Single.ActualMonster3BSingleActionProducer
linearProducer core =
  LinearZeta.singleActionProducer (linearZetaProducer core)

producerEquality :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  compiledVOAProducer core ≡ linearProducer core
producerEquality =
  compiledProducerIsLinearProducer

constituentCarrierIsSelectedState :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  Linear.Vector
    (WeightTwo.constituentLinearCarrier
      (weightTwoLinearBridge core))
  ≡ Single.State (linearProducer core)
constituentCarrierIsSelectedState core =
  trans
    (constituentCarrierIsSelectedAmbient core)
    (LinearZeta.ambientCarrierIsActualState
      (linearZetaProducer core))

------------------------------------------------------------------------
-- 3. Normalizer carrier is compiler-equivalent to Monster.
------------------------------------------------------------------------

compiledNormalizerIsMonster :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  Single.Normalizer (compiledVOAProducer core) ≡ Monster
compiledNormalizerIsMonster core = refl

normalizerCarrierEquality :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  Single.Normalizer (compiledVOAProducer core)
  ≡ Single.Normalizer (linearProducer core)
normalizerCarrierEquality core =
  cong Single.Normalizer (producerEquality core)

normalizerToMonster :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  Single.Normalizer (linearProducer core) →
  Monster
normalizerToMonster core normalizer =
  subst
    (λ Carrier → Carrier)
    (sym (normalizerCarrierEquality core))
    normalizer

monsterToNormalizer :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  Monster →
  Single.Normalizer (linearProducer core)
monsterToNormalizer core monster =
  subst
    (λ Carrier → Carrier)
    (normalizerCarrierEquality core)
    (subst
      (λ Carrier → Carrier)
      (sym (compiledNormalizerIsMonster core))
      monster)

normalizerMonsterRoundTrip :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  (normalizer : Single.Normalizer (linearProducer core)) →
  monsterToNormalizer core (normalizerToMonster core normalizer)
  ≡ normalizer
normalizerMonsterRoundTrip core normalizer
  rewrite producerEquality core = refl

monsterNormalizerRoundTrip :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  (monster : Monster) →
  normalizerToMonster core (monsterToNormalizer core monster)
  ≡ monster
monsterNormalizerRoundTrip core monster
  rewrite producerEquality core = refl

------------------------------------------------------------------------
-- 4. Canonical linear multiplicity route is already core output.
------------------------------------------------------------------------

canonicalLinearRoute :
  ∀ {Monster K}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) →
  WrongType.CanonicalLinearMultiplicityRoute
canonicalLinearRoute core =
  record
    { linearRepresentation =
        Hom.sameObjectLinearRepresentation
          (multiplicityHomSpace core)

    ; sourcePaidTwelvePlusSeventyEightCharacter =
        Hom.sourcePaidCharacterOnSameMultiplicity
          (multiplicityHomSpace core)

    ; sameObjectWithChosenZetaMultiplicity =
        Cocycle.Multiplicity
          (Hom.cocycleCompensatedAction
            (multiplicityHomSpace core))
        ≡
        Linear.Vector
          (WrongType.linearCarrier
            (Hom.sameObjectLinearRepresentation
              (multiplicityHomSpace core)))

    ; linearEvaluationIntertwiner =
        Hom.evaluationIsLinearIntertwiner
          (multiplicityHomSpace core)
    }

------------------------------------------------------------------------
-- 5. One action equation is the remaining same-action payment.
------------------------------------------------------------------------

record CanonicalSelected3BActionIntertwining
    {Monster K : Set}
    (core : CanonicalSelected3BLinearCore {Monster} {K}) : Setω where
  field
    intertwines :
      (normalizer : Single.Normalizer (linearProducer core)) →
      (state :
        Linear.Vector
          (WeightTwo.constituentLinearCarrier
            (weightTwoLinearBridge core))) →
      subst
        (λ Carrier → Carrier)
        (constituentCarrierIsSelectedState core)
        (WeightTwo.constituentAct
          (weightTwoLinearBridge core)
          (normalizerToMonster core normalizer)
          state)
      ≡
      Inertia.act
        (Single.normalizerAction (linearProducer core))
        normalizer
        (subst
          (λ Carrier → Carrier)
          (constituentCarrierIsSelectedState core)
          state)

open CanonicalSelected3BActionIntertwining public

record CanonicalSelected3BLinearCompletion
    {Monster K : Set} : Setω where
  field
    core : CanonicalSelected3BLinearCore {Monster} {K}
    actionIntertwining : CanonicalSelected3BActionIntertwining core

open CanonicalSelected3BLinearCompletion public

completionLinearRoute :
  ∀ {Monster K}
    (completion : CanonicalSelected3BLinearCompletion {Monster} {K}) →
  WrongType.CanonicalLinearMultiplicityRoute
completionLinearRoute completion =
  canonicalLinearRoute (core completion)

------------------------------------------------------------------------
-- 6. WrongType firewalls.
------------------------------------------------------------------------

data DimensionCreatesCanonicalCore : Set where
data CharacterCreatesActionIntertwining : Set where
data FiniteBasisCreatesLinearCore : Set where
data NormalizerNameCreatesCarrierBidi : Set where

dimensionDoesNotCreateCanonicalCore :
  DimensionCreatesCanonicalCore → ⊥
dimensionDoesNotCreateCanonicalCore ()

characterDoesNotCreateActionIntertwining :
  CharacterCreatesActionIntertwining → ⊥
characterDoesNotCreateActionIntertwining ()

finiteBasisDoesNotCreateLinearCore :
  FiniteBasisCreatesLinearCore → ⊥
finiteBasisDoesNotCreateLinearCore ()

normalizerNameDoesNotCreateCarrierBidi :
  NormalizerNameCreatesCarrierBidi → ⊥
normalizerNameDoesNotCreateCarrierBidi ()

------------------------------------------------------------------------
-- 7. Machine-readable frontier.
------------------------------------------------------------------------

record Trialectic369CanonicalSelected3BLinearCoreBoundary : Set where
  constructor trialectic-369-canonical-selected3b-linear-core-boundary
  field
    historicalAcquisitionNotCanonicalTarget : Bool
    recognizedSameElementSourceRequired : Bool
    weightTwoLinearBridgeRequired : Bool
    linearZetaProducerRequired : Bool
    actualHomSpaceRequired : Bool
    constituentStateEqualityRequired : Bool
    normalizerMonsterCarrierBidiCompilerOutput : Bool
    canonicalLinearRouteCompilerOutput : Bool
    onlyOneActionEquationRemainsAfterCore : Bool
    finiteBasisNotCanonicalInput : Bool
    canonicalCoreInhabitedHere : Bool
    actionIntertwiningInhabitedHere : Bool
    completionInhabitedHere : Bool

canonicalTrialectic369CanonicalSelected3BLinearCoreBoundary :
  Trialectic369CanonicalSelected3BLinearCoreBoundary
canonicalTrialectic369CanonicalSelected3BLinearCoreBoundary =
  trialectic-369-canonical-selected3b-linear-core-boundary
    true true true true true true true true true true
    false false false
