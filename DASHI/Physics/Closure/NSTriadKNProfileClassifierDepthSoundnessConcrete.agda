module DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundnessConcrete where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤)

import DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundnessSurface
  as Surface
import DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement as Refinement
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (adversarialGeometryProfile)

------------------------------------------------------------------------
-- Concrete Blocker 1 theorem surface for FT→adv.
--
-- This module does not assert the current classifier construction is
-- sufficient. It isolates the exact local theorems that a real
-- construction would have to provide:
--
--   restricted incidence -> classifier landing   (now projectional)
--   restricted incidence -> classified depth witness
--   depth witness        -> source / target depth inequalities
--
-- Immediate status:
-- the first field `classifierLandingSound` is no longer blocked:
-- FTToAdversarialIncidence now carries its classifier landing.
--
-- If the existing profile classifier remains label-only, this surface
-- must stay open.
------------------------------------------------------------------------

data NSTriadKNProfileClassifierDepthSoundnessConcretePromotion : Set where

profileClassifierDepthSoundnessConcretePromotionImpossibleHere :
  NSTriadKNProfileClassifierDepthSoundnessConcretePromotion → ⊥
profileClassifierDepthSoundnessConcretePromotionImpossibleHere ()

ClassifiedProfileWitness : Nat → Nat → Nat → Set₁
ClassifiedProfileWitness =
  Surface.ClassifiedProfileWitness
    WeightModel.entryDepth
    WeightModel.ForcedTailSource
    WeightModel.AdversarialTarget
    WeightModel.TransitionTarget

classifierLandingSound :
  (N i j : Nat) →
  (inc : Refinement.FTToAdversarialIncidence N i j) →
  Surface.ExistingFTToAdversarialIncidence
    (Refinement.FTToAdversarialIncidence.classifierSurface inc) N i j
classifierLandingSound =
  Refinement.classifierLandingSound

classifierWitnessFromConstruction :
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  ClassifiedProfileWitness N i j
classifierWitnessFromConstruction N i j inc = record
  { profileLabel = adversarialGeometryProfile
  ; sourceDepth = WeightModel.entryDepth i
  ; targetDepth = WeightModel.entryDepth j
  ; sourceDepthCorrect = refl
  ; targetDepthCorrect = refl
  ; forcedTailSourceWitness = λ ()
  ; adversarialTargetWitness =
      λ _ →
        Refinement.FTToAdversarialIncidence.targetIsAdversarial inc
  ; transitionTargetWitness = λ ()
  }

record FTAdvClassifierDepthConcreteTarget : Set₁ where
  field
    forcedTailSourceDepthUpperFromWitness :
      (N i j : Nat) →
      ClassifiedProfileWitness N i j →
      WeightModel.entryDepth i ≤ WeightModel.forcedTailSourceDepthCap N

    adversarialTargetDepthLowerFromWitness :
      (N i j : Nat) →
      ClassifiedProfileWitness N i j →
      WeightModel.forcedTailSourceDepthCap N + WeightModel.advLogDepthRequired N
        ≤ WeightModel.entryDepth j

ftAdvDepthSeparationLinearFromConcrete :
  (target : FTAdvClassifierDepthConcreteTarget) →
  (N i j : Nat) →
  Refinement.FTToAdversarialIncidence N i j →
  WeightModel.entryDepth i + WeightModel.advLogDepthRequired N
    ≤ WeightModel.entryDepth j
ftAdvDepthSeparationLinearFromConcrete target N i j inc =
  let
    witness = classifierWitnessFromConstruction N i j inc
  in
  ≤-trans
    (+-mono-≤
      (FTAdvClassifierDepthConcreteTarget.forcedTailSourceDepthUpperFromWitness
        target N i j witness)
      (≤-refl {WeightModel.advLogDepthRequired N}))
    (FTAdvClassifierDepthConcreteTarget.adversarialTargetDepthLowerFromWitness
      target N i j witness)

canonicalReceiptText : String
canonicalReceiptText =
  "Concrete FT->adv Blocker 1 target: the carried classifier landing now packages a classified witness; the remaining local work is to derive source/target depth inequalities yielding entryDepth i + N <= entryDepth j."

canonicalClassifierLandingOpenReasonText : String
canonicalClassifierLandingOpenReasonText =
  "The first local theorem is now projectional: FTToAdversarialIncidence carries its classifier landing into adversarialGeometryProfile."

canonicalClassifierLandingNextStepText : String
canonicalClassifierLandingNextStepText =
  "Next step after classifierLandingSound: use the carried restricted-incidence data to package ClassifiedProfileWitness, then isolate the remaining depth-semantics obligations."

canonicalOpenReasonText : String
canonicalOpenReasonText =
  "The remaining blocker is now depth semantics, not classifier landing: ForcedTailSource and AdversarialTarget are still abstract predicates with no concrete theorem in the repo connecting them to entryDepth bounds."

canonicalNextStepText : String
canonicalNextStepText =
  "Next step: prove forcedTailSourceDepthUpper and adversarialTargetDepthLower, or keep a fail-closed concrete ProfileDepthSemantics surface until those entryDepth inequalities are inhabited."

record NSTriadKNProfileClassifierDepthSoundnessConcreteReceipt : Setω where
  constructor mkNSTriadKNProfileClassifierDepthSoundnessConcreteReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNProfileClassifierDepthSoundnessConcreteReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    classifierLandingOpenReasonText : String
    classifierLandingOpenReasonTextIsCanonical :
      classifierLandingOpenReasonText ≡ canonicalClassifierLandingOpenReasonText

    classifierLandingNextStepText : String
    classifierLandingNextStepTextIsCanonical :
      classifierLandingNextStepText ≡ canonicalClassifierLandingNextStepText

    openReasonText : String
    openReasonTextIsCanonical :
      openReasonText ≡ canonicalOpenReasonText

    nextStepText : String
    nextStepTextIsCanonical :
      nextStepText ≡ canonicalNextStepText

    theoremSurfaceImplemented : Bool
    theoremSurfaceImplementedIsTrue :
      theoremSurfaceImplemented ≡ true

    classifierLandingClosed : Bool
    classifierLandingClosedIsTrue :
      classifierLandingClosed ≡ true

    classifierWitnessClosed : Bool
    classifierWitnessClosedIsTrue :
      classifierWitnessClosed ≡ true

    sourceDepthUpperClosed : Bool
    sourceDepthUpperClosedIsFalse :
      sourceDepthUpperClosed ≡ false

    targetDepthLowerClosed : Bool
    targetDepthLowerClosedIsFalse :
      targetDepthLowerClosed ≡ false

    ftAdvDepthSeparationClosed : Bool
    ftAdvDepthSeparationClosedIsFalse :
      ftAdvDepthSeparationClosed ≡ false

canonicalNSTriadKNProfileClassifierDepthSoundnessConcreteReceipt :
  NSTriadKNProfileClassifierDepthSoundnessConcreteReceipt
canonicalNSTriadKNProfileClassifierDepthSoundnessConcreteReceipt =
  mkNSTriadKNProfileClassifierDepthSoundnessConcreteReceipt
    "NSTriadKNProfileClassifierDepthSoundnessConcreteReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalClassifierLandingOpenReasonText
    refl
    canonicalClassifierLandingNextStepText
    refl
    canonicalOpenReasonText
    refl
    canonicalNextStepText
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

classifierDepthSoundnessConcreteClosed : Bool
classifierDepthSoundnessConcreteClosed = false
