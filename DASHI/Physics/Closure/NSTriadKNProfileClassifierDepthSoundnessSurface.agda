module DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundnessSurface where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( NSTriadKNPairIncidenceProfileDecompositionModel
        ; PairIncidenceProfile
        ; profileClassifier
        ; forcedTailProfile
        ; adversarialGeometryProfile
        ; transitionProfile
        )

record ExistingProfileClassifierSurface : Set₁ where
  field
    decompositionModel :
      NSTriadKNPairIncidenceProfileDecompositionModel
        {lzero} {lzero} {lzero} {lzero}

    shellOf :
      Nat →
      NSTriadKNPairIncidenceProfileDecompositionModel.Shell
        decompositionModel

    entryOf :
      Nat →
      NSTriadKNPairIncidenceProfileDecompositionModel.Entry
        decompositionModel

ExistingFTToAdversarialIncidence :
  ExistingProfileClassifierSurface → Nat → Nat → Nat → Set
ExistingFTToAdversarialIncidence surface N i j =
  profileClassifier
    (ExistingProfileClassifierSurface.decompositionModel surface)
    (ExistingProfileClassifierSurface.shellOf surface N)
    (ExistingProfileClassifierSurface.entryOf surface i)
    (ExistingProfileClassifierSurface.entryOf surface j)
    ≡ adversarialGeometryProfile

ExistingFTToTransitionIncidence :
  ExistingProfileClassifierSurface → Nat → Nat → Nat → Set
ExistingFTToTransitionIncidence surface N i j =
  profileClassifier
    (ExistingProfileClassifierSurface.decompositionModel surface)
    (ExistingProfileClassifierSurface.shellOf surface N)
    (ExistingProfileClassifierSurface.entryOf surface i)
    (ExistingProfileClassifierSurface.entryOf surface j)
    ≡ transitionProfile

record ClassifiedProfileWitness
    (entryDepth : Nat → Nat)
    (ForcedTailSource : Nat → Nat → Set)
    (AdversarialTarget : Nat → Nat → Set)
    (TransitionTarget : Nat → Nat → Set)
    (N i j : Nat) : Set₁ where
  field
    profileLabel : PairIncidenceProfile

    sourceDepth : Nat
    targetDepth : Nat

    sourceDepthCorrect :
      sourceDepth ≡ entryDepth i

    targetDepthCorrect :
      targetDepth ≡ entryDepth j

    forcedTailSourceWitness :
      profileLabel ≡ forcedTailProfile →
      ForcedTailSource N i

    adversarialTargetWitness :
      profileLabel ≡ adversarialGeometryProfile →
      AdversarialTarget N j

    transitionTargetWitness :
      profileLabel ≡ transitionProfile →
      TransitionTarget N j

record FTAdvClassifierDepthSoundnessTarget
    (entryDepth : Nat → Nat)
    (ForcedTailSource : Nat → Nat → Set)
    (AdversarialTarget : Nat → Nat → Set)
    (TransitionTarget : Nat → Nat → Set)
    (FTToAdversarialIncidence : Nat → Nat → Nat → Set₁) : Set₁ where
  field
    classifierSurface : ExistingProfileClassifierSurface

    restrictedLandsInClassifier :
      (N i j : Nat) →
      FTToAdversarialIncidence N i j →
      ExistingFTToAdversarialIncidence classifierSurface N i j

    classifierHasDepthWitness :
      (N i j : Nat) →
      ExistingFTToAdversarialIncidence classifierSurface N i j →
      ClassifiedProfileWitness
        entryDepth
        ForcedTailSource
        AdversarialTarget
        TransitionTarget
        N i j

    classifierImpliesForcedTailSource :
      (N i j : Nat) →
      ExistingFTToAdversarialIncidence classifierSurface N i j →
      ForcedTailSource N i

    classifierImpliesAdversarialTarget :
      (N i j : Nat) →
      ExistingFTToAdversarialIncidence classifierSurface N i j →
      AdversarialTarget N j
