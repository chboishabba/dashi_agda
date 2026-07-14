module DASHI.Physics.Closure.NSTriadKNConcreteIndexClassifierBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin using (toℕ)

import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialConcrete
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailConcrete
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as Profile
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundnessSurface as ClassifierSurface
import DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement as Refinement
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionConcrete
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition

------------------------------------------------------------------------
-- Concrete-to-classifier bridge.
--
-- The concrete relation is already a tagged union whose payloads are Fin
-- indices.  The canonical Nat classifier uses the two axes as binary
-- quadrant bits: zero denotes the forced-tail side and suc _ denotes a
-- non-forced-tail side.  The payload is retained in the successor branch so
-- the map remains a genuine entry-code map rather than a bare tag erasure.
------------------------------------------------------------------------

sourceEntryCode :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
sourceEntryCode (Relation.forcedTailFiniteIndex _ _) = zero
sourceEntryCode (Relation.adversarialFiniteIndex _ h) = suc (toℕ h)
sourceEntryCode (Relation.transitionFiniteIndex _ h) = suc (toℕ h)

targetEntryCode :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
targetEntryCode (Relation.forcedTailTailIndex _ _) = zero
targetEntryCode (Relation.adversarialTailIndex _ h) = suc (toℕ h)
targetEntryCode (Relation.transitionTailIndex _ h) = suc (toℕ h)

sourceEntryDepth :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N -> Nat
sourceEntryDepth f = WeightModel.entryDepth (sourceEntryCode f)

targetEntryDepth :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N -> Nat
targetEntryDepth t = WeightModel.entryDepth (targetEntryCode t)

sourceProfile :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Profile.PairIncidenceProfile
sourceProfile (Relation.forcedTailFiniteIndex _ _) = Profile.forcedTailProfile
sourceProfile (Relation.adversarialFiniteIndex _ _) =
  Profile.adversarialGeometryProfile
sourceProfile (Relation.transitionFiniteIndex _ _) =
  Profile.transitionProfile

targetProfile :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N ->
  Profile.PairIncidenceProfile
targetProfile (Relation.forcedTailTailIndex _ _) = Profile.forcedTailProfile
targetProfile (Relation.adversarialTailIndex _ _) =
  Profile.adversarialGeometryProfile
targetProfile (Relation.transitionTailIndex _ _) =
  Profile.transitionProfile

classifierAtConcretePair :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Relation.ConcreteNonResidualTailIndex N ->
  Profile.PairIncidenceProfile
classifierAtConcretePair {N = N} f t =
  Profile.canonicalNSClassifier
    N
    (sourceEntryCode f)
    (targetEntryCode t)

------------------------------------------------------------------------
-- The canonical profile model can be exposed through the classifier
-- surface.  This is only a classifier bridge: it does not manufacture the
-- depth-bearing source/target witnesses required by Refinement.
------------------------------------------------------------------------

canonicalProfileClassifierSurface :
  ClassifierSurface.ExistingProfileClassifierSurface
canonicalProfileClassifierSurface = record
  { decompositionModel = Profile.canonicalNSProfileDecompositionModel
  ; shellOf = λ N → N
  ; entryOf = λ i → i
  }

canonicalFTToTransitionClassifierLanding :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  ClassifierSurface.ExistingFTToTransitionIncidence
    canonicalProfileClassifierSurface
    N
    (sourceEntryCode (Relation.forcedTailFiniteIndex c h))
    (targetEntryCode (Relation.transitionTailIndex d t))
canonicalFTToTransitionClassifierLanding _ _ _ _ = refl

-- The same canonical surface does not land an FT row and an adversarial
-- column in the adversarial quadrant: the current entry map reduces that
-- pair to the transition profile.  It therefore cannot inhabit
-- ConcreteFTToAdversarialPremise, and it supplies no missing depth witness
-- for ConcreteFTToTransitionPremise.

------------------------------------------------------------------------
-- Structural projections from the tagged Fin constructors.
------------------------------------------------------------------------

sourceEntryCodeForcedTail :
  {N : Nat} (c : ForcedTail.ForcedTailClass)
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  sourceEntryCode (Relation.forcedTailFiniteIndex c h) ≡ zero
sourceEntryCodeForcedTail _ _ = refl

sourceEntryCodeAdversarial :
  {N : Nat} (c : Adversarial.AdversarialClass)
  (h : AdversarialConcrete.AdversarialHead c N) ->
  sourceEntryCode (Relation.adversarialFiniteIndex c h) ≡ suc (toℕ h)
sourceEntryCodeAdversarial _ _ = refl

sourceEntryCodeTransition :
  {N : Nat} (c : Transition.TransitionClass)
  (h : TransitionConcrete.TransitionHead c N) ->
  sourceEntryCode (Relation.transitionFiniteIndex c h) ≡ suc (toℕ h)
sourceEntryCodeTransition _ _ = refl

targetEntryCodeForcedTail :
  {N : Nat} (c : ForcedTail.ForcedTailClass)
  (t : ForcedTailConcrete.ForcedTailTail c N) ->
  targetEntryCode (Relation.forcedTailTailIndex c t) ≡ zero
targetEntryCodeForcedTail _ _ = refl

targetEntryCodeAdversarial :
  {N : Nat} (c : Adversarial.AdversarialClass)
  (t : AdversarialConcrete.AdversarialTail c N) ->
  targetEntryCode (Relation.adversarialTailIndex c t) ≡ suc (toℕ t)
targetEntryCodeAdversarial _ _ = refl

targetEntryCodeTransition :
  {N : Nat} (c : Transition.TransitionClass)
  (t : TransitionConcrete.TransitionTail c N) ->
  targetEntryCode (Relation.transitionTailIndex c t) ≡ suc (toℕ t)
targetEntryCodeTransition _ _ = refl

------------------------------------------------------------------------
-- The four canonical classifier quadrants are constructive.  These are
-- deliberately not identified with the FT→adversarial or FT→transition
-- refinement records: the latter carry additional depth and classifier
-- witnesses that the concrete relation does not currently export.
------------------------------------------------------------------------

classifierForcedTailForcedTail :
  {N : Nat} (c d : ForcedTail.ForcedTailClass)
  (h : ForcedTailConcrete.ForcedTailHead c N)
  (t : ForcedTailConcrete.ForcedTailTail d N) ->
  classifierAtConcretePair
    (Relation.forcedTailFiniteIndex c h)
    (Relation.forcedTailTailIndex d t)
    ≡ Profile.forcedTailProfile
classifierForcedTailForcedTail _ _ _ _ = refl

classifierAdversarialForcedTail :
  {N : Nat} (c : Adversarial.AdversarialClass)
  (d : ForcedTail.ForcedTailClass)
  (h : AdversarialConcrete.AdversarialHead c N)
  (t : ForcedTailConcrete.ForcedTailTail d N) ->
  classifierAtConcretePair
    (Relation.adversarialFiniteIndex c h)
    (Relation.forcedTailTailIndex d t)
    ≡ Profile.adversarialGeometryProfile
classifierAdversarialForcedTail _ _ _ _ = refl

classifierTransitionForcedTail :
  {N : Nat} (c : Transition.TransitionClass)
  (d : ForcedTail.ForcedTailClass)
  (h : TransitionConcrete.TransitionHead c N)
  (t : ForcedTailConcrete.ForcedTailTail d N) ->
  classifierAtConcretePair
    (Relation.transitionFiniteIndex c h)
    (Relation.forcedTailTailIndex d t)
    ≡ Profile.adversarialGeometryProfile
classifierTransitionForcedTail _ _ _ _ = refl

classifierForcedTailAdversarial :
  {N : Nat} (c : ForcedTail.ForcedTailClass)
  (d : Adversarial.AdversarialClass)
  (h : ForcedTailConcrete.ForcedTailHead c N)
  (t : AdversarialConcrete.AdversarialTail d N) ->
  classifierAtConcretePair
    (Relation.forcedTailFiniteIndex c h)
    (Relation.adversarialTailIndex d t)
    ≡ Profile.transitionProfile
classifierForcedTailAdversarial _ _ _ _ = refl

classifierForcedTailTransition :
  {N : Nat} (c : ForcedTail.ForcedTailClass)
  (d : Transition.TransitionClass)
  (h : ForcedTailConcrete.ForcedTailHead c N)
  (t : TransitionConcrete.TransitionTail d N) ->
  classifierAtConcretePair
    (Relation.forcedTailFiniteIndex c h)
    (Relation.transitionTailIndex d t)
    ≡ Profile.transitionProfile
classifierForcedTailTransition _ _ _ _ = refl

classifierAdversarialAdversarial :
  {N : Nat} (c : Adversarial.AdversarialClass)
  (d : Adversarial.AdversarialClass)
  (h : AdversarialConcrete.AdversarialHead c N)
  (t : AdversarialConcrete.AdversarialTail d N) ->
  classifierAtConcretePair
    (Relation.adversarialFiniteIndex c h)
    (Relation.adversarialTailIndex d t)
    ≡ Profile.residualProfile
classifierAdversarialAdversarial _ _ _ _ = refl

classifierAdversarialTransition :
  {N : Nat} (c : Adversarial.AdversarialClass)
  (d : Transition.TransitionClass)
  (h : AdversarialConcrete.AdversarialHead c N)
  (t : TransitionConcrete.TransitionTail d N) ->
  classifierAtConcretePair
    (Relation.adversarialFiniteIndex c h)
    (Relation.transitionTailIndex d t)
    ≡ Profile.residualProfile
classifierAdversarialTransition _ _ _ _ = refl

classifierTransitionAdversarial :
  {N : Nat} (c : Transition.TransitionClass)
  (d : Adversarial.AdversarialClass)
  (h : TransitionConcrete.TransitionHead c N)
  (t : AdversarialConcrete.AdversarialTail d N) ->
  classifierAtConcretePair
    (Relation.transitionFiniteIndex c h)
    (Relation.adversarialTailIndex d t)
    ≡ Profile.residualProfile
classifierTransitionAdversarial _ _ _ _ = refl

classifierTransitionTransition :
  {N : Nat} (c d : Transition.TransitionClass)
  (h : TransitionConcrete.TransitionHead c N)
  (t : TransitionConcrete.TransitionTail d N) ->
  classifierAtConcretePair
    (Relation.transitionFiniteIndex c h)
    (Relation.transitionTailIndex d t)
    ≡ Profile.residualProfile
classifierTransitionTransition _ _ _ _ = refl

------------------------------------------------------------------------
-- Exact typed premises still missing from the concrete relation.
------------------------------------------------------------------------

ConcreteFTToAdversarialPremise : Nat -> Set₁
ConcreteFTToAdversarialPremise N =
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialConcrete.AdversarialTail d N) ->
  Refinement.FTToAdversarialIncidence
    N
    (sourceEntryCode (Relation.forcedTailFiniteIndex c h))
    (targetEntryCode (Relation.adversarialTailIndex d t))

ConcreteFTToTransitionPremise : Nat -> Set₁
ConcreteFTToTransitionPremise N =
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  Refinement.FTToTransitionIncidence
    N
    (sourceEntryCode (Relation.forcedTailFiniteIndex c h))
    (targetEntryCode (Relation.transitionTailIndex d t))

ConcreteForcedTailDepthPremise : Nat -> Set
ConcreteForcedTailDepthPremise N =
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  Refinement.ForcedTailSource
    N
    (sourceEntryCode (Relation.forcedTailFiniteIndex c h))

ConcreteAdversarialDepthPremise : Nat -> Set
ConcreteAdversarialDepthPremise N =
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialConcrete.AdversarialTail d N) ->
  Refinement.AdversarialTarget
    N
    (targetEntryCode (Relation.adversarialTailIndex d t))

ConcreteTransitionDepthPremise : Nat -> Set
ConcreteTransitionDepthPremise N =
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  Refinement.TransitionTarget
    N
    (targetEntryCode (Relation.transitionTailIndex d t))

record ConcreteIndexClassifierBridgePremises (N : Nat) : Set₁ where
  constructor mkConcreteIndexClassifierBridgePremises
  field
    forcedTailDepth : ConcreteForcedTailDepthPremise N
    adversarialDepth : ConcreteAdversarialDepthPremise N
    transitionDepth : ConcreteTransitionDepthPremise N
    ftToAdversarial : ConcreteFTToAdversarialPremise N
    ftToTransition : ConcreteFTToTransitionPremise N

------------------------------------------------------------------------
-- Projectional consumption of the refinement records.  These are available
-- as soon as either exact typed premise is supplied; no additional theorem
-- is hidden in the bridge.
------------------------------------------------------------------------

ftToAdversarialSourceWitness :
  {N : Nat} ->
  ConcreteFTToAdversarialPremise N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialConcrete.AdversarialTail d N) ->
  Refinement.ForcedTailSource
    N
    (sourceEntryCode (Relation.forcedTailFiniteIndex c h))
ftToAdversarialSourceWitness p c h d t =
  Refinement.FTToAdversarialIncidence.sourceIsForcedTail
    (p c h d t)

ftToAdversarialTargetWitness :
  {N : Nat} ->
  ConcreteFTToAdversarialPremise N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialConcrete.AdversarialTail d N) ->
  Refinement.AdversarialTarget
    N
    (targetEntryCode (Relation.adversarialTailIndex d t))
ftToAdversarialTargetWitness p c h d t =
  Refinement.FTToAdversarialIncidence.targetIsAdversarial
    (p c h d t)

ftToTransitionSourceWitness :
  {N : Nat} ->
  ConcreteFTToTransitionPremise N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  Refinement.ForcedTailSource
    N
    (sourceEntryCode (Relation.forcedTailFiniteIndex c h))
ftToTransitionSourceWitness p c h d t =
  Refinement.FTToTransitionIncidence.sourceIsForcedTail
    (p c h d t)

ftToTransitionTargetWitness :
  {N : Nat} ->
  ConcreteFTToTransitionPremise N ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  Refinement.TransitionTarget
    N
    (targetEntryCode (Relation.transitionTailIndex d t))
ftToTransitionTargetWitness p c h d t =
  Refinement.FTToTransitionIncidence.targetIsTransition
    (p c h d t)

------------------------------------------------------------------------
-- Inhabited structural bridge.  The premise record above intentionally has
-- no canonical inhabitant: its fields are the exact missing analytic input.
------------------------------------------------------------------------

record ConcreteIndexClassifierBridge (N : Nat) : Set₁ where
  constructor mkConcreteIndexClassifierBridge
  field
    sourceCode :
      Relation.ConcreteNonResidualFiniteIndex N -> Nat
    targetCode :
      Relation.ConcreteNonResidualTailIndex N -> Nat
    sourceDepth :
      Relation.ConcreteNonResidualFiniteIndex N -> Nat
    targetDepth :
      Relation.ConcreteNonResidualTailIndex N -> Nat
    sourceClassProfile :
      Relation.ConcreteNonResidualFiniteIndex N -> Profile.PairIncidenceProfile
    targetClassProfile :
      Relation.ConcreteNonResidualTailIndex N -> Profile.PairIncidenceProfile

canonicalConcreteIndexClassifierBridge :
  (N : Nat) -> ConcreteIndexClassifierBridge N
canonicalConcreteIndexClassifierBridge N =
  mkConcreteIndexClassifierBridge
    sourceEntryCode
    targetEntryCode
    sourceEntryDepth
    targetEntryDepth
    sourceProfile
    targetProfile
