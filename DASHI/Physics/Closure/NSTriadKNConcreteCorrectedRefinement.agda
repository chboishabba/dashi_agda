module DASHI.Physics.Closure.NSTriadKNConcreteCorrectedRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_≤_; _*_)

import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialConcrete
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNConcreteClassifierCorrection as Corrected
import DASHI.Physics.Closure.NSTriadKNConcreteIndexClassifierBridge as ConcreteBridge
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailConcrete
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as Profile
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionConcrete
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition

------------------------------------------------------------------------
-- Corrected concrete refinement premises.
--
-- The legacy refinement records use the binary Nat classifier surface.  The
-- concrete relation has separate adversarial and transition tags, so this
-- surface keeps the corrected classifier landing and the depth witnesses in
-- one typed record.  It intentionally has no canonical inhabitant: the
-- source/target depth witnesses are the remaining analytic input.
------------------------------------------------------------------------

record CorrectedFTToAdversarialIncidence
    (N : Nat)
    (c : ForcedTail.ForcedTailClass)
    (h : ForcedTailConcrete.ForcedTailHead c N)
    (d : Adversarial.AdversarialClass)
    (t : AdversarialConcrete.AdversarialTail d N) : Set₁ where
  constructor mkCorrectedFTToAdversarialIncidence
  field
    classifierLanding :
      Corrected.correctedConcreteClassifier
        (Relation.forcedTailFiniteIndex c h)
        (Relation.adversarialTailIndex d t)
        ≡ Profile.adversarialGeometryProfile

    sourceIsForcedTail :
      WeightModel.ForcedTailSource
        N
        (ConcreteBridge.sourceEntryCode
          (Relation.forcedTailFiniteIndex c h))

    targetIsAdversarial :
      WeightModel.AdversarialTarget
        N
        (ConcreteBridge.targetEntryCode
          (Relation.adversarialTailIndex d t))

record CorrectedFTToTransitionIncidence
    (N : Nat)
    (c : ForcedTail.ForcedTailClass)
    (h : ForcedTailConcrete.ForcedTailHead c N)
    (d : Transition.TransitionClass)
    (t : TransitionConcrete.TransitionTail d N) : Set₁ where
  constructor mkCorrectedFTToTransitionIncidence
  field
    classifierLanding :
      Corrected.correctedConcreteClassifier
        (Relation.forcedTailFiniteIndex c h)
        (Relation.transitionTailIndex d t)
        ≡ Profile.transitionProfile

    sourceIsForcedTail :
      WeightModel.ForcedTailSource
        N
        (ConcreteBridge.sourceEntryCode
          (Relation.forcedTailFiniteIndex c h))

    targetIsTransition :
      WeightModel.TransitionTarget
        N
        (ConcreteBridge.targetEntryCode
          (Relation.transitionTailIndex d t))

open CorrectedFTToAdversarialIncidence public
open CorrectedFTToTransitionIncidence public

------------------------------------------------------------------------
-- The classifier part is constructive.  The only arguments required by
-- these constructors are the actual depth/profile witnesses.
------------------------------------------------------------------------

correctedFTToAdversarialIncidenceFromDepth :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialConcrete.AdversarialTail d N) ->
  WeightModel.ForcedTailSource
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h)) ->
  WeightModel.AdversarialTarget
    N
    (ConcreteBridge.targetEntryCode
      (Relation.adversarialTailIndex d t)) ->
  CorrectedFTToAdversarialIncidence N c h d t
correctedFTToAdversarialIncidenceFromDepth c h d t source target =
  mkCorrectedFTToAdversarialIncidence
    refl
    source
    target

correctedFTToTransitionIncidenceFromDepth :
  {N : Nat} ->
  (c : ForcedTail.ForcedTailClass) ->
  (h : ForcedTailConcrete.ForcedTailHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  WeightModel.ForcedTailSource
    N
    (ConcreteBridge.sourceEntryCode
      (Relation.forcedTailFiniteIndex c h)) ->
  WeightModel.TransitionTarget
    N
    (ConcreteBridge.targetEntryCode
      (Relation.transitionTailIndex d t)) ->
  CorrectedFTToTransitionIncidence N c h d t
correctedFTToTransitionIncidenceFromDepth c h d t source target =
  mkCorrectedFTToTransitionIncidence
    refl
    source
    target

------------------------------------------------------------------------
-- A bundle for the two cross-profile routes.  Keeping the quantifiers over
-- concrete class/index data makes the missing geometry visible at the exact
-- row/column pair where it is needed.
------------------------------------------------------------------------

record CorrectedConcreteRefinementPremises (N : Nat) : Set₁ where
  constructor mkCorrectedConcreteRefinementPremises
  field
    ftToAdversarial :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailConcrete.ForcedTailHead c N) ->
      (d : Adversarial.AdversarialClass) ->
      (t : AdversarialConcrete.AdversarialTail d N) ->
      CorrectedFTToAdversarialIncidence N c h d t

    ftToTransition :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailConcrete.ForcedTailHead c N) ->
      (d : Transition.TransitionClass) ->
      (t : TransitionConcrete.TransitionTail d N) ->
      CorrectedFTToTransitionIncidence N c h d t

------------------------------------------------------------------------
-- Exact weight-oriented consequences of the corrected premises.
------------------------------------------------------------------------

correctedFTToAdversarialWeightOrientationFromIncidence :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  {h : ForcedTailConcrete.ForcedTailHead c N} ->
  {d : Adversarial.AdversarialClass} ->
  {t : AdversarialConcrete.AdversarialTail d N} ->
  CorrectedFTToAdversarialIncidence N c h d t ->
  suc N * WeightModel.weightOf
    (ConcreteBridge.targetEntryCode
      (Relation.adversarialTailIndex d t))
    ≤ WeightModel.weightOf
      (ConcreteBridge.sourceEntryCode
        (Relation.forcedTailFiniteIndex c h))
correctedFTToAdversarialWeightOrientationFromIncidence inc =
  Corrected.correctedFTToAdversarialWeightSeparation
    _
    _
    _
    (sourceIsForcedTail inc)
    (targetIsAdversarial inc)

correctedFTToTransitionWeightOrientationFromIncidence :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  {h : ForcedTailConcrete.ForcedTailHead c N} ->
  {d : Transition.TransitionClass} ->
  {t : TransitionConcrete.TransitionTail d N} ->
  CorrectedFTToTransitionIncidence N c h d t ->
  suc N * WeightModel.weightOf
    (ConcreteBridge.targetEntryCode
      (Relation.transitionTailIndex d t))
    ≤ WeightModel.weightOf
      (ConcreteBridge.sourceEntryCode
        (Relation.forcedTailFiniteIndex c h))
correctedFTToTransitionWeightOrientationFromIncidence inc =
  Corrected.correctedFTToTransitionWeightSeparation
    _
    _
    _
    (sourceIsForcedTail inc)
    (targetIsTransition inc)
