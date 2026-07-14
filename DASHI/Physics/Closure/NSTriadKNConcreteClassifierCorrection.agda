module DASHI.Physics.Closure.NSTriadKNConcreteClassifierCorrection where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Data.Nat using (_≤_; _∸_)
open import Data.Nat.Properties using
  ( ≤-refl
  ; ≤-trans
  ; +-mono-≤
  ; *-mono-≤
  ; m≤m+n
  )

import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialConcrete
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailConcrete
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as Profile
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionConcrete
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel

------------------------------------------------------------------------
-- The canonical Nat classifier is a binary quadrant classifier.  The
-- concrete relation has a finer target tag, so the correction is made on
-- concrete source/target profiles rather than by pretending that all
-- non-forced-tail targets share one refinement label.
------------------------------------------------------------------------

correctedProfileClassifier :
  Profile.PairIncidenceProfile ->
  Profile.PairIncidenceProfile ->
  Profile.PairIncidenceProfile
correctedProfileClassifier Profile.forcedTailProfile
  Profile.forcedTailProfile = Profile.forcedTailProfile
correctedProfileClassifier Profile.forcedTailProfile
  Profile.adversarialGeometryProfile = Profile.adversarialGeometryProfile
correctedProfileClassifier Profile.forcedTailProfile
  Profile.transitionProfile = Profile.transitionProfile
correctedProfileClassifier Profile.forcedTailProfile
  Profile.residualProfile = Profile.transitionProfile
correctedProfileClassifier Profile.adversarialGeometryProfile
  Profile.forcedTailProfile = Profile.adversarialGeometryProfile
correctedProfileClassifier Profile.adversarialGeometryProfile _ =
  Profile.residualProfile
correctedProfileClassifier Profile.transitionProfile
  Profile.forcedTailProfile = Profile.adversarialGeometryProfile
correctedProfileClassifier Profile.transitionProfile _ =
  Profile.residualProfile
correctedProfileClassifier Profile.residualProfile
  Profile.forcedTailProfile = Profile.adversarialGeometryProfile
correctedProfileClassifier Profile.residualProfile _ =
  Profile.residualProfile

correctedSourceProfile :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Profile.PairIncidenceProfile
correctedSourceProfile (Relation.forcedTailFiniteIndex _ _) =
  Profile.forcedTailProfile
correctedSourceProfile (Relation.adversarialFiniteIndex _ _) =
  Profile.adversarialGeometryProfile
correctedSourceProfile (Relation.transitionFiniteIndex _ _) =
  Profile.transitionProfile

correctedTargetProfile :
  {N : Nat} ->
  Relation.ConcreteNonResidualTailIndex N ->
  Profile.PairIncidenceProfile
correctedTargetProfile (Relation.forcedTailTailIndex _ _) =
  Profile.forcedTailProfile
correctedTargetProfile (Relation.adversarialTailIndex _ _) =
  Profile.adversarialGeometryProfile
correctedTargetProfile (Relation.transitionTailIndex _ _) =
  Profile.transitionProfile

correctedConcreteClassifier :
  {N : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex N ->
  Relation.ConcreteNonResidualTailIndex N ->
  Profile.PairIncidenceProfile
correctedConcreteClassifier f t =
  correctedProfileClassifier
    (correctedSourceProfile f)
    (correctedTargetProfile t)

------------------------------------------------------------------------
-- Typed model and its concrete inhabitant.  The fields are equalities, not
-- status markers: the two refinement landings are the corrected theorem.
------------------------------------------------------------------------

record CorrectedConcreteClassifierModel (N : Nat) : Set₁ where
  constructor mkCorrectedConcreteClassifierModel
  field
    classifier :
      Relation.ConcreteNonResidualFiniteIndex N ->
      Relation.ConcreteNonResidualTailIndex N ->
      Profile.PairIncidenceProfile

    forcedTailToForcedTail :
      (c d : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailConcrete.ForcedTailHead c N) ->
      (t : ForcedTailConcrete.ForcedTailTail d N) ->
      classifier
        (Relation.forcedTailFiniteIndex c h)
        (Relation.forcedTailTailIndex d t)
        ≡ Profile.forcedTailProfile

    forcedTailToAdversarial :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailConcrete.ForcedTailHead c N) ->
      (d : Adversarial.AdversarialClass) ->
      (t : AdversarialConcrete.AdversarialTail d N) ->
      classifier
        (Relation.forcedTailFiniteIndex c h)
        (Relation.adversarialTailIndex d t)
        ≡ Profile.adversarialGeometryProfile

    forcedTailToTransition :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailConcrete.ForcedTailHead c N) ->
      (d : Transition.TransitionClass) ->
      (t : TransitionConcrete.TransitionTail d N) ->
      classifier
        (Relation.forcedTailFiniteIndex c h)
        (Relation.transitionTailIndex d t)
        ≡ Profile.transitionProfile

correctedConcreteClassifierModel :
  (N : Nat) -> CorrectedConcreteClassifierModel N
correctedConcreteClassifierModel N =
  mkCorrectedConcreteClassifierModel
    correctedConcreteClassifier
    (λ _ _ _ _ → refl)
    (λ _ _ _ _ → refl)
    (λ _ _ _ _ → refl)

------------------------------------------------------------------------
-- Corrected incidence can consume the existing depth/weight arithmetic
-- directly.  The classifier correction changes the landing label; the
-- numerical separation still follows from the same source/target depth
-- witnesses used by the profile weight model.
------------------------------------------------------------------------

correctedFTToAdversarialWeightSeparation :
  (N i j : Nat) ->
  WeightModel.ForcedTailSource N i ->
  WeightModel.AdversarialTarget N j ->
  Nat.suc N * WeightModel.weightOf j ≤ WeightModel.weightOf i
correctedFTToAdversarialWeightSeparation N i j source target =
  let
    d-i = WeightModel.entryDepth i
    d-j = WeightModel.entryDepth j
    k = d-j ∸ d-i

    linear : d-i + WeightModel.advLogDepthRequired N ≤ d-j
    linear =
      ≤-trans
        (+-mono-≤
          (WeightModel.forcedTailSourceDepthUpper N i source)
          (≤-refl {WeightModel.advLogDepthRequired N}))
        (WeightModel.adversarialTargetDepthLower N j target)

    ordering : d-i ≤ d-j
    ordering =
      ≤-trans
        (m≤m+n d-i (WeightModel.advLogDepthRequired N))
        linear

    separation : WeightModel.advLogDepthRequired N ≤ d-j ∸ d-i
    separation =
      WeightModel.m+n≤p→n≤p∸m
        d-i
        (WeightModel.advLogDepthRequired N)
        d-j
        linear

    gain : Nat.suc N ≤ WeightModel.pow2 (d-j ∸ d-i)
    gain =
      ≤-trans
        (WeightModel.pow2GeqSucN N)
        (WeightModel.pow2-mono separation)

    shifted : WeightModel.pow2 k * WeightModel.weightOf j
      ≤ WeightModel.weightOf i
    shifted =
      WeightModel.depthWeightSeparation
        i
        j
        k
        (WeightModel.entryDepthBound i)
        (WeightModel.entryDepthBound j)
        (WeightModel.m+[n∸m]≤n ordering)
  in
    ≤-trans
      (*-mono-≤ gain (≤-refl {WeightModel.weightOf j}))
      shifted

correctedFTToTransitionWeightSeparation :
  (N i j : Nat) ->
  WeightModel.ForcedTailSource N i ->
  WeightModel.TransitionTarget N j ->
  Nat.suc N * WeightModel.weightOf j ≤ WeightModel.weightOf i
correctedFTToTransitionWeightSeparation N i j source target =
  let
    d-i = WeightModel.entryDepth i
    d-j = WeightModel.entryDepth j
    k = d-j ∸ d-i

    linear : d-i + WeightModel.transLogDepthRequired N ≤ d-j
    linear =
      ≤-trans
        (+-mono-≤
          (WeightModel.forcedTailSourceDepthUpper N i source)
          (≤-refl {WeightModel.transLogDepthRequired N}))
        (WeightModel.transitionTargetDepthLower N j target)

    ordering : d-i ≤ d-j
    ordering =
      ≤-trans
        (m≤m+n d-i (WeightModel.transLogDepthRequired N))
        linear

    separation : WeightModel.transLogDepthRequired N ≤ d-j ∸ d-i
    separation =
      WeightModel.m+n≤p→n≤p∸m
        d-i
        (WeightModel.transLogDepthRequired N)
        d-j
        linear

    gain : Nat.suc N ≤ WeightModel.pow2 (d-j ∸ d-i)
    gain =
      ≤-trans
        (WeightModel.pow2GeqSucN N)
        (WeightModel.pow2-mono separation)

    shifted : WeightModel.pow2 k * WeightModel.weightOf j
      ≤ WeightModel.weightOf i
    shifted =
      WeightModel.depthWeightSeparation
        i
        j
        k
        (WeightModel.entryDepthBound i)
        (WeightModel.entryDepthBound j)
        (WeightModel.m+[n∸m]≤n ordering)
  in
    ≤-trans
      (*-mono-≤ gain (≤-refl {WeightModel.weightOf j}))
      shifted

------------------------------------------------------------------------
-- The correction is local on the existing concrete cells.  These equalities
-- preserve the other non-residual classifier cells used by the decomposition.
------------------------------------------------------------------------

correctedAdversarialToForcedTail :
  {N : Nat} ->
  (c : Adversarial.AdversarialClass) ->
  (h : AdversarialConcrete.AdversarialHead c N) ->
  (d : ForcedTail.ForcedTailClass) ->
  (t : ForcedTailConcrete.ForcedTailTail d N) ->
  correctedConcreteClassifier
    (Relation.adversarialFiniteIndex c h)
    (Relation.forcedTailTailIndex d t)
    ≡ Profile.adversarialGeometryProfile
correctedAdversarialToForcedTail _ _ _ _ = refl

correctedTransitionToForcedTail :
  {N : Nat} ->
  (c : Transition.TransitionClass) ->
  (h : TransitionConcrete.TransitionHead c N) ->
  (d : ForcedTail.ForcedTailClass) ->
  (t : ForcedTailConcrete.ForcedTailTail d N) ->
  correctedConcreteClassifier
    (Relation.transitionFiniteIndex c h)
    (Relation.forcedTailTailIndex d t)
    ≡ Profile.adversarialGeometryProfile
correctedTransitionToForcedTail _ _ _ _ = refl

correctedAdversarialToAdversarial :
  {N : Nat} ->
  (c : Adversarial.AdversarialClass) ->
  (h : AdversarialConcrete.AdversarialHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialConcrete.AdversarialTail d N) ->
  correctedConcreteClassifier
    (Relation.adversarialFiniteIndex c h)
    (Relation.adversarialTailIndex d t)
    ≡ Profile.residualProfile
correctedAdversarialToAdversarial _ _ _ _ = refl

correctedAdversarialToTransition :
  {N : Nat} ->
  (c : Adversarial.AdversarialClass) ->
  (h : AdversarialConcrete.AdversarialHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  correctedConcreteClassifier
    (Relation.adversarialFiniteIndex c h)
    (Relation.transitionTailIndex d t)
    ≡ Profile.residualProfile
correctedAdversarialToTransition _ _ _ _ = refl

correctedTransitionToAdversarial :
  {N : Nat} ->
  (c : Transition.TransitionClass) ->
  (h : TransitionConcrete.TransitionHead c N) ->
  (d : Adversarial.AdversarialClass) ->
  (t : AdversarialConcrete.AdversarialTail d N) ->
  correctedConcreteClassifier
    (Relation.transitionFiniteIndex c h)
    (Relation.adversarialTailIndex d t)
    ≡ Profile.residualProfile
correctedTransitionToAdversarial _ _ _ _ = refl

correctedTransitionToTransition :
  {N : Nat} ->
  (c : Transition.TransitionClass) ->
  (h : TransitionConcrete.TransitionHead c N) ->
  (d : Transition.TransitionClass) ->
  (t : TransitionConcrete.TransitionTail d N) ->
  correctedConcreteClassifier
    (Relation.transitionFiniteIndex c h)
    (Relation.transitionTailIndex d t)
    ≡ Profile.residualProfile
correctedTransitionToTransition _ _ _ _ = refl
