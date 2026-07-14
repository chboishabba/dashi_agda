module DASHI.Physics.Closure.NSTriadKNConcreteIndexClassifierBridgeFromCorrected where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNAdversarialConcreteIncidenceType as AdversarialConcrete
import DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates as Adversarial
import DASHI.Physics.Closure.NSTriadKNConcreteClassifierCorrection as CorrectedClassifier
import DASHI.Physics.Closure.NSTriadKNConcreteCorrectedRefinement as Corrected
import DASHI.Physics.Closure.NSTriadKNConcreteIndexClassifierBridge as ConcreteBridge
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as ForcedTailConcrete
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundnessSurface as ClassifierSurface
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as Profile
import DASHI.Physics.Closure.NSTriadKNTransitionConcreteIncidenceType as TransitionConcrete
import DASHI.Physics.Closure.NSTriadKNTransitionPrimitiveEstimates as Transition

------------------------------------------------------------------------
-- Exact obligations for crossing from the corrected concrete surface to
-- the legacy Nat-indexed refinement surface.
--
-- CorrectedConcreteRefinementPremises supplies source/target depth data only
-- at an inhabited FT-to-adversarial or FT-to-transition pair.  It does not
-- supply standalone coverage for every source or target constructor.  Also,
-- sourceEntryCode and targetEntryCode intentionally erase the adversarial /
-- transition target tag, so a corrected landing cannot be recovered from the
-- old Nat classifier by computation.  These are therefore explicit inputs,
-- not postulate-backed defaults.
------------------------------------------------------------------------

record CorrectedConcreteRefinementBridgeAssumptions (N : Nat) : Set₁ where
  constructor mkCorrectedConcreteRefinementBridgeAssumptions
  field
    forcedTailDepthCoverage :
      ConcreteBridge.ConcreteForcedTailDepthPremise N

    adversarialDepthCoverage :
      ConcreteBridge.ConcreteAdversarialDepthPremise N

    transitionDepthCoverage :
      ConcreteBridge.ConcreteTransitionDepthPremise N

    legacyClassifierSurface :
      ClassifierSurface.ExistingProfileClassifierSurface

    legacyFTToAdversarialCompatibility :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailConcrete.ForcedTailHead c N) ->
      (d : Adversarial.AdversarialClass) ->
      (t : AdversarialConcrete.AdversarialTail d N) ->
      Profile.profileClassifier
        (ClassifierSurface.ExistingProfileClassifierSurface.decompositionModel
          legacyClassifierSurface)
        (ClassifierSurface.ExistingProfileClassifierSurface.shellOf
          legacyClassifierSurface N)
        (ClassifierSurface.ExistingProfileClassifierSurface.entryOf
          legacyClassifierSurface
          (ConcreteBridge.sourceEntryCode
            (Relation.forcedTailFiniteIndex c h)))
        (ClassifierSurface.ExistingProfileClassifierSurface.entryOf
          legacyClassifierSurface
          (ConcreteBridge.targetEntryCode
            (Relation.adversarialTailIndex d t)))
      ≡
      CorrectedClassifier.correctedConcreteClassifier
        (Relation.forcedTailFiniteIndex c h)
        (Relation.adversarialTailIndex d t)

    legacyFTToTransitionCompatibility :
      (c : ForcedTail.ForcedTailClass) ->
      (h : ForcedTailConcrete.ForcedTailHead c N) ->
      (d : Transition.TransitionClass) ->
      (t : TransitionConcrete.TransitionTail d N) ->
      Profile.profileClassifier
        (ClassifierSurface.ExistingProfileClassifierSurface.decompositionModel
          legacyClassifierSurface)
        (ClassifierSurface.ExistingProfileClassifierSurface.shellOf
          legacyClassifierSurface N)
        (ClassifierSurface.ExistingProfileClassifierSurface.entryOf
          legacyClassifierSurface
          (ConcreteBridge.sourceEntryCode
            (Relation.forcedTailFiniteIndex c h)))
        (ClassifierSurface.ExistingProfileClassifierSurface.entryOf
          legacyClassifierSurface
          (ConcreteBridge.targetEntryCode
            (Relation.transitionTailIndex d t)))
      ≡
      CorrectedClassifier.correctedConcreteClassifier
        (Relation.forcedTailFiniteIndex c h)
        (Relation.transitionTailIndex d t)

------------------------------------------------------------------------
-- Route-specific constructors.
------------------------------------------------------------------------

correctedFTToAdversarialIncidenceFromBridgeAssumptions :
  {N : Nat} ->
  Corrected.CorrectedConcreteRefinementPremises N ->
  CorrectedConcreteRefinementBridgeAssumptions N ->
  ConcreteBridge.ConcreteFTToAdversarialPremise N
correctedFTToAdversarialIncidenceFromBridgeAssumptions premises assumptions
  c h d t =
  record
  { classifierSurface =
      CorrectedConcreteRefinementBridgeAssumptions.legacyClassifierSurface
        assumptions
  ; classifierLanding =
      trans
        (CorrectedConcreteRefinementBridgeAssumptions.legacyFTToAdversarialCompatibility
          assumptions c h d t)
        (Corrected.CorrectedFTToAdversarialIncidence.classifierLanding
          (Corrected.CorrectedConcreteRefinementPremises.ftToAdversarial
            premises c h d t))
  ; sourceIsForcedTail =
      Corrected.CorrectedFTToAdversarialIncidence.sourceIsForcedTail
        (Corrected.CorrectedConcreteRefinementPremises.ftToAdversarial
          premises c h d t)
  ; targetIsAdversarial =
      Corrected.CorrectedFTToAdversarialIncidence.targetIsAdversarial
        (Corrected.CorrectedConcreteRefinementPremises.ftToAdversarial
          premises c h d t)
  }

correctedFTToTransitionIncidenceFromBridgeAssumptions :
  {N : Nat} ->
  Corrected.CorrectedConcreteRefinementPremises N ->
  CorrectedConcreteRefinementBridgeAssumptions N ->
  ConcreteBridge.ConcreteFTToTransitionPremise N
correctedFTToTransitionIncidenceFromBridgeAssumptions premises assumptions
  c h d t =
  record
  { classifierSurface =
      CorrectedConcreteRefinementBridgeAssumptions.legacyClassifierSurface
        assumptions
  ; classifierLanding =
      trans
        (CorrectedConcreteRefinementBridgeAssumptions.legacyFTToTransitionCompatibility
          assumptions c h d t)
        (Corrected.CorrectedFTToTransitionIncidence.classifierLanding
          (Corrected.CorrectedConcreteRefinementPremises.ftToTransition
            premises c h d t))
  ; sourceIsForcedTail =
      Corrected.CorrectedFTToTransitionIncidence.sourceIsForcedTail
        (Corrected.CorrectedConcreteRefinementPremises.ftToTransition
          premises c h d t)
  ; targetIsTransition =
      Corrected.CorrectedFTToTransitionIncidence.targetIsTransition
        (Corrected.CorrectedConcreteRefinementPremises.ftToTransition
          premises c h d t)
  }

------------------------------------------------------------------------
-- Bundle constructor.  The returned premise record is conditional exactly
-- on the five assumption fields above; this module does not provide a
-- canonical value.
------------------------------------------------------------------------

concreteIndexClassifierBridgePremisesFromCorrected :
  {N : Nat} ->
  Corrected.CorrectedConcreteRefinementPremises N ->
  CorrectedConcreteRefinementBridgeAssumptions N ->
  ConcreteBridge.ConcreteIndexClassifierBridgePremises N
concreteIndexClassifierBridgePremisesFromCorrected premises assumptions =
  ConcreteBridge.mkConcreteIndexClassifierBridgePremises
    (CorrectedConcreteRefinementBridgeAssumptions.forcedTailDepthCoverage
      assumptions)
    (CorrectedConcreteRefinementBridgeAssumptions.adversarialDepthCoverage
      assumptions)
    (CorrectedConcreteRefinementBridgeAssumptions.transitionDepthCoverage
      assumptions)
    (correctedFTToAdversarialIncidenceFromBridgeAssumptions
      premises assumptions)
    (correctedFTToTransitionIncidenceFromBridgeAssumptions
      premises assumptions)
