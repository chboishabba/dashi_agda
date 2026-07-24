module DASHI.Cognition.BayesianReflexiveDynamicsBridge where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Belief.BayesianEvidenceIntegration as Bayes
import DASHI.Cognition.ReflexivePsychologicalDynamics as Dynamics

------------------------------------------------------------------------
-- Action-conditioned, provenance-aware evidence.  The existing Bayesian model
-- remains the base; this bridge prevents endogenous observations from being
-- silently scored as independent exogenous evidence.
------------------------------------------------------------------------

record ReflexiveBayesianEvidenceModel
    (Hypothesis Observation Action : Set)
    (W : Bayes.WeightStructure {lzero}) : Set₁ where

  private
    module WS = Bayes.WeightStructure W
    Weight = Bayes.WeightStructure.Weight W
    _⊗_ = Bayes.WeightStructure._*_ W

  field
    baseModel :
      Bayes.BayesianEvidenceModel Hypothesis Observation W

    actionConditionedLikelihood :
      Hypothesis → Observation → Action → Weight

    originAdmissible :
      Dynamics.ObservationOrigin → Bool

  boolWeight : Bool → Weight
  boolWeight true = WS.1#
  boolWeight false = WS.0#

  originWeight : Dynamics.ObservationOrigin → Weight
  originWeight origin = boolWeight (originAdmissible origin)

  reflexiveEvidenceFactor :
    Hypothesis →
    Dynamics.SituatedObservation Observation Action →
    Weight
  reflexiveEvidenceFactor hypothesis observation =
    originWeight (Dynamics.origin observation)
      ⊗ actionConditionedLikelihood
          hypothesis
          (Dynamics.payload observation)
          (Dynamics.priorAction observation)

open ReflexiveBayesianEvidenceModel public

record EvidenceProvenanceBoundary : Set where
  constructor evidenceProvenanceBoundary
  field
    exogenousAndActionMediatedSeparated : Bool
    ownActionTreatedAsIndependentEvidence : Bool
    ownActionTreatedAsIndependentEvidenceIsFalse :
      ownActionTreatedAsIndependentEvidence ≡ false
    performativityAutomaticallyProvesCausation : Bool
    performativityAutomaticallyProvesCausationIsFalse :
      performativityAutomaticallyProvesCausation ≡ false

canonicalEvidenceProvenanceBoundary : EvidenceProvenanceBoundary
canonicalEvidenceProvenanceBoundary =
  evidenceProvenanceBoundary true false refl false refl
