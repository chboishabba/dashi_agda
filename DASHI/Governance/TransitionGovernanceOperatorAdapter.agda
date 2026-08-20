module DASHI.Governance.TransitionGovernanceOperatorAdapter where

open import Data.Empty using (⊥)
import DASHI.Governance.EmancipatoryTransitionSafety as Transition
import DASHI.Governance.ProvenancePolicyTransport as Policy
import DASHI.Governance.AsymmetricReflectionPropositionLocality as Reflection
import DASHI.Governance.CorrectiveReachabilityEquivariance as Reachability
import DASHI.Governance.TraumaWeightingTerminalisationLift as Trauma

------------------------------------------------------------------------
-- Adapter from governance/pathology witnesses into the existing transition
-- geometry.  This does not redefine emancipation: it states which application
-- supplied governance witnesses refute a purported SafeEmancipatoryTransition.
------------------------------------------------------------------------

UnsafeTransition :
  (G : Transition.TransitionGeometry) →
  (T : Transition.TransitionOperator G) → Set₁
UnsafeTransition G T = Transition.SafeEmancipatoryTransition G T → ⊥

record TransitionGovernanceInterpretation
    (G : Transition.TransitionGeometry)
    (T : Transition.TransitionOperator G) : Set₁ where
  field
    PolicySystem : Policy.ProvenancePolicySystem
    MembershipSystem : Policy.CollectiveMembershipSystem PolicySystem

    CorrectiveSystem : Reflection.CorrectiveReachabilitySystem
    CorrectiveLanguage : Reachability.PairedCorrectiveLanguage CorrectiveSystem

    TraumaDynamics : Trauma.ProvenanceActionDynamics

    collectivePropagationUnsafe :
      Policy.CollectiveGuiltWitness PolicySystem MembershipSystem →
      UnsafeTransition G T

    correctiveAsymmetryUnsafe :
      Reachability.AsymmetricCorrectiveAccessWitness CorrectiveLanguage →
      UnsafeTransition G T

    terminalisedHistoricalGainUnsafe :
      Trauma.TerminalisedGain TraumaDynamics →
      UnsafeTransition G T

open TransitionGovernanceInterpretation public

------------------------------------------------------------------------
-- Extracted theorems: once an application supplies the bridge from a concrete
-- witness to transition metrics, the existing safety certificate is refuted.
------------------------------------------------------------------------

collectivePropagationRefutesTransitionSafety :
  ∀ {G T} →
  (I : TransitionGovernanceInterpretation G T) →
  Policy.CollectiveGuiltWitness
    (PolicySystem I)
    (MembershipSystem I) →
  UnsafeTransition G T
collectivePropagationRefutesTransitionSafety I =
  collectivePropagationUnsafe I

correctiveAsymmetryRefutesTransitionSafety :
  ∀ {G T} →
  (I : TransitionGovernanceInterpretation G T) →
  Reachability.AsymmetricCorrectiveAccessWitness
    (CorrectiveLanguage I) →
  UnsafeTransition G T
correctiveAsymmetryRefutesTransitionSafety I =
  correctiveAsymmetryUnsafe I

terminalisedHistoricalGainRefutesTransitionSafety :
  ∀ {G T} →
  (I : TransitionGovernanceInterpretation G T) →
  Trauma.TerminalisedGain (TraumaDynamics I) →
  UnsafeTransition G T
terminalisedHistoricalGainRefutesTransitionSafety I =
  terminalisedHistoricalGainUnsafe I

------------------------------------------------------------------------
-- High historical weighting alone is not enough to refute a safe transition.
-- The generic layer deliberately exposes no constructor from
-- TraumaLikeWeighting to UnsafeTransition; applications need an additional
-- terminalisation, collective-propagation, command/dependency, or related
-- safety violation witness.
------------------------------------------------------------------------

data HighHistoricalGainAutomaticallyUnsafe
    {G : Transition.TransitionGeometry}
    {T : Transition.TransitionOperator G}
    {D : Trauma.ProvenanceActionDynamics}
    (w : Trauma.TraumaLikeWeighting D) : Set where

highHistoricalGainDoesNotAutomaticallyRefuteTransition :
  ∀ {G T D} {w : Trauma.TraumaLikeWeighting D} →
  HighHistoricalGainAutomaticallyUnsafe {G} {T} w → ⊥
highHistoricalGainDoesNotAutomaticallyRefuteTransition ()
