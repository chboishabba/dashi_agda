module DASHI.Ontology.ProgenitorParentObserverFutureSafetyExact where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl; ⊥)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Parent observer future safety.
--
-- Two states can have the same public parent surface now while an admissible
-- authority-resolution step exposes different future-relevant observations.
-- The public consumer may remain safe because it deliberately observes only
-- the stable public surface; that cannot be promoted to the authority consumer.
------------------------------------------------------------------------

data ParentDecisionState : Set where
  donorNow adoptiveNow donorResolved adoptiveResolved : ParentDecisionState

data ParentDecisionAction : Set where
  resolveCurrentAuthority : ParentDecisionAction

data ParentDecisionPrecondition : ParentDecisionState → ParentDecisionAction → Set where
  donorReady : ParentDecisionPrecondition donorNow resolveCurrentAuthority
  adoptiveReady : ParentDecisionPrecondition adoptiveNow resolveCurrentAuthority

data ParentDecisionPostcondition :
  ParentDecisionState → ParentDecisionAction → ParentDecisionState → Set where
  donorResolves :
    ParentDecisionPostcondition donorNow resolveCurrentAuthority donorResolved
  adoptiveResolves :
    ParentDecisionPostcondition adoptiveNow resolveCurrentAuthority adoptiveResolved

parentDecisionActionLabel : ParentDecisionAction → String
parentDecisionActionLabel resolveCurrentAuthority =
  "resolve authority using the fine parent relation state"

parentDecisionSystem :
  Dependency.DependentActionSystem ParentDecisionState ParentDecisionAction
parentDecisionSystem = record
  { Precondition = ParentDecisionPrecondition
  ; Postcondition = ParentDecisionPostcondition
  ; actionLabel = parentDecisionActionLabel
  }

donorResolution :
  Dependency.AdmissibleAction parentDecisionSystem donorNow resolveCurrentAuthority
donorResolution = record
  { precondition = donorReady
  ; after = donorResolved
  ; postcondition = donorResolves
  ; dependencyReceipt = "anonymous genetic donor has no legal-parent route in the witness"
  }

adoptiveResolution :
  Dependency.AdmissibleAction parentDecisionSystem adoptiveNow resolveCurrentAuthority
adoptiveResolution = record
  { precondition = adoptiveReady
  ; after = adoptiveResolved
  ; postcondition = adoptiveResolves
  ; dependencyReceipt = "adoptive parent has the legal-parent route in the witness"
  }

donorResolutionExecutes :
  Reachability.Executes parentDecisionSystem
    (resolveCurrentAuthority ∷ []) donorNow donorResolved
donorResolutionExecutes =
  Reachability.executesCons donorResolution Reachability.executesNil

adoptiveResolutionExecutes :
  Reachability.Executes parentDecisionSystem
    (resolveCurrentAuthority ∷ []) adoptiveNow adoptiveResolved
adoptiveResolutionExecutes =
  Reachability.executesCons adoptiveResolution Reachability.executesNil

------------------------------------------------------------------------
-- Consumer-relative observations.
------------------------------------------------------------------------

data ParentDecisionObservation : Set where
  publicP8810 noCurrentLegalAuthority currentLegalAuthority : ParentDecisionObservation

data ParentDecisionConsumer : Set where
  publicRegistryConsumer authorityDecisionConsumer : ParentDecisionConsumer

parentDecisionProject :
  ParentDecisionConsumer → ParentDecisionState → ParentDecisionObservation
parentDecisionProject publicRegistryConsumer _ = publicP8810
parentDecisionProject authorityDecisionConsumer donorNow = publicP8810
parentDecisionProject authorityDecisionConsumer adoptiveNow = publicP8810
parentDecisionProject authorityDecisionConsumer donorResolved = noCurrentLegalAuthority
parentDecisionProject authorityDecisionConsumer adoptiveResolved = currentLegalAuthority

parentDecisionFamily :
  Plural.ConsumerProjectionFamily
    ParentDecisionState ParentDecisionAction
    ParentDecisionConsumer ParentDecisionObservation
parentDecisionFamily =
  Plural.consumerProjectionFamily parentDecisionSystem parentDecisionProject

publicRegistryIsDynamicallySafe :
  Dynamic.DynamicConsumerSafety
    parentDecisionSystem
    (parentDecisionProject publicRegistryConsumer)
publicRegistryIsDynamicallySafe =
  Dynamic.dynamicConsumerSafety
    (λ sameCurrent leftRun rightRun → refl)

authorityDecisionTerminalisationDefect :
  Dynamic.TerminalisationDefect
    parentDecisionSystem
    (parentDecisionProject authorityDecisionConsumer)
authorityDecisionTerminalisationDefect =
  Dynamic.terminalisationDefect
    (resolveCurrentAuthority ∷ [])
    donorNow
    adoptiveNow
    donorResolved
    adoptiveResolved
    refl
    donorResolutionExecutes
    adoptiveResolutionExecutes
    (λ ())

authorityDecisionProjectionIsNotDynamicallySafe :
  Dynamic.DynamicConsumerSafety
    parentDecisionSystem
    (parentDecisionProject authorityDecisionConsumer) → ⊥
authorityDecisionProjectionIsNotDynamicallySafe safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety authorityDecisionTerminalisationDefect

publicSafetyDoesNotPromoteToPluralParentSafety :
  Plural.PluralDynamicSafety parentDecisionFamily → ⊥
publicSafetyDoesNotPromoteToPluralParentSafety plural =
  authorityDecisionProjectionIsNotDynamicallySafe
    (Plural.safeFor plural authorityDecisionConsumer)

parentConsumerSafetyAsymmetry :
  Plural.ConsumerSafetyAsymmetry
    parentDecisionFamily publicRegistryConsumer authorityDecisionConsumer
parentConsumerSafetyAsymmetry =
  Plural.consumerSafetyAsymmetry
    publicRegistryIsDynamicallySafe
    authorityDecisionTerminalisationDefect

------------------------------------------------------------------------
-- Policy-relative strengthening.
--
-- The coarse authority policy sees the same current `publicP8810` atom and
-- therefore selects the same resolution action for both states. The selected
-- future observations nevertheless differ. This is exactly the existing DASHI
-- PolicyExposedQuotientDefect shape.
------------------------------------------------------------------------

parentAuthorityPolicy :
  Policy.CoarseInterventionPolicy ParentDecisionObservation ParentDecisionAction
parentAuthorityPolicy =
  Policy.coarseInterventionPolicy (λ _ → resolveCurrentAuthority)

parentAuthorityPolicyDefect :
  Policy.PolicyExposedQuotientDefect
    parentDecisionSystem
    (parentDecisionProject authorityDecisionConsumer)
    parentAuthorityPolicy
parentAuthorityPolicyDefect =
  Policy.policyExposedQuotientDefect
    donorNow
    adoptiveNow
    donorResolved
    adoptiveResolved
    resolveCurrentAuthority
    refl
    refl
    refl
    donorResolutionExecutes
    adoptiveResolutionExecutes
    (λ ())

coarseParentAuthorityPolicyIsUnsafe :
  Policy.PolicyRelativeSafety
    parentDecisionSystem
    (parentDecisionProject authorityDecisionConsumer)
    parentAuthorityPolicy → ⊥
coarseParentAuthorityPolicyIsUnsafe safety =
  Policy.policyDefectContradictsPolicySafety safety parentAuthorityPolicyDefect

record ParentObserverFutureSafetyBoundary : Set where
  constructor parentObserverFutureSafetyBoundary
  field
    publicRegistryCanRemainSafe : Bool
    publicRegistryCanRemainSafeIsTrue : publicRegistryCanRemainSafe ≡ true
    authorityConsumerCanExposeHiddenFuture : Bool
    authorityConsumerCanExposeHiddenFutureIsTrue :
      authorityConsumerCanExposeHiddenFuture ≡ true
    coarseAuthorityPolicyCanBeUnsafe : Bool
    coarseAuthorityPolicyCanBeUnsafeIsTrue :
      coarseAuthorityPolicyCanBeUnsafe ≡ true
    localConsumerSafetyPromotesToPluralSafety : Bool
    localConsumerSafetyPromotesToPluralSafetyIsFalse :
      localConsumerSafetyPromotesToPluralSafety ≡ false

canonicalParentObserverFutureSafetyBoundary : ParentObserverFutureSafetyBoundary
canonicalParentObserverFutureSafetyBoundary =
  parentObserverFutureSafetyBoundary true refl true refl true refl false refl
