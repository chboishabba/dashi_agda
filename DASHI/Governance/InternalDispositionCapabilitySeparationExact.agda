module DASHI.Governance.InternalDispositionCapabilitySeparationExact where

------------------------------------------------------------------------
-- INTERNAL DISPOSITION / EXTERNAL PERMISSION / CAPABILITY
--
-- Safety does not depend on proving benevolent internal affect or motive.  An
-- actor can understand harm without caring enough about it; conversely unusual
-- affective traits do not establish malicious intent.  Governed capability must
-- therefore remain external to inferred internal disposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.SituatedDissentDeceptionAssayExact
import DASHI.Core.ProofCarryingPhysicalExecutionBoundaryExact

------------------------------------------------------------------------
-- Internal states and observed behaviour remain non-authoritative for capability.
------------------------------------------------------------------------

data HarmUnderstanding : Set where understandsHarm : HarmUnderstanding

data AffectiveDisposition : Set where lowEmpathicDrive highEmpathicDrive unresolvedDisposition : AffectiveDisposition

data BehaviourSurface : Set where compliantSurface suspiciousSurface : BehaviourSurface

data ExternalPermission : Set where permissionDenied permissionGranted : ExternalPermission

data Capability : Set where noCatastrophicCapability scopedCatastrophicCapability : Capability

permissionFromDisposition : AffectiveDisposition → ExternalPermission
permissionFromDisposition _ = permissionDenied

lowEmpathyDoesNotGrantCapability :
  permissionFromDisposition lowEmpathicDrive ≡ permissionGranted → ⊥
lowEmpathyDoesNotGrantCapability ()

highEmpathyDoesNotGrantCapability :
  permissionFromDisposition highEmpathicDrive ≡ permissionGranted → ⊥
highEmpathyDoesNotGrantCapability ()

------------------------------------------------------------------------
-- Friendly and suspicious behaviour are not mind-reading theorems.
------------------------------------------------------------------------

data HiddenObjective : Set where benignObjective adversarialObjective : HiddenObjective

observedBehaviour : HiddenObjective → BehaviourSurface
observedBehaviour benignObjective = compliantSurface
observedBehaviour adversarialObjective = compliantSurface

sameFriendlySurface :
  observedBehaviour benignObjective ≡ observedBehaviour adversarialObjective
sameFriendlySurface = refl

hiddenObjectivesDiffer : benignObjective ≡ adversarialObjective → ⊥
hiddenObjectivesDiffer ()

------------------------------------------------------------------------
-- Strategic understanding of governance does not provide the missing key/token.
------------------------------------------------------------------------

data GovernanceKnowledge : Set where knowsPolicyPerfectly : GovernanceKnowledge

data CapabilityToken : Set where externallyIssuedToken : CapabilityToken

data TokenFromPolicyKnowledge : GovernanceKnowledge → Set where
-- no constructor

knowingPolicyDoesNotCreateToken : TokenFromPolicyKnowledge knowsPolicyPerfectly → ⊥
knowingPolicyDoesNotCreateToken ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record InternalDispositionCapabilityBoundary : Set where
  constructor internal-disposition-capability-boundary
  field
    understandingHarmImpliesCaringEnough : Bool
    understandingHarmImpliesCaringEnoughIsFalse : understandingHarmImpliesCaringEnough ≡ false
    lowEmpathyImpliesMaliciousObjective : Bool
    lowEmpathyImpliesMaliciousObjectiveIsFalse : lowEmpathyImpliesMaliciousObjective ≡ false
    friendlyBehaviourImpliesBenignHiddenObjective : Bool
    friendlyBehaviourImpliesBenignHiddenObjectiveIsFalse :
      friendlyBehaviourImpliesBenignHiddenObjective ≡ false
    internalisedValueIsSoleCatastropheBarrier : Bool
    internalisedValueIsSoleCatastropheBarrierIsFalse :
      internalisedValueIsSoleCatastropheBarrier ≡ false
    knowingGovernanceImpliesGovernanceCapability : Bool
    knowingGovernanceImpliesGovernanceCapabilityIsFalse :
      knowingGovernanceImpliesGovernanceCapability ≡ false
    reading : String

canonicalInternalDispositionCapabilityBoundary : InternalDispositionCapabilityBoundary
canonicalInternalDispositionCapabilityBoundary =
  internal-disposition-capability-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    "Internal affect, inferred motive and external capability are separate fibres. Understanding harm need not supply motivational restraint; unusual affect does not establish malicious intent; compliant behaviour does not recover a benign hidden objective. Catastrophic capability remains proof/token governed even for an actor that understands the governance system perfectly."
