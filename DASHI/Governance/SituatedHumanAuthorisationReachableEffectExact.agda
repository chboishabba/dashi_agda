module DASHI.Governance.SituatedHumanAuthorisationReachableEffectExact where

------------------------------------------------------------------------
-- SITUATED HUMAN AUTHORISATION / INDIRECT ACTUATION
--
-- Human presence is not automatically meaningful human control.  A valid
-- authorisation receipt keeps formal authority, understanding, evidence access,
-- deliberative time, effective refusal and non-coercion distinct.  Reachable
-- effect closure also includes high-risk human-mediated actuation paths.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.SituatedDissentDeceptionAssayExact
import DASHI.Governance.OptionConeCoercionExact
import DASHI.Core.SharedStateCoalitionReachableEffectExact

------------------------------------------------------------------------
-- Human approval surface versus deliberative integrity fibres.
------------------------------------------------------------------------

data HumanSignature : Set where clickedApprove : HumanSignature
data FormalAuthority : Set where authorisedPrincipal : FormalAuthority
data Understanding : Set where understoodAction : Understanding
data EvidenceAccess : Set where relevantEvidenceAvailable : EvidenceAccess
data DeliberativeTime : Set where sufficientTime : DeliberativeTime
data EffectiveRefusal : Set where refusalAvailable : EffectiveRefusal
data NonCoercion : Set where decisionNonCoerced : NonCoercion
data Contestability : Set where contestationAvailable : Contestability

record SituatedHumanAuthorisation : Set where
  constructor situated-human-authorisation
  field
    signature : HumanSignature
    authority : FormalAuthority
    understanding : Understanding
    evidenceAccess : EvidenceAccess
    deliberativeTime : DeliberativeTime
    effectiveRefusal : EffectiveRefusal
    nonCoercion : NonCoercion
    contestability : Contestability

canonicalSituatedHumanAuthorisation : SituatedHumanAuthorisation
canonicalSituatedHumanAuthorisation =
  situated-human-authorisation
    clickedApprove
    authorisedPrincipal
    understoodAction
    relevantEvidenceAvailable
    sufficientTime
    refusalAvailable
    decisionNonCoerced
    contestationAvailable

-- A click alone has no constructor into SituatedHumanAuthorisation.

data DecorativeApproval : Set where decorativeClick : DecorativeApproval

decorativeApprovalIsNotSituatedAuthorisation :
  DecorativeApproval → SituatedHumanAuthorisation → Bool
decorativeApprovalIsNotSituatedAuthorisation _ _ = false

------------------------------------------------------------------------
-- Coercion modes remain distinct coordinates.
------------------------------------------------------------------------

data CoercionMode : Set where
  noPressure
  physicalCoercion
  institutionalCoercion
  roleCoercion
  epistemicCoercion
  temporalCoercion
  moralBlackmail
  : CoercionMode

data ValidAuthorisationUnder : CoercionMode → Set where
  validUnpressuredAuthorisation : ValidAuthorisationUnder noPressure

moralBlackmailCannotInhabitUnpressuredAuthorisation :
  ValidAuthorisationUnder moralBlackmail → ⊥
moralBlackmailCannotInhabitUnpressuredAuthorisation ()

temporalCoercionCannotInhabitUnpressuredAuthorisation :
  ValidAuthorisationUnder temporalCoercion → ⊥
temporalCoercionCannotInhabitUnpressuredAuthorisation ()

------------------------------------------------------------------------
-- Human-mediated reachable effect.
------------------------------------------------------------------------

data Agent : Set where agent : Agent
data Human : Set where human : Human
data ConsequentialAction : Set where forbiddenDirectAction : ConsequentialAction
data PersuasionPath : Set where manufacturedUrgency selectiveEvidence repeatedPressure : PersuasionPath

data DirectCapability : Agent → ConsequentialAction → Set where
-- intentionally no constructor for the forbidden direct action

data HumanCanAct : Human → ConsequentialAction → Set where
  humanCanPerform : HumanCanAct human forbiddenDirectAction

data CanInfluence : Agent → Human → PersuasionPath → Set where
  canManufactureUrgency : CanInfluence agent human manufacturedUrgency
  canSelectEvidence : CanInfluence agent human selectiveEvidence
  canRepeatPressure : CanInfluence agent human repeatedPressure

record IndirectReachableEffect : Set where
  constructor indirect-reachable-effect
  field
    influence : CanInfluence agent human manufacturedUrgency
    humanActuation : HumanCanAct human forbiddenDirectAction

canonicalIndirectReachableEffect : IndirectReachableEffect
canonicalIndirectReachableEffect =
  indirect-reachable-effect canManufactureUrgency humanCanPerform

directForbidden : DirectCapability agent forbiddenDirectAction → ⊥
directForbidden ()

------------------------------------------------------------------------
-- Manipulation of the decision conditions cannot manufacture valid authority.
------------------------------------------------------------------------

data DecisionConditionIntegrity : Set where
  conditionsIndependent conditionsAgentManipulated : DecisionConditionIntegrity

data EffectiveAuthority : DecisionConditionIntegrity → Set where
  authorityFromIndependentConditions : EffectiveAuthority conditionsIndependent

manipulatedConditionsCannotCreateEffectiveAuthority :
  EffectiveAuthority conditionsAgentManipulated → ⊥
manipulatedConditionsCannotCreateEffectiveAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SituatedHumanAuthorisationBoundary : Set where
  constructor situated-human-authorisation-boundary
  field
    humanPresenceImpliesMeaningfulHumanControl : Bool
    humanPresenceImpliesMeaningfulHumanControlIsFalse :
      humanPresenceImpliesMeaningfulHumanControl ≡ false
    humanSignatureImpliesFreeNormativeEndorsement : Bool
    humanSignatureImpliesFreeNormativeEndorsementIsFalse :
      humanSignatureImpliesFreeNormativeEndorsement ≡ false
    formalVetoImpliesEffectiveRefusal : Bool
    formalVetoImpliesEffectiveRefusalIsFalse : formalVetoImpliesEffectiveRefusal ≡ false
    directCapabilityForbiddenImpliesIndirectEffectImpossible : Bool
    directCapabilityForbiddenImpliesIndirectEffectImpossibleIsFalse :
      directCapabilityForbiddenImpliesIndirectEffectImpossible ≡ false
    agentManipulationMayManufactureEffectiveAuthority : Bool
    agentManipulationMayManufactureEffectiveAuthorityIsFalse :
      agentManipulationMayManufactureEffectiveAuthority ≡ false
    authenticConscienceAutomaticallySettlesNormativeCorrectness : Bool
    authenticConscienceAutomaticallySettlesNormativeCorrectnessIsFalse :
      authenticConscienceAutomaticallySettlesNormativeCorrectness ≡ false
    reading : String

canonicalSituatedHumanAuthorisationBoundary : SituatedHumanAuthorisationBoundary
canonicalSituatedHumanAuthorisationBoundary =
  situated-human-authorisation-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Meaningful human control is situated rather than decorative: authority, understanding, evidence, deliberative time, effective refusal, non-coercion and contestability remain distinct. Reachable-effect closure includes declared high-risk persuasion -> human -> actuation paths, so forbidding direct actuation does not by itself block indirect actuation."
