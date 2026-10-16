module DASHI.Governance.DeliberativeViableNonDominationLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.GeneralizedRoleUnifiedDomains as Roles
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as BaseLoop
import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Governance.CybersynVSMSourceAtlasExact as Sources
import DASHI.Governance.ITIRNonDominationReappropriationExact as NonDom
import DASHI.Governance.ITIRPluralViabilityTSFVExact as Plural
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GodsEye

------------------------------------------------------------------------
-- DELIBERATIVE + VIABLE + NON-DOMINATING CYBERNETIC ACTION GATE
------------------------------------------------------------------------

record DeliberativeControlCheckpoint
    (fibre : BaseLoop.LiveResidualFibre) : Set₁ where
  constructor deliberative-control-checkpoint
  field
    epistemicCandidate : Delib.ExtendedCandidateMove fibre
    liveResidualReference : String
    affectedVoiceReference : String
    dissentReference : String
    unresolvedResidualReference : String

open DeliberativeControlCheckpoint public

record AdmittedNonDominatingPhysicalAction
    (fibre : BaseLoop.LiveResidualFibre) : Set₁ where
  constructor admitted-non-dominating-physical-action
  field
    physicalAction : BaseLoop.PhysicalActionMoveReceipt fibre
    deliberativeCheckpoint : DeliberativeControlCheckpoint fibre
    worldQueryAdmission : GodsEye.WorldQueryAdmission
    nonDomination : NonDom.NonDominationOperationalReceipt
    pluralViabilityReference : String
    correctionAndAppealReference : String

open AdmittedNonDominatingPhysicalAction public

-- There is intentionally no coercion from observation, deliberation, political
-- identity, VSM role, model prediction, or a God’s-Eye view to this record.
-- The action package itself must contain an already-admitted physical action,
-- a deliberative checkpoint on the same live residual fibre, a real world-query
-- admission and the proof-relevant non-domination receipt.

record CyberneticRoleSpine : Set where
  constructor cybernetic-role-spine
  field
    realState : Roles.CyberneticState
    sensed : Roles.CyberneticState
    modelled : Roles.CyberneticState
    decision : Roles.CyberneticState
    updated : Roles.CyberneticState
    sensingOperator : Roles.CyberneticOperator
    simulationOperator : Roles.CyberneticOperator
    decisionOperator : Roles.CyberneticOperator
    interventionOperator : Roles.CyberneticOperator
    feedbackOperator : Roles.CyberneticOperator

open CyberneticRoleSpine public

canonicalCyberneticRoleSpine : CyberneticRoleSpine
canonicalCyberneticRoleSpine =
  cybernetic-role-spine
    Roles.realActivity
    Roles.sensedState
    Roles.modelState
    Roles.decisionState
    Roles.updatedState
    Roles.sense
    Roles.simulate
    Roles.decide
    Roles.intervene
    Roles.feedback

sourceBoundaryAnchor : Sources.CybersynVSMSourceBoundary
sourceBoundaryAnchor = Sources.canonicalCybersynVSMSourceBoundary

baseActionBoundaryAnchor : BaseLoop.ProofExperimentActionLoopBoundary
baseActionBoundaryAnchor = BaseLoop.canonicalProofExperimentActionLoopBoundary

deliberativeBoundaryAnchor : Delib.DeliberativeCyberneticBoundary
deliberativeBoundaryAnchor = Delib.canonicalDeliberativeCyberneticBoundary

posiwidBoundaryAnchor : POSIWID.OperationalDescriptionBoundary
posiwidBoundaryAnchor = POSIWID.canonicalOperationalDescriptionBoundary

nonDominationBoundaryAnchor : NonDom.ReappropriationBoundary
nonDominationBoundaryAnchor = NonDom.canonicalReappropriationBoundary

pluralBoundaryAnchor : Plural.PluralViabilityBoundary
pluralBoundaryAnchor = Plural.canonicalPluralViabilityBoundary

antiPanopticonBoundaryAnchor : GodsEye.AntiPanopticonBoundary
antiPanopticonBoundaryAnchor = GodsEye.canonicalAntiPanopticonBoundary

baseObservationDoesNotAuthoriseAction :
  BaseLoop.ProofExperimentActionLoopBoundary.observationAutomaticallyAuthorisesAction
    baseActionBoundaryAnchor ≡ false
baseObservationDoesNotAuthoriseAction = refl

deliberationDoesNotAuthoriseAction :
  Delib.DeliberativeCyberneticBoundary.actionAuthorityStillSeparate
    deliberativeBoundaryAnchor ≡ true
deliberationDoesNotAuthoriseAction = refl

realizedOperationRetained :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundaryAnchor ≡ true
realizedOperationRetained = refl

declaredPurposeDoesNotOverrideRealizedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundaryAnchor ≡ false
declaredPurposeDoesNotOverrideRealizedEffect = refl

antiPanopticonEvidenceRemainsInspectable :
  GodsEye.AntiPanopticonBoundary.evidencePathMustRemainInspectable
    antiPanopticonBoundaryAnchor ≡ true
antiPanopticonEvidenceRemainsInspectable = refl

record DeliberativeViableNonDominationBoundary : Set where
  constructor deliberative-viable-nondomination-boundary
  field
    observationAuthorisesAction : Bool
    deliberationAuthorisesAction : Bool
    controllerIdentityPaysActionGate : Bool
    controllerIdeologyPaysActionGate : Bool
    systemFiveRolePaysActionGate : Bool
    modelPredictionPaysActionGate : Bool
    declaredPurposePaysRealizedEffect : Bool
    futureViabilityIsPrediction : Bool
    futureViabilityIsRetrocausalCommand : Bool

    sameActionCarriesNonDominationReceipt : Bool
    sameResidualCarriesDeliberativeCheckpoint : Bool
    actionCarriesWorldQueryAdmission : Bool
    realizedBehaviourRetained : Bool
    correctionResponseRetained : Bool
    affectedVoiceRetained : Bool
    dissentResidualRetained : Bool
    evidencePathRetained : Bool
    actionAuthoritySeparateFromObservation : Bool
    actionAuthoritySeparateFromDeliberation : Bool
    pluralViabilityRemainsConsumerRelative : Bool

open DeliberativeViableNonDominationBoundary public

canonicalDeliberativeViableNonDominationBoundary :
  DeliberativeViableNonDominationBoundary
canonicalDeliberativeViableNonDominationBoundary =
  deliberative-viable-nondomination-boundary
    false false false false false false false false false
    true true true true true true true true true true true

canonicalDeliberativeViableNonDominationReceipt : GenericReceipt.GenericReceipt
canonicalDeliberativeViableNonDominationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "deliberative viable non-domination action loop"
    "DASHI.Governance.DeliberativeViableNonDominationLoopExact"
    "canonicalDeliberativeViableNonDominationBoundary"
    "welds the existing history-indexed proof/experiment/action controller, ask/listen/deliberate extension, Beer/POSIWID realised-operation semantics, God’s-Eye query admission/evidence inspectability, proof-relevant non-domination receipt and plural viability/TSFV boundary at one physical-action gate"
    "observation, deliberation, controller identity/ideology, VSM role, model prediction and declared purpose do not authorise action; future viability is a constraint on admissible continuation rather than prediction or retrocausal command; no unique political telos is manufactured"
    "agda -i . DASHI/Governance/DeliberativeViableNonDominationLoopRegression.agda"
