module DASHI.Culture.MissingDeceasedActorIntersectionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ActorBenefitVisibilityDisruptionIntersectionExact as A
import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Core.CommonSelectorVisibilityHyperfabricExact as Visibility
import DASHI.Culture.MissingDeceasedDisruptionBenefitEvidenceExact as Evidence

------------------------------------------------------------------------
-- Current actor-class intersection frontiers.
--
-- Positive support is recorded only where the current evidence actually pays
-- that axis.  Missing axes remain missing rather than being inferred from a
-- historical precedent, economic plausibility, or public visibility.
------------------------------------------------------------------------

positive : Support.SupportSquare
positive = Support.supportSquare true false

missing : Support.SupportSquare
missing = Support.supportSquare false false

------------------------------------------------------------------------
-- Incumbent-energy hypothesis.
-- Fusion proper gives a coherent affected capability, but no specific incumbent
-- actor is yet bound here to Loureiro, no actor-specific threat perception is
-- established, and no operational axis is populated.
------------------------------------------------------------------------

energyIncumbentHypothesis : A.ActorCapabilityHypothesis
energyIncumbentHypothesis = A.actor-capability-hypothesis
  "unspecified incumbent energy actor materially exposed to commercial fusion"
  "Nuno F. G. Loureiro"
  "commercial fusion power / magnetic-confinement fusion capability"
  Evidence.incumbentEnergyInterest
  Visibility.publicInternetObserver
  "candidate class only; actor identity, exposure magnitude and person-specific visibility remain acquisition targets"

energyIncumbentEvidence : A.ActorCaseAxis → Support.SupportSquare
energyIncumbentEvidence A.benefitAxis = missing
energyIncumbentEvidence A.visibilityAxis = missing
energyIncumbentEvidence A.disruptionEffectAxis = missing
energyIncumbentEvidence A.threatPerceptionAxis = missing
energyIncumbentEvidence A.opportunityOrAccessAxis = missing
energyIncumbentEvidence A.operationalEvidenceAxis = missing

energyIncumbentReference : A.ActorCaseAxis → String
energyIncumbentReference A.benefitAxis = "Need actor-specific economic exposure to fusion deployment, not sector-level intuition."
energyIncumbentReference A.visibilityAxis = "Need evidence the exact actor/system could identify or observe Loureiro specifically."
energyIncumbentReference A.disruptionEffectAxis = "Need evidence that Loureiro's loss caused measurable fusion-programme/capability disruption beyond ordinary succession."
energyIncumbentReference A.threatPerceptionAxis = "Need contemporaneous evidence the actor perceived the relevant fusion capability/person as a material threat or competitive risk."
energyIncumbentReference A.opportunityOrAccessAxis = "Need lawful source-backed access/opportunity evidence."
energyIncumbentReference A.operationalEvidenceAxis = "Need case-specific operational, communications, financial, surveillance, witness or forensic evidence."

energyIncumbentState : A.ActorCaseEvidenceState
energyIncumbentState = A.actor-case-evidence-state
  energyIncumbentHypothesis
  energyIncumbentEvidence
  energyIncumbentReference

energyIncumbentBenefitMissing :
  Support.MissingRequiredAxis (A.actorEvidenceFamily energyIncumbentState)
energyIncumbentBenefitMissing = Support.missingRequiredAxis A.benefitAxis tt (refl , refl)

energyIncumbentNotCaseSpecific :
  A.CaseSpecificActorIntersection energyIncumbentState → ⊥
energyIncumbentNotCaseSpecific =
  A.missingAxisBlocksCaseSpecificIntersection energyIncumbentBenefitMissing

------------------------------------------------------------------------
-- Foreign-strategic-denial hypothesis.
-- Stuxnet supplies a historical capability/willingness analogue for specific
-- reported state actors, but it cannot populate any roster-specific axis.
------------------------------------------------------------------------

foreignStrategicHypothesis : A.ActorCapabilityHypothesis
foreignStrategicHypothesis = A.actor-capability-hypothesis
  "foreign strategic competitor"
  "named roster member"
  "fusion / nuclear / space / sensing / national-security technical capability"
  Evidence.foreignStrategicCompetitor
  Visibility.intelligenceCollectionObserver
  "actor class only; Stuxnet is retained separately as mode-of-action precedent"

foreignStrategicEvidence : A.ActorCaseAxis → Support.SupportSquare
foreignStrategicEvidence _ = missing

foreignStrategicReference : A.ActorCaseAxis → String
foreignStrategicReference A.benefitAxis = "Identify a specific foreign actor and source the strategic value of delaying the exact capability."
foreignStrategicReference A.visibilityAxis = "Recover person-specific visibility/collection/assessment evidence for the same actor."
foreignStrategicReference A.disruptionEffectAxis = "Measure actual effect of the person's loss on the capability."
foreignStrategicReference A.threatPerceptionAxis = "Recover actor-specific strategy/intelligence statements addressing the capability."
foreignStrategicReference A.opportunityOrAccessAxis = "Recover source-backed access/opportunity evidence."
foreignStrategicReference A.operationalEvidenceAxis = "Recover same-case operational/forensic evidence; historical precedent is non-compensating."

foreignStrategicState : A.ActorCaseEvidenceState
foreignStrategicState = A.actor-case-evidence-state
  foreignStrategicHypothesis
  foreignStrategicEvidence
  foreignStrategicReference

------------------------------------------------------------------------
-- Programme/contract competition hypothesis.
------------------------------------------------------------------------

rivalProgrammeHypothesis : A.ActorCapabilityHypothesis
rivalProgrammeHypothesis = A.actor-capability-hypothesis
  "specific rival programme, contractor or funding claimant"
  "named roster member"
  "specific programme, award, contract, IP or technical milestone"
  Evidence.rivalProgrammeOrContractor
  Visibility.contractorOrProcurementObserver
  "requires same-object competition and material post-loss benefit"

rivalProgrammeEvidence : A.ActorCaseAxis → Support.SupportSquare
rivalProgrammeEvidence _ = missing

rivalProgrammeReference : A.ActorCaseAxis → String
rivalProgrammeReference A.benefitAxis = "Recover competing award/contract/IP position and material benefit from delay or reassignment."
rivalProgrammeReference A.visibilityAxis = "Show the rival actor actually knew the named person/role through procurement, programme or professional records."
rivalProgrammeReference A.disruptionEffectAxis = "Recover before/after milestone, staffing, funding or programme-delay evidence."
rivalProgrammeReference A.threatPerceptionAxis = "Recover contemporaneous competitive-risk or dispute evidence."
rivalProgrammeReference A.opportunityOrAccessAxis = "Recover source-backed opportunity/access evidence."
rivalProgrammeReference A.operationalEvidenceAxis = "Recover direct case evidence before any causal promotion."

rivalProgrammeState : A.ActorCaseEvidenceState
rivalProgrammeState = A.actor-case-evidence-state
  rivalProgrammeHypothesis
  rivalProgrammeEvidence
  rivalProgrammeReference

------------------------------------------------------------------------
-- Search ordering: actual disruption effect is a particularly high-information
-- discriminator because if removing a person did not materially delay or impair
-- the relevant capability, disruption-benefit explanations lose force even
-- before actor attribution is considered.
------------------------------------------------------------------------

data FrontierPriority : Set where
  firstPriority secondPriority downstreamPriority : FrontierPriority

record ActorFrontierTarget : Set where
  constructor actor-frontier-target
  field
    priority : FrontierPriority
    axis : A.ActorCaseAxis
    targetDescription : String
    whyInformative : String

open ActorFrontierTarget public

actualDisruptionPriority : ActorFrontierTarget
actualDisruptionPriority = actor-frontier-target
  firstPriority
  A.disruptionEffectAxis
  "measure whether each person's loss caused a detectable programme/capability delay, substitution problem, milestone slip, knowledge gap or reorganisation"
  "a null disruption result directly weakens key-person/tacit-disruption hypotheses without needing to identify any actor"

matchedActorBenefitPriority : ActorFrontierTarget
matchedActorBenefitPriority = actor-frontier-target
  firstPriority
  A.benefitAxis
  "quantify actor-specific economic/strategic gain from delay relative to realistic counterfactual timing and substitute personnel"
  "distinguishes material beneficiary from a merely imaginable beneficiary"

visibilityPriority : ActorFrontierTarget
visibilityPriority = actor-frontier-target
  secondPriority
  A.visibilityAxis
  "recover same-actor records demonstrating person-specific visibility through public, programme, funding, contractor, personnel, professional or official intelligence surfaces"
  "benefit without awareness of the particular person is a much weaker selection hypothesis"

operationalPriority : ActorFrontierTarget
operationalPriority = actor-frontier-target
  downstreamPriority
  A.operationalEvidenceAxis
  "case-specific operational/forensic linkage"
  "this is required for actor attribution but should not be fabricated from economic motive, technical precedent or public visibility"

record ActorFrontierBoundary : Set where
  constructor actor-frontier-boundary
  field
    stuxnetCanPopulateRosterOperationalAxis : Bool
    stuxnetCanPopulateRosterOperationalAxisIsFalse :
      stuxnetCanPopulateRosterOperationalAxis ≡ false
    materialDisruptionCanBeTestedBeforeActorIdentification : Bool
    materialDisruptionCanBeTestedBeforeActorIdentificationIsTrue :
      materialDisruptionCanBeTestedBeforeActorIdentification ≡ true
    nullDisruptionEffectWeakensDisruptionBenefitHypothesis : Bool
    nullDisruptionEffectWeakensDisruptionBenefitHypothesisIsTrue :
      nullDisruptionEffectWeakensDisruptionBenefitHypothesis ≡ true
    beneficiaryClassEqualsCaseSpecificActor : Bool
    beneficiaryClassEqualsCaseSpecificActorIsFalse :
      beneficiaryClassEqualsCaseSpecificActor ≡ false

canonicalActorFrontierBoundary : ActorFrontierBoundary
canonicalActorFrontierBoundary = actor-frontier-boundary
  false refl
  true refl
  true refl
  false refl
