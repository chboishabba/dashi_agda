module DASHI.Cognition.PNF.SensibLawDoctrinalGateInterventionDistributionExact where

------------------------------------------------------------------------
-- DOCTRINAL GATE / INTERVENTION / DISTRIBUTIONAL EFFECT
--
-- This module formalises distinctions developed in the Mabo/Pabai thread:
--   no duty != no legal intervention;
--   preservation of an existing loss/risk allocation != absence of legal choice;
--   judicially generated doctrine != legislation;
--   a stated institutional rationale != a neutral or distribution-free effect;
--   a hegemonic-effect hypothesis != proof of subjective bias or bad faith.
--
-- Legal calibration / stable identifiers:
--   * Donoghue v Stevenson [1932] AC 562; [1932] UKHL 100.
--   * Mallonland Pty Ltd v Advanta Seeds Pty Ltd [2024] HCA 25.
--     High Court of Australia, 7 August 2024. The judgment's duty analysis uses
--     salient features including reasonable foreseeability, assumption of
--     responsibility, control, vulnerability and indeterminacy.
--   * Pabai v Commonwealth of Australia (No 2) [2025] FCA 796.
--
-- Critical-theory calibration:
--   * Glen Sean Coulthard, Red Skin, White Masks: Rejecting the Colonial
--     Politics of Recognition (University of Minnesota Press, 2014),
--     ISBN 9780816679652.
--   * Robert Nichols, Theft Is Property! Dispossession and Critical Theory
--     (Duke University Press, 2020), DOI 10.1215/9781478007500.
--
-- The formal gate/effect relations below are DASHI reconstructions and are not
-- attributed as propositions to the cited courts or authors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawJudicialInstitutionalProductionContextExact as Context
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate

mallonlandAuthority : Edge.SourceIdentity
mallonlandAuthority = Edge.source-identity
  "High Court of Australia"
  "Mallonland Pty Ltd v Advanta Seeds Pty Ltd"
  "[2024] HCA 25"
  Edge.bindingPrecedent

coulthardAuthority : Edge.SourceIdentity
coulthardAuthority = Edge.source-identity
  "Glen Sean Coulthard"
  "Red Skin, White Masks: Rejecting the Colonial Politics of Recognition"
  "ISBN 9780816679652"
  Edge.criticalTheorySource

nicholsAuthority : Edge.SourceIdentity
nicholsAuthority = Edge.source-identity
  "Robert Nichols"
  "Theft Is Property! Dispossession and Critical Theory"
  "DOI 10.1215/9781478007500"
  Edge.criticalTheorySource

------------------------------------------------------------------------
-- Gate provenance and intervention type.
------------------------------------------------------------------------

data GateProducer : Set where
  parliamentaryRule : GateProducer
  constitutionalRule : GateProducer
  judicialCommonLawDevelopment : GateProducer
  judicialPolicyConsideration : GateProducer
  evidentialFinding : GateProducer
  dashReconstruction : GateProducer


record GateInterventionReceipt : Set where
  constructor gate-intervention-receipt
  field
    gateName : String
    predicate : String
    producer : GateProducer
    authority : Edge.SourceIdentity
    statedRationale : String
    preservesExistingAllocation : Bool
    changesReachableRemedies : Bool
    directlyLegislated : Bool

open GateInterventionReceipt public

salientFeaturesGate : GateInterventionReceipt
salientFeaturesGate = gate-intervention-receipt
  "salient-features duty gate"
  "foreseeability alone is insufficient; additional relationship features are evaluated"
  judicialCommonLawDevelopment
  mallonlandAuthority
  "duty recognition is assessed through salient features rather than foreseeability alone"
  true
  true
  false

pabaiPolicyGate : GateInterventionReceipt
pabaiPolicyGate = gate-intervention-receipt
  "Pabai climate-policy duty gate"
  "the pleaded negligence duty does not arise in the challenged core-government-policy setting"
  judicialCommonLawDevelopment
  Edge.pabaiAuthority
  "institutional and doctrinal limits on negligence liability for the pleaded policy decisions"
  true
  true
  false

------------------------------------------------------------------------
-- No-duty is an outcome with allocative effects, not a magic neutral state.
------------------------------------------------------------------------

data NoDutyMeansNoIntervention : Set where
data PreserveExistingAllocationMeansNoLegalChoice : Set where
data JudiciallyCreatedGateIsLegislation : Set where
data StatedRationaleDeterminesDistributionalNeutrality : Set where
data HegemonicEffectProvesSubjectiveJudicialBias : Set where

noDutyIsNotNoIntervention : NoDutyMeansNoIntervention → ⊥
noDutyIsNotNoIntervention ()

preservationIsStillAChoiceInTheModel : PreserveExistingAllocationMeansNoLegalChoice → ⊥
preservationIsStillAChoiceInTheModel ()

judicialGateDoesNotBecomeLegislation : JudiciallyCreatedGateIsLegislation → ⊥
judicialGateDoesNotBecomeLegislation ()

rationaleDoesNotProveNeutralEffect : StatedRationaleDeterminesDistributionalNeutrality → ⊥
rationaleDoesNotProveNeutralEffect ()

hegemonyHypothesisDoesNotMindRead : HegemonicEffectProvesSubjectiveJudicialBias → ⊥
hegemonyHypothesisDoesNotMindRead ()

------------------------------------------------------------------------
-- Distributional audit: stated reasons and realised allocation stay separate.
------------------------------------------------------------------------

data LossBearer : Set where
  claimantOrAffectedPerson : LossBearer
  defendantOrRiskController : LossBearer
  publicRevenue : LossBearer
  distributedOrMixed : LossBearer
  unresolvedBearer : LossBearer


record DistributionalGateEffect : Set where
  constructor distributional-gate-effect
  field
    gate : GateInterventionReceipt
    beforeGateBearer : LossBearer
    afterGateBearer : LossBearer
    effectDescription : String
    effectDirectlyStatedByCourt : Bool
    effectIsDashReconstruction : Bool
    actorIntentInferred : Bool
    actorIntentInferredIsFalse : actorIntentInferred ≡ false

open DistributionalGateEffect public

pabaiNoDutyAllocationAudit : DistributionalGateEffect
pabaiNoDutyAllocationAudit = distributional-gate-effect
  pabaiPolicyGate
  unresolvedBearer
  claimantOrAffectedPerson
  "where the pleaded duty/remedy route is unavailable, the negligence action does not transfer the claimed climate loss to the Commonwealth through that route"
  false
  true
  false refl

------------------------------------------------------------------------
-- Hegemony is represented as a corpus-level testable hypothesis about repeated
-- asymmetric effects, not as an axiom or an accusation of conscious conspiracy.
------------------------------------------------------------------------

record HegemonyAuditHypothesis : Set where
  constructor hegemony-audit-hypothesis
  field
    candidateGateFamily : String
    protectedOrStabilisedInterest : String
    displacedOrExternalisedHarm : String
    comparisonPopulation : String
    requiresCorpusEvidence : Bool
    subjectiveIntentRequired : Bool
    automaticallyEstablished : Bool
    automaticallyEstablishedIsFalse : automaticallyEstablished ≡ false

open HegemonyAuditHypothesis public

liabilityBoundaryHegemonyHypothesis : HegemonyAuditHypothesis
liabilityBoundaryHegemonyHypothesis = hegemony-audit-hypothesis
  "indeterminacy / policy / institutional-competence / statutory-coherence duty restrictions"
  "existing institutional and economic allocation of decision authority and liability"
  "harm left outside the pleaded private-law remedy route"
  "matched negligence/public-authority cases across actor classes and harm types"
  true
  false
  false refl

------------------------------------------------------------------------
-- Judicial production context x-pollination.
------------------------------------------------------------------------

individualImpartialityStillDoesNotProveSystemNeutrality :
  Context.IndividualImpartialityImpliesSystemOutputNeutrality → ⊥
individualImpartialityStillDoesNotProveSystemNeutrality =
  Context.individualImpartialityDoesNotProveSystemNeutrality

appealStillNotPopularElection :
  Context.AppellateRecourseEqualsPopularPoliticalRecourse → ⊥
appealStillNotPopularElection = Context.appealIsNotPopularElection

------------------------------------------------------------------------
-- Climate route x-pollination: the current negative calibration does not close
-- every reformulated climate-duty path as a matter of logic.
------------------------------------------------------------------------

pabaiDoesNotCloseEveryClimateDutyFormulation :
  Climate.PabaiNoDutyClosesEveryPossibleClimateDuty → ⊥
pabaiDoesNotCloseEveryClimateDutyFormulation =
  Climate.pabaiDoesNotCloseEveryReformulatedDutyByDefinition
