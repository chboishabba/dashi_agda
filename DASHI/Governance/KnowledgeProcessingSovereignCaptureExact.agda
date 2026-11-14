module DASHI.Governance.KnowledgeProcessingSovereignCaptureExact where

------------------------------------------------------------------------
-- KNOWLEDGE-PROCESSING MONOPOLY / REGULATORY / SOVEREIGN CONTROL
--
-- New DASHI synthetic finite countermodels + conditional generic contract.
-- Existing proof owners are imported rather than reimplemented:
--   Regulatory moat, authority mandate, epistemic meta-observer capture,
--   option-cone contraction, distributed epistemic planes, local inference.
-- This is NOT a proof of observed state control, current model monopoly,
-- company insolvency, collusion, vulnerability manipulation, or real P2P.
--
-- Source atlas: KnowledgeProcessingCaptureSourceAtlas20261101Exact.
-- Original theoretical precedents include G. J. Stigler (1971),
-- "The Theory of Economic Regulation", Bell J. Econ. 2(1), pp. 3-21,
-- DOI:10.2307/3003160; Hanna Fenichel Pitkin (1967),
-- The Concept of Representation; original authors retain ownership.
-- Finite witness constructions and module composition are DASHI work.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Economics.AISafetyRegulatoryMoatGameExact as Moat
import DASHI.Economics.AIUbiquityRentInversionExact as Ubiquity
import DASHI.Governance.AuthorityMandateCore as Mandate
import DASHI.Governance.EpistemicCaptureProfessionalClosureExact as Epistemic
import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Governance.InstitutionalDependencyEntrapmentBridgeExact as Entrapment
import DASHI.Interop.DistributedEpistemicPlaneSeparationExact as Planes
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Atlas

------------------------------------------------------------------------
-- A capability is accessible only if the actual user can obtain, compute
-- and inspect/verify its output within the declared scope and resource
-- constraints. These are uninterpreted positive predicates until evidence
-- from a real consumer/deployment supplies their inhabitants.
------------------------------------------------------------------------

record KnowledgeAccess
    (User Capability Route Actor : Set) : Set₁ where
  constructor knowledgeAccess
  field
    Feasible : User → Capability → Route → Set
    MayUnilaterallyBlock : Actor → Route → Set

open KnowledgeAccess public

record ActorIndependentKnowledge
    {User Capability Route Actor : Set}
    (system : KnowledgeAccess User Capability Route Actor)
    (user : User) (capability : Capability) : Set₁ where
  constructor actorIndependentKnowledge
  field
    routeForActor : Actor → Route
    routeFeasible : (actor : Actor) →
      Feasible system user capability (routeForActor actor)
    routeOutsideActorControl : (actor : Actor) →
      MayUnilaterallyBlock system actor (routeForActor actor) → ⊥

open ActorIndependentKnowledge public

-- This does NOT imply independence against colluding coalitions, physical
-- seizure, legal coercion, shared upstream compute, or undeclared control.
-- A coalition version needs independently observed joint-control relations.

------------------------------------------------------------------------
-- Exact negative example: TWO functioning frontier application routes
-- share ONE upstream revocation/identity gate. Redundant output count is
-- therefore not equivalent to independent information-processing access.
------------------------------------------------------------------------

data DemoRoute : Set where
  cloudOne cloudTwo privateLocal federatedPeer : DemoRoute

data DemoActor : Set where
  sharedPlatform localOperator peerOperator : DemoActor

data DemoUser : Set where
  citizen : DemoUser

data DemoCapability : Set where
  independentScientificCheck : DemoCapability

data DemoFeasible :
  DemoUser → DemoCapability → DemoRoute → Set where
  cloudOneRuns : DemoFeasible citizen independentScientificCheck cloudOne
  cloudTwoRuns : DemoFeasible citizen independentScientificCheck cloudTwo
  privateLocalRuns : DemoFeasible citizen independentScientificCheck privateLocal
  federatedPeerRuns : DemoFeasible citizen independentScientificCheck federatedPeer

data DemoControl : DemoActor → DemoRoute → Set where
  gateOne : DemoControl sharedPlatform cloudOne
  gateTwo : DemoControl sharedPlatform cloudTwo
  localOwned : DemoControl localOperator privateLocal
  peerOwned : DemoControl peerOperator federatedPeer

data CloudOnlyRoute : DemoRoute → Set where
  firstCloud : CloudOnlyRoute cloudOne
  secondCloud : CloudOnlyRoute cloudTwo

allCloudOnlyRoutesShareOneGate :
  (route : DemoRoute) → CloudOnlyRoute route →
  DemoControl sharedPlatform route
allCloudOnlyRoutesShareOneGate cloudOne firstCloud = gateOne
allCloudOnlyRoutesShareOneGate cloudTwo secondCloud = gateTwo

-- Positive typed witness of a common-cut two-route instance.
record TwoRoutesOneController : Set where
  constructor twoRoutesOneController
  field
    firstIsFeasible :
      DemoFeasible citizen independentScientificCheck cloudOne
    secondIsFeasible :
      DemoFeasible citizen independentScientificCheck cloudTwo
    firstIsControlled : DemoControl sharedPlatform cloudOne
    secondIsControlled : DemoControl sharedPlatform cloudTwo

canonicalSharedCut : TwoRoutesOneController
canonicalSharedCut =
  twoRoutesOneController cloudOneRuns cloudTwoRuns gateOne gateTwo

privateRouteDoesNotDependOnSharedGate :
  DemoControl sharedPlatform privateLocal → ⊥
privateRouteDoesNotDependOnSharedGate ()

peerRouteDoesNotDependOnSharedGate :
  DemoControl sharedPlatform federatedPeer → ⊥
peerRouteDoesNotDependOnSharedGate ()

------------------------------------------------------------------------
-- Exact POSITIVE synthetic witness: 3 declared actor classes and two
-- independently controlled routes preserve an alternative against ANY
-- one of those three actors. Declared control is the entire toy universe.
------------------------------------------------------------------------

demoAccess : KnowledgeAccess DemoUser DemoCapability DemoRoute DemoActor
demoAccess = knowledgeAccess DemoFeasible DemoControl

chooseIndependent : DemoActor → DemoRoute
chooseIndependent sharedPlatform = privateLocal
chooseIndependent localOperator = federatedPeer
chooseIndependent peerOperator = privateLocal

chosenIsFeasible : (actor : DemoActor) →
  DemoFeasible citizen independentScientificCheck
               (chooseIndependent actor)
chosenIsFeasible sharedPlatform = privateLocalRuns
chosenIsFeasible localOperator = federatedPeerRuns
chosenIsFeasible peerOperator = privateLocalRuns

chosenIsNotBlockable : (actor : DemoActor) →
  DemoControl actor (chooseIndependent actor) → ⊥
chosenIsNotBlockable sharedPlatform ()
chosenIsNotBlockable localOperator ()
chosenIsNotBlockable peerOperator ()

canonicalNoSingleActorCut :
  ActorIndependentKnowledge demoAccess citizen independentScientificCheck
canonicalNoSingleActorCut =
  actorIndependentKnowledge
    chooseIndependent chosenIsFeasible chosenIsNotBlockable

-- Two available routes is not the generic admission criterion.
-- The positive result needs a controller-relative escape and a witness
-- that THAT controller cannot deny the route.

------------------------------------------------------------------------
-- Exact reachability loss is weaker than a finding of coercive conduct:
-- it becomes the existing OptionConeCoercion owner only on an additional
-- dependency and refusal-penalty witness.
------------------------------------------------------------------------

data KnowledgeRegime : Set where
  pluralKnowledge capturedAdmission : KnowledgeRegime

data KnowledgeOption : Set where
  independentVerification permissionedVerification : KnowledgeOption

data RegimeAvailable : KnowledgeRegime → KnowledgeOption → Set where
  pluralIndependent :
    RegimeAvailable pluralKnowledge independentVerification
  pluralPermissioned :
    RegimeAvailable pluralKnowledge permissionedVerification
  capturedPermissioned :
    RegimeAvailable capturedAdmission permissionedVerification

knowledgeCone :
  Cone.SafeReachabilitySystem KnowledgeRegime KnowledgeOption
knowledgeCone = Cone.safeReachabilitySystem RegimeAvailable

capturedIncludedInPlural :
  (option : KnowledgeOption) →
  RegimeAvailable capturedAdmission option →
  RegimeAvailable pluralKnowledge option
capturedIncludedInPlural permissionedVerification capturedPermissioned =
  pluralPermissioned

canonicalEpistemicOptionLoss :
  Cone.StrictSafeReachabilityContraction
    knowledgeCone pluralKnowledge capturedAdmission
canonicalEpistemicOptionLoss =
  Cone.strictSafeReachabilityContraction
    capturedIncludedInPlural
    independentVerification
    pluralIndependent
    (λ ())

-- Coercion is NOT inferred merely from a smaller feasible set.
-- Entrapment and coercion need the prior owners' penalty/dependency proofs.

------------------------------------------------------------------------
-- Economic / legal / narrative observations are separate producer claims.
-- A memory supplier's reported margin cannot instantiate a lab's ability
-- to finance its whole lifecycle; procurement ceilings are not obligations.
-- The sovereign-control gate is deliberately left uninhabited by sources
-- which only establish contact, procurement, rhetoric, risk or a policy.
------------------------------------------------------------------------

data EconomicObject : Set where
  memoryManufacturer frontierModelLab datacentreFinancingSPV : EconomicObject

supplierIsNotLab :
  memoryManufacturer ≡ frontierModelLab → ⊥
supplierIsNotLab ()

financingVehicleIsNotLab :
  datacentreFinancingSPV ≡ frontierModelLab → ⊥
financingVehicleIsNotLab ()

data CyberNarrativeObject : Set where
  php2shellActualDisclosure html2shellParodyClaim : CyberNarrativeObject

vulnerabilityAndParodyDistinct :
  php2shellActualDisclosure ≡ html2shellParodyClaim → ⊥
vulnerabilityAndParodyDistinct ()

data SovereignStage : Set where
  publicContract institutionalDependency financialIntervention
    governmentOperatingControl exclusiveKnowledgeControl : SovereignStage

record SovereignPromotionProducer : Set where
  constructor sovereignPromotionProducer
  field
    sameObjectSourceReference : String
    datedGovernmentInstrument : String
    actorIdentityEvidence : String
    operativeControlRightEvidence : String
    observedExecutionOrDenial : String

-- Model contracts and source data remain distinct; a source row by itself
-- NEVER constructs a SovereignPromotionProducer. Nothing in the module
-- declares any actual government/firm to have exclusive knowledge control.

record CaptureEvidenceResidual : Set where
  constructor captureEvidenceResidual
  field
    matchedLabCapitalRecovery : Bool
    supplierMarginObserved : Bool
    actualDependencyExitCostMeasured : Bool
    policyBurdenSameBasisMeasured : Bool
    marketConcentrationCausallyIdentified : Bool
    systemicRiskTransmissionMeasured : Bool
    rescueLegalMechanismObserved : Bool
    operatingControlRightsObserved : Bool
    realMultiOperatorCutTested : Bool
    incidentDeliberateManufactureEvidenced : Bool
    thielToCommandingHeightsIdeologyTransmissionEvidenced : Bool
open CaptureEvidenceResidual public

-- This receipt states which items were directly encountered in the
-- inspected material, not a world-wide negative finding.
sourceBoundNovemberFirstResidual : CaptureEvidenceResidual
sourceBoundNovemberFirstResidual =
  captureEvidenceResidual
    false true false false false false false false false false false

-- Reuse existing authority surfaces without falsely promoting them.
regulatoryMoatOwner : Moat.RegulatoryMoatReceipt
regulatoryMoatOwner = Moat.canonicalStructuralMoatWithoutIntent

metaObserverOwner :
  Epistemic.EpistemicCaptureProfessionalClosureBoundary
metaObserverOwner =
  Epistemic.canonicalEpistemicCaptureProfessionalClosureBoundary

antiSovereignOntologyOwner : (x : Planes.CIDCreatesAuthority) → ⊥
antiSovereignOntologyOwner = Planes.cidIsNotAuthority

mandateRequiresProvenance : Mandate.AuthoritySource
mandateRequiresProvenance = Mandate.constituencyMandate

localInferenceOwner : Ubiquity.DeploymentRegime →
  Bool
localInferenceOwner = Ubiquity.localCommoditisationRegime

-- Attribution-bearing sources; these typed objects do not prove content.
whiteHouseNationalSecuritySource : Atlas.SourceReceipt
whiteHouseNationalSecuritySource = Atlas.usNSPM

thielFirstPersonSource : Atlas.SourceReceipt
thielFirstPersonSource = Atlas.thielWolfeOriginal

sourceStatement : String
sourceStatement =
  "Knowledge-processing concentration is the protected-risk object. Two remote providers may share an admission/revocation cut. Regulatory capture, corporate dependence, rescue and sovereign operating control require separately witnessed transitions. Thiel's authored eschatology, Manidis/Roberts' rhetoric, PHP2Shell technical evidence and HTML2Shell parody are distinct source objects."
