module DASHI.Interop.SLRResidualDrivenProducerPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire
import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact as Compiler
import DASHI.Interop.SLRAppendOnlyActiveResidualFrontierExact as Frontier
import DASHI.Interop.SLRConsumerRequirementV2Exact as ConsumerV2

------------------------------------------------------------------------
-- RESIDUAL-DRIVEN PRODUCER PLANNER
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-residual-planner
--
-- Input is the active binary frontier produced by the append-only world store.
-- OBL1 carries parser/PNF needs; OBL2 carries substantive evidence needs.
-- GAP rows remain diagnostic and do not independently create duplicate actions.
------------------------------------------------------------------------

data ProducerFamily : Set where
  articleSemantic : ProducerFamily
  revisionTemporal : ProducerFamily
  parserRepair : ProducerFamily
  identitySource : ProducerFamily
  authoritySource : ProducerFamily
  mechanismEvidence : ProducerFamily
  measurementEvidence : ProducerFamily
  comparatorEvidence : ProducerFamily
  classificationEvidence : ProducerFamily

producerFamilyTag : ProducerFamily → Nat
producerFamilyTag articleSemantic = 1
producerFamilyTag revisionTemporal = 2
producerFamilyTag parserRepair = 3
producerFamilyTag identitySource = 4
producerFamilyTag authoritySource = 5
producerFamilyTag mechanismEvidence = 6
producerFamilyTag measurementEvidence = 7
producerFamilyTag comparatorEvidence = 8
producerFamilyTag classificationEvidence = 9

producerForFragment : Compiler.CompilerFragmentKind → ProducerFamily
producerForFragment Compiler.actorFragment = articleSemantic
producerForFragment Compiler.patientFragment = articleSemantic
producerForFragment Compiler.propertyFragment = articleSemantic
producerForFragment Compiler.relationFragment = articleSemantic
producerForFragment Compiler.conjunctionFragment = articleSemantic
producerForFragment Compiler.negationFragment = articleSemantic
producerForFragment Compiler.modalityFragment = articleSemantic
producerForFragment Compiler.quantifierFragment = articleSemantic
producerForFragment Compiler.temporalFragment = revisionTemporal
producerForFragment Compiler.contentClauseFragment = articleSemantic
producerForFragment Compiler.clauseAttachmentFragment = articleSemantic
producerForFragment Compiler.unresolvedFragment = parserRepair

producerForEvidence : ConsumerV2.EvidenceCoordinateKind → ProducerFamily
producerForEvidence ConsumerV2.sourceIdentity = identitySource
producerForEvidence ConsumerV2.sameObject = identitySource
producerForEvidence ConsumerV2.authority = authoritySource
producerForEvidence ConsumerV2.mechanism = mechanismEvidence
producerForEvidence ConsumerV2.quantification = measurementEvidence
producerForEvidence ConsumerV2.probability = measurementEvidence
producerForEvidence ConsumerV2.counterfactual = comparatorEvidence
producerForEvidence ConsumerV2.instrumentComparison = comparatorEvidence
producerForEvidence ConsumerV2.incidence = measurementEvidence
producerForEvidence ConsumerV2.classification = classificationEvidence

routeActionWorldWireKindTag : Nat
routeActionWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.routeAction

record ResidualDrivenProducerPlannerParity : Set where
  constructor residualDrivenProducerPlannerParity
  field
    inputIsActiveFrontier : Bool
    obligationsOneAndTwoSupported : Bool
    onlyObligationsCreateProducerIntents : Bool
    gapRowsCreateDuplicateIntent : Bool
    producerTagsOneThroughNineExact : Bool
    temporalRequirementUsesRevisionTemporal : Bool
    unresolvedRequirementUsesParserRepair : Bool
    unresolvedRequirementUsesExternalResearch : Bool
    sourceIdentityAndSameObjectUseIdentitySource : Bool
    authorityUsesAuthoritySource : Bool
    mechanismUsesMechanismEvidence : Bool
    quantificationProbabilityIncidenceUseMeasurementEvidence : Bool
    counterfactualAndInstrumentComparisonUseComparatorEvidence : Bool
    classificationUsesClassificationEvidence : Bool
    routeIntentUsesWorldWireKindSix : Bool
    routeIntentRetainsNeedClassAndTag : Bool
    routeIntentRetainsObligationReference : Bool
    routeIntentRetainsConsumerRequirement : Bool
    routeIntentRetainsSourceScope : Bool
    routeIntentIsClaimTruth : Bool
    routeIntentCreatesSemanticAuthority : Bool
    plannerUsesJson : Bool
    plannerUsesRegex : Bool
    candidateOnly : Bool
    semanticPromotion : Bool

open ResidualDrivenProducerPlannerParity public

canonicalResidualDrivenProducerPlannerParity : ResidualDrivenProducerPlannerParity
canonicalResidualDrivenProducerPlannerParity =
  residualDrivenProducerPlannerParity
    true true true false true true true false
    true true true true true true true true true true true
    false false false false true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GapCreatesDuplicateProducerIntent : Set where
data UnresolvedDependencyTriggersExternalResearch : Set where
data RouteIntentCreatesClaimTruth : Set where
data RouteIntentCreatesSemanticAuthority : Set where
data PlannerUsesJsonTransport : Set where
data PlannerUsesRegexSemantics : Set where

gapDoesNotCreateDuplicateProducerIntent : GapCreatesDuplicateProducerIntent → ⊥
gapDoesNotCreateDuplicateProducerIntent ()

unresolvedDependencyRoutesToRepairNotResearch : UnresolvedDependencyTriggersExternalResearch → ⊥
unresolvedDependencyRoutesToRepairNotResearch ()

routeIntentDoesNotCreateClaimTruth : RouteIntentCreatesClaimTruth → ⊥
routeIntentDoesNotCreateClaimTruth ()

routeIntentDoesNotCreateSemanticAuthority : RouteIntentCreatesSemanticAuthority → ⊥
routeIntentDoesNotCreateSemanticAuthority ()

plannerJsonTransportForbidden : PlannerUsesJsonTransport → ⊥
plannerJsonTransportForbidden ()

plannerRegexSemanticsForbidden : PlannerUsesRegexSemantics → ⊥
plannerRegexSemanticsForbidden ()

activeFrontierAnchor : Frontier.ActiveResidualFrontierParity
activeFrontierAnchor = Frontier.canonicalActiveResidualFrontierParity
