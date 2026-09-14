module DASHI.Interop.SLRResidualDrivenProducerPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire
import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact as Compiler
import DASHI.Interop.SLRAppendOnlyActiveResidualFrontierExact as Frontier

------------------------------------------------------------------------
-- RESIDUAL-DRIVEN PRODUCER PLANNER
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-residual-planner
--
-- Input is the active binary frontier produced by the append-only world store.
-- Only OBL1 obligations generate producer intents. GAP1 rows remain diagnostic
-- and do not independently create duplicate actions.
--
-- RTA1 body:
--   "RTA1" | producerFamily:u8 | fragmentKind:u8 |
--   candidateOnly:u8=1 | semanticPromotion:u8=0 |
--   obligationId:text | consumerId:text | requirementId:text |
--   scopeTag:u8 | [sourceManifestation:text]
------------------------------------------------------------------------

data ProducerFamily : Set where
  articleSemantic : ProducerFamily
  revisionTemporal : ProducerFamily
  parserRepair : ProducerFamily

producerFamilyTag : ProducerFamily → Nat
producerFamilyTag articleSemantic = 1
producerFamilyTag revisionTemporal = 2
producerFamilyTag parserRepair = 3

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

routeActionWorldWireKindTag : Nat
routeActionWorldWireKindTag = WorldWire.worldWireKindTag WorldWire.routeAction

record ResidualDrivenProducerPlannerParity : Set where
  constructor residualDrivenProducerPlannerParity
  field
    inputIsActiveFrontier : Bool
    onlyObligationsCreateProducerIntents : Bool
    gapRowsCreateDuplicateIntent : Bool
    articleSemanticTagIsOne : Bool
    revisionTemporalTagIsTwo : Bool
    parserRepairTagIsThree : Bool
    temporalRequirementUsesRevisionTemporal : Bool
    unresolvedRequirementUsesParserRepair : Bool
    unresolvedRequirementUsesExternalResearch : Bool
    allOtherCurrentFragmentFamiliesUseArticleSemantic : Bool
    routeIntentUsesWorldWireKindSix : Bool
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
    true true false true true true true true false true
    true true true true false false false false true false

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
