module DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact where

------------------------------------------------------------------------
-- GOD'S EYE VIEW x DASHI / SENSIBLAW PROOF-CARRYING WORLD ONTOLOGY
--
-- Upstream software inspiration / product surface only:
--   Bilawal Sidhu, gods-eye-view
--   https://github.com/bilawalsidhu/gods-eye-view
--   associated open-source walkthrough:
--   https://www.youtube.com/watch?v=GRJaKcXZS94
--   accessed 2026-09-08.
--
-- Attribution boundary:
--   upstream GEV architecture / UI intent
--   != DASHI ontology
--   != SensibLaw legal semantics
--   != Wikidata source authority
--   != PNF proof authority
--   != market/trading permission
--   != Foucault doctrine
--   != Amalek identity/command transport.
--
-- No GEV code is copied here.  The only imported idea is the application-level
-- need to project heterogeneous live/simulated spatial feeds into a selectable,
-- interrogable world surface.  DASHI supplies the proof/evidence ontology.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Sensib
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Ontology.WikidataEpistemicBridge as Wikidata
import DASHI.Interop.PNFBraidTransportField as PNF
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as WrongTypePNF
import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek
import DASHI.Culture.FoucaultFourfoldRetreatPrimarySourceBoundaryExact as Foucault
import DASHI.Finance.DashiTradeFibreBridgeExact as DashiTrade
import DASHI.Finance.DeepStatArbFibrePipelineExact as Statistics
import DASHI.Economics.MarketTransitionGrammarCyberneticsExact as Market
import DASHI.Trading.PermissionKernel as Trading

------------------------------------------------------------------------
-- 1. World-object identity is not a display label or provider-layer identity.
------------------------------------------------------------------------

data WorldObjectKind : Set where
  physicalObject : WorldObjectKind
  agent : WorldObjectKind
  facility : WorldObjectKind
  geographicFeature : WorldObjectKind
  sensor : WorldObjectKind
  eventObject : WorldObjectKind
  informationObject : WorldObjectKind
  simulatedObject : WorldObjectKind

record WorldObjectRef : Set where
  constructor world-object-ref
  field
    objectId : Sensib.StableId
    objectKind : WorldObjectKind
    displayLabel : String
    identityBasisReference : String

open WorldObjectRef public

------------------------------------------------------------------------
-- 2. Observation epistemics.  "Real" is not a Boolean.
------------------------------------------------------------------------

data EpistemicMode : Set where
  directlyObserved : EpistemicMode
  externallyReported : EpistemicMode
  derived : EpistemicMode
  interpolated : EpistemicMode
  predicted : EpistemicMode
  estimated : EpistemicMode
  simulated : EpistemicMode

-- Coverage is about the relevant source/property family, not merely whether a
-- row happened to be returned for one object.
data CoverageStatus : Set where
  observedFamily : CoverageStatus
  incompleteFamily : CoverageStatus
  uninspectedFamily : CoverageStatus
  invalidFamily : CoverageStatus


data PresenceStatus : Set where
  present : PresenceStatus
  absent : PresenceStatus
  unresolved : PresenceStatus

presenceFromCoverage : CoverageStatus → Bool → PresenceStatus
presenceFromCoverage observedFamily true = present
presenceFromCoverage observedFamily false = absent
presenceFromCoverage incompleteFamily _ = unresolved
presenceFromCoverage uninspectedFamily _ = unresolved
presenceFromCoverage invalidFamily _ = unresolved

-- A negative observation is admissible only when the relevant family was
-- actually covered and returned no row.  There is intentionally no constructor
-- for incomplete/uninspected/invalid coverage.
data NegativeObservationAdmissible : CoverageStatus → Bool → Set where
  observed-no-row : NegativeObservationAdmissible observedFamily false

incompleteCannotProveAbsence :
  NegativeObservationAdmissible incompleteFamily false → ⊥
incompleteCannotProveAbsence ()

uninspectedCannotProveAbsence :
  NegativeObservationAdmissible uninspectedFamily false → ⊥
uninspectedCannotProveAbsence ()

invalidCannotProveAbsence :
  NegativeObservationAdmissible invalidFamily false → ⊥
invalidCannotProveAbsence ()

------------------------------------------------------------------------
-- 3. Source attribution is stratified.
--
-- The repository-wide attribution rule is preserved literally: upstream
-- source, provider record, Wikidata statement, DASHI reconstruction/theorem,
-- renderer and model-generated summary are distinct provenance fibres.
------------------------------------------------------------------------

data AttributionLayer : Set where
  upstreamPrimarySource : AttributionLayer
  providerObservationRecord : AttributionLayer
  wikidataStatementLayer : AttributionLayer
  dashIReconstructionLayer : AttributionLayer
  dashIDerivedTheoremLayer : AttributionLayer
  presentationLayer : AttributionLayer
  languageModelSummaryLayer : AttributionLayer

record SourceAttribution : Set where
  constructor source-attribution
  field
    attributionLayer : AttributionLayer
    upstreamAuthorOrProvider : String
    sourceTitleOrFeed : String
    sourceRevision : String
    sourceLocation : String
    sourceTime : String
    licenceOrTermsReference : String
    dashITransformationReference : String

open SourceAttribution public

------------------------------------------------------------------------
-- 4. Observation receipt.
--
-- A live feed row becomes evidence about a world object.  It does not mutate an
-- eternal object-level fact and it does not become source authority merely by
-- being rendered.
------------------------------------------------------------------------

record ObservationReceipt : Set where
  constructor observation-receipt
  field
    observationId : Sensib.StableId
    subject : WorldObjectRef
    observedPropertyReference : String
    observedValueReference : String
    geometryReference : String
    observedAt : String
    receivedAt : String
    mode : EpistemicMode
    familyCoverage : CoverageStatus
    rowReturned : Bool
    attribution : SourceAttribution
    evidence : Sensib.EvidenceItem

    -- Same-object weld: the evidence-side subject identifier is explicitly the
    -- same world-object identifier carried by the receipt.
    evidenceSubject : Sensib.StableId
    evidenceSubjectIsSubject : evidenceSubject ≡ objectId subject

open ObservationReceipt public

observationPresence : ObservationReceipt → PresenceStatus
observationPresence receipt =
  presenceFromCoverage (familyCoverage receipt) (rowReturned receipt)

asSensibLawEvidence : ObservationReceipt → Sensib.EvidenceItem
asSensibLawEvidence = evidence

------------------------------------------------------------------------
-- 5. Resolved state is downstream of observations.
------------------------------------------------------------------------

record ResolvedWorldState : Set where
  constructor resolved-world-state
  field
    resolvedSubject : WorldObjectRef
    resolvedAt : String
    contributingObservations : List Sensib.StableId
    resolutionPolicyReference : String
    resolvedStateReference : String
    uncertaintyReference : String

open ResolvedWorldState public

------------------------------------------------------------------------
-- 6. Presentation context is a consumer projection, not the ontology object.
--
-- This is the seam intended for a GEV-style contextStore/Cesium entity.  A UI
-- carrier may point at a resolved state and evidence set without becoming the
-- world object itself.
------------------------------------------------------------------------

record PresentationContext : Set where
  constructor presentation-context
  field
    presentationId : String
    layerId : String
    presentationObject : WorldObjectRef
    state : ResolvedWorldState
    presentationSameObject : objectId presentationObject ≡ objectId (resolvedSubject state)
    selected : Bool
    evidenceReferences : List Sensib.StableId
    rendererReference : String

open PresentationContext public

------------------------------------------------------------------------
-- 7. Consumer-indexed projection.
--
-- The same resolved state can be projected differently for a map, a Wikidata
-- solver, legal WrongType analysis, PNF, statistics, proof search, or markets.
-- Projection does not transfer authority between consumers.
------------------------------------------------------------------------

data WorldConsumer : Set where
  spatialPresentationConsumer : WorldConsumer
  wikidataSolverConsumer : WorldConsumer
  sensibLawWrongTypeConsumer : WorldConsumer
  pnfConsumer : WorldConsumer
  proofSearchConsumer : WorldConsumer
  experimentDesignConsumer : WorldConsumer
  statisticsConsumer : WorldConsumer
  marketConsumer : WorldConsumer
  dashiTradeConsumer : WorldConsumer

record ConsumerProjection : Set where
  constructor consumer-projection
  field
    consumer : WorldConsumer
    projectedState : ResolvedWorldState
    projectionReference : String
    retainedEvidence : List Sensib.StableId

open ConsumerProjection public

------------------------------------------------------------------------
-- 8. Observation coordinates reuse the repository experiment-design role
-- language.  More coordinates may increase observational resolution, but they
-- do not create authority to manipulate or surveil.
------------------------------------------------------------------------

record ObservationCoordinate : Set where
  constructor observation-coordinate
  field
    coordinateId : String
    coordinateRole : Experiment.CoordinateRole
    coordinateReference : String
    calibrationOrDerivationReference : String
    observationAuthorityReference : String

open ObservationCoordinate public

------------------------------------------------------------------------
-- 9. Proof-search admission for world queries.
--
-- World interrogation is a theorem/query route with the same least-privilege
-- obligations as any other DASHI proof search: exact target, same-object spine,
-- prerequisites, no silent strengthening, authority, novelty and exact
-- consumer improvement all remain explicit in RouteAdmission.
------------------------------------------------------------------------

record WorldQueryAdmission : Set where
  constructor world-query-admission
  field
    targetReference : String
    targetObject : WorldObjectRef
    targetConsumer : WorldConsumer
    routeAdmission : ProofSearch.RouteAdmission
    identityResolutionReference : String
    coverageReference : String
    sourceAuthorityReference : String
    temporalReference : String

open WorldQueryAdmission public

------------------------------------------------------------------------
-- 10. Market/statistical transport is receipted and no-lookahead.
--
-- A spatial/news/world observation may become a market-model input only after
-- source binding, event-time, entity resolution, mechanism/regime and
-- no-lookahead references are explicit.  It never directly creates trading
-- permission.
------------------------------------------------------------------------

record MarketObservationTransport : Set where
  constructor market-observation-transport
  field
    worldObservation : ObservationReceipt
    entityResolutionReference : String
    eventTimeReference : String
    sourceBindingReference : String
    noLookaheadReference : String
    mechanismReference : String
    regimeReference : String
    statisticalValidationReference : String

open MarketObservationTransport public

------------------------------------------------------------------------
-- 11. Source/authority firewalls.
------------------------------------------------------------------------

data DisplayLabelCreatesIdentity : Set where

displayLabelDoesNotCreateIdentity : DisplayLabelCreatesIdentity → ⊥
displayLabelDoesNotCreateIdentity ()


data PresentationCreatesSourceAuthority : Set where

presentationDoesNotCreateSourceAuthority : PresentationCreatesSourceAuthority → ⊥
presentationDoesNotCreateSourceAuthority ()


data ProviderRecordCreatesOntologyTruth : Set where

providerRecordDoesNotCreateOntologyTruth : ProviderRecordCreatesOntologyTruth → ⊥
providerRecordDoesNotCreateOntologyTruth ()


data WikidataStatementCreatesExternalSourceAuthority : Set where

wikidataStatementDoesNotCreateExternalSourceAuthority :
  WikidataStatementCreatesExternalSourceAuthority → ⊥
wikidataStatementDoesNotCreateExternalSourceAuthority ()


data DASHIReconstructionCreatesUpstreamAuthorship : Set where

dashIReconstructionDoesNotCreateUpstreamAuthorship :
  DASHIReconstructionCreatesUpstreamAuthorship → ⊥
dashIReconstructionDoesNotCreateUpstreamAuthorship ()


data MarketSignalCreatesTradePermission : Set where

marketSignalDoesNotCreateTradePermission : MarketSignalCreatesTradePermission → ⊥
marketSignalDoesNotCreateTradePermission ()

------------------------------------------------------------------------
-- 12. Foucault and Amalek are audit/role-binding lanes, not identity engines.
--
-- The anti-panopticon policy below is a DASHI/SensibLaw construction informed
-- by the repository's surveillance/power audit.  It is NOT attributed to
-- Foucault as a theorem or whole-work doctrine.  Likewise an Amalek analogy is
-- never an identity assignment or command transport.
------------------------------------------------------------------------

data FoucaultAuditCreatesSurveillanceAuthority : Set where

foucaultAuditDoesNotCreateSurveillanceAuthority :
  FoucaultAuditCreatesSurveillanceAuthority → ⊥
foucaultAuditDoesNotCreateSurveillanceAuthority ()


data AmalekAnalogyCreatesIdentity : Set where

amalekAnalogyDoesNotCreateIdentity : AmalekAnalogyCreatesIdentity → ⊥
amalekAnalogyDoesNotCreateIdentity ()

------------------------------------------------------------------------
-- 13. SensibLaw anti-panopticon boundary.
--
-- A "god's-eye" presentation is explicitly treated as partial, provenance-
-- bearing and consumer-scoped.  Visibility is not omniscience; observation is
-- not authority; absence outside covered observation is unresolved; and a
-- rendered subject remains linked back to inspectable evidence rather than
-- being silently reduced to a surveillance label.
------------------------------------------------------------------------

record AntiPanopticonBoundary : Set where
  constructor anti-panopticon-boundary
  field
    completeWorldVisibilityAssumed : Bool
    completeWorldVisibilityAssumedIsFalse : completeWorldVisibilityAssumed ≡ false

    renderingCreatesSurveillanceAuthority : Bool
    renderingCreatesSurveillanceAuthorityIsFalse : renderingCreatesSurveillanceAuthority ≡ false

    observationCreatesInterventionAuthority : Bool
    observationCreatesInterventionAuthorityIsFalse : observationCreatesInterventionAuthority ≡ false

    absenceOutsideCoveredObservationMayBeAsserted : Bool
    absenceOutsideCoveredObservationMayBeAssertedIsFalse :
      absenceOutsideCoveredObservationMayBeAsserted ≡ false

    displayLabelMayReplaceResolvedIdentity : Bool
    displayLabelMayReplaceResolvedIdentityIsFalse : displayLabelMayReplaceResolvedIdentity ≡ false

    provenanceMustSurviveProjection : Bool
    provenanceMustSurviveProjectionIsTrue : provenanceMustSurviveProjection ≡ true

    evidencePathMustRemainInspectable : Bool
    evidencePathMustRemainInspectableIsTrue : evidencePathMustRemainInspectable ≡ true

    interpretationMaySilentlyBecomeSourceAuthority : Bool
    interpretationMaySilentlyBecomeSourceAuthorityIsFalse :
      interpretationMaySilentlyBecomeSourceAuthority ≡ false

canonicalAntiPanopticonBoundary : AntiPanopticonBoundary
canonicalAntiPanopticonBoundary =
  anti-panopticon-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- 14. Imported boundary anchors.
--
-- These are not new proofs.  They pin the integration to existing owners so a
-- future refactor cannot silently replace their semantics with similarly named
-- prose.
------------------------------------------------------------------------

proofSearchBoundaryAnchor : ProofSearch.ProofSearchLeastPrivilegeBoundary
proofSearchBoundaryAnchor = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary

experimentDesignBoundaryAnchor : Experiment.ExperimentalCoordinateBoundary
experimentDesignBoundaryAnchor = Experiment.canonicalExperimentalCoordinateBoundary

foucaultBoundaryAnchor : Foucault.FoucaultFourfoldSourceBoundary
foucaultBoundaryAnchor = Foucault.canonicalFoucaultFourfoldSourceBoundary

amalekBoundaryAnchor : Amalek.AmalekBoundary
amalekBoundaryAnchor = Amalek.canonicalAmalekBoundary

wikidataRankIsNotTruthAnchor : Wikidata.rankIsTruthValue ≡ false
wikidataRankIsNotTruthAnchor = Wikidata.rankIsTruthValueIsFalse

------------------------------------------------------------------------
-- 15. Canonical integration boundary.
------------------------------------------------------------------------

record GodsEyeViewOntologyBoundary : Set where
  constructor gods-eye-view-ontology-boundary
  field
    presentationEntityEqualsWorldObject : Bool
    presentationEntityEqualsWorldObjectIsFalse : presentationEntityEqualsWorldObject ≡ false

    observationEqualsResolvedWorldState : Bool
    observationEqualsResolvedWorldStateIsFalse : observationEqualsResolvedWorldState ≡ false

    noReturnedRowEqualsObjectAbsent : Bool
    noReturnedRowEqualsObjectAbsentIsFalse : noReturnedRowEqualsObjectAbsent ≡ false

    moreObservationCoordinatesCreateAuthority : Bool
    moreObservationCoordinatesCreateAuthorityIsFalse : moreObservationCoordinatesCreateAuthority ≡ false

    sourceNameCreatesReceipt : Bool
    sourceNameCreatesReceiptIsFalse : sourceNameCreatesReceipt ≡ false

    consumerProjectionTransfersAuthority : Bool
    consumerProjectionTransfersAuthorityIsFalse : consumerProjectionTransfersAuthority ≡ false

    worldObservationDirectlyCreatesTradePermission : Bool
    worldObservationDirectlyCreatesTradePermissionIsFalse :
      worldObservationDirectlyCreatesTradePermission ≡ false

    proofSearchAdmissionRemainsRequired : Bool
    proofSearchAdmissionRemainsRequiredIsTrue : proofSearchAdmissionRemainsRequired ≡ true

    attributionFibresRemainDistinct : Bool
    attributionFibresRemainDistinctIsTrue : attributionFibresRemainDistinct ≡ true

canonicalGodsEyeViewOntologyBoundary : GodsEyeViewOntologyBoundary
canonicalGodsEyeViewOntologyBoundary =
  gods-eye-view-ontology-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
