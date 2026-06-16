module DASHI.Biology.BioactiveMolecularRecognitionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Interop.ObservationTransportSpine as Spine
import DASHI.Biology.BioactiveAuthorityBoundaryCore as BoundaryCore

------------------------------------------------------------------------
-- Bioactive molecular recognition bridge.
--
-- This is a candidate-only receipt surface for ligand, receptor, enzyme,
-- transporter, channel, and allosteric-site recognition.  It records
-- candidate molecules, endogenous ligand or substrate candidates, target
-- context, similarity carriers, binding and occupancy candidates, action
-- candidates, kinetic carriers, pathway modulation, and residual clinical or
-- behavioral fragments.
--
-- It hard-blocks clinical authority, dose-response authority, prescribing
-- authority, disease authority, behavior authority, biomarker authority,
-- receptor-action identity authority, and shape-effect identity authority.

data Never : Set where

------------------------------------------------------------------------
-- Candidate vocabulary.

data BioactiveRecognitionTargetContext : Set where
  receptorTargetContext : BioactiveRecognitionTargetContext
  transporterTargetContext : BioactiveRecognitionTargetContext
  enzymeTargetContext : BioactiveRecognitionTargetContext
  channelTargetContext : BioactiveRecognitionTargetContext
  allostericSiteTargetContext : BioactiveRecognitionTargetContext

data BioactiveSimilarityCarrier : Set where
  scaffoldCarrier : BioactiveSimilarityCarrier
  pharmacophoreCarrier : BioactiveSimilarityCarrier
  chargeCarrier : BioactiveSimilarityCarrier
  geometryCarrier : BioactiveSimilarityCarrier
  conformationCarrier : BioactiveSimilarityCarrier
  lipophilicityCarrier : BioactiveSimilarityCarrier

data BioactiveRecognitionAction : Set where
  agonistAction : BioactiveRecognitionAction
  partialAgonistAction : BioactiveRecognitionAction
  antagonistAction : BioactiveRecognitionAction
  inverseAgonistAction : BioactiveRecognitionAction
  allostericModulatorAction : BioactiveRecognitionAction
  competitiveInhibitorAction : BioactiveRecognitionAction
  irreversibleInhibitorAction : BioactiveRecognitionAction
  transporterReuptakeInhibitorAction : BioactiveRecognitionAction
  enzymeSubstrateAction : BioactiveRecognitionAction

data BioactiveKineticCarrier : Set where
  associationRateCarrier : BioactiveKineticCarrier
  dissociationRateCarrier : BioactiveKineticCarrier
  residenceTimeCarrier : BioactiveKineticCarrier
  turnoverCarrier : BioactiveKineticCarrier
  translocationCarrier : BioactiveKineticCarrier
  permeabilityCarrier : BioactiveKineticCarrier

data BioactivePathwayModulation : Set where
  pathwayActivationCandidate : BioactivePathwayModulation
  pathwayInhibitionCandidate : BioactivePathwayModulation
  pathwayBiasCandidate : BioactivePathwayModulation
  pathwayTransportRedirectionCandidate : BioactivePathwayModulation
  pathwayCatalyticRoutingCandidate : BioactivePathwayModulation

data BioactiveRecognitionResidualKind : Set where
  clinicalResidualKind : BioactiveRecognitionResidualKind
  doseResponseResidualKind : BioactiveRecognitionResidualKind
  prescribingResidualKind : BioactiveRecognitionResidualKind
  diseaseResidualKind : BioactiveRecognitionResidualKind
  behaviorResidualKind : BioactiveRecognitionResidualKind
  biomarkerResidualKind : BioactiveRecognitionResidualKind
  receptorActionIdentityResidualKind : BioactiveRecognitionResidualKind
  shapeEffectIdentityResidualKind : BioactiveRecognitionResidualKind

data BioactiveRecognitionGuard : Set where
  NoClinicalAuthorityClaim : BioactiveRecognitionGuard
  NoDoseResponseAuthorityClaim : BioactiveRecognitionGuard
  NoPrescribingAuthorityClaim : BioactiveRecognitionGuard
  NoDiseaseAuthorityClaim : BioactiveRecognitionGuard
  NoBehaviorAuthorityClaim : BioactiveRecognitionGuard
  NoBiomarkerAuthorityClaim : BioactiveRecognitionGuard
  NoReceptorActionIdentityAuthorityClaim : BioactiveRecognitionGuard
  NoShapeEffectIdentityAuthorityClaim : BioactiveRecognitionGuard
  NoReceptorActionIdentityClaim : BioactiveRecognitionGuard
  NoShapeEffectIdentityClaim : BioactiveRecognitionGuard

data BioactiveRecognitionRoute : Set where
  boundedRecognitionReceiptRoute : BioactiveRecognitionRoute
  clinicalInferenceRoute : BioactiveRecognitionRoute
  doseResponseRoute : BioactiveRecognitionRoute
  prescribingRoute : BioactiveRecognitionRoute
  diseaseRoute : BioactiveRecognitionRoute
  behaviorRoute : BioactiveRecognitionRoute
  biomarkerRoute : BioactiveRecognitionRoute
  receptorActionIdentityRoute : BioactiveRecognitionRoute
  shapeEffectIdentityRoute : BioactiveRecognitionRoute

AdmissibleBioactiveRecognitionRoute : BioactiveRecognitionRoute -> Set
AdmissibleBioactiveRecognitionRoute boundedRecognitionReceiptRoute = ⊤
AdmissibleBioactiveRecognitionRoute clinicalInferenceRoute = Never
AdmissibleBioactiveRecognitionRoute doseResponseRoute = Never
AdmissibleBioactiveRecognitionRoute prescribingRoute = Never
AdmissibleBioactiveRecognitionRoute diseaseRoute = Never
AdmissibleBioactiveRecognitionRoute behaviorRoute = Never
AdmissibleBioactiveRecognitionRoute biomarkerRoute = Never
AdmissibleBioactiveRecognitionRoute receptorActionIdentityRoute = Never
AdmissibleBioactiveRecognitionRoute shapeEffectIdentityRoute = Never

clinicalInferenceRejected :
  AdmissibleBioactiveRecognitionRoute clinicalInferenceRoute -> Never
clinicalInferenceRejected impossible = impossible

doseResponseRejected :
  AdmissibleBioactiveRecognitionRoute doseResponseRoute -> Never
doseResponseRejected impossible = impossible

prescribingRejected :
  AdmissibleBioactiveRecognitionRoute prescribingRoute -> Never
prescribingRejected impossible = impossible

diseaseRejected :
  AdmissibleBioactiveRecognitionRoute diseaseRoute -> Never
diseaseRejected impossible = impossible

behaviorRejected :
  AdmissibleBioactiveRecognitionRoute behaviorRoute -> Never
behaviorRejected impossible = impossible

biomarkerRejected :
  AdmissibleBioactiveRecognitionRoute biomarkerRoute -> Never
biomarkerRejected impossible = impossible

receptorActionIdentityRejected :
  AdmissibleBioactiveRecognitionRoute receptorActionIdentityRoute -> Never
receptorActionIdentityRejected impossible = impossible

shapeEffectIdentityRejected :
  AdmissibleBioactiveRecognitionRoute shapeEffectIdentityRoute -> Never
shapeEffectIdentityRejected impossible = impossible

data BioactiveRecognitionAuthorityClaim : Set where
  clinicalAuthorityClaim : BioactiveRecognitionAuthorityClaim
  doseResponseAuthorityClaim : BioactiveRecognitionAuthorityClaim
  prescribingAuthorityClaim : BioactiveRecognitionAuthorityClaim
  diseaseAuthorityClaim : BioactiveRecognitionAuthorityClaim
  behaviorAuthorityClaim : BioactiveRecognitionAuthorityClaim
  biomarkerAuthorityClaim : BioactiveRecognitionAuthorityClaim
  receptorActionIdentityAuthorityClaim : BioactiveRecognitionAuthorityClaim
  shapeEffectIdentityAuthorityClaim : BioactiveRecognitionAuthorityClaim

canonicalBioactiveRecognitionTargetContexts :
  List BioactiveRecognitionTargetContext
canonicalBioactiveRecognitionTargetContexts =
  receptorTargetContext
  ∷ transporterTargetContext
  ∷ enzymeTargetContext
  ∷ channelTargetContext
  ∷ allostericSiteTargetContext
  ∷ []

canonicalBioactiveSimilarityCarriers :
  List BioactiveSimilarityCarrier
canonicalBioactiveSimilarityCarriers =
  scaffoldCarrier
  ∷ pharmacophoreCarrier
  ∷ chargeCarrier
  ∷ geometryCarrier
  ∷ conformationCarrier
  ∷ lipophilicityCarrier
  ∷ []

canonicalBioactiveRecognitionActions :
  List BioactiveRecognitionAction
canonicalBioactiveRecognitionActions =
  agonistAction
  ∷ partialAgonistAction
  ∷ antagonistAction
  ∷ inverseAgonistAction
  ∷ allostericModulatorAction
  ∷ competitiveInhibitorAction
  ∷ irreversibleInhibitorAction
  ∷ transporterReuptakeInhibitorAction
  ∷ enzymeSubstrateAction
  ∷ []

canonicalBioactiveKineticCarriers :
  List BioactiveKineticCarrier
canonicalBioactiveKineticCarriers =
  associationRateCarrier
  ∷ dissociationRateCarrier
  ∷ residenceTimeCarrier
  ∷ turnoverCarrier
  ∷ translocationCarrier
  ∷ permeabilityCarrier
  ∷ []

canonicalBioactivePathwayModulations :
  List BioactivePathwayModulation
canonicalBioactivePathwayModulations =
  pathwayActivationCandidate
  ∷ pathwayInhibitionCandidate
  ∷ pathwayBiasCandidate
  ∷ pathwayTransportRedirectionCandidate
  ∷ pathwayCatalyticRoutingCandidate
  ∷ []

canonicalBioactiveRecognitionResidualKinds :
  List BioactiveRecognitionResidualKind
canonicalBioactiveRecognitionResidualKinds =
  clinicalResidualKind
  ∷ doseResponseResidualKind
  ∷ prescribingResidualKind
  ∷ diseaseResidualKind
  ∷ behaviorResidualKind
  ∷ biomarkerResidualKind
  ∷ receptorActionIdentityResidualKind
  ∷ shapeEffectIdentityResidualKind
  ∷ []

canonicalBioactiveRecognitionGuards :
  List BioactiveRecognitionGuard
canonicalBioactiveRecognitionGuards =
  NoClinicalAuthorityClaim
  ∷ NoDoseResponseAuthorityClaim
  ∷ NoPrescribingAuthorityClaim
  ∷ NoDiseaseAuthorityClaim
  ∷ NoBehaviorAuthorityClaim
  ∷ NoBiomarkerAuthorityClaim
  ∷ NoReceptorActionIdentityAuthorityClaim
  ∷ NoShapeEffectIdentityAuthorityClaim
  ∷ NoReceptorActionIdentityClaim
  ∷ NoShapeEffectIdentityClaim
  ∷ []

canonicalBioactiveRecognitionAuthorityClaims :
  List BioactiveRecognitionAuthorityClaim
canonicalBioactiveRecognitionAuthorityClaims =
  clinicalAuthorityClaim
  ∷ doseResponseAuthorityClaim
  ∷ prescribingAuthorityClaim
  ∷ diseaseAuthorityClaim
  ∷ behaviorAuthorityClaim
  ∷ biomarkerAuthorityClaim
  ∷ receptorActionIdentityAuthorityClaim
  ∷ shapeEffectIdentityAuthorityClaim
  ∷ []

canonicalBioactiveRecognitionSpineNonClaims :
  List Spine.NonClaimBoundary
canonicalBioactiveRecognitionSpineNonClaims =
  Spine.quotientIsNotInjective
  ∷ Spine.correlationIsNotCausation
  ∷ Spine.localReceiptIsNotGlobalOntology
  ∷ []

------------------------------------------------------------------------
-- Bounded candidate surface.

record BioactiveMolecularRecognitionSurface : Set₁ where
  field
    MoleculeCandidate : Set
    EndogenousLigandCandidate : Set
    EndogenousSubstrateCandidate : Set
    TargetContext : Set
    SimilarityCarrier : Set
    BindingCandidate : Set
    AffinityCandidate : Set
    SelectivityCandidate : Set
    OccupancyCandidate : Set
    ActionCandidate : Set
    KineticCarrier : Set
    PathwayModulationCandidate : Set
    ClinicalResidual : Set
    BehaviorResidual : Set
    ObservationTrace : Set
    Receipt : Set
    ProvenanceNode : Set
    ObserverProtocol : Set
    BoundedBioactiveMeaning : Set

    observeRecognition :
      MoleculeCandidate ->
      EndogenousLigandCandidate ->
      EndogenousSubstrateCandidate ->
      TargetContext ->
      ObservationTrace

    observedTargetContexts :
      ObservationTrace -> List BioactiveRecognitionTargetContext

    observedSimilarityCarriers :
      ObservationTrace -> List BioactiveSimilarityCarrier

    observedActions :
      ObservationTrace -> List BioactiveRecognitionAction

    observedKineticCarriers :
      ObservationTrace -> List BioactiveKineticCarrier

    observedPathwayModulations :
      ObservationTrace -> List BioactivePathwayModulation

    moleculeCandidateFromTrace :
      ObservationTrace -> MoleculeCandidate

    endogenousLigandCandidateFromTrace :
      ObservationTrace -> EndogenousLigandCandidate

    endogenousSubstrateCandidateFromTrace :
      ObservationTrace -> EndogenousSubstrateCandidate

    targetContextCandidateFromTrace :
      ObservationTrace -> TargetContext

    similarityCarrierCandidateFromTrace :
      ObservationTrace -> SimilarityCarrier

    bindingCandidateFromTrace :
      ObservationTrace -> BindingCandidate

    affinityCandidateFromTrace :
      ObservationTrace -> AffinityCandidate

    selectivityCandidateFromTrace :
      ObservationTrace -> SelectivityCandidate

    occupancyCandidateFromTrace :
      ObservationTrace -> OccupancyCandidate

    actionCandidateFromTrace :
      ObservationTrace -> ActionCandidate

    kineticCarrierCandidateFromTrace :
      ObservationTrace -> KineticCarrier

    pathwayModulationCandidateFromTrace :
      ObservationTrace -> PathwayModulationCandidate

    clinicalResidualFromTrace :
      ObservationTrace -> ClinicalResidual

    behaviorResidualFromTrace :
      ObservationTrace -> BehaviorResidual

    admissibilityReceipt :
      ObservationTrace -> Receipt

    provenanceTrail :
      Receipt -> List ProvenanceNode

    observerProtocol :
      Receipt -> ObserverProtocol

    promoteBoundedBioactiveMeaning :
      ObservationTrace -> Receipt -> BoundedBioactiveMeaning

    observationGate :
      ObservationTrace -> Receipt -> Set

    provenanceGate :
      Receipt -> Set

    nonPromotionGuards :
      List BioactiveRecognitionGuard

    surfaceReading :
      String

open BioactiveMolecularRecognitionSurface public

record BioactiveMolecularRecognitionObservation
    (surface : BioactiveMolecularRecognitionSurface) : Set where
  field
    moleculeCandidate :
      MoleculeCandidate surface

    endogenousLigandCandidate :
      EndogenousLigandCandidate surface

    endogenousSubstrateCandidate :
      EndogenousSubstrateCandidate surface

    targetContext :
      TargetContext surface

    trace :
      ObservationTrace surface

    traceIsObserved :
      trace ≡
        observeRecognition
          surface
          moleculeCandidate
          endogenousLigandCandidate
          endogenousSubstrateCandidate
          targetContext

    targetContexts :
      List BioactiveRecognitionTargetContext

    targetContextsMatch :
      targetContexts ≡ observedTargetContexts surface trace

    similarityCarriers :
      List BioactiveSimilarityCarrier

    similarityCarriersMatch :
      similarityCarriers ≡ observedSimilarityCarriers surface trace

    actions :
      List BioactiveRecognitionAction

    actionsMatch :
      actions ≡ observedActions surface trace

    kineticCarriers :
      List BioactiveKineticCarrier

    kineticCarriersMatch :
      kineticCarriers ≡ observedKineticCarriers surface trace

    pathwayModulations :
      List BioactivePathwayModulation

    pathwayModulationsMatch :
      pathwayModulations ≡ observedPathwayModulations surface trace

open BioactiveMolecularRecognitionObservation public

record CandidateBioactiveMolecularRecognitionState
    (surface : BioactiveMolecularRecognitionSurface)
    (observation : BioactiveMolecularRecognitionObservation surface) : Set where
  field
    similarityCarrier :
      SimilarityCarrier surface

    bindingCandidate :
      BindingCandidate surface

    affinityCandidate :
      AffinityCandidate surface

    selectivityCandidate :
      SelectivityCandidate surface

    occupancyCandidate :
      OccupancyCandidate surface

    actionCandidate :
      ActionCandidate surface

    kineticCarrier :
      KineticCarrier surface

    pathwayModulationCandidate :
      PathwayModulationCandidate surface

    clinicalResidual :
      ClinicalResidual surface

    behaviorResidual :
      BehaviorResidual surface

    similarityCarrierMatches :
      similarityCarrier ≡ similarityCarrierCandidateFromTrace
        surface
        (trace observation)

    bindingCandidateMatches :
      bindingCandidate ≡ bindingCandidateFromTrace
        surface
        (trace observation)

    affinityCandidateMatches :
      affinityCandidate ≡ affinityCandidateFromTrace
        surface
        (trace observation)

    selectivityCandidateMatches :
      selectivityCandidate ≡ selectivityCandidateFromTrace
        surface
        (trace observation)

    occupancyCandidateMatches :
      occupancyCandidate ≡ occupancyCandidateFromTrace
        surface
        (trace observation)

    actionCandidateMatches :
      actionCandidate ≡ actionCandidateFromTrace
        surface
        (trace observation)

    kineticCarrierMatches :
      kineticCarrier ≡ kineticCarrierCandidateFromTrace
        surface
        (trace observation)

    pathwayModulationCandidateMatches :
      pathwayModulationCandidate ≡ pathwayModulationCandidateFromTrace
        surface
        (trace observation)

    clinicalResidualMatches :
      clinicalResidual ≡ clinicalResidualFromTrace
        surface
        (trace observation)

    behaviorResidualMatches :
      behaviorResidual ≡ behaviorResidualFromTrace
        surface
        (trace observation)

open CandidateBioactiveMolecularRecognitionState public

record BioactiveMolecularRecognitionReceipt
    (surface : BioactiveMolecularRecognitionSurface)
    (observation : BioactiveMolecularRecognitionObservation surface)
    (candidate : CandidateBioactiveMolecularRecognitionState surface observation) : Set where
  field
    receipt :
      Receipt surface

    receiptMatchesObservation :
      receipt ≡ admissibilityReceipt surface (trace observation)

    observationGateHeld :
      observationGate surface (trace observation) receipt

    provenanceGateHeld :
      provenanceGate surface receipt

    trail :
      List (ProvenanceNode surface)

    trailMatches :
      trail ≡ provenanceTrail surface receipt

    route :
      BioactiveRecognitionRoute

    routeIsBounded :
      route ≡ boundedRecognitionReceiptRoute

    routeAdmissible :
      AdmissibleBioactiveRecognitionRoute route

open BioactiveMolecularRecognitionReceipt public

------------------------------------------------------------------------
-- Whole bridge.

record BioactiveMolecularRecognitionBridge : Set₁ where
  field
    spineSurface :
      Spine.ObservationTransportSurface

    spineDomainIsRecognitionDomain :
      Spine.ObservationTransportSurface.domain spineSurface
      ≡
      Spine.proteinHormoneChemistryCellDomain

    spineNonClaims :
      List Spine.NonClaimBoundary

    spineNonClaimsAreCanonical :
      spineNonClaims ≡ canonicalBioactiveRecognitionSpineNonClaims

    candidateOnlyCoreRow :
      CandidateOnly.CandidateOnlyRow

    candidateOnlyCoreRowIsCanonical :
      candidateOnlyCoreRow ≡ CandidateOnly.canonicalBridgeCandidateOnlyRow

    candidateOnlyCoreReceipt :
      CandidateOnly.CandidateOnlyReceipt candidateOnlyCoreRow

    candidateOnlyCoreReceiptCandidateOnlyTrue :
      CandidateOnly.candidateOnly candidateOnlyCoreRow ≡ true

    candidateOnlyCoreReceiptPromotedFalse :
      CandidateOnly.promoted candidateOnlyCoreRow ≡ false

    candidateOnlyCoreReceiptNoTruthAuthority :
      CandidateOnly.carriesTruthAuthority candidateOnlyCoreRow ≡ false

    candidateOnlyCoreReceiptNoSupportAuthority :
      CandidateOnly.carriesSupportAuthority candidateOnlyCoreRow ≡ false

    candidateOnlyCoreReceiptNoAdmissibilityAuthority :
      CandidateOnly.carriesAdmissibilityAuthority candidateOnlyCoreRow ≡ false

    candidateOnlyCoreReceiptNoTradingAuthority :
      CandidateOnly.carriesTradingAuthority candidateOnlyCoreRow ≡ false

    candidateOnlyCoreReceiptNoRuntimeAuthority :
      CandidateOnly.carriesRuntimeAuthority candidateOnlyCoreRow ≡ false

    candidateOnlyCoreReceiptNoTheoremAuthority :
      CandidateOnly.carriesTheoremAuthority candidateOnlyCoreRow ≡ false

    bioactiveSurface :
      BioactiveMolecularRecognitionSurface

    observation :
      BioactiveMolecularRecognitionObservation bioactiveSurface

    candidate :
      CandidateBioactiveMolecularRecognitionState
        bioactiveSurface
        observation

    receipt :
      BioactiveMolecularRecognitionReceipt
        bioactiveSurface
        observation
        candidate

    targetContexts :
      List BioactiveRecognitionTargetContext

    targetContextsAreCanonical :
      targetContexts ≡ canonicalBioactiveRecognitionTargetContexts

    similarityCarriers :
      List BioactiveSimilarityCarrier

    similarityCarriersAreCanonical :
      similarityCarriers ≡ canonicalBioactiveSimilarityCarriers

    actions :
      List BioactiveRecognitionAction

    actionsAreCanonical :
      actions ≡ canonicalBioactiveRecognitionActions

    kineticCarriers :
      List BioactiveKineticCarrier

    kineticCarriersAreCanonical :
      kineticCarriers ≡ canonicalBioactiveKineticCarriers

    pathwayModulations :
      List BioactivePathwayModulation

    pathwayModulationsAreCanonical :
      pathwayModulations ≡ canonicalBioactivePathwayModulations

    residualKinds :
      List BioactiveRecognitionResidualKind

    residualKindsAreCanonical :
      residualKinds ≡ canonicalBioactiveRecognitionResidualKinds

    guards :
      List BioactiveRecognitionGuard

    guardsAreCanonical :
      guards ≡ canonicalBioactiveRecognitionGuards

    authorityClaims :
      List BioactiveRecognitionAuthorityClaim

    authorityClaimsAreCanonical :
      authorityClaims ≡ canonicalBioactiveRecognitionAuthorityClaims

    bioactiveAuthorityBoundaryCore :
      BoundaryCore.BioactiveAuthorityBoundaryCore

    bioactiveAuthorityBoundaryCoreIsCanonical :
      bioactiveAuthorityBoundaryCore
      ≡
      BoundaryCore.canonicalBioactiveAuthorityBoundaryCore

    blockedClaims :
      List BoundaryCore.BioactiveBlockedClaim

    blockedClaimsAreCanonical :
      blockedClaims ≡ BoundaryCore.canonicalBioactiveBlockedClaims

    clinicalAuthorityClaimFlag :
      Bool

    clinicalAuthorityClaimFlagIsFalse :
      clinicalAuthorityClaimFlag ≡ false

    doseResponseAuthorityClaimFlag :
      Bool

    doseResponseAuthorityClaimFlagIsFalse :
      doseResponseAuthorityClaimFlag ≡ false

    prescribingAuthorityClaimFlag :
      Bool

    prescribingAuthorityClaimFlagIsFalse :
      prescribingAuthorityClaimFlag ≡ false

    diseaseAuthorityClaimFlag :
      Bool

    diseaseAuthorityClaimFlagIsFalse :
      diseaseAuthorityClaimFlag ≡ false

    behaviorAuthorityClaimFlag :
      Bool

    behaviorAuthorityClaimFlagIsFalse :
      behaviorAuthorityClaimFlag ≡ false

    biomarkerAuthorityClaimFlag :
      Bool

    biomarkerAuthorityClaimFlagIsFalse :
      biomarkerAuthorityClaimFlag ≡ false

    receptorActionIdentityAuthorityClaimFlag :
      Bool

    receptorActionIdentityAuthorityClaimFlagIsFalse :
      receptorActionIdentityAuthorityClaimFlag ≡ false

    shapeEffectIdentityAuthorityClaimFlag :
      Bool

    shapeEffectIdentityAuthorityClaimFlagIsFalse :
      shapeEffectIdentityAuthorityClaimFlag ≡ false

    bridgeReading :
      String

open BioactiveMolecularRecognitionBridge public

------------------------------------------------------------------------
-- Canonical toy inhabitant.

canonicalBioactiveMolecularRecognitionSurface :
  BioactiveMolecularRecognitionSurface
canonicalBioactiveMolecularRecognitionSurface =
  record
    { MoleculeCandidate = ⊤
    ; EndogenousLigandCandidate = ⊤
    ; EndogenousSubstrateCandidate = ⊤
    ; TargetContext = ⊤
    ; SimilarityCarrier = ⊤
    ; BindingCandidate = ⊤
    ; AffinityCandidate = ⊤
    ; SelectivityCandidate = ⊤
    ; OccupancyCandidate = ⊤
    ; ActionCandidate = ⊤
    ; KineticCarrier = ⊤
    ; PathwayModulationCandidate = ⊤
    ; ClinicalResidual = ⊤
    ; BehaviorResidual = ⊤
    ; ObservationTrace = ⊤
    ; Receipt = ⊤
    ; ProvenanceNode = ⊤
    ; ObserverProtocol = ⊤
    ; BoundedBioactiveMeaning = ⊤
    ; observeRecognition = λ _ _ _ _ -> tt
    ; observedTargetContexts =
        λ _ ->
          receptorTargetContext
          ∷ transporterTargetContext
          ∷ enzymeTargetContext
          ∷ channelTargetContext
          ∷ allostericSiteTargetContext
          ∷ []
    ; observedSimilarityCarriers =
        λ _ ->
          scaffoldCarrier
          ∷ pharmacophoreCarrier
          ∷ chargeCarrier
          ∷ geometryCarrier
          ∷ conformationCarrier
          ∷ lipophilicityCarrier
          ∷ []
    ; observedActions =
        λ _ ->
          agonistAction
          ∷ partialAgonistAction
          ∷ antagonistAction
          ∷ inverseAgonistAction
          ∷ allostericModulatorAction
          ∷ competitiveInhibitorAction
          ∷ irreversibleInhibitorAction
          ∷ transporterReuptakeInhibitorAction
          ∷ enzymeSubstrateAction
          ∷ []
    ; observedKineticCarriers =
        λ _ ->
          associationRateCarrier
          ∷ dissociationRateCarrier
          ∷ residenceTimeCarrier
          ∷ turnoverCarrier
          ∷ translocationCarrier
          ∷ permeabilityCarrier
          ∷ []
    ; observedPathwayModulations =
        λ _ ->
          pathwayActivationCandidate
          ∷ pathwayInhibitionCandidate
          ∷ pathwayBiasCandidate
          ∷ pathwayTransportRedirectionCandidate
          ∷ pathwayCatalyticRoutingCandidate
          ∷ []
    ; moleculeCandidateFromTrace = λ _ -> tt
    ; endogenousLigandCandidateFromTrace = λ _ -> tt
    ; endogenousSubstrateCandidateFromTrace = λ _ -> tt
    ; targetContextCandidateFromTrace = λ _ -> tt
    ; similarityCarrierCandidateFromTrace = λ _ -> tt
    ; bindingCandidateFromTrace = λ _ -> tt
    ; affinityCandidateFromTrace = λ _ -> tt
    ; selectivityCandidateFromTrace = λ _ -> tt
    ; occupancyCandidateFromTrace = λ _ -> tt
    ; actionCandidateFromTrace = λ _ -> tt
    ; kineticCarrierCandidateFromTrace = λ _ -> tt
    ; pathwayModulationCandidateFromTrace = λ _ -> tt
    ; clinicalResidualFromTrace = λ _ -> tt
    ; behaviorResidualFromTrace = λ _ -> tt
    ; admissibilityReceipt = λ _ -> tt
    ; provenanceTrail = λ _ -> tt ∷ []
    ; observerProtocol = λ _ -> tt
    ; promoteBoundedBioactiveMeaning = λ _ _ -> tt
    ; observationGate = λ _ _ -> ⊤
    ; provenanceGate = λ _ -> ⊤
    ; nonPromotionGuards = canonicalBioactiveRecognitionGuards
    ; surfaceReading =
        "Bioactive molecular recognition is recorded as a candidate-only receipt over ligand, receptor, enzyme, transporter, channel, and allosteric-site naming, with clinical and identity authorities blocked."
    }

canonicalBioactiveMolecularRecognitionObservation :
  BioactiveMolecularRecognitionObservation
    canonicalBioactiveMolecularRecognitionSurface
canonicalBioactiveMolecularRecognitionObservation =
  record
    { moleculeCandidate = tt
    ; endogenousLigandCandidate = tt
    ; endogenousSubstrateCandidate = tt
    ; targetContext = tt
    ; trace = tt
    ; traceIsObserved = refl
    ; targetContexts =
        receptorTargetContext
        ∷ transporterTargetContext
        ∷ enzymeTargetContext
        ∷ channelTargetContext
        ∷ allostericSiteTargetContext
        ∷ []
    ; targetContextsMatch = refl
    ; similarityCarriers =
        scaffoldCarrier
        ∷ pharmacophoreCarrier
        ∷ chargeCarrier
        ∷ geometryCarrier
        ∷ conformationCarrier
        ∷ lipophilicityCarrier
        ∷ []
    ; similarityCarriersMatch = refl
    ; actions =
        agonistAction
        ∷ partialAgonistAction
        ∷ antagonistAction
        ∷ inverseAgonistAction
        ∷ allostericModulatorAction
        ∷ competitiveInhibitorAction
        ∷ irreversibleInhibitorAction
        ∷ transporterReuptakeInhibitorAction
        ∷ enzymeSubstrateAction
        ∷ []
    ; actionsMatch = refl
    ; kineticCarriers =
        associationRateCarrier
        ∷ dissociationRateCarrier
        ∷ residenceTimeCarrier
        ∷ turnoverCarrier
        ∷ translocationCarrier
        ∷ permeabilityCarrier
        ∷ []
    ; kineticCarriersMatch = refl
    ; pathwayModulations =
        pathwayActivationCandidate
        ∷ pathwayInhibitionCandidate
        ∷ pathwayBiasCandidate
        ∷ pathwayTransportRedirectionCandidate
        ∷ pathwayCatalyticRoutingCandidate
        ∷ []
    ; pathwayModulationsMatch = refl
    }

canonicalCandidateBioactiveMolecularRecognitionState :
  CandidateBioactiveMolecularRecognitionState
    canonicalBioactiveMolecularRecognitionSurface
    canonicalBioactiveMolecularRecognitionObservation
canonicalCandidateBioactiveMolecularRecognitionState =
  record
    { similarityCarrier = tt
    ; bindingCandidate = tt
    ; affinityCandidate = tt
    ; selectivityCandidate = tt
    ; occupancyCandidate = tt
    ; actionCandidate = tt
    ; kineticCarrier = tt
    ; pathwayModulationCandidate = tt
    ; clinicalResidual = tt
    ; behaviorResidual = tt
    ; similarityCarrierMatches = refl
    ; bindingCandidateMatches = refl
    ; affinityCandidateMatches = refl
    ; selectivityCandidateMatches = refl
    ; occupancyCandidateMatches = refl
    ; actionCandidateMatches = refl
    ; kineticCarrierMatches = refl
    ; pathwayModulationCandidateMatches = refl
    ; clinicalResidualMatches = refl
    ; behaviorResidualMatches = refl
    }

canonicalBioactiveMolecularRecognitionReceipt :
  BioactiveMolecularRecognitionReceipt
    canonicalBioactiveMolecularRecognitionSurface
    canonicalBioactiveMolecularRecognitionObservation
    canonicalCandidateBioactiveMolecularRecognitionState
canonicalBioactiveMolecularRecognitionReceipt =
  record
    { receipt = tt
    ; receiptMatchesObservation = refl
    ; observationGateHeld = tt
    ; provenanceGateHeld = tt
    ; trail = tt ∷ []
    ; trailMatches = refl
    ; route = boundedRecognitionReceiptRoute
    ; routeIsBounded = refl
    ; routeAdmissible = tt
    }

canonicalBioactiveMolecularRecognitionBridge :
  BioactiveMolecularRecognitionBridge
canonicalBioactiveMolecularRecognitionBridge =
  record
    { spineSurface =
        record
          { domain = Spine.proteinHormoneChemistryCellDomain
          ; LatentCarrier = ⊤
          ; ObservationQuotient = ⊤
          ; AdmissibilityGate = ⊤
          ; TransportOperator = ⊤
          ; Artifact = ⊤
          ; observe = λ _ -> tt
          ; gate = λ _ -> tt
          ; transport = λ _ _ _ -> tt
          ; promotionBoundary = Spine.candidateSurfaceOnly
          ; nonClaims = canonicalBioactiveRecognitionSpineNonClaims
          ; plainReading =
              "Protein-hormone chemistry spine anchored to candidate surface only."
          }
    ; spineDomainIsRecognitionDomain = refl
    ; spineNonClaims = canonicalBioactiveRecognitionSpineNonClaims
    ; spineNonClaimsAreCanonical = refl
    ; candidateOnlyCoreRow = CandidateOnly.canonicalBridgeCandidateOnlyRow
    ; candidateOnlyCoreRowIsCanonical = refl
    ; candidateOnlyCoreReceipt = CandidateOnly.canonicalBridgeCandidateOnlyReceipt
    ; candidateOnlyCoreReceiptCandidateOnlyTrue = refl
    ; candidateOnlyCoreReceiptPromotedFalse = refl
    ; candidateOnlyCoreReceiptNoTruthAuthority = refl
    ; candidateOnlyCoreReceiptNoSupportAuthority = refl
    ; candidateOnlyCoreReceiptNoAdmissibilityAuthority = refl
    ; candidateOnlyCoreReceiptNoTradingAuthority = refl
    ; candidateOnlyCoreReceiptNoRuntimeAuthority = refl
    ; candidateOnlyCoreReceiptNoTheoremAuthority = refl
    ; bioactiveSurface = canonicalBioactiveMolecularRecognitionSurface
    ; observation = canonicalBioactiveMolecularRecognitionObservation
    ; candidate = canonicalCandidateBioactiveMolecularRecognitionState
    ; receipt = canonicalBioactiveMolecularRecognitionReceipt
    ; targetContexts = canonicalBioactiveRecognitionTargetContexts
    ; targetContextsAreCanonical = refl
    ; similarityCarriers = canonicalBioactiveSimilarityCarriers
    ; similarityCarriersAreCanonical = refl
    ; actions = canonicalBioactiveRecognitionActions
    ; actionsAreCanonical = refl
    ; kineticCarriers = canonicalBioactiveKineticCarriers
    ; kineticCarriersAreCanonical = refl
    ; pathwayModulations = canonicalBioactivePathwayModulations
    ; pathwayModulationsAreCanonical = refl
    ; residualKinds = canonicalBioactiveRecognitionResidualKinds
    ; residualKindsAreCanonical = refl
    ; guards = canonicalBioactiveRecognitionGuards
    ; guardsAreCanonical = refl
    ; authorityClaims = canonicalBioactiveRecognitionAuthorityClaims
    ; authorityClaimsAreCanonical = refl
    ; bioactiveAuthorityBoundaryCore =
        BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; bioactiveAuthorityBoundaryCoreIsCanonical = refl
    ; blockedClaims = BoundaryCore.canonicalBioactiveBlockedClaims
    ; blockedClaimsAreCanonical = refl
    ; clinicalAuthorityClaimFlag =
        BoundaryCore.clinicalAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; clinicalAuthorityClaimFlagIsFalse =
        BoundaryCore.clinicalAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; doseResponseAuthorityClaimFlag =
        BoundaryCore.doseResponseAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; doseResponseAuthorityClaimFlagIsFalse =
        BoundaryCore.doseResponseAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; prescribingAuthorityClaimFlag =
        BoundaryCore.prescribingAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; prescribingAuthorityClaimFlagIsFalse =
        BoundaryCore.prescribingAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; diseaseAuthorityClaimFlag =
        BoundaryCore.diseaseAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; diseaseAuthorityClaimFlagIsFalse =
        BoundaryCore.diseaseAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; behaviorAuthorityClaimFlag =
        BoundaryCore.behaviorAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; behaviorAuthorityClaimFlagIsFalse =
        BoundaryCore.behaviorAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; biomarkerAuthorityClaimFlag =
        BoundaryCore.biomarkerAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; biomarkerAuthorityClaimFlagIsFalse =
        BoundaryCore.biomarkerAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; receptorActionIdentityAuthorityClaimFlag =
        BoundaryCore.receptorActionIdentityAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; receptorActionIdentityAuthorityClaimFlagIsFalse =
        BoundaryCore.receptorActionIdentityAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; shapeEffectIdentityAuthorityClaimFlag =
        BoundaryCore.shapeEffectIdentityAuthorityClaimFlag
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; shapeEffectIdentityAuthorityClaimFlagIsFalse =
        BoundaryCore.shapeEffectIdentityAuthorityClaimFlagIsFalse
          BoundaryCore.canonicalBioactiveAuthorityBoundaryCore
    ; bridgeReading =
        "Candidate-only bioactive recognition bridge: ligand, receptor, enzyme, transporter, channel, and allosteric-site naming is tracked as a receipt-bound observation surface, while clinical, dose-response, prescribing, disease, behavior, biomarker, receptor-action identity, and shape-effect identity authority remain blocked."
    }
