module DASHI.Biology.CellDifferentiationCommunicationBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Empty type for explicitly rejected promotion routes.
------------------------------------------------------------------------

data Never : Set where

------------------------------------------------------------------------
-- Physiology vocabulary.
------------------------------------------------------------------------

data PhysiologyDomain : Set where
  cellDifferentiation : PhysiologyDomain
  cellCommunication : PhysiologyDomain
  metabolism : PhysiologyDomain
  circulation : PhysiologyDomain
  endocrine : PhysiologyDomain
  immune : PhysiologyDomain

data ObservationChannel : Set where
  lineageTrace : ObservationChannel
  receptorLigandTrace : ObservationChannel
  metaboliteFluxTrace : ObservationChannel
  vascularFlowTrace : ObservationChannel
  hormoneTrace : ObservationChannel
  cytokineTrace : ObservationChannel
  tissueContextTrace : ObservationChannel

data CandidatePhysiologyAspect : Set where
  differentiationStateCandidate : CandidatePhysiologyAspect
  communicationStateCandidate : CandidatePhysiologyAspect
  metabolicStateCandidate : CandidatePhysiologyAspect
  perfusionStateCandidate : CandidatePhysiologyAspect
  endocrineStateCandidate : CandidatePhysiologyAspect
  immuneStateCandidate : CandidatePhysiologyAspect
  tissueCoordinationCandidate : CandidatePhysiologyAspect

data NonPromotionGuard : Set where
  NoDiseaseCausationClaim : NonPromotionGuard
  NoFullDevelopmentRecovery : NonPromotionGuard
  NoCellFatePredictionClaim : NonPromotionGuard
  NoBiologyClosureClaim : NonPromotionGuard

data PromotionRoute : Set where
  boundedObservationReceiptRoute : PromotionRoute
  diseaseCausationRoute : PromotionRoute
  fullDevelopmentRecoveryRoute : PromotionRoute
  cellFatePredictionRoute : PromotionRoute
  biologyClosureRoute : PromotionRoute

AdmissibleRoute : PromotionRoute -> Set
AdmissibleRoute boundedObservationReceiptRoute = ⊤
AdmissibleRoute diseaseCausationRoute = Never
AdmissibleRoute fullDevelopmentRecoveryRoute = Never
AdmissibleRoute cellFatePredictionRoute = Never
AdmissibleRoute biologyClosureRoute = Never

diseaseCausationRejected :
  AdmissibleRoute diseaseCausationRoute -> Never
diseaseCausationRejected impossible = impossible

fullDevelopmentRecoveryRejected :
  AdmissibleRoute fullDevelopmentRecoveryRoute -> Never
fullDevelopmentRecoveryRejected impossible = impossible

cellFatePredictionRejected :
  AdmissibleRoute cellFatePredictionRoute -> Never
cellFatePredictionRejected impossible = impossible

biologyClosureRejected :
  AdmissibleRoute biologyClosureRoute -> Never
biologyClosureRejected impossible = impossible

------------------------------------------------------------------------
-- Bounded physiology surface.
------------------------------------------------------------------------

record CellDifferentiationCommunicationBridge : Set₁ where
  field
    Organism : Set
    Tissue : Set
    CellPopulation : Set
    CellLineage : Set
    CommunicationSignal : Set
    MetabolicFlux : Set
    CirculatoryFlow : Set
    EndocrineSignal : Set
    ImmuneSignal : Set
    ObservationTrace : Set
    CandidatePhysiologyState : Set
    BoundedPhysiologyMeaning : Set
    Receipt : Set
    ProvenanceNode : Set
    ObserverProtocol : Set

    observePhysiology :
      Organism -> Tissue -> CellPopulation -> ObservationTrace

    observedDomains :
      ObservationTrace -> List PhysiologyDomain

    observedChannels :
      ObservationTrace -> List ObservationChannel

    lineageCandidate :
      ObservationTrace -> CellLineage

    communicationCandidate :
      ObservationTrace -> CommunicationSignal

    metabolismCandidate :
      ObservationTrace -> MetabolicFlux

    circulationCandidate :
      ObservationTrace -> CirculatoryFlow

    endocrineCandidate :
      ObservationTrace -> EndocrineSignal

    immuneCandidate :
      ObservationTrace -> ImmuneSignal

    integrateCandidateState :
      ObservationTrace ->
      CellLineage ->
      CommunicationSignal ->
      MetabolicFlux ->
      CirculatoryFlow ->
      EndocrineSignal ->
      ImmuneSignal ->
      CandidatePhysiologyState

    candidateAspects :
      CandidatePhysiologyState -> List CandidatePhysiologyAspect

    admissibilityReceipt :
      ObservationTrace -> CandidatePhysiologyState -> Receipt

    provenanceTrail :
      Receipt -> List ProvenanceNode

    observerProtocol :
      Receipt -> ObserverProtocol

    promoteBoundedMeaning :
      ObservationTrace ->
      CandidatePhysiologyState ->
      Receipt ->
      BoundedPhysiologyMeaning

    observationGate :
      ObservationTrace -> CandidatePhysiologyState -> Receipt -> Set

    provenanceGate :
      Receipt -> Set

    nonPromotionGuards :
      List NonPromotionGuard

    surfaceReading :
      String

open CellDifferentiationCommunicationBridge public

record PhysiologyObservation
    (bridge : CellDifferentiationCommunicationBridge) : Set where
  field
    organism : Organism bridge
    tissue : Tissue bridge
    cellPopulation : CellPopulation bridge
    trace : ObservationTrace bridge
    traceIsObserved :
      trace ≡ observePhysiology bridge organism tissue cellPopulation
    domains :
      List PhysiologyDomain
    domainsMatch :
      domains ≡ observedDomains bridge trace
    channels :
      List ObservationChannel
    channelsMatch :
      channels ≡ observedChannels bridge trace

open PhysiologyObservation public

record CandidateIntegratedPhysiologyState
    (bridge : CellDifferentiationCommunicationBridge)
    (observation : PhysiologyObservation bridge) : Set where
  field
    lineage : CellLineage bridge
    communication : CommunicationSignal bridge
    metabolicFlux : MetabolicFlux bridge
    flow : CirculatoryFlow bridge
    endocrineSignal : EndocrineSignal bridge
    immuneSignal : ImmuneSignal bridge
    candidateState : CandidatePhysiologyState bridge
    lineageMatches :
      lineage ≡ lineageCandidate bridge (trace observation)
    communicationMatches :
      communication ≡ communicationCandidate bridge (trace observation)
    metabolismMatches :
      metabolicFlux ≡ metabolismCandidate bridge (trace observation)
    circulationMatches :
      flow ≡ circulationCandidate bridge (trace observation)
    endocrineMatches :
      endocrineSignal ≡ endocrineCandidate bridge (trace observation)
    immuneMatches :
      immuneSignal ≡ immuneCandidate bridge (trace observation)
    candidateStateMatches :
      candidateState ≡
        integrateCandidateState
          bridge
          (trace observation)
          lineage
          communication
          metabolicFlux
          flow
          endocrineSignal
          immuneSignal
    aspectEvidence :
      List CandidatePhysiologyAspect

open CandidateIntegratedPhysiologyState public

record PhysiologyPromotionReceipt
    (bridge : CellDifferentiationCommunicationBridge)
    (observation : PhysiologyObservation bridge)
    (candidate : CandidateIntegratedPhysiologyState bridge observation) : Set where
  field
    receipt :
      Receipt bridge
    receiptMatchesCandidate :
      receipt ≡
        admissibilityReceipt
          bridge
          (trace observation)
          (candidateState candidate)
    observationGateHeld :
      observationGate
        bridge
        (trace observation)
        (candidateState candidate)
        receipt
    provenanceGateHeld :
      provenanceGate bridge receipt
    trail :
      List (ProvenanceNode bridge)
    trailMatches :
      trail ≡ provenanceTrail bridge receipt
    route :
      PromotionRoute
    routeIsBounded :
      route ≡ boundedObservationReceiptRoute
    routeAdmissible :
      AdmissibleRoute route

open PhysiologyPromotionReceipt public

record PromotedBoundedPhysiologyMeaning
    (bridge : CellDifferentiationCommunicationBridge)
    (observation : PhysiologyObservation bridge)
    (candidate : CandidateIntegratedPhysiologyState bridge observation)
    (receipt : PhysiologyPromotionReceipt bridge observation candidate) : Set where
  field
    meaning :
      BoundedPhysiologyMeaning bridge
    meaningMatchesPromotion :
      meaning ≡
        promoteBoundedMeaning
          bridge
          (trace observation)
          (candidateState candidate)
          (PhysiologyPromotionReceipt.receipt receipt)
    boundedObservationOnly :
      Bool
    boundedObservationOnlyIsTrue :
      boundedObservationOnly ≡ true
    diseaseCausationClaim :
      Bool
    diseaseCausationClaimIsFalse :
      diseaseCausationClaim ≡ false
    fullDevelopmentRecovered :
      Bool
    fullDevelopmentRecoveredIsFalse :
      fullDevelopmentRecovered ≡ false
    cellFatePredicted :
      Bool
    cellFatePredictedIsFalse :
      cellFatePredicted ≡ false
    biologyClosureClaim :
      Bool
    biologyClosureClaimIsFalse :
      biologyClosureClaim ≡ false

open PromotedBoundedPhysiologyMeaning public

record NonPromotionGuardCertificate
    (bridge : CellDifferentiationCommunicationBridge) : Set where
  field
    guards :
      List NonPromotionGuard
    guardsMatch :
      guards ≡ nonPromotionGuards bridge
    noDiseaseCausation :
      Bool
    noDiseaseCausationIsTrue :
      noDiseaseCausation ≡ true
    noFullDevelopmentRecovery :
      Bool
    noFullDevelopmentRecoveryIsTrue :
      noFullDevelopmentRecovery ≡ true
    noCellFatePrediction :
      Bool
    noCellFatePredictionIsTrue :
      noCellFatePrediction ≡ true
    noBiologyClosure :
      Bool
    noBiologyClosureIsTrue :
      noBiologyClosure ≡ true
    guardReading :
      String

open NonPromotionGuardCertificate public

promoteWithPhysiologyReceipts :
  (bridge : CellDifferentiationCommunicationBridge) ->
  (observation : PhysiologyObservation bridge) ->
  (candidate : CandidateIntegratedPhysiologyState bridge observation) ->
  (receipt : PhysiologyPromotionReceipt bridge observation candidate) ->
  BoundedPhysiologyMeaning bridge
promoteWithPhysiologyReceipts bridge observation candidate receipt =
  promoteBoundedMeaning
    bridge
    (trace observation)
    (candidateState candidate)
    (PhysiologyPromotionReceipt.receipt receipt)

canonicalPhysiologyRouteAdmissible :
  AdmissibleRoute boundedObservationReceiptRoute
canonicalPhysiologyRouteAdmissible = tt

canonicalNonPromotionGuards : List NonPromotionGuard
canonicalNonPromotionGuards =
  NoDiseaseCausationClaim ∷
  NoFullDevelopmentRecovery ∷
  NoCellFatePredictionClaim ∷
  NoBiologyClosureClaim ∷
  []

------------------------------------------------------------------------
-- Canonical toy inhabitant.

canonicalCellDifferentiationCommunicationBridge :
  CellDifferentiationCommunicationBridge
canonicalCellDifferentiationCommunicationBridge =
  record
    { Organism = ⊤
    ; Tissue = ⊤
    ; CellPopulation = ⊤
    ; CellLineage = ⊤
    ; CommunicationSignal = ⊤
    ; MetabolicFlux = ⊤
    ; CirculatoryFlow = ⊤
    ; EndocrineSignal = ⊤
    ; ImmuneSignal = ⊤
    ; ObservationTrace = ⊤
    ; CandidatePhysiologyState = ⊤
    ; BoundedPhysiologyMeaning = ⊤
    ; Receipt = ⊤
    ; ProvenanceNode = ⊤
    ; ObserverProtocol = ⊤
    ; observePhysiology = λ _ _ _ → tt
    ; observedDomains =
        λ _ →
          cellDifferentiation
          ∷ cellCommunication
          ∷ metabolism
          ∷ circulation
          ∷ endocrine
          ∷ immune
          ∷ []
    ; observedChannels =
        λ _ →
          lineageTrace
          ∷ receptorLigandTrace
          ∷ metaboliteFluxTrace
          ∷ vascularFlowTrace
          ∷ hormoneTrace
          ∷ cytokineTrace
          ∷ tissueContextTrace
          ∷ []
    ; lineageCandidate = λ _ → tt
    ; communicationCandidate = λ _ → tt
    ; metabolismCandidate = λ _ → tt
    ; circulationCandidate = λ _ → tt
    ; endocrineCandidate = λ _ → tt
    ; immuneCandidate = λ _ → tt
    ; integrateCandidateState = λ _ _ _ _ _ _ _ → tt
    ; candidateAspects =
        λ _ →
          differentiationStateCandidate
          ∷ communicationStateCandidate
          ∷ metabolicStateCandidate
          ∷ perfusionStateCandidate
          ∷ endocrineStateCandidate
          ∷ immuneStateCandidate
          ∷ tissueCoordinationCandidate
          ∷ []
    ; admissibilityReceipt = λ _ _ → tt
    ; provenanceTrail = λ _ → tt ∷ []
    ; observerProtocol = λ _ → tt
    ; promoteBoundedMeaning = λ _ _ _ → tt
    ; observationGate = λ _ _ _ → ⊤
    ; provenanceGate = λ _ → ⊤
    ; nonPromotionGuards = canonicalNonPromotionGuards
    ; surfaceReading =
        "Toy cell-communication physiology bridge inhabits the bounded observation route only."
    }

canonicalPhysiologyObservation :
  PhysiologyObservation canonicalCellDifferentiationCommunicationBridge
canonicalPhysiologyObservation =
  record
    { organism = tt
    ; tissue = tt
    ; cellPopulation = tt
    ; trace = tt
    ; traceIsObserved = refl
    ; domains =
        cellDifferentiation
        ∷ cellCommunication
        ∷ metabolism
        ∷ circulation
        ∷ endocrine
        ∷ immune
        ∷ []
    ; domainsMatch = refl
    ; channels =
        lineageTrace
        ∷ receptorLigandTrace
        ∷ metaboliteFluxTrace
        ∷ vascularFlowTrace
        ∷ hormoneTrace
        ∷ cytokineTrace
        ∷ tissueContextTrace
        ∷ []
    ; channelsMatch = refl
    }

canonicalCandidateIntegratedPhysiologyState :
  CandidateIntegratedPhysiologyState
    canonicalCellDifferentiationCommunicationBridge
    canonicalPhysiologyObservation
canonicalCandidateIntegratedPhysiologyState =
  record
    { lineage = tt
    ; communication = tt
    ; metabolicFlux = tt
    ; flow = tt
    ; endocrineSignal = tt
    ; immuneSignal = tt
    ; candidateState = tt
    ; lineageMatches = refl
    ; communicationMatches = refl
    ; metabolismMatches = refl
    ; circulationMatches = refl
    ; endocrineMatches = refl
    ; immuneMatches = refl
    ; candidateStateMatches = refl
    ; aspectEvidence =
        differentiationStateCandidate
        ∷ communicationStateCandidate
        ∷ metabolicStateCandidate
        ∷ perfusionStateCandidate
        ∷ endocrineStateCandidate
        ∷ immuneStateCandidate
        ∷ tissueCoordinationCandidate
        ∷ []
    }

canonicalPhysiologyPromotionReceipt :
  PhysiologyPromotionReceipt
    canonicalCellDifferentiationCommunicationBridge
    canonicalPhysiologyObservation
    canonicalCandidateIntegratedPhysiologyState
canonicalPhysiologyPromotionReceipt =
  record
    { receipt = tt
    ; receiptMatchesCandidate = refl
    ; observationGateHeld = tt
    ; provenanceGateHeld = tt
    ; trail = tt ∷ []
    ; trailMatches = refl
    ; route = boundedObservationReceiptRoute
    ; routeIsBounded = refl
    ; routeAdmissible = tt
    }

canonicalPromotedBoundedPhysiologyMeaning :
  PromotedBoundedPhysiologyMeaning
    canonicalCellDifferentiationCommunicationBridge
    canonicalPhysiologyObservation
    canonicalCandidateIntegratedPhysiologyState
    canonicalPhysiologyPromotionReceipt
canonicalPromotedBoundedPhysiologyMeaning =
  record
    { meaning = tt
    ; meaningMatchesPromotion = refl
    ; boundedObservationOnly = true
    ; boundedObservationOnlyIsTrue = refl
    ; diseaseCausationClaim = false
    ; diseaseCausationClaimIsFalse = refl
    ; fullDevelopmentRecovered = false
    ; fullDevelopmentRecoveredIsFalse = refl
    ; cellFatePredicted = false
    ; cellFatePredictedIsFalse = refl
    ; biologyClosureClaim = false
    ; biologyClosureClaimIsFalse = refl
    }

canonicalNonPromotionGuardCertificate :
  NonPromotionGuardCertificate
    canonicalCellDifferentiationCommunicationBridge
canonicalNonPromotionGuardCertificate =
  record
    { guards = canonicalNonPromotionGuards
    ; guardsMatch = refl
    ; noDiseaseCausation = true
    ; noDiseaseCausationIsTrue = refl
    ; noFullDevelopmentRecovery = true
    ; noFullDevelopmentRecoveryIsTrue = refl
    ; noCellFatePrediction = true
    ; noCellFatePredictionIsTrue = refl
    ; noBiologyClosure = true
    ; noBiologyClosureIsTrue = refl
    ; guardReading =
        "The physiology bridge has toy receipts only and blocks disease, full development, cell-fate, and closure promotion."
    }
