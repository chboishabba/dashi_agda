module DASHI.Biology.EvolutionaryTransportMDLBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Computation.PersistentTransportMotifs as Motifs

------------------------------------------------------------------------
-- Empty type for explicitly rejected promotion routes.
------------------------------------------------------------------------

data Never : Set where

------------------------------------------------------------------------
-- Evolutionary transport vocabulary.
--
-- This is a bounded bridge from physics and chemistry into conserved
-- molecular machinery, cell signalling, and body/behaviour observations.
-- It records an MDL-guided reading of persistent transport motifs only.
--
-- It does not prove biology inevitability, abiogenesis, fitness
-- universality, origin-of-life closure, or molecular simulation closure.

data EvolutionaryTransportScale : Set where
  physicsBoundaryScale : EvolutionaryTransportScale
  chemistryNetworkScale : EvolutionaryTransportScale
  molecularMachineScale : EvolutionaryTransportScale
  cellSignallingScale : EvolutionaryTransportScale
  bodyBehaviourScale : EvolutionaryTransportScale

data EvolutionaryObservationChannel : Set where
  geochemicalBoundaryTrace : EvolutionaryObservationChannel
  reactionNetworkTrace : EvolutionaryObservationChannel
  polymerTemplateTrace : EvolutionaryObservationChannel
  membraneGradientTrace : EvolutionaryObservationChannel
  catalyticCycleTrace : EvolutionaryObservationChannel
  signallingCascadeTrace : EvolutionaryObservationChannel
  sensorimotorBehaviourTrace : EvolutionaryObservationChannel
  comparativeConservationTrace : EvolutionaryObservationChannel

data ConservedMolecularMachinery : Set where
  boundaryCompartmentMachinery : ConservedMolecularMachinery
  polymerTemplateMachinery : ConservedMolecularMachinery
  catalystCycleMachinery : ConservedMolecularMachinery
  ionGradientMachinery : ConservedMolecularMachinery
  ribosomeLikeTranslationMachinery : ConservedMolecularMachinery
  atpSynthaseLikeCouplingMachinery : ConservedMolecularMachinery
  receptorCascadeMachinery : ConservedMolecularMachinery
  cytoskeletalMotorMachinery : ConservedMolecularMachinery

data EvolutionaryTransportAspect : Set where
  gradientCaptureAspect : EvolutionaryTransportAspect
  compartmentPersistenceAspect : EvolutionaryTransportAspect
  templateCopyingAspect : EvolutionaryTransportAspect
  catalyticTurnoverAspect : EvolutionaryTransportAspect
  machineCouplingAspect : EvolutionaryTransportAspect
  signallingRoutingAspect : EvolutionaryTransportAspect
  behaviourLoopAspect : EvolutionaryTransportAspect
  conservationCompressionAspect : EvolutionaryTransportAspect

data NonPromotionGuard : Set where
  NoBiologyInevitabilityTheorem : NonPromotionGuard
  NoExplicitMDLOptimizerClaim : NonPromotionGuard
  NoAbiogenesisProof : NonPromotionGuard
  NoFullMolecularSimulation : NonPromotionGuard
  NoFitnessUniversality : NonPromotionGuard
  NoOriginOfLifeClosure : NonPromotionGuard

data PromotionRoute : Set where
  boundedMDLTransportReceiptRoute : PromotionRoute
  biologyInevitabilityRoute : PromotionRoute
  explicitMDLOptimizerRoute : PromotionRoute
  abiogenesisProofRoute : PromotionRoute
  fullMolecularSimulationRoute : PromotionRoute
  fitnessUniversalityRoute : PromotionRoute
  originOfLifeClosureRoute : PromotionRoute

AdmissibleRoute : PromotionRoute -> Set
AdmissibleRoute boundedMDLTransportReceiptRoute = ⊤
AdmissibleRoute biologyInevitabilityRoute = Never
AdmissibleRoute explicitMDLOptimizerRoute = Never
AdmissibleRoute abiogenesisProofRoute = Never
AdmissibleRoute fullMolecularSimulationRoute = Never
AdmissibleRoute fitnessUniversalityRoute = Never
AdmissibleRoute originOfLifeClosureRoute = Never

biologyInevitabilityRejected :
  AdmissibleRoute biologyInevitabilityRoute -> Never
biologyInevitabilityRejected impossible = impossible

explicitMDLOptimizerRejected :
  AdmissibleRoute explicitMDLOptimizerRoute -> Never
explicitMDLOptimizerRejected impossible = impossible

abiogenesisProofRejected :
  AdmissibleRoute abiogenesisProofRoute -> Never
abiogenesisProofRejected impossible = impossible

fullMolecularSimulationRejected :
  AdmissibleRoute fullMolecularSimulationRoute -> Never
fullMolecularSimulationRejected impossible = impossible

fitnessUniversalityRejected :
  AdmissibleRoute fitnessUniversalityRoute -> Never
fitnessUniversalityRejected impossible = impossible

originOfLifeClosureRejected :
  AdmissibleRoute originOfLifeClosureRoute -> Never
originOfLifeClosureRejected impossible = impossible

canonicalEvolutionaryScales : List EvolutionaryTransportScale
canonicalEvolutionaryScales =
  physicsBoundaryScale
  ∷ chemistryNetworkScale
  ∷ molecularMachineScale
  ∷ cellSignallingScale
  ∷ bodyBehaviourScale
  ∷ []

canonicalEvolutionaryChannels : List EvolutionaryObservationChannel
canonicalEvolutionaryChannels =
  geochemicalBoundaryTrace
  ∷ reactionNetworkTrace
  ∷ polymerTemplateTrace
  ∷ membraneGradientTrace
  ∷ catalyticCycleTrace
  ∷ signallingCascadeTrace
  ∷ sensorimotorBehaviourTrace
  ∷ comparativeConservationTrace
  ∷ []

canonicalConservedMachinery : List ConservedMolecularMachinery
canonicalConservedMachinery =
  boundaryCompartmentMachinery
  ∷ polymerTemplateMachinery
  ∷ catalystCycleMachinery
  ∷ ionGradientMachinery
  ∷ ribosomeLikeTranslationMachinery
  ∷ atpSynthaseLikeCouplingMachinery
  ∷ receptorCascadeMachinery
  ∷ cytoskeletalMotorMachinery
  ∷ []

canonicalEvolutionaryTransportAspects : List EvolutionaryTransportAspect
canonicalEvolutionaryTransportAspects =
  gradientCaptureAspect
  ∷ compartmentPersistenceAspect
  ∷ templateCopyingAspect
  ∷ catalyticTurnoverAspect
  ∷ machineCouplingAspect
  ∷ signallingRoutingAspect
  ∷ behaviourLoopAspect
  ∷ conservationCompressionAspect
  ∷ []

canonicalNonPromotionGuards : List NonPromotionGuard
canonicalNonPromotionGuards =
  NoBiologyInevitabilityTheorem
  ∷ NoExplicitMDLOptimizerClaim
  ∷ NoAbiogenesisProof
  ∷ NoFullMolecularSimulation
  ∷ NoFitnessUniversality
  ∷ NoOriginOfLifeClosure
  ∷ []

------------------------------------------------------------------------
-- Bounded MDL-guided evolutionary transport surface.

record EvolutionaryTransportMDLBridge : Set₁ where
  field
    PhysicsBoundary : Set
    ChemicalNetwork : Set
    MolecularMachine : Set
    CellSignal : Set
    BodyBehaviour : Set
    LineageContext : Set
    ObservationTrace : Set
    CandidateTransportState : Set
    MDLScore : Set
    MDLReceipt : Set
    ProvenanceNode : Set
    BoundedEvolutionaryMeaning : Set

    observeThread :
      PhysicsBoundary ->
      ChemicalNetwork ->
      LineageContext ->
      ObservationTrace

    observedScales :
      ObservationTrace -> List EvolutionaryTransportScale

    observedChannels :
      ObservationTrace -> List EvolutionaryObservationChannel

    physicsCandidate :
      ObservationTrace -> PhysicsBoundary

    chemistryCandidate :
      ObservationTrace -> ChemicalNetwork

    machineCandidate :
      ObservationTrace -> MolecularMachine

    cellSignalCandidate :
      ObservationTrace -> CellSignal

    bodyBehaviourCandidate :
      ObservationTrace -> BodyBehaviour

    conservedMachinery :
      ObservationTrace -> List ConservedMolecularMachinery

    persistentMotifs :
      ObservationTrace -> List Motifs.TransportMotif

    integrateCandidateState :
      ObservationTrace ->
      PhysicsBoundary ->
      ChemicalNetwork ->
      MolecularMachine ->
      CellSignal ->
      BodyBehaviour ->
      CandidateTransportState

    candidateAspects :
      CandidateTransportState -> List EvolutionaryTransportAspect

    mdlGuide :
      ObservationTrace -> CandidateTransportState -> MDLScore

    admissibilityReceipt :
      ObservationTrace -> CandidateTransportState -> MDLScore -> MDLReceipt

    provenanceTrail :
      MDLReceipt -> List ProvenanceNode

    promoteBoundedMeaning :
      ObservationTrace ->
      CandidateTransportState ->
      MDLScore ->
      MDLReceipt ->
      BoundedEvolutionaryMeaning

    observationGate :
      ObservationTrace -> CandidateTransportState -> Set

    mdlReceiptGate :
      ObservationTrace -> CandidateTransportState -> MDLScore -> MDLReceipt -> Set

    provenanceGate :
      MDLReceipt -> Set

    nonPromotionGuards :
      List NonPromotionGuard

    surfaceReading :
      String

open EvolutionaryTransportMDLBridge public

record EvolutionaryTransportObservation
    (bridge : EvolutionaryTransportMDLBridge) : Set where
  field
    physicsBoundary : PhysicsBoundary bridge
    chemicalNetwork : ChemicalNetwork bridge
    lineageContext : LineageContext bridge
    trace : ObservationTrace bridge
    traceIsObserved :
      trace ≡
        observeThread
          bridge
          physicsBoundary
          chemicalNetwork
          lineageContext
    scales :
      List EvolutionaryTransportScale
    scalesMatch :
      scales ≡ observedScales bridge trace
    channels :
      List EvolutionaryObservationChannel
    channelsMatch :
      channels ≡ observedChannels bridge trace

open EvolutionaryTransportObservation public

record CandidateEvolutionaryTransportState
    (bridge : EvolutionaryTransportMDLBridge)
    (observation : EvolutionaryTransportObservation bridge) : Set where
  field
    physics : PhysicsBoundary bridge
    chemistry : ChemicalNetwork bridge
    machine : MolecularMachine bridge
    cellSignal : CellSignal bridge
    bodyBehaviour : BodyBehaviour bridge
    candidateState : CandidateTransportState bridge
    physicsMatches :
      physics ≡ physicsCandidate bridge (trace observation)
    chemistryMatches :
      chemistry ≡ chemistryCandidate bridge (trace observation)
    machineMatches :
      machine ≡ machineCandidate bridge (trace observation)
    cellSignalMatches :
      cellSignal ≡ cellSignalCandidate bridge (trace observation)
    bodyBehaviourMatches :
      bodyBehaviour ≡ bodyBehaviourCandidate bridge (trace observation)
    candidateStateMatches :
      candidateState ≡
        integrateCandidateState
          bridge
          (trace observation)
          physics
          chemistry
          machine
          cellSignal
          bodyBehaviour
    machineryEvidence :
      List ConservedMolecularMachinery
    machineryEvidenceMatches :
      machineryEvidence ≡ conservedMachinery bridge (trace observation)
    motifEvidence :
      List Motifs.TransportMotif
    motifEvidenceMatches :
      motifEvidence ≡ persistentMotifs bridge (trace observation)
    aspectEvidence :
      List EvolutionaryTransportAspect
    aspectEvidenceMatches :
      aspectEvidence ≡ candidateAspects bridge candidateState

open CandidateEvolutionaryTransportState public

record EvolutionaryMDLTransportReceipt
    (bridge : EvolutionaryTransportMDLBridge)
    (observation : EvolutionaryTransportObservation bridge)
    (candidate : CandidateEvolutionaryTransportState bridge observation) : Set where
  field
    mdlScore :
      MDLScore bridge
    mdlScoreMatches :
      mdlScore ≡
        mdlGuide
          bridge
          (trace observation)
          (candidateState candidate)
    receipt :
      MDLReceipt bridge
    receiptMatchesCandidate :
      receipt ≡
        admissibilityReceipt
          bridge
          (trace observation)
          (candidateState candidate)
          mdlScore
    observationGateHeld :
      observationGate
        bridge
        (trace observation)
        (candidateState candidate)
    mdlReceiptGateHeld :
      mdlReceiptGate
        bridge
        (trace observation)
        (candidateState candidate)
        mdlScore
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
      route ≡ boundedMDLTransportReceiptRoute
    routeAdmissible :
      AdmissibleRoute route

open EvolutionaryMDLTransportReceipt public

record PromotedBoundedEvolutionaryMeaning
    (bridge : EvolutionaryTransportMDLBridge)
    (observation : EvolutionaryTransportObservation bridge)
    (candidate : CandidateEvolutionaryTransportState bridge observation)
    (receipt : EvolutionaryMDLTransportReceipt bridge observation candidate) : Set where
  field
    meaning :
      BoundedEvolutionaryMeaning bridge
    meaningMatchesPromotion :
      meaning ≡
        promoteBoundedMeaning
          bridge
          (trace observation)
          (candidateState candidate)
          (mdlScore receipt)
          (EvolutionaryMDLTransportReceipt.receipt receipt)
    boundedMDLTransportOnly :
      Bool
    boundedMDLTransportOnlyIsTrue :
      boundedMDLTransportOnly ≡ true
    biologyInevitabilityTheorem :
      Bool
    biologyInevitabilityTheoremIsFalse :
      biologyInevitabilityTheorem ≡ false
    explicitMDLOptimizerClaim :
      Bool
    explicitMDLOptimizerClaimIsFalse :
      explicitMDLOptimizerClaim ≡ false
    abiogenesisProof :
      Bool
    abiogenesisProofIsFalse :
      abiogenesisProof ≡ false
    fullMolecularSimulation :
      Bool
    fullMolecularSimulationIsFalse :
      fullMolecularSimulation ≡ false
    fitnessUniversality :
      Bool
    fitnessUniversalityIsFalse :
      fitnessUniversality ≡ false
    originOfLifeClosure :
      Bool
    originOfLifeClosureIsFalse :
      originOfLifeClosure ≡ false

open PromotedBoundedEvolutionaryMeaning public

record EvolutionaryTransportNonPromotionCertificate
    (bridge : EvolutionaryTransportMDLBridge) : Set where
  field
    guards :
      List NonPromotionGuard
    guardsMatch :
      guards ≡ nonPromotionGuards bridge
    noBiologyInevitabilityTheorem :
      Bool
    noBiologyInevitabilityTheoremIsTrue :
      noBiologyInevitabilityTheorem ≡ true
    noExplicitMDLOptimizerClaim :
      Bool
    noExplicitMDLOptimizerClaimIsTrue :
      noExplicitMDLOptimizerClaim ≡ true
    noAbiogenesisProof :
      Bool
    noAbiogenesisProofIsTrue :
      noAbiogenesisProof ≡ true
    noFullMolecularSimulation :
      Bool
    noFullMolecularSimulationIsTrue :
      noFullMolecularSimulation ≡ true
    noFitnessUniversality :
      Bool
    noFitnessUniversalityIsTrue :
      noFitnessUniversality ≡ true
    noOriginOfLifeClosure :
      Bool
    noOriginOfLifeClosureIsTrue :
      noOriginOfLifeClosure ≡ true
    guardReading :
      String

open EvolutionaryTransportNonPromotionCertificate public

promoteWithEvolutionaryTransportReceipts :
  (bridge : EvolutionaryTransportMDLBridge) ->
  (observation : EvolutionaryTransportObservation bridge) ->
  (candidate : CandidateEvolutionaryTransportState bridge observation) ->
  (receipt : EvolutionaryMDLTransportReceipt bridge observation candidate) ->
  BoundedEvolutionaryMeaning bridge
promoteWithEvolutionaryTransportReceipts bridge observation candidate receipt =
  promoteBoundedMeaning
    bridge
    (trace observation)
    (candidateState candidate)
    (mdlScore receipt)
    (EvolutionaryMDLTransportReceipt.receipt receipt)

canonicalEvolutionaryRouteAdmissible :
  AdmissibleRoute boundedMDLTransportReceiptRoute
canonicalEvolutionaryRouteAdmissible = tt

------------------------------------------------------------------------
-- Canonical toy inhabitants.

canonicalEvolutionaryTransportMDLBridge :
  EvolutionaryTransportMDLBridge
canonicalEvolutionaryTransportMDLBridge =
  record
    { PhysicsBoundary = ⊤
    ; ChemicalNetwork = ⊤
    ; MolecularMachine = ⊤
    ; CellSignal = ⊤
    ; BodyBehaviour = ⊤
    ; LineageContext = ⊤
    ; ObservationTrace = ⊤
    ; CandidateTransportState = ⊤
    ; MDLScore = ⊤
    ; MDLReceipt = ⊤
    ; ProvenanceNode = ⊤
    ; BoundedEvolutionaryMeaning = ⊤
    ; observeThread = λ _ _ _ -> tt
    ; observedScales = λ _ -> canonicalEvolutionaryScales
    ; observedChannels = λ _ -> canonicalEvolutionaryChannels
    ; physicsCandidate = λ _ -> tt
    ; chemistryCandidate = λ _ -> tt
    ; machineCandidate = λ _ -> tt
    ; cellSignalCandidate = λ _ -> tt
    ; bodyBehaviourCandidate = λ _ -> tt
    ; conservedMachinery = λ _ -> canonicalConservedMachinery
    ; persistentMotifs = λ _ -> Motifs.canonicalTransportMotifBasis
    ; integrateCandidateState = λ _ _ _ _ _ _ -> tt
    ; candidateAspects = λ _ -> canonicalEvolutionaryTransportAspects
    ; mdlGuide = λ _ _ -> tt
    ; admissibilityReceipt = λ _ _ _ -> tt
    ; provenanceTrail = λ _ -> tt ∷ []
    ; promoteBoundedMeaning = λ _ _ _ _ -> tt
    ; observationGate = λ _ _ -> ⊤
    ; mdlReceiptGate = λ _ _ _ _ -> ⊤
    ; provenanceGate = λ _ -> ⊤
    ; nonPromotionGuards = canonicalNonPromotionGuards
    ; surfaceReading =
        "Toy evolutionary bridge reads conserved molecular machinery as MDL-guided persistent transport motifs across physics, chemistry, molecular machines, cell signalling, and body/behaviour."
    }

canonicalEvolutionaryTransportObservation :
  EvolutionaryTransportObservation canonicalEvolutionaryTransportMDLBridge
canonicalEvolutionaryTransportObservation =
  record
    { physicsBoundary = tt
    ; chemicalNetwork = tt
    ; lineageContext = tt
    ; trace = tt
    ; traceIsObserved = refl
    ; scales = canonicalEvolutionaryScales
    ; scalesMatch = refl
    ; channels = canonicalEvolutionaryChannels
    ; channelsMatch = refl
    }

canonicalCandidateEvolutionaryTransportState :
  CandidateEvolutionaryTransportState
    canonicalEvolutionaryTransportMDLBridge
    canonicalEvolutionaryTransportObservation
canonicalCandidateEvolutionaryTransportState =
  record
    { physics = tt
    ; chemistry = tt
    ; machine = tt
    ; cellSignal = tt
    ; bodyBehaviour = tt
    ; candidateState = tt
    ; physicsMatches = refl
    ; chemistryMatches = refl
    ; machineMatches = refl
    ; cellSignalMatches = refl
    ; bodyBehaviourMatches = refl
    ; candidateStateMatches = refl
    ; machineryEvidence = canonicalConservedMachinery
    ; machineryEvidenceMatches = refl
    ; motifEvidence = Motifs.canonicalTransportMotifBasis
    ; motifEvidenceMatches = refl
    ; aspectEvidence = canonicalEvolutionaryTransportAspects
    ; aspectEvidenceMatches = refl
    }

canonicalEvolutionaryMDLTransportReceipt :
  EvolutionaryMDLTransportReceipt
    canonicalEvolutionaryTransportMDLBridge
    canonicalEvolutionaryTransportObservation
    canonicalCandidateEvolutionaryTransportState
canonicalEvolutionaryMDLTransportReceipt =
  record
    { mdlScore = tt
    ; mdlScoreMatches = refl
    ; receipt = tt
    ; receiptMatchesCandidate = refl
    ; observationGateHeld = tt
    ; mdlReceiptGateHeld = tt
    ; provenanceGateHeld = tt
    ; trail = tt ∷ []
    ; trailMatches = refl
    ; route = boundedMDLTransportReceiptRoute
    ; routeIsBounded = refl
    ; routeAdmissible = tt
    }

canonicalPromotedBoundedEvolutionaryMeaning :
  PromotedBoundedEvolutionaryMeaning
    canonicalEvolutionaryTransportMDLBridge
    canonicalEvolutionaryTransportObservation
    canonicalCandidateEvolutionaryTransportState
    canonicalEvolutionaryMDLTransportReceipt
canonicalPromotedBoundedEvolutionaryMeaning =
  record
    { meaning = tt
    ; meaningMatchesPromotion = refl
    ; boundedMDLTransportOnly = true
    ; boundedMDLTransportOnlyIsTrue = refl
    ; biologyInevitabilityTheorem = false
    ; biologyInevitabilityTheoremIsFalse = refl
    ; explicitMDLOptimizerClaim = false
    ; explicitMDLOptimizerClaimIsFalse = refl
    ; abiogenesisProof = false
    ; abiogenesisProofIsFalse = refl
    ; fullMolecularSimulation = false
    ; fullMolecularSimulationIsFalse = refl
    ; fitnessUniversality = false
    ; fitnessUniversalityIsFalse = refl
    ; originOfLifeClosure = false
    ; originOfLifeClosureIsFalse = refl
    }

canonicalEvolutionaryTransportNonPromotionCertificate :
  EvolutionaryTransportNonPromotionCertificate
    canonicalEvolutionaryTransportMDLBridge
canonicalEvolutionaryTransportNonPromotionCertificate =
  record
    { guards = canonicalNonPromotionGuards
    ; guardsMatch = refl
    ; noBiologyInevitabilityTheorem = true
    ; noBiologyInevitabilityTheoremIsTrue = refl
    ; noExplicitMDLOptimizerClaim = true
    ; noExplicitMDLOptimizerClaimIsTrue = refl
    ; noAbiogenesisProof = true
    ; noAbiogenesisProofIsTrue = refl
    ; noFullMolecularSimulation = true
    ; noFullMolecularSimulationIsTrue = refl
    ; noFitnessUniversality = true
    ; noFitnessUniversalityIsTrue = refl
    ; noOriginOfLifeClosure = true
    ; noOriginOfLifeClosureIsTrue = refl
    ; guardReading =
        "The evolutionary transport MDL bridge is non-promoting: it supplies bounded motif receipts only, not inevitability, an explicit optimizer, abiogenesis, molecular simulation, fitness universality, or origin-of-life closure."
    }
