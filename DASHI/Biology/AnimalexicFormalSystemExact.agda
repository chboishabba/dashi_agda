module DASHI.Biology.AnimalexicFormalSystemExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalexicSourceAtlas as Sources
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Core.DualEffectAdaptiveFidelityExact as Fidelity
import DASHI.Core.AssumptionIndexedReopeningExact as Reopen
import DASHI.Core.ExplodedGraphGeometry as Graph

record AnimalexicState
    (Geometry Pose Vocal Facial Attention Environment History Interpretation : Set)
    : Set₁ where
  constructor animalexicState
  field
    geometry : Geometry
    pose : Pose
    vocal : Vocal
    facial : Facial
    attention : Attention
    environment : Environment
    history : History
    interpretation : Interpretation

open AnimalexicState public

record AnimalObservation
    (Modality Sensor Time Value Quality Provenance : Set) : Set₁ where
  constructor animalObservation
  field
    modality : Modality
    sensor : Sensor
    time : Time
    value : Value
    quality : Quality
    provenance : Provenance

open AnimalObservation public

record ObservationPromotion
    {Observation Candidate State : Set}
    (inferCandidate : Observation → Candidate)
    (promote : Candidate → Base.AlternativeStatus)
    (materialise : Candidate → State) : Set₁ where
  constructor observationPromotion
  field
    observation : Observation
    candidate : Candidate
    candidateIsInferred : candidate ≡ inferCandidate observation
    status : Base.AlternativeStatus
    statusIsPromotion : status ≡ promote candidate

open ObservationPromotion public

record AnimalSurfel
    (Point Normal Radius Weight Frame Residual Spread : Set) : Set₁ where
  constructor animalSurfel
  field
    observedAnchor : Point
    fusedCentroid : Point
    estimatedNormal : Normal
    supportRadius : Radius
    confidenceWeight : Weight
    FrameSupports : Frame → Set
    residual : Residual
    supportSpread : Spread
    promotionStatus : Base.AlternativeStatus

open AnimalSurfel public

record DistinctFrameSupport
    {Frame : Set}
    (Supports : Frame → Set) : Set₁ where
  constructor distinctFrameSupport
  field
    first second : Frame
    firstSupports : Supports first
    secondSupports : Supports second
    distinct : first ≡ second → ⊥

open DistinctFrameSupport public

record SpatialHashConsistency
    (Surfel Point Cell : Set)
    (anchor : Surfel → Point)
    (cellOf : Point → Cell)
    (Member : Surfel → Cell → Set) : Set₁ where
  constructor spatialHashConsistency
  field
    memberOnlyAtAnchorCell :
      ∀ surfel cell →
      Member surfel cell →
      cellOf (anchor surfel) ≡ cell
    anchorCellHasMember :
      ∀ surfel → Member surfel (cellOf (anchor surfel))

open SpatialHashConsistency public

record NonPeriodicBoundaryWitness
    {Node : Set}
    (Adjacent : Node → Node → Set) : Set₁ where
  constructor nonPeriodicBoundaryWitness
  field
    lowBoundary highBoundary : Node
    oppositeFacesNotAdjacent : Adjacent lowBoundary highBoundary → ⊥

open NonPeriodicBoundaryWitness public

AnimalGeometryGraph : Set → Set₁
AnimalGeometryGraph = Graph.GraphGeometry

record WeightedGeometrySupport
    (Node Weight : Set) : Set₁ where
  constructor weightedGeometrySupport
  field
    graph : Graph.GraphGeometry Node
    weight : Node → Node → Weight
    baseline : Node → Node → Weight
    supportSemantics : String
    temporalIndependenceSemantics : String

open WeightedGeometrySupport public

record PromotionMargin
    (Candidate Margin : Set) : Set₁ where
  constructor promotionMargin
  field
    margin : Candidate → Margin
    Ascend : Margin → Set
    Plateau : Margin → Set
    Reject : Margin → Set
    categoriesDisjointReference : String
    normalizationReference : String

open PromotionMargin public

record DefectLocalizedToLowMargin
    {Candidate : Set}
    (Defect LowMargin : Candidate → Set) : Set₁ where
  constructor defectLocalizedToLowMargin
  field
    confined : ∀ candidate → Defect candidate → LowMargin candidate

open DefectLocalizedToLowMargin public

record ObjectSupportSelection
    (Node : Set)
    (graph : Graph.GraphGeometry Node)
    (Ascended Plateau : Node → Set) : Set₁ where
  constructor objectSupportSelection
  field
    CoreMember : Node → Set
    coreIsAscended : ∀ node → CoreMember node → Ascended node
    coreConnected :
      ∀ left right →
      CoreMember left → CoreMember right →
      Graph.Connected graph left right
    shellRadius : Nat
    ShellMember : Node → Set
    shellIsPlateau : ∀ node → ShellMember node → Plateau node
    shellAffiliated :
      ∀ node → ShellMember node →
      Σ Node (λ core →
        CoreMember core ×
        Σ Nat (λ distance →
          Graph.ExactDistance graph node core distance
          × distance ≤ shellRadius))

open ObjectSupportSelection public

record AmbiguousPlateauAffiliation
    {Node : Set}
    (graph : Graph.GraphGeometry Node)
    (CoreMember Plateau : Node → Set)
    (shellRadius : Nat) : Set₁ where
  constructor ambiguousPlateauAffiliation
  field
    node : Node
    plateau : Plateau node
    leftCore rightCore : Node
    leftCoreMember : CoreMember leftCore
    rightCoreMember : CoreMember rightCore
    distinctCores : leftCore ≡ rightCore → ⊥
    equalDistance : Nat
    leftExact : Graph.ExactDistance graph node leftCore equalDistance
    rightExact : Graph.ExactDistance graph node rightCore equalDistance
    withinShell : equalDistance ≤ shellRadius

open AmbiguousPlateauAffiliation public

record IncrementalFactorState
    (Variable Factor : Set) : Set₁ where
  constructor incrementalFactorState
  field
    variables : List Variable
    factors : List Factor
    DependsOn : Factor → Variable → Set
    factorSemantics : Factor → String
    probabilityInterpretationJustified : Bool

open IncrementalFactorState public

AnimalHypothesisFamily : Set → Set
AnimalHypothesisFamily = Base.LiveAlternativeFamily

record IndividualAnimalModel
    (Animal Morphology Repertoire InteractionHistory ContextPrior : Set) : Set₁ where
  constructor individualAnimalModel
  field
    animal : Animal
    morphology : Morphology
    repertoire : Repertoire
    interactionHistory : InteractionHistory
    contextPrior : ContextPrior
    provenance : String

open IndividualAnimalModel public

record AnimalCommunicationLoop
    (State Action Evidence Observation : Set) : Set₁ where
  constructor animalCommunicationLoop
  field
    actionSystem : Fidelity.DualEffectActionSystem State Action Evidence
    observe : State → Observation
    updateFromEvidence : State → Evidence → State
    actionPolicyReference : String
    welfareAndSafetyPolicyReference : String

open AnimalCommunicationLoop public

AnimalInterventionalSeparation :
  ∀ {State Action Observation : Set} →
  (State → Observation) →
  (Action → State → State) →
  State → State → Set₁
AnimalInterventionalSeparation = Refine.TraceSeparatingWitness

AnimalEvidenceLineage : Set → Set → Set₁
AnimalEvidenceLineage = Reopen.EvidenceLineage

record AnimalReopenableCarrier
    (Payload : Set) : Set₁ where
  constructor animalReopenableCarrier
  field
    alternatives : Base.LiveAlternativeFamily Payload
    activeInterpretationReference : String
    reopeningTriggerReference : String
    expiryOrRefutationReference : String

open AnimalReopenableCarrier public

record AnimalexicEpistemicBoundary : Set where
  constructor animalexicEpistemicBoundary
  field
    sensorMeasurementDoesNotImplyGeometricFact : Bool
    geometricFactDoesNotImplyBehaviouralEvent : Bool
    behaviouralEventDoesNotImplyCommunicativeAct : Bool
    communicativeActDoesNotImplySemanticMeaning : Bool
    semanticCorrelationDoesNotImplyIntentionalLanguage : Bool
    behaviouralClusterDoesNotNameItself : Bool
    missingModalityEvidenceIsNotOpposition : Bool
    classifierConfidenceDoesNotAuthorizeMeaning : Bool
    interventionCanRefinePassiveAmbiguity : Bool
    inactiveHypothesisDoesNotMeanRefuted : Bool

open AnimalexicEpistemicBoundary public

canonicalAnimalexicEpistemicBoundary : AnimalexicEpistemicBoundary
canonicalAnimalexicEpistemicBoundary =
  animalexicEpistemicBoundary true true true true true true true true true true

record AnimalexicFormalDeliverableBoundary : Set where
  constructor animalexicFormalDeliverableBoundary
  field
    embodiedSensoriumRepresented : Bool
    persistentGeometryRepresented : Bool
    poseAndSignalAdaptersRemainReplaceable : Bool
    temporalBehaviourRequiresSeparateEvidence : Bool
    semanticHypothesesRemainDefeasible : Bool
    individualModelIsExplicit : Bool
    bidirectionalActionLoopRepresented : Bool
    sourceAtlasImportedWithoutProofPromotion : Bool
    runtimeStereoBenchmarksRemainApplicationObligations : Bool
    sharedLexiconRequiresInterventionalEvidenceBeyondThisCarrier : Bool

open AnimalexicFormalDeliverableBoundary public

canonicalAnimalexicFormalDeliverableBoundary :
  AnimalexicFormalDeliverableBoundary
canonicalAnimalexicFormalDeliverableBoundary =
  animalexicFormalDeliverableBoundary true true true true true true true true true true

animalexicSourceAtlasRecorded : Sources.AnimalexicSourceBoundary
animalexicSourceAtlasRecorded = Sources.canonicalAnimalexicSourceBoundary
