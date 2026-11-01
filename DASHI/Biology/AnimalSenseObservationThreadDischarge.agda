module DASHI.Biology.AnimalSenseObservationThreadDischarge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Biology.AnimalexicAnimalUtteranceSurface
open import DASHI.Biology.AvianCompassExamples
open import DASHI.Biology.EvolvedSensoryTransport
open import DASHI.Biology.GenomeSensorimotorConnectomeBridge
open import DASHI.Biology.RetinalPerturbationObservationBridge
import DASHI.Core.AuthorityNonPromotionCore as AuthorityCore
import DASHI.Core.BridgeRequirementCore as BridgeCore
import DASHI.Core.CandidateOnlyCore as CandidateCore
open import DASHI.Interop.ObservationTransportSpine
open import DASHI.Interop.SeaMeInItROMKernelFormalism
open import DASHI.Physics.Closure.BidirectionalBrainObservationQuotient
open import DASHI.Physics.Closure.SensoryAttractorClasses

------------------------------------------------------------------------
-- Thread-local surface coverage for "Quantum Mechanism in Birds".

data ThreadSurface : Set where
  avianRetinalBridgeSurface : ThreadSurface
  genomeSensorimotorSurface : ThreadSurface
  animalexicUtteranceSurface : ThreadSurface
  generalizedSensoryAttractorSurface : ThreadSurface
  bidirectionalBrainObservationSurface : ThreadSurface
  seaMeInItROMKernelSurface : ThreadSurface
  observationTransportSpineSurface : ThreadSurface

data ThreadDischargeBoundary : Set where
  noQualiaRecovery : ThreadDischargeBoundary
  noBrainClosure : ThreadDischargeBoundary
  noSoundToWordDictionary : ThreadDischargeBoundary
  noDNAEncodesMeaning : ThreadDischargeBoundary
  noArbitraryCrossSenseIdentityDischarge : ThreadDischargeBoundary
  noReceiptlessPromotion : ThreadDischargeBoundary
  noUnsupportedBiologyTheorem : ThreadDischargeBoundary

coveredSurfaces : List ThreadSurface
coveredSurfaces =
  avianRetinalBridgeSurface
  ∷ genomeSensorimotorSurface
  ∷ animalexicUtteranceSurface
  ∷ generalizedSensoryAttractorSurface
  ∷ bidirectionalBrainObservationSurface
  ∷ seaMeInItROMKernelSurface
  ∷ observationTransportSpineSurface
  ∷ []

canonicalDischargeBoundaries : List ThreadDischargeBoundary
canonicalDischargeBoundaries =
  noQualiaRecovery
  ∷ noBrainClosure
  ∷ noSoundToWordDictionary
  ∷ noDNAEncodesMeaning
  ∷ noArbitraryCrossSenseIdentityDischarge
  ∷ noReceiptlessPromotion
  ∷ noUnsupportedBiologyTheorem
  ∷ []

------------------------------------------------------------------------
-- Canonical toy inhabitants for the new worker surfaces.

canonicalAnimalexicSurface :
  AnimalexicAnimalUtteranceSurface
canonicalAnimalexicSurface =
  record
    { Animal = ⊤
    ; Context = ⊤
    ; UtteranceEvent = ⊤
    ; ObservationTrace = ⊤
    ; BodyStateCandidate = ⊤
    ; SocialStateCandidate = ⊤
    ; LatentCandidate = ⊤
    ; BehaviouralMeaning = ⊤
    ; Receipt = ⊤
    ; ProvenanceNode = ⊤
    ; ObserverProtocol = ⊤
    ; observe = λ _ _ _ → tt
    ; observedModalities =
        λ _ →
          acousticTrace
          ∷ postureTrace
          ∷ motionTrace
          ∷ socialTrace
          ∷ []
    ; candidateBodyState = λ _ → tt
    ; candidateSocialState = λ _ → tt
    ; candidateLatentState = λ _ _ _ → tt
    ; latentAspects =
        λ _ →
          bodyArousal
          ∷ environmentalAttention
          ∷ []
    ; admissibilityReceipt = λ _ _ → tt
    ; provenanceTrail = λ _ → tt ∷ []
    ; observerProtocol = λ _ → tt
    ; promoteBehaviouralMeaning = λ _ _ _ → tt
    ; multimodalReceiptComplete = λ _ _ _ → ⊤
    ; provenanceAdmissible = λ _ → ⊤
    ; boundaryReading =
        noSoundToWordDirectSemantics
        ∷ noDirectQualiaClaim
        ∷ noPromotionWithoutReceipts
        ∷ noSingleChannelCertainty
        ∷ []
    }

canonicalAnimalexicObservation :
  AnimalUtteranceObservation canonicalAnimalexicSurface
canonicalAnimalexicObservation =
  record
    { animal = tt
    ; context = tt
    ; utterance = tt
    ; trace = tt
    ; traceIsObserved = refl
    ; modalities =
        acousticTrace
        ∷ postureTrace
        ∷ motionTrace
        ∷ socialTrace
        ∷ []
    ; modalitiesMatch = refl
    }

canonicalAnimalexicCandidate :
  CandidateLatentBodySocialState
    canonicalAnimalexicSurface
    canonicalAnimalexicObservation
canonicalAnimalexicCandidate =
  record
    { bodyCandidate = tt
    ; socialCandidate = tt
    ; latentCandidate = tt
    ; bodyCandidateMatches = refl
    ; socialCandidateMatches = refl
    ; latentCandidateMatches = refl
    ; latentAspectEvidence =
        bodyArousal
        ∷ environmentalAttention
        ∷ []
    }

canonicalAnimalexicPromotionReceipt :
  AnimalexicPromotionReceipt
    canonicalAnimalexicSurface
    canonicalAnimalexicObservation
    canonicalAnimalexicCandidate
canonicalAnimalexicPromotionReceipt =
  record
    { receipt = tt
    ; receiptMatchesCandidate = refl
    ; multimodalGate = tt
    ; provenanceGate = tt
    ; trail = tt ∷ []
    ; trailMatches = refl
    ; route = multimodalLatentReceiptRoute
    ; routeIsReceiptRoute = refl
    ; routeAdmissible = tt
    }

canonicalPromotedAnimalexicMeaning :
  PromotedAnimalexicMeaning
    canonicalAnimalexicSurface
    canonicalAnimalexicObservation
    canonicalAnimalexicCandidate
    canonicalAnimalexicPromotionReceipt
canonicalPromotedAnimalexicMeaning =
  record
    { meaning = tt
    ; meaningMatchesPromotion = refl
    ; promotedBehaviourOnly = true
    ; promotedBehaviourOnlyIsTrue = refl
    ; directWordSemanticsRecovered = false
    ; directWordSemanticsRecoveredIsFalse = refl
    ; directQualiaRecovered = false
    ; directQualiaRecoveredIsFalse = refl
    }

canonicalGeneralizedSensoryTransport :
  GeneralizedSensoryTransport
canonicalGeneralizedSensoryTransport =
  record
    { WorldPhysics = ⊤
    ; Environment = ⊤
    ; PhysicalTransport = ⊤
    ; ReceptorChemistry = ⊤
    ; NeuralEncoding = ⊤
    ; ConnectomeBodyState = ⊤
    ; PerceptualBehaviorClass = ⊤
    ; EvolutionaryLineage = ⊤
    ; FitnessSignal = ⊤
    ; modalityClass = λ _ → multimodalLike
    ; worldToPhysicalTransport = λ _ _ → tt
    ; physicalTransportToReceptorChemistry = λ _ → tt
    ; receptorChemistryToNeuralEncoding = λ _ → tt
    ; neuralEncodingToConnectomeBodyPropagation = λ _ _ → tt
    ; connectomeBodyToPerceptualBehaviorQuotient = λ _ → tt
    ; perceptualBehaviorToEvolutionaryRetention = λ _ _ → tt
    ; retainedUnder = λ _ _ → ⊤
    ; samePerceptualBehaviorClass = λ _ _ → ⊤
    ; crossSenseComparisonReceipt = λ _ _ → ⊤
    ; pipeline = defaultSensoryTransportPipeline
    ; transportReading =
        "World physics is transported through receptor chemistry and embodied neural constraints into a behavioral quotient."
    }

canonicalLowDimensionalSensoryAttractor :
  LowDimensionalSensoryAttractor canonicalGeneralizedSensoryTransport
canonicalLowDimensionalSensoryAttractor =
  record
    { AttractorCoordinate = ⊤
    ; ResidualWidth = ⊤
    ; attractorClass = metastableBasinClass
    ; coordinateFromNeuralEncoding = λ _ → tt
    ; coordinateFromConnectomeBody = λ _ → tt
    ; coordinateFromPerceptualBehavior = λ _ → tt
    ; coordinateStep = λ _ → tt
    ; basin = λ _ → ⊤
    ; residualWidth = λ _ → tt
    ; quotientRespectsAttractorClass = λ _ → ⊤
    ; lowDimensionalReading =
        "The quotient is represented as a low-dimensional attractor class, not an exact experience."
    }

canonicalEvolvedLowDimensionalSensoryAttractor :
  EvolvedLowDimensionalSensoryAttractor
    canonicalGeneralizedSensoryTransport
canonicalEvolvedLowDimensionalSensoryAttractor =
  record
    { attractor = canonicalLowDimensionalSensoryAttractor
    ; retainedCoordinate = λ _ _ _ → ⊤
    ; retainedBehaviorQuotient = λ _ _ _ → ⊤
    ; behavioralRetentionFactors =
        energyCostReduced
        ∷ environmentalRobustnessImproves
        ∷ socialOrEcologicalPolicyImproves
        ∷ []
    ; retentionReading =
        "Evolutionary retention is modeled by criteria, not by an optimality theorem."
    }

canonicalSensoryAttractorRetentionSurface :
  SensoryAttractorRetentionSurface
    canonicalGeneralizedSensoryTransport
    canonicalEvolvedLowDimensionalSensoryAttractor
canonicalSensoryAttractorRetentionSurface =
  record
    { PopulationSample = ⊤
    ; DevelopmentalHistory = ⊤
    ; EcologicalContext = ⊤
    ; MeasurementReceipt = ⊤
    ; sampleLineage = λ _ → tt
    ; developmentalContext = λ _ → tt
    ; ecologicalContext = λ _ → tt
    ; measurementReceiptFor = λ _ → tt
    ; retainedInSample = λ _ _ → ⊤
    ; retentionRequiresReceipt = λ _ _ → tt
    ; retentionSurfaceReading =
        "Retention claims require a population sample and measurement receipt."
    }

canonicalEvolvedSensoryTransportReceipt :
  EvolvedSensoryTransportReceipt
canonicalEvolvedSensoryTransportReceipt =
  record
    { transport = canonicalGeneralizedSensoryTransport
    ; evolvedAttractor =
        canonicalEvolvedLowDimensionalSensoryAttractor
    ; retentionSurface =
        canonicalSensoryAttractorRetentionSurface
    ; biologicalDomains =
        photicDomain
        ∷ acousticDomain
        ∷ chemicalDomain
        ∷ magneticDomain
        ∷ mechanicalDomain
        ∷ thermalDomain
        ∷ bodyInternalDomain
        ∷ multimodalDomain
        ∷ []
    ; transportPipeline = defaultSensoryTransportPipeline
    ; status = retainedAsQuotientClassOnly
    ; nonPromotionCertificate =
        canonicalSensoryTransportNonPromotionCertificate
          canonicalGeneralizedSensoryTransport
    ; exactQualiaRecovery = false
    ; exactQualiaRecoveryIsFalse = refl
    ; arbitraryCrossSenseIdentity = false
    ; arbitraryCrossSenseIdentityIsFalse = refl
    ; theoremLevelBiologyClaimWithoutReceipts = false
    ; theoremLevelBiologyClaimWithoutReceiptsIsFalse = refl
    ; allowedClaim =
        "low-dimensional sensory attractor quotient"
        ∷ "evolutionary-retention criterion with receipts"
        ∷ []
    ; forbiddenClaim =
        "exact qualia recovery"
        ∷ "arbitrary cross-sense identity"
        ∷ "receiptless biology theorem"
        ∷ []
    ; receiptReading =
        "General sensory transport is retained only as a receipt-bound quotient class."
    }

canonicalEvolvedSensoryTransportPipelineWitness :
  EvolvedSensoryTransportPipelineWitness
    canonicalEvolvedSensoryTransportReceipt
canonicalEvolvedSensoryTransportPipelineWitness =
  safeEvolvedSensoryTransportPipelineWitness
    canonicalEvolvedSensoryTransportReceipt
    refl
    refl

------------------------------------------------------------------------
-- Minimal SeaMeInIt inhabitant used only to show the ROM lane is present.

canonicalBodyCarrierForDischarge : BodyCarrier
canonicalBodyCarrierForDischarge =
  record
    { Vertex = ⊤
    ; Face = ⊤
    ; RegionMask = ⊤
    ; ForbiddenZone = ⊤
    ; Atlas = ⊤
    ; vertices = tt ∷ []
    ; faces = tt ∷ []
    ; atlas = tt
    ; regionMasks = tt ∷ []
    ; forbiddenZones = tt ∷ []
    ; bodyReceipt = "Toy body carrier receipt for thread discharge."
    }

canonicalKernelBasisForDischarge :
  KernelBasis canonicalBodyCarrierForDischarge
canonicalKernelBasisForDischarge =
  record
    { BasisComponent = ⊤
    ; CoefficientVector = ⊤
    ; FieldValue = ⊤
    ; components = tt ∷ []
    ; basisVector = λ _ _ → tt
    ; coefficientLengthMatchesComponents = gateDiagnostic
    ; vertexSetMatchesBody = gateDiagnostic
    ; areaWeightedOrthonormalReceipt = gateDiagnostic
    ; basisReceipt = "Diagnostic ROM basis receipt."
    }

canonicalROMOperatorForDischarge :
  ROMOperator
    canonicalBodyCarrierForDischarge
    canonicalKernelBasisForDischarge
canonicalROMOperatorForDischarge =
  record
    { Pose = ⊤
    ; Parameter = ⊤
    ; DerivationToken = ⊤
    ; DerivationStream = ⊤
    ; tokenGate = λ _ → gateDiagnostic
    ; streamGate = λ _ → gateDiagnostic
    ; decode = λ _ → tt
    ; validPose = λ _ → gateDiagnostic
    ; projectPose = λ _ → tt
    ; encodePose = λ _ → tt
    ; romReceipt = "Diagnostic ROM operator receipt."
    }

canonicalCouplingForDischarge : CouplingCocycle
canonicalCouplingForDischarge =
  record
    { Demand = ⊤
    ; Response = ⊤
    ; Debt = ⊤
    ; demand = tt
    ; response = tt
    ; delta = λ _ _ → tt
    ; obligationProjection = λ _ → gateDiagnostic
    ; debtGate = gateDiagnostic
    ; blockingDebt = false
    ; couplingReceipt = "Diagnostic coupling cocycle receipt."
    }

canonicalProjectedFieldForDischarge :
  ProjectedField
    canonicalBodyCarrierForDischarge
    canonicalKernelBasisForDischarge
    canonicalROMOperatorForDischarge
canonicalProjectedFieldForDischarge =
  record
    { Task = ⊤
    ; Fabric = ⊤
    ; ProjectedValue = ⊤
    ; fieldKind = pressureField
    ; coefficientFor = λ _ _ _ → tt
    ; reconstruct = λ _ _ → tt
    ; fieldGate = gateDiagnostic
    ; romAggregationReceipt = "Diagnostic projected field receipt."
    }

canonicalSeamGraphForDischarge :
  SeamGraph canonicalBodyCarrierForDischarge
canonicalSeamGraphForDischarge =
  record
    { Node = ⊤
    ; Edge = ⊤
    ; EdgeCost = ⊤
    ; nodes = tt ∷ []
    ; edges = tt ∷ []
    ; endpointA = λ _ → tt
    ; endpointB = λ _ → tt
    ; seamOK = λ _ → gateDiagnostic
    ; edgeCost = λ _ → tt
    ; topologyReceipt = "Diagnostic seam graph receipt."
    }

canonicalPanelizationForDischarge :
  SeamCutPanelization
    canonicalBodyCarrierForDischarge
    canonicalSeamGraphForDischarge
canonicalPanelizationForDischarge =
  record
    { SeamCut = ⊤
    ; Panel = ⊤
    ; cutEdges = λ _ → tt ∷ []
    ; panels = λ _ → tt ∷ []
    ; cutGate = λ _ → gateDiagnostic
    ; panelGate = λ _ → gateDiagnostic
    ; panelUnwrapReceipt = "Diagnostic panelization receipt."
    }

canonicalCompressionCellForDischarge :
  CompressionCell
    canonicalBodyCarrierForDischarge
    canonicalKernelBasisForDischarge
    canonicalROMOperatorForDischarge
canonicalCompressionCellForDischarge =
  record
    { PoseRegion = ⊤
    ; ConstraintStack = ⊤
    ; BoundaryResidual = ⊤
    ; kind = hypersheet
    ; poseRegion = tt
    ; admissibilityStack = tt
    ; equivalentUnderStack = λ _ _ → ⊤
    ; boundaryResidual = λ _ → tt
    ; needsFineGraining = λ _ → false
    ; compressionReceipt = "Diagnostic compression cell receipt."
    }

canonicalManufacturingReceiptForDischarge :
  ManufacturingReceipt
    canonicalBodyCarrierForDischarge
    canonicalSeamGraphForDischarge
    canonicalPanelizationForDischarge
canonicalManufacturingReceiptForDischarge =
  record
    { ManufacturingArtifact = ⊤
    ; selectedCut = tt
    ; artifact = tt
    ; panelExportGate = gateDiagnostic
    ; manufacturingGate = gateDiagnostic
    ; manufacturingReceipt = "Diagnostic manufacturing receipt."
    }

canonicalSeaMeInItROMKernelSurfaceForDischarge :
  SeaMeInItROMKernelSurface
canonicalSeaMeInItROMKernelSurfaceForDischarge =
  record
    { body = canonicalBodyCarrierForDischarge
    ; basis = canonicalKernelBasisForDischarge
    ; rom = canonicalROMOperatorForDischarge
    ; couplings = canonicalCouplingForDischarge ∷ []
    ; projectedFields = canonicalProjectedFieldForDischarge ∷ []
    ; seamGraph = canonicalSeamGraphForDischarge
    ; panelization = canonicalPanelizationForDischarge
    ; compressionCells = canonicalCompressionCellForDischarge ∷ []
    ; manufacturing = canonicalManufacturingReceiptForDischarge
    ; carrierGate = gateDiagnostic
    ; basisGate = gateDiagnostic
    ; romGate = gateDiagnostic
    ; couplingGate = gateDiagnostic
    ; seamCostGate = gateDiagnostic
    ; topologyGate = gateDiagnostic
    ; panelizationGate = gateDiagnostic
    ; solverDomainGate = gateDiagnostic
    ; manufacturingReceiptGate = gateDiagnostic
    ; nonPromotionBoundary =
        engineeringReceiptModelOnly
        ∷ noExternalPipelineValidationClaim
        ∷ noTrueInverseDeformationClaim
        ∷ noManufacturingSafetyClaim
        ∷ []
    ; plainReading =
        "SeaMeInIt ROM is present as a diagnostic body-carrier receipt lane."
    }

canonicalSeaMeInItNonPromotionCertificateForDischarge :
  NonPromotionCertificate
    canonicalSeaMeInItROMKernelSurfaceForDischarge
canonicalSeaMeInItNonPromotionCertificateForDischarge =
  record
    { stateIsDiagnosticOnly = refl
    ; reason =
        "Diagnostic gates keep the ROM kernel surface below artifact promotion."
    }

------------------------------------------------------------------------
-- Reusable non-authority core adapters.

canonicalAnimalSenseCandidateOnlyCoreAdapter :
  CandidateCore.CandidateOnlyRow
canonicalAnimalSenseCandidateOnlyCoreAdapter =
  CandidateCore.mkCandidateOnlyRow
    "animal sense observation thread candidate-only adapter"
    "DASHI.Biology.AnimalSenseObservationThreadDischarge"
    "canonicalAnimalSenseCandidateOnlyCoreAdapter"
    CandidateCore.bridgeCandidateKind
    CandidateCore.bridgeCandidateOnlyStatus
    "Thread surfaces are inhabited as observation-transport candidates and receipt-bound bridges."
    "Qualia recovery, DNA-meaning semantics, cross-sense identity, and theorem-level biology authority remain outside this discharge."

canonicalAnimalSenseCandidateOnlyCoreAdapterReceipt :
  CandidateCore.CandidateOnlyReceipt
    canonicalAnimalSenseCandidateOnlyCoreAdapter
canonicalAnimalSenseCandidateOnlyCoreAdapterReceipt =
  CandidateCore.canonicalCandidateOnlyReceipt
    canonicalAnimalSenseCandidateOnlyCoreAdapter
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalAnimalSenseCandidateOnlyAdapterCandidateOnly :
  CandidateCore.candidateOnly
    canonicalAnimalSenseCandidateOnlyCoreAdapter
  ≡
  true
canonicalAnimalSenseCandidateOnlyAdapterCandidateOnly =
  CandidateCore.candidateOnlyIsTrue
    canonicalAnimalSenseCandidateOnlyCoreAdapterReceipt

canonicalAnimalSenseCandidateOnlyAdapterPromotedFalse :
  CandidateCore.promoted
    canonicalAnimalSenseCandidateOnlyCoreAdapter
  ≡
  false
canonicalAnimalSenseCandidateOnlyAdapterPromotedFalse =
  CandidateCore.candidatePromotedIsFalse
    canonicalAnimalSenseCandidateOnlyCoreAdapterReceipt

canonicalAnimalSenseCandidateOnlyAdapterTheoremAuthorityFalse :
  CandidateCore.carriesTheoremAuthority
    canonicalAnimalSenseCandidateOnlyCoreAdapter
  ≡
  false
canonicalAnimalSenseCandidateOnlyAdapterTheoremAuthorityFalse =
  CandidateCore.candidateNoTheoremAuthority
    canonicalAnimalSenseCandidateOnlyCoreAdapterReceipt

canonicalAnimalSenseAuthorityNonPromotionCoreAdapter :
  AuthorityCore.AuthorityNonPromotionBundle
canonicalAnimalSenseAuthorityNonPromotionCoreAdapter =
  AuthorityCore.mkClosedAuthorityNonPromotionBundle
    "animal sense observation thread authority non-promotion adapter"

canonicalAnimalSenseAuthorityNonPromotionCoreAdapterKindsFalse :
  AuthorityCore.AllAuthorityKindsFalse
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter
    AuthorityCore.canonicalAuthorityKinds
canonicalAnimalSenseAuthorityNonPromotionCoreAdapterKindsFalse =
  AuthorityCore.proveAllAuthorityKindsFalse
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter
    AuthorityCore.canonicalAuthorityKinds

canonicalAnimalSenseAuthorityAdapterScientificAuthorityFalse :
  AuthorityCore.scientificAuthorityFlag
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalAnimalSenseAuthorityAdapterScientificAuthorityFalse =
  AuthorityCore.bundleScientificAuthorityIsFalse
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter

canonicalAnimalSenseAuthorityAdapterEmpiricalAuthorityFalse :
  AuthorityCore.empiricalAuthorityFlag
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalAnimalSenseAuthorityAdapterEmpiricalAuthorityFalse =
  AuthorityCore.bundleEmpiricalAuthorityIsFalse
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter

canonicalAnimalSenseAuthorityAdapterPromotesAnyAuthorityFalse :
  AuthorityCore.promotesAnyAuthority
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter
  ≡
  false
canonicalAnimalSenseAuthorityAdapterPromotesAnyAuthorityFalse =
  AuthorityCore.bundlePromotesAnyAuthorityIsFalse
    canonicalAnimalSenseAuthorityNonPromotionCoreAdapter

canonicalAnimalSenseBridgeRequirementCoreAdapter :
  BridgeCore.BridgeRequirementCoreReceipt
canonicalAnimalSenseBridgeRequirementCoreAdapter =
  BridgeCore.canonicalBridgeRequirementCoreReceipt

canonicalAnimalSenseBridgeRequirementCoreAdapterIsCanonical :
  canonicalAnimalSenseBridgeRequirementCoreAdapter
  ≡
  BridgeCore.canonicalBridgeRequirementCoreReceipt
canonicalAnimalSenseBridgeRequirementCoreAdapterIsCanonical =
  refl

canonicalAnimalSenseBridgeAdapterAuthorityPromotionFalse :
  BridgeCore.receiptAuthorityPromotion
    canonicalAnimalSenseBridgeRequirementCoreAdapter
  ≡
  false
canonicalAnimalSenseBridgeAdapterAuthorityPromotionFalse =
  BridgeCore.receiptAuthorityPromotionFalse
    canonicalAnimalSenseBridgeRequirementCoreAdapter

canonicalAnimalSenseBridgeAdapterTransportMapAuthorityFalse :
  BridgeCore.receiptTransportMapAuthority
    canonicalAnimalSenseBridgeRequirementCoreAdapter
  ≡
  false
canonicalAnimalSenseBridgeAdapterTransportMapAuthorityFalse =
  BridgeCore.receiptTransportMapAuthorityFalse
    canonicalAnimalSenseBridgeRequirementCoreAdapter

canonicalAnimalSenseBridgeAdapterBackgroundBridgeAuthorityFalse :
  BridgeCore.receiptBackgroundBridgeAuthority
    canonicalAnimalSenseBridgeRequirementCoreAdapter
  ≡
  false
canonicalAnimalSenseBridgeAdapterBackgroundBridgeAuthorityFalse =
  BridgeCore.receiptBackgroundBridgeAuthorityFalse
    canonicalAnimalSenseBridgeRequirementCoreAdapter

------------------------------------------------------------------------
-- Whole thread discharge.

record AnimalSenseObservationThreadDischarge : Set₁ where
  field
    title : String
    onlineThreadId : String
    canonicalThreadId : String

    surfaces : List ThreadSurface
    dischargeBoundaries : List ThreadDischargeBoundary

    retinalBridge :
      RetinalPerturbationObservationBridge canonicalAvianCompassSurface

    retinalCertificate :
      ObservationBridgeNonPromotionCertificate retinalBridge

    genomeBridge :
      GenomeSensorimotorConnectomeBridge

    animalexicSurface :
      AnimalexicAnimalUtteranceSurface

    animalexicMeaning :
      PromotedAnimalexicMeaning
        canonicalAnimalexicSurface
        canonicalAnimalexicObservation
        canonicalAnimalexicCandidate
        canonicalAnimalexicPromotionReceipt

    sensoryReceipt :
      EvolvedSensoryTransportReceipt

    sensoryWitness :
      EvolvedSensoryTransportPipelineWitness sensoryReceipt

    brainBoundary :
      BidirectionalBrainObservationBoundary

    romSurface :
      SeaMeInItROMKernelSurface

    romNonPromotion :
      NonPromotionCertificate romSurface

    observationSpineNoRecovery :
      canonicalNoRecoveryFlag ≡ true

    threadCandidateOnlyCoreAdapter :
      CandidateCore.CandidateOnlyRow

    threadCandidateOnlyCoreAdapterReceipt :
      CandidateCore.CandidateOnlyReceipt
        threadCandidateOnlyCoreAdapter

    threadCandidateOnlyCoreAdapterCandidateOnly :
      CandidateCore.candidateOnly
        threadCandidateOnlyCoreAdapter
      ≡
      true

    threadCandidateOnlyCoreAdapterPromotedFalse :
      CandidateCore.promoted
        threadCandidateOnlyCoreAdapter
      ≡
      false

    threadCandidateOnlyCoreAdapterTheoremAuthorityFalse :
      CandidateCore.carriesTheoremAuthority
        threadCandidateOnlyCoreAdapter
      ≡
      false

    threadAuthorityNonPromotionCoreAdapter :
      AuthorityCore.AuthorityNonPromotionBundle

    threadAuthorityNonPromotionCoreAdapterKindsFalse :
      AuthorityCore.AllAuthorityKindsFalse
        threadAuthorityNonPromotionCoreAdapter
        AuthorityCore.canonicalAuthorityKinds

    threadAuthorityAdapterScientificAuthorityFalse :
      AuthorityCore.scientificAuthorityFlag
        threadAuthorityNonPromotionCoreAdapter
      ≡
      false

    threadAuthorityAdapterEmpiricalAuthorityFalse :
      AuthorityCore.empiricalAuthorityFlag
        threadAuthorityNonPromotionCoreAdapter
      ≡
      false

    threadAuthorityAdapterPromotesAnyAuthorityFalse :
      AuthorityCore.promotesAnyAuthority
        threadAuthorityNonPromotionCoreAdapter
      ≡
      false

    threadBridgeRequirementCoreAdapter :
      BridgeCore.BridgeRequirementCoreReceipt

    threadBridgeRequirementCoreAdapterIsCanonical :
      threadBridgeRequirementCoreAdapter
      ≡
      BridgeCore.canonicalBridgeRequirementCoreReceipt

    threadBridgeAdapterAuthorityPromotionFalse :
      BridgeCore.receiptAuthorityPromotion
        threadBridgeRequirementCoreAdapter
      ≡
      false

    threadBridgeAdapterTransportMapAuthorityFalse :
      BridgeCore.receiptTransportMapAuthority
        threadBridgeRequirementCoreAdapter
      ≡
      false

    threadBridgeAdapterBackgroundBridgeAuthorityFalse :
      BridgeCore.receiptBackgroundBridgeAuthority
        threadBridgeRequirementCoreAdapter
      ≡
      false

    allRequestedSurfacesInhabited : Bool
    allRequestedSurfacesInhabitedIsTrue :
      allRequestedSurfacesInhabited ≡ true

    allUnsafeRoutesDischarged : Bool
    allUnsafeRoutesDischargedIsTrue :
      allUnsafeRoutesDischarged ≡ true

    safeSummary : String

open AnimalSenseObservationThreadDischarge public

canonicalAnimalSenseObservationThreadDischarge :
  AnimalSenseObservationThreadDischarge
canonicalAnimalSenseObservationThreadDischarge =
  record
    { title = "Quantum Mechanism in Birds"
    ; onlineThreadId = "6a09e6c0-2cb8-83ec-b3de-6fcb9433f5f7"
    ; canonicalThreadId = "6d744bfcd774a11523de7beb4c5cf534f617e034"
    ; surfaces = coveredSurfaces
    ; dischargeBoundaries = canonicalDischargeBoundaries
    ; retinalBridge = canonicalRetinalPerturbationObservationBridge
    ; retinalCertificate =
        canonicalObservationBridgeNonPromotionCertificate
    ; genomeBridge =
        canonicalGenomeSensorimotorConnectomeBridge
    ; animalexicSurface =
        canonicalAnimalexicSurface
    ; animalexicMeaning =
        canonicalPromotedAnimalexicMeaning
    ; sensoryReceipt =
        canonicalEvolvedSensoryTransportReceipt
    ; sensoryWitness =
        canonicalEvolvedSensoryTransportPipelineWitness
    ; brainBoundary =
        canonicalBidirectionalBrainObservationBoundary
    ; romSurface =
        canonicalSeaMeInItROMKernelSurfaceForDischarge
    ; romNonPromotion =
        canonicalSeaMeInItNonPromotionCertificateForDischarge
    ; observationSpineNoRecovery =
        canonicalNoRecoveryFlagIsTrue
    ; threadCandidateOnlyCoreAdapter =
        canonicalAnimalSenseCandidateOnlyCoreAdapter
    ; threadCandidateOnlyCoreAdapterReceipt =
        canonicalAnimalSenseCandidateOnlyCoreAdapterReceipt
    ; threadCandidateOnlyCoreAdapterCandidateOnly =
        canonicalAnimalSenseCandidateOnlyAdapterCandidateOnly
    ; threadCandidateOnlyCoreAdapterPromotedFalse =
        canonicalAnimalSenseCandidateOnlyAdapterPromotedFalse
    ; threadCandidateOnlyCoreAdapterTheoremAuthorityFalse =
        canonicalAnimalSenseCandidateOnlyAdapterTheoremAuthorityFalse
    ; threadAuthorityNonPromotionCoreAdapter =
        canonicalAnimalSenseAuthorityNonPromotionCoreAdapter
    ; threadAuthorityNonPromotionCoreAdapterKindsFalse =
        canonicalAnimalSenseAuthorityNonPromotionCoreAdapterKindsFalse
    ; threadAuthorityAdapterScientificAuthorityFalse =
        canonicalAnimalSenseAuthorityAdapterScientificAuthorityFalse
    ; threadAuthorityAdapterEmpiricalAuthorityFalse =
        canonicalAnimalSenseAuthorityAdapterEmpiricalAuthorityFalse
    ; threadAuthorityAdapterPromotesAnyAuthorityFalse =
        canonicalAnimalSenseAuthorityAdapterPromotesAnyAuthorityFalse
    ; threadBridgeRequirementCoreAdapter =
        canonicalAnimalSenseBridgeRequirementCoreAdapter
    ; threadBridgeRequirementCoreAdapterIsCanonical =
        canonicalAnimalSenseBridgeRequirementCoreAdapterIsCanonical
    ; threadBridgeAdapterAuthorityPromotionFalse =
        canonicalAnimalSenseBridgeAdapterAuthorityPromotionFalse
    ; threadBridgeAdapterTransportMapAuthorityFalse =
        canonicalAnimalSenseBridgeAdapterTransportMapAuthorityFalse
    ; threadBridgeAdapterBackgroundBridgeAuthorityFalse =
        canonicalAnimalSenseBridgeAdapterBackgroundBridgeAuthorityFalse
    ; allRequestedSurfacesInhabited = true
    ; allRequestedSurfacesInhabitedIsTrue = refl
    ; allUnsafeRoutesDischarged = true
    ; allUnsafeRoutesDischargedIsTrue = refl
    ; safeSummary =
        "The fetched thread is discharged as observation transport: avian retinal perturbation, genome-sensorimotor development, Animalexic meaning, generalized sensory attractors, brain/body quotient, SeaMeInIt ROM, and the common non-recovery spine are present without qualia, direct dictionary, DNA-meaning, cross-sense identity, or receiptless-promotion claims."
    }
