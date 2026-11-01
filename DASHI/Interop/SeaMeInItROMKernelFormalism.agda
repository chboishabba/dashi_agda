module DASHI.Interop.SeaMeInItROMKernelFormalism where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Tri-valued admissibility
------------------------------------------------------------------------

data TriGate : Set where
  gateReject : TriGate
  gateDiagnostic : TriGate
  gateAdmissible : TriGate

data PromotionState : Set where
  diagnosticOnly : PromotionState
  promotedArtifact : PromotionState

gateAnd : TriGate → TriGate → TriGate
gateAnd gateReject _ = gateReject
gateAnd gateDiagnostic gateReject = gateReject
gateAnd gateDiagnostic _ = gateDiagnostic
gateAnd gateAdmissible b = b

gateAnd-idem : (g : TriGate) → gateAnd g g ≡ g
gateAnd-idem gateReject = refl
gateAnd-idem gateDiagnostic = refl
gateAnd-idem gateAdmissible = refl

gateAnd-reject-left : (g : TriGate) → gateAnd gateReject g ≡ gateReject
gateAnd-reject-left g = refl

gateAnd-admissible-left : (g : TriGate) → gateAnd gateAdmissible g ≡ g
gateAnd-admissible-left g = refl

allAdmissible : List TriGate → Bool
allAdmissible [] = true
allAdmissible (gateAdmissible ∷ rest) = allAdmissible rest
allAdmissible (_ ∷ rest) = false

promotionFromGates : List TriGate → PromotionState
promotionFromGates gates with allAdmissible gates
... | true = promotedArtifact
... | false = diagnosticOnly

------------------------------------------------------------------------
-- Carrier and ROM kernel vocabulary
------------------------------------------------------------------------

data FieldKind : Set where
  tensionField : FieldKind
  pressureField : FieldKind
  shearField : FieldKind
  supportField : FieldKind

data CompressionKind : Set where
  hypervoxel : CompressionKind
  hypersheet : CompressionKind

data ClaimBoundary : Set where
  engineeringReceiptModelOnly : ClaimBoundary
  noExternalPipelineValidationClaim : ClaimBoundary
  noTrueInverseDeformationClaim : ClaimBoundary
  noRendererMorphologyClaim : ClaimBoundary
  noManufacturingSafetyClaim : ClaimBoundary

record BodyCarrier : Set₁ where
  field
    Vertex : Set
    Face : Set
    RegionMask : Set
    ForbiddenZone : Set
    Atlas : Set

    vertices : List Vertex
    faces : List Face
    atlas : Atlas
    regionMasks : List RegionMask
    forbiddenZones : List ForbiddenZone
    bodyReceipt : String

open BodyCarrier public

record KernelBasis (body : BodyCarrier) : Set₁ where
  field
    BasisComponent : Set
    CoefficientVector : Set
    FieldValue : Set

    components : List BasisComponent
    basisVector : BasisComponent → Vertex body → FieldValue
    coefficientLengthMatchesComponents : TriGate
    vertexSetMatchesBody : TriGate
    areaWeightedOrthonormalReceipt : TriGate
    basisReceipt : String

open KernelBasis public

record ROMOperator (body : BodyCarrier) (basis : KernelBasis body) : Set₁ where
  field
    Pose : Set
    Parameter : Set
    DerivationToken : Set
    DerivationStream : Set

    tokenGate : DerivationToken → TriGate
    streamGate : DerivationStream → TriGate
    decode : DerivationStream → Pose
    validPose : Pose → TriGate
    projectPose : Pose → CoefficientVector basis
    encodePose : Pose → DerivationStream
    romReceipt : String

open ROMOperator public

record CouplingCocycle : Set₁ where
  field
    Demand : Set
    Response : Set
    Debt : Set

    demand : Demand
    response : Response
    delta : Demand → Response → Debt
    obligationProjection : Debt → TriGate
    debtGate : TriGate
    blockingDebt : Bool
    couplingReceipt : String

open CouplingCocycle public

record ProjectedField
    (body : BodyCarrier)
    (basis : KernelBasis body)
    (rom : ROMOperator body basis) : Set₁ where
  field
    Task : Set
    Fabric : Set
    ProjectedValue : Set

    fieldKind : FieldKind
    coefficientFor :
      Task →
      Fabric →
      Pose rom →
      CoefficientVector basis
    reconstruct :
      CoefficientVector basis →
      Vertex body →
      ProjectedValue
    fieldGate : TriGate
    romAggregationReceipt : String

open ProjectedField public

record SeamGraph (body : BodyCarrier) : Set₁ where
  field
    Node : Set
    Edge : Set
    EdgeCost : Set

    nodes : List Node
    edges : List Edge
    endpointA : Edge → Node
    endpointB : Edge → Node
    seamOK : Edge → TriGate
    edgeCost : Edge → EdgeCost
    topologyReceipt : String

open SeamGraph public

record SeamCutPanelization
    (body : BodyCarrier)
    (graph : SeamGraph body) : Set₁ where
  field
    SeamCut : Set
    Panel : Set

    cutEdges : SeamCut → List (Edge graph)
    panels : SeamCut → List Panel
    cutGate : SeamCut → TriGate
    panelGate : Panel → TriGate
    panelUnwrapReceipt : String

open SeamCutPanelization public

record CompressionCell
    (body : BodyCarrier)
    (basis : KernelBasis body)
    (rom : ROMOperator body basis) : Set₁ where
  field
    PoseRegion : Set
    ConstraintStack : Set
    BoundaryResidual : Set

    kind : CompressionKind
    poseRegion : PoseRegion
    admissibilityStack : ConstraintStack
    equivalentUnderStack : PoseRegion → PoseRegion → Set
    boundaryResidual : PoseRegion → BoundaryResidual
    needsFineGraining : PoseRegion → Bool
    compressionReceipt : String

open CompressionCell public

record ManufacturingReceipt
    (body : BodyCarrier)
    (graph : SeamGraph body)
    (panelization : SeamCutPanelization body graph) : Set₁ where
  field
    ManufacturingArtifact : Set
    selectedCut : SeamCut panelization
    artifact : ManufacturingArtifact
    panelExportGate : TriGate
    manufacturingGate : TriGate
    manufacturingReceipt : String

open ManufacturingReceipt public

------------------------------------------------------------------------
-- Global SeaMeInIt / ROM kernel receipt surface
------------------------------------------------------------------------

record SeaMeInItROMKernelSurface : Set₁ where
  field
    body : BodyCarrier
    basis : KernelBasis body
    rom : ROMOperator body basis
    couplings : List CouplingCocycle
    projectedFields :
      List (ProjectedField body basis rom)
    seamGraph : SeamGraph body
    panelization : SeamCutPanelization body seamGraph
    compressionCells : List (CompressionCell body basis rom)
    manufacturing : ManufacturingReceipt body seamGraph panelization

    carrierGate : TriGate
    basisGate : TriGate
    romGate : TriGate
    couplingGate : TriGate
    seamCostGate : TriGate
    topologyGate : TriGate
    panelizationGate : TriGate
    solverDomainGate : TriGate
    manufacturingReceiptGate : TriGate

    nonPromotionBoundary : List ClaimBoundary
    plainReading : String

  strictPromotionGates : List TriGate
  strictPromotionGates =
    carrierGate
    ∷ basisGate
    ∷ romGate
    ∷ couplingGate
    ∷ seamCostGate
    ∷ topologyGate
    ∷ panelizationGate
    ∷ solverDomainGate
    ∷ manufacturingReceiptGate
    ∷ []

  promotionState : PromotionState
  promotionState = promotionFromGates strictPromotionGates

open SeaMeInItROMKernelSurface public

record PipelineOrderWitness
    (surface : SeaMeInItROMKernelSurface) : Set₁ where
  field
    carrierToBasis : BodyCarrier
    basisToROM : KernelBasis carrierToBasis
    romToFields : ROMOperator carrierToBasis basisToROM
    fieldsToSeams : SeamGraph carrierToBasis
    seamsToPanels : SeamCutPanelization carrierToBasis fieldsToSeams
    panelsToManufacturing :
      ManufacturingReceipt carrierToBasis fieldsToSeams seamsToPanels
    sameBody : carrierToBasis ≡ body surface

open PipelineOrderWitness public

record NonPromotionCertificate
    (surface : SeaMeInItROMKernelSurface) : Set where
  field
    stateIsDiagnosticOnly : promotionState surface ≡ diagnosticOnly
    reason : String

open NonPromotionCertificate public

record PromotionCertificate
    (surface : SeaMeInItROMKernelSurface) : Set where
  field
    stateIsPromoted : promotionState surface ≡ promotedArtifact
    allGatesClear : allAdmissible (strictPromotionGates surface) ≡ true
    externalValidationReceipt : String

open PromotionCertificate public
