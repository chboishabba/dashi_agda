module DASHI.Interop.SeaMeInItSeamDerivationFormalism where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)

import UFTC_Lattice as UFTC

open import DASHI.Interop.SeaMeInItROMKernelFormalism
  using
    ( TriGate
    ; gateReject
    ; gateDiagnostic
    ; gateAdmissible
    ; PromotionState
    ; diagnosticOnly
    ; promotedArtifact
    ; promotionFromGates
    ; allAdmissible
    ; BodyCarrier
    ; KernelBasis
    ; ROMOperator
    ; ProjectedField
    ; SeamGraph
    ; SeamCutPanelization
    ; ManufacturingReceipt
    ; SeaMeInItROMKernelSurface
    )

------------------------------------------------------------------------
-- ROM as an admissible derivation language
------------------------------------------------------------------------

data ROMAdmissibility : Set where
  romRejected : ROMAdmissibility
  romUnresolved : ROMAdmissibility
  romPromoted : ROMAdmissibility

romAdmissibilityGate : ROMAdmissibility → TriGate
romAdmissibilityGate romRejected = gateReject
romAdmissibilityGate romUnresolved = gateDiagnostic
romAdmissibilityGate romPromoted = gateAdmissible

record ROMCarrier : Set₁ where
  field
    Body : Set
    MotionToken : Set
    Derivation : Set
    Pose : Set
    SurfaceField : Set
    PrefixWitness : Derivation → Derivation → Set

    realizePose : Derivation → Pose
    projectField : Derivation → SurfaceField
    derivationHash : Derivation → String
    sourceReceipt : String

open ROMCarrier public

record MotionTokenReceipt (rom : ROMCarrier) : Set₁ where
  field
    token : ROMCarrier.MotionToken rom
    generator : String
    region : String
    directionBin : Nat
    amplitudeBin : Nat
    phase : String
    loadContext : Maybe String
    tokenGate : TriGate

open MotionTokenReceipt public

record ROMBlocker : Set where
  field
    code : String
    severity : UFTC.Severity
    region : String
    cause : String
    unpaidObligation : String
    suggestedDischarge : String

open ROMBlocker public

record ROMPDA (rom : ROMCarrier) : Set₁ where
  field
    accept :
      ROMCarrier.Derivation rom →
      ROMAdmissibility
    costPDA : Nat
    blockerLog :
      ROMCarrier.Derivation rom →
      List ROMBlocker
    pdaReceipt : String

open ROMPDA public

record ROMCouplingDebt (rom : ROMCarrier) : Set₁ where
  field
    Cocycle : Set
    debt :
      ROMCarrier.Derivation rom →
      Cocycle
    discharge : Cocycle → Set
    debtSeverity : Cocycle → UFTC.Severity
    debtGate :
      ROMCarrier.Derivation rom →
      TriGate
    couplingReceipt : String

open ROMCouplingDebt public

record ROMUltrametric (rom : ROMCarrier) : Set₁ where
  field
    dROM :
      ROMCarrier.Derivation rom →
      ROMCarrier.Derivation rom →
      Nat
    agreementDepth :
      ROMCarrier.Derivation rom →
      ROMCarrier.Derivation rom →
      Nat
    idZero :
      (γ : ROMCarrier.Derivation rom) →
      dROM γ γ ≡ 0
    symmetric :
      (γ η : ROMCarrier.Derivation rom) →
      dROM γ η ≡ dROM η γ
    ultrametricWitness : Set

open ROMUltrametric public

record ROMKernelBodyMap
    (body : BodyCarrier)
    (basis : KernelBasis body)
    (rom : ROMCarrier) : Set₁ where
  field
    Coeff : Set
    encodeROM :
      ROMCarrier.Derivation rom →
      Coeff
    fieldMap :
      Coeff →
      ROMCarrier.SurfaceField rom
    basisCarrier : KernelBasis body
    coefficientGate : TriGate
    projectionReceipt : String

open ROMKernelBodyMap public

------------------------------------------------------------------------
-- Fabric, seam state, and design admissibility feedback
------------------------------------------------------------------------

data FabricationMethod : Set where
  homeSewing : FabricationMethod
  overlock : FabricationMethod
  flatlock : FabricationMethod
  bonded : FabricationMethod
  welded : FabricationMethod
  laserCut : FabricationMethod
  threeDKnit : FabricationMethod
  variableKnit : FabricationMethod

record FabricCarrier : Set₁ where
  field
    FabricProfile : Set
    profile : FabricProfile
    fabricationMethod : FabricationMethod
    userAccessible : Bool
    fabricCarrierGate : TriGate
    fabricHash : String

open FabricCarrier public

record SeamState (body : BodyCarrier) (graph : SeamGraph body) : Set₁ where
  field
    selectedEdges : List (SeamGraph.Edge graph)
    seamStateHash : String
    seamStateGate : TriGate

open SeamState public

record ROMDesignAdmissibility
    (rom : ROMCarrier)
    (fabric : FabricCarrier)
    (body : BodyCarrier)
    (graph : SeamGraph body) : Set₁ where
  field
    acceptDesign :
      ROMCarrier.Derivation rom →
      FabricCarrier.FabricProfile fabric →
      SeamState body graph →
      ROMAdmissibility
    seamDebtGate :
      ROMCarrier.Derivation rom →
      SeamState body graph →
      TriGate
    designReceipt : String

open ROMDesignAdmissibility public

record SeamFeedbackOperator
    (body : BodyCarrier)
    (basis : KernelBasis body)
    (romOp : ROMOperator body basis)
    (graph : SeamGraph body) : Set₁ where
  field
    FieldCoeff : Set
    seamState :
      SeamState body graph
    applySeamOperator :
      FieldCoeff →
      FieldCoeff
    attenuatesAcrossCutEdges : TriGate
    reinforcesAlongSeams : TriGate
    allowsPanelDiscontinuity : TriGate
    feedbackStabilityGate : TriGate
    feedbackReceipt : String

open SeamFeedbackOperator public

------------------------------------------------------------------------
-- Seam costs, panel residuals, and shaping as metric correction
------------------------------------------------------------------------

data EdgeAdmissibility : Set where
  edgeForbidden : EdgeAdmissibility
  edgeRisky : EdgeAdmissibility
  edgePreferred : EdgeAdmissibility

edgeGate : EdgeAdmissibility → TriGate
edgeGate edgeForbidden = gateReject
edgeGate edgeRisky = gateDiagnostic
edgeGate edgePreferred = gateAdmissible

record SeamCostWitness (body : BodyCarrier) (graph : SeamGraph body) : Set₁ where
  field
    EdgeCost : Set
    naturalBoundaryReward :
      SeamGraph.Edge graph →
      EdgeCost
    riskPenalty :
      SeamGraph.Edge graph →
      EdgeCost
    manufacturingPenalty :
      SeamGraph.Edge graph →
      EdgeCost
    uncertaintyPenalty :
      SeamGraph.Edge graph →
      EdgeCost
    admissibility :
      SeamGraph.Edge graph →
      EdgeAdmissibility
    forbiddenMeansNoPromotion :
      (edge : SeamGraph.Edge graph) →
      admissibility edge ≡ edgeForbidden →
      Set
    seamCostReceipt : String

open SeamCostWitness public

record PanelMetricResidual
    (body : BodyCarrier)
    (graph : SeamGraph body)
    (panelization : SeamCutPanelization body graph) : Set₁ where
  field
    Residual : Set
    panel :
      SeamCutPanelization.Panel panelization
    areaResidual : Residual
    angleResidual : Residual
    shearResidual : Residual
    boundaryResidual : Residual
    grainResidual : Residual
    flatteningFoldoversZero : Bool
    residualGate : TriGate
    residualReceipt : String

open PanelMetricResidual public

data ShapingOperatorKind : Set where
  dart : ShapingOperatorKind
  doubleDart : ShapingOperatorKind
  ease : ShapingOperatorKind
  gather : ShapingOperatorKind
  pleat : ShapingOperatorKind
  gusset : ShapingOperatorKind
  reliefCut : ShapingOperatorKind
  splitPanel : ShapingOperatorKind
  stretchPanel : ShapingOperatorKind
  biasCut : ShapingOperatorKind
  variableKnitCorrection : ShapingOperatorKind

data FinishedSeamNonClaim : Set where
  exportIsNotGeometryTruth : FinishedSeamNonClaim
  noFinishedSeamGlobalOptimum : FinishedSeamNonClaim
  noFinishedSeamIsometry : FinishedSeamNonClaim
  noFinishedSeamTrueInverse : FinishedSeamNonClaim
  noUngatedManufacturingAuthority : FinishedSeamNonClaim
  noProductionPromotionWithoutGate : FinishedSeamNonClaim

record MetricCorrectionOperator : Set₁ where
  field
    SupportRegion : Set
    CorrectionTensor : Set
    kind : ShapingOperatorKind
    supportRegion : SupportRegion
    apexOrAnchor : Maybe String
    orientationSector6 : Nat
    magnitude : Nat
    termination : Maybe String
    correctionTensor : CorrectionTensor
    manufacturingCost : Nat
    comfortCost : Nat
    accessCost : Nat
    metricGain : Nat
    descriptionLengthDelta : Nat
    promotedByMDL :
      descriptionLengthDelta ≤ metricGain
    correctionGate : TriGate
    correctionReceipt : String

open MetricCorrectionOperator public

record SeamAllowanceField
    (body : BodyCarrier)
    (graph : SeamGraph body)
    (panelization : SeamCutPanelization body graph) : Set₁ where
  field
    BoundaryPoint : Set
    Allowance : Set
    panel :
      SeamCutPanelization.Panel panelization
    allowanceAt :
      BoundaryPoint →
      Allowance
    adaptsToFabrication : TriGate
    adaptsAroundDarts : TriGate
    asymmetricLoadAllowed : Bool
    allowanceReceipt : String

open SeamAllowanceField public

------------------------------------------------------------------------
-- Finished seam / pattern receipt
------------------------------------------------------------------------

record SeamReceipt
    (body : BodyCarrier)
    (graph : SeamGraph body)
    (panelization : SeamCutPanelization body graph) : Set₁ where
  field
    selectedEdgePath : List (SeamGraph.Edge graph)
    adjacentPanels : List (SeamCutPanelization.Panel panelization)
    seamType : String
    allowanceLeftHash : String
    allowanceRightHash : String
    riskPercentileOverROM : Nat
    supportBoundaryScore : Nat
    grainAlignmentScore : Nat
    promotionReason : String
    seamReceiptHash : String

open SeamReceipt public

record ShapingReceipt
    (body : BodyCarrier)
    (graph : SeamGraph body)
    (panelization : SeamCutPanelization body graph) : Set₁ where
  field
    panel :
      SeamCutPanelization.Panel panelization
    operator :
      MetricCorrectionOperator
    residualBeforeHash : String
    residualAfterHash : String
    mdlGain : Nat
    manufacturingMethodRequired : FabricationMethod
    shapingReceiptHash : String

open ShapingReceipt public

record FinishedSeamReceipt
    (body : BodyCarrier)
    (basis : KernelBasis body)
    (romOp : ROMOperator body basis)
    (graph : SeamGraph body)
    (panelization : SeamCutPanelization body graph) : Set₁ where
  field
    inputHashes : List String
    bodyReceiptHash : String
    romReceiptHash : String
    fabricReceiptHash : String
    basisReceiptHash : String
    seamCostFieldHash : String
    seamAtlasHash : String
    panelAtlasHash : String

    selectedSeams :
      List (SeamReceipt body graph panelization)
    panelResiduals :
      List (PanelMetricResidual body graph panelization)
    shapingOps :
      List (ShapingReceipt body graph panelization)
    seamAllowances :
      List (SeamAllowanceField body graph panelization)
    manufacturing :
      ManufacturingReceipt body graph panelization

    bodyGate : TriGate
    romGate : TriGate
    fabricGate : TriGate
    basisGate : TriGate
    seamGraphGate : TriGate
    panelTopologyGate : TriGate
    flatteningGate : TriGate
    metricCorrectionGate : TriGate
    allowanceGate : TriGate
    manufacturingGate : TriGate
    claimBoundaryGate : TriGate

    severityReport : UFTC.Code
    blockerLog : List ROMBlocker
    manufacturingExportHashes : List String
    claimBoundary : List FinishedSeamNonClaim
    finishedReceiptHash : String
    plainReading : String

  strictPatternGates : List TriGate
  strictPatternGates =
    bodyGate
    ∷ romGate
    ∷ fabricGate
    ∷ basisGate
    ∷ seamGraphGate
    ∷ panelTopologyGate
    ∷ flatteningGate
    ∷ metricCorrectionGate
    ∷ allowanceGate
    ∷ manufacturingGate
    ∷ claimBoundaryGate
    ∷ []

  patternPromotionState : PromotionState
  patternPromotionState =
    promotionFromGates strictPatternGates

open FinishedSeamReceipt public

record FinishedSeamReceiptSoundBoundary
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    (receipt : FinishedSeamReceipt body basis romOp graph panelization)
    : Set₁ where
  field
    hasInputHashes : Set
    hasBodyGate : Set
    hasROMGate : Set
    hasFabricGate : Set
    hasBasisGate : Set
    hasSeamAtlas : Set
    hasPanelAtlas : Set
    hasFlatteningMetrics : Set
    hasCorrectionOps : Set
    hasAllowanceField : Set
    hasManufacturingOut : Set
    hasSeverityReport : Set
    hasBlockerLog : Set

    noGeometryTruthClaim : Set
    noGlobalOptimumClaim : Set
    noIsometryClaim : Set
    noTrueInverseClaim : Set
    noUngatedManufacturingAuthorityClaim : Set
    noProductionPromotionWithoutGateClaim : Set

    bodyGateMatchesReceipt :
      bodyGate receipt ≡ bodyGate receipt
    romGateMatchesReceipt :
      romGate receipt ≡ romGate receipt
    fabricGateMatchesReceipt :
      fabricGate receipt ≡ fabricGate receipt
    basisGateMatchesReceipt :
      basisGate receipt ≡ basisGate receipt
    seamAtlasHashAvailable :
      seamAtlasHash receipt ≡ seamAtlasHash receipt
    panelAtlasHashAvailable :
      panelAtlasHash receipt ≡ panelAtlasHash receipt

open FinishedSeamReceiptSoundBoundary public

record FinishedPatternPromoted
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    (receipt : FinishedSeamReceipt body basis romOp graph panelization)
    : Set₁ where
  field
    stateIsPromoted :
      patternPromotionState receipt ≡ promotedArtifact
    allGatesClear :
      allAdmissible (strictPatternGates receipt) ≡ true
    soundBoundary :
      FinishedSeamReceiptSoundBoundary receipt
    noSeverityMasking : Set
    noManufacturingClaimWithoutReceipt : Set

open FinishedPatternPromoted public

record SeamDerivationOrderWitness
    {body : BodyCarrier}
    {basis : KernelBasis body}
    {romOp : ROMOperator body basis}
    {graph : SeamGraph body}
    {panelization : SeamCutPanelization body graph}
    (receipt : FinishedSeamReceipt body basis romOp graph panelization)
    : Set₁ where
  field
    inputToBodyCarrier : String
    bodyToProjectedFields : List (ProjectedField body basis romOp)
    fieldsToSeamCosts : SeamCostWitness body graph
    seamsToPanelTopology : SeamCutPanelization body graph
    panelsToFlatteningResiduals :
      List (PanelMetricResidual body graph panelization)
    residualsToMetricCorrections :
      List (ShapingReceipt body graph panelization)
    correctionsToAllowances :
      List (SeamAllowanceField body graph panelization)
    allowancesToFinishedReceipt :
      FinishedSeamReceipt body basis romOp graph panelization
    sameFinishedReceipt :
      allowancesToFinishedReceipt ≡ receipt

open SeamDerivationOrderWitness public

record SeaMeInItSeamDerivationSurface : Set₁ where
  field
    baseSurface : SeaMeInItROMKernelSurface
    RomCarrierObject : Set
    SeamStateObject : Set
    MetricCorrectionObject : Set
    FinishedReceiptObject : Set

    romIsDerivationLanguage : Set
    posesAreProjectionOnly : Set
    seamsFeedBackIntoROMAdmissibility : Set
    dartsEaseGussetsSplitsAreMetricCorrections : Set
    flatteningIsDownstreamOfPanelTopology : Set
    noPatternPromotionWithoutAllGates : Set

    plainReading : String

open SeaMeInItSeamDerivationSurface public
