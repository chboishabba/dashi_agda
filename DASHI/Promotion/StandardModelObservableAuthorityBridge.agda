module DASHI.Promotion.StandardModelObservableAuthorityBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; Setω)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Standard Model observable authority bridge.
--
-- This module formalizes the non-promoting bridge from finite Standard Model
-- bookkeeping to physical observable prediction packages.  It records the
-- required QFT, detector, covariance, holdout, and public authority rows that
-- must be inhabited before any QFT observable, empirical validation, or
-- terminal unification guard can flip.

listCount : {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

appendRows : {a : Level} {A : Set a} → List A → List A → List A
appendRows [] ys = ys
appendRows (x ∷ xs) ys = x ∷ appendRows xs ys

------------------------------------------------------------------------
-- Bridge taxonomy.

data BridgeStage : Set where
  finiteSMBookkeepingStage : BridgeStage
  lagrangianNormalizationStage : BridgeStage
  qftConstructionStage : BridgeStage
  renormalizationPrescriptionStage : BridgeStage
  scatteringAmplitudeStage : BridgeStage
  crossSectionStage : BridgeStage
  decayRateStage : BridgeStage
  detectorUnfoldingStage : BridgeStage
  covarianceStage : BridgeStage
  holdoutStage : BridgeStage
  publicAuthorityStage : BridgeStage
  comparisonLawStage : BridgeStage

data ObservablePredictionKind : Set where
  finiteRepresentationBookkeeping : ObservablePredictionKind
  normalizedLagrangianInput : ObservablePredictionKind
  qftConstructedStateSpace : ObservablePredictionKind
  renormalizedParameterScheme : ObservablePredictionKind
  matrixElementAmplitude : ObservablePredictionKind
  differentialCrossSection : ObservablePredictionKind
  inclusiveCrossSection : ObservablePredictionKind
  partialDecayRate : ObservablePredictionKind
  unfoldedDetectorObservable : ObservablePredictionKind
  covarianceAwareResidual : ObservablePredictionKind
  holdoutValidationObservable : ObservablePredictionKind
  authorityIndexedObservable : ObservablePredictionKind

data AuthoritySource : Set where
  internalFiniteSMSource : AuthoritySource
  pdgAuthoritySource : AuthoritySource
  atlasAuthoritySource : AuthoritySource
  cmsAuthoritySource : AuthoritySource
  hepDataAuthoritySource : AuthoritySource
  runtimeReplayAuthoritySource : AuthoritySource
  comparisonLawAuthoritySource : AuthoritySource
  terminalClaimAuthoritySource : AuthoritySource

authoritySourceLabel : AuthoritySource → String
authoritySourceLabel internalFiniteSMSource =
  "internal finite SM bookkeeping"
authoritySourceLabel pdgAuthoritySource =
  "PDG"
authoritySourceLabel atlasAuthoritySource =
  "ATLAS"
authoritySourceLabel cmsAuthoritySource =
  "CMS"
authoritySourceLabel hepDataAuthoritySource =
  "HEPData"
authoritySourceLabel runtimeReplayAuthoritySource =
  "runtime replay"
authoritySourceLabel comparisonLawAuthoritySource =
  "comparison law"
authoritySourceLabel terminalClaimAuthoritySource =
  "terminal claim"

data ObservablePromotionGuard : Set where
  qftObservablePromotionGuard : ObservablePromotionGuard
  empiricalValidationGuard : ObservablePromotionGuard
  terminalUnificationGuard : ObservablePromotionGuard

data BridgeRowStatus : Set where
  finiteBookkeepingAvailable : BridgeRowStatus
  proofRequired : BridgeRowStatus
  authorityRequired : BridgeRowStatus
  runtimeReplayRequired : BridgeRowStatus
  validationRequired : BridgeRowStatus
  blockedByUpstreamGuard : BridgeRowStatus

record ObservableAuthorityBridgeRow : Set₁ where
  field
    rowLabel : String
    bridgeStage : BridgeStage
    predictionKind : ObservablePredictionKind
    authoritySource : AuthoritySource
    authorityLabel : String
    authorityLabelIsCanonical :
      authorityLabel ≡ authoritySourceLabel authoritySource
    upstreamModuleNames : List String
    requiredReceipts : List String
    physicalContent : List String
    currentGaps : List String
    rowStatus : BridgeRowStatus
    guardToFlip : ObservablePromotionGuard
    validationCommand : String
    finiteBookkeepingOnly : Bool
    finiteBookkeepingOnlyIsTrue :
      finiteBookkeepingOnly ≡ true
    qftObservablePromoted : Bool
    qftObservablePromotedIsFalse :
      qftObservablePromoted ≡ false
    empiricalValidationPromoted : Bool
    empiricalValidationPromotedIsFalse :
      empiricalValidationPromoted ≡ false
    terminalUnificationPromoted : Bool
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false

open ObservableAuthorityBridgeRow public

mkBridgeRow :
  String →
  BridgeStage →
  ObservablePredictionKind →
  AuthoritySource →
  List String →
  List String →
  List String →
  List String →
  BridgeRowStatus →
  ObservablePromotionGuard →
  String →
  ObservableAuthorityBridgeRow
mkBridgeRow label stage kind authority upstream required content gaps status guard
  validation =
  record
    { rowLabel = label
    ; bridgeStage = stage
    ; predictionKind = kind
    ; authoritySource = authority
    ; authorityLabel = authoritySourceLabel authority
    ; authorityLabelIsCanonical = refl
    ; upstreamModuleNames = upstream
    ; requiredReceipts = required
    ; physicalContent = content
    ; currentGaps = gaps
    ; rowStatus = status
    ; guardToFlip = guard
    ; validationCommand = validation
    ; finiteBookkeepingOnly = true
    ; finiteBookkeepingOnlyIsTrue = refl
    ; qftObservablePromoted = false
    ; qftObservablePromotedIsFalse = refl
    ; empiricalValidationPromoted = false
    ; empiricalValidationPromotedIsFalse = refl
    ; terminalUnificationPromoted = false
    ; terminalUnificationPromotedIsFalse = refl
    }

------------------------------------------------------------------------
-- Canonical finite-to-prediction rows.

finiteSMBookkeepingRow : ObservableAuthorityBridgeRow
finiteSMBookkeepingRow =
  mkBridgeRow
    "finite SM bookkeeping"
    finiteSMBookkeepingStage
    finiteRepresentationBookkeeping
    internalFiniteSMSource
    ( "DASHI.Promotion.StandardModelFiniteRepresentationNarrowing"
    ∷ "DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck"
    ∷ "DASHI.Promotion.StandardModelTerminalObligations"
    ∷ []
    )
    ( "finite gauge-name rows"
    ∷ "one-generation representation target rows"
    ∷ "anomaly and hypercharge bookkeeping rows"
    ∷ []
    )
    ( "SU3c/SU2L/U1Y names"
    ∷ "finite chiral matter labels"
    ∷ "finite hypercharge convention candidates"
    ∷ []
    )
    ( "finite rows are not a physical Lagrangian"
    ∷ "continuous representation theorem remains absent"
    ∷ []
    )
    finiteBookkeepingAvailable
    qftObservablePromotionGuard
    "agda -i . -l standard-library DASHI/Promotion/StandardModelFiniteRepresentationNarrowing.agda"

lagrangianNormalizationRow : ObservableAuthorityBridgeRow
lagrangianNormalizationRow =
  mkBridgeRow
    "Lagrangian normalization"
    lagrangianNormalizationStage
    normalizedLagrangianInput
    pdgAuthoritySource
    ( "DASHI.Constants.Registry"
    ∷ "DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization"
    ∷ []
    )
    ( "field normalization convention"
    ∷ "gauge coupling normalization"
    ∷ "Yukawa and CKM/PMNS parameter convention"
    ∷ "mass and width input scheme"
    ∷ []
    )
    ( "canonically normalized SM Lagrangian"
    ∷ "PDG-bound numerical inputs"
    ∷ "unit and uncertainty policy"
    ∷ []
    )
    ( "measured constants are authority-gated"
    ∷ "finite content does not fix physical normalization"
    ∷ []
    )
    authorityRequired
    qftObservablePromotionGuard
    "agda -i . -l standard-library DASHI/Constants/Registry.agda"

qftConstructionRow : ObservableAuthorityBridgeRow
qftConstructionRow =
  mkBridgeRow
    "QFT construction"
    qftConstructionStage
    qftConstructedStateSpace
    internalFiniteSMSource
    ( "DASHI.Promotion.QuantumQFTObligations"
    ∷ "DASHI.Promotion.FiniteQuantumQFTScopedClosure"
    ∷ "DASHI.Physics.QFT.ExactSMMatchToken"
    ∷ []
    )
    ( "field algebra or path-integral construction"
    ∷ "state space and domain prescription"
    ∷ "gauge fixing and ghost convention where required"
    ∷ "unitarity and causality boundary"
    ∷ []
    )
    ( "constructive QFT surface for the normalized SM input"
    ∷ "observable algebra and state preparation interface"
    ∷ []
    )
    ( "finite bookkeeping is not a QFT construction"
    ∷ "exact SM match and DHR-to-SM bridge remain blocked"
    ∷ []
    )
    proofRequired
    qftObservablePromotionGuard
    "agda -i . -l standard-library DASHI/Promotion/QuantumQFTObligations.agda"

renormalizationPrescriptionRow : ObservableAuthorityBridgeRow
renormalizationPrescriptionRow =
  mkBridgeRow
    "renormalization prescription"
    renormalizationPrescriptionStage
    renormalizedParameterScheme
    pdgAuthoritySource
    ( "DASHI.Physics.Closure.RGObservableInvariance"
    ∷ "DASHI.Promotion.NumericAndAuthorityObligations"
    ∷ []
    )
    ( "scheme choice such as MSbar or on-shell"
    ∷ "scale-setting law"
    ∷ "counterterm and running-coupling convention"
    ∷ "uncertainty propagation rule"
    ∷ []
    )
    ( "renormalized SM parameters"
    ∷ "scale-dependent prediction interface"
    ∷ []
    )
    ( "renormalization scheme is not derivable from finite rows"
    ∷ "PDG numeric authority remains unaccepted"
    ∷ []
    )
    authorityRequired
    qftObservablePromotionGuard
    "agda -i . -l standard-library DASHI/Physics/Closure/RGObservableInvariance.agda"

scatteringAmplitudeRow : ObservableAuthorityBridgeRow
scatteringAmplitudeRow =
  mkBridgeRow
    "scattering amplitude"
    scatteringAmplitudeStage
    matrixElementAmplitude
    runtimeReplayAuthoritySource
    ( "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    ∷ "DASHI.Physics.Closure.ObservablePredictionPackage"
    ∷ []
    )
    ( "external-state convention"
    ∷ "matrix element definition"
    ∷ "loop/order prescription"
    ∷ "runtime replay digest for amplitude generation"
    ∷ []
    )
    ( "SM matrix element amplitude"
    ∷ "replayable amplitude artifact"
    ∷ []
    )
    ( "amplitude generator receipt is absent"
    ∷ "runtime replay authority remains false"
    ∷ []
    )
    runtimeReplayRequired
    qftObservablePromotionGuard
    "agda -i . -l standard-library DASHI/Promotion/EmpiricalRuntimeReplayAdapter.agda"

crossSectionRow : ObservableAuthorityBridgeRow
crossSectionRow =
  mkBridgeRow
    "cross section"
    crossSectionStage
    differentialCrossSection
    hepDataAuthoritySource
    ( "DASHI.Physics.Closure.HEPDataObservableDefinitionReceipt"
    ∷ "DASHI.Physics.Closure.HEPDataComparisonAuthorityRouteDiagnostic"
    ∷ "DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter"
    ∷ []
    )
    ( "phase-space convention"
    ∷ "PDF and luminosity convention where applicable"
    ∷ "fiducial or inclusive selection"
    ∷ "binning and units"
    ∷ []
    )
    ( "differential or inclusive cross-section prediction"
    ∷ "observable bins comparable to public data"
    ∷ []
    )
    ( "HEPData observable authority is not accepted"
    ∷ "luminosity and PDF conventions need external receipts"
    ∷ []
    )
    authorityRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Physics/Closure/HEPDataObservableDefinitionReceipt.agda"

decayRateRow : ObservableAuthorityBridgeRow
decayRateRow =
  mkBridgeRow
    "decay rate"
    decayRateStage
    partialDecayRate
    pdgAuthoritySource
    ( "DASHI.Physics.Closure.PenguinDecayObservableContract"
    ∷ "DASHI.Physics.Closure.PenguinDecaySMBaselineAuthority"
    ∷ []
    )
    ( "initial-state normalization"
    ∷ "phase-space integral"
    ∷ "branching-ratio or partial-width convention"
    ∷ "lifetime and mass authority receipt"
    ∷ []
    )
    ( "SM decay-rate prediction"
    ∷ "PDG-comparable branching or width observable"
    ∷ []
    )
    ( "decay authority row is process-specific"
    ∷ "PDG lifetimes, masses, and correlations remain authority-gated"
    ∷ []
    )
    authorityRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Physics/Closure/PenguinDecayObservableContract.agda"

detectorUnfoldingRow : ObservableAuthorityBridgeRow
detectorUnfoldingRow =
  mkBridgeRow
    "detector unfolding"
    detectorUnfoldingStage
    unfoldedDetectorObservable
    atlasAuthoritySource
    ( "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    ∷ "DASHI.Physics.Closure.HEPDataEmpiricalResidualBridgeCore"
    ∷ []
    )
    ( "response matrix or unfolding prescription"
    ∷ "fiducial object definition"
    ∷ "efficiency and acceptance policy"
    ∷ "detector-level to particle-level map"
    ∷ []
    )
    ( "unfolded ATLAS-compatible observable"
    ∷ "detector-response-aware projection digest"
    ∷ []
    )
    ( "detector response is an external collaboration authority item"
    ∷ "unfolding replay and checksum are absent"
    ∷ []
    )
    authorityRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Physics/Closure/HEPDataEmpiricalResidualBridgeCore.agda"

covarianceRow : ObservableAuthorityBridgeRow
covarianceRow =
  mkBridgeRow
    "covariance"
    covarianceStage
    covarianceAwareResidual
    cmsAuthoritySource
    ( "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    ∷ "DASHI.Physics.Closure.HEPDataResidualComparisonLawRequest"
    ∷ "DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter"
    ∷ []
    )
    ( "statistical covariance"
    ∷ "systematic covariance"
    ∷ "normalization uncertainty convention"
    ∷ "bin-to-bin correlation matrix"
    ∷ []
    )
    ( "covariance-aware residual"
    ∷ "chi-square or likelihood comparison payload"
    ∷ []
    )
    ( "covariance authority token is not accepted"
    ∷ "shape, units, and correlations remain parsed-only obligations"
    ∷ []
    )
    validationRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Promotion/EmpiricalRuntimeReplayAdapter.agda"

holdoutRow : ObservableAuthorityBridgeRow
holdoutRow =
  mkBridgeRow
    "holdout"
    holdoutStage
    holdoutValidationObservable
    runtimeReplayAuthoritySource
    ( "DASHI.Promotion.EmpiricalReplayAcceptanceCriteria"
    ∷ "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    ∷ []
    )
    ( "frozen training source"
    ∷ "independent holdout source"
    ∷ "predeclared pass/fail criterion"
    ∷ "replayable validation run"
    ∷ []
    )
    ( "holdout validation protocol"
    ∷ "non-inspected validation artifact"
    ∷ []
    )
    ( "holdout acceptance is false"
    ∷ "semantic adequacy review and aggregate empirical adequacy are absent"
    ∷ []
    )
    validationRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Promotion/EmpiricalReplayAcceptanceCriteria.agda"

pdgAuthorityRow : ObservableAuthorityBridgeRow
pdgAuthorityRow =
  mkBridgeRow
    "PDG authority"
    publicAuthorityStage
    authorityIndexedObservable
    pdgAuthoritySource
    ( "DASHI.Constants.Registry"
    ∷ "DASHI.Promotion.NumericAuthorityTokenIntake"
    ∷ []
    )
    ( "versioned PDG source"
    ∷ "source checksum"
    ∷ "access date"
    ∷ "rounding and uncertainty policy"
    ∷ []
    )
    ( "public particle-property authority payload"
    ∷ "mass, width, branching, mixing, and coupling inputs"
    ∷ []
    )
    ( "accepted PDG authority token is absent"
    ∷ "numeric values cannot be promoted from placeholders"
    ∷ []
    )
    authorityRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Promotion/NumericAuthorityTokenIntake.agda"

atlasAuthorityRow : ObservableAuthorityBridgeRow
atlasAuthorityRow =
  mkBridgeRow
    "ATLAS authority"
    publicAuthorityStage
    authorityIndexedObservable
    atlasAuthoritySource
    ( "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    ∷ "DASHI.Physics.Closure.HEPDataEmpiricalAuthorityReceiptCollation"
    ∷ "DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter"
    ∷ []
    )
    ( "ATLAS publication identifier"
    ∷ "analysis and detector object definitions"
    ∷ "unfolding and covariance source"
    ∷ "checksum-bound public table"
    ∷ []
    )
    ( "ATLAS public measurement authority payload"
    ∷ "collaboration-specific systematic model"
    ∷ []
    )
    ( "ATLAS token is not accepted"
    ∷ "collaboration source must be bound before empirical validation"
    ∷ []
    )
    authorityRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Physics/Closure/HEPDataEmpiricalAuthorityReceiptCollation.agda"

cmsAuthorityRow : ObservableAuthorityBridgeRow
cmsAuthorityRow =
  mkBridgeRow
    "CMS authority"
    publicAuthorityStage
    authorityIndexedObservable
    cmsAuthoritySource
    ( "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    ∷ "DASHI.Physics.Closure.HEPDataCMSSMP20003ExternalSourceAuthorityReceipt"
    ∷ []
    )
    ( "CMS publication identifier"
    ∷ "analysis and detector object definitions"
    ∷ "unfolding and covariance source"
    ∷ "checksum-bound public table"
    ∷ []
    )
    ( "CMS public measurement authority payload"
    ∷ "collaboration-specific systematic model"
    ∷ []
    )
    ( "CMS token is not accepted"
    ∷ "external source authority remains diagnostic-only"
    ∷ []
    )
    authorityRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Physics/Closure/HEPDataCMSSMP20003ExternalSourceAuthorityReceipt.agda"

hepDataAuthorityRow : ObservableAuthorityBridgeRow
hepDataAuthorityRow =
  mkBridgeRow
    "HEPData authority"
    publicAuthorityStage
    authorityIndexedObservable
    hepDataAuthoritySource
    ( "DASHI.Physics.Closure.HEPDataObservableSchema"
    ∷ "DASHI.Physics.Closure.HEPDataObservableDefinitionReceipt"
    ∷ "DASHI.Physics.Closure.HEPDataEmpiricalResidualBridgeCore"
    ∷ "DASHI.Promotion.StandardModelHiggsHEPDataReceiptAdapter"
    ∷ []
    )
    ( "HEPData record identifier"
    ∷ "table path and version"
    ∷ "observable schema"
    ∷ "checksum-bound payload"
    ∷ []
    )
    ( "HEPData-indexed observable definition"
    ∷ "public table compatible with comparison law"
    ∷ []
    )
    ( "HEPData provider receipt is not constructed"
    ∷ "source selection remains authority-gated"
    ∷ []
    )
    authorityRequired
    empiricalValidationGuard
    "agda -i . -l standard-library DASHI/Physics/Closure/HEPDataObservableSchema.agda"

comparisonLawRow : ObservableAuthorityBridgeRow
comparisonLawRow =
  mkBridgeRow
    "comparison law"
    comparisonLawStage
    covarianceAwareResidual
    comparisonLawAuthoritySource
    ( "DASHI.Physics.Closure.HEPDataComparisonLawReceiptRequest"
    ∷ "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
    ∷ []
    )
    ( "left prediction digest"
    ∷ "right measurement digest"
    ∷ "metric and tolerance policy"
    ∷ "covariance and holdout consumption"
    ∷ []
    )
    ( "lawful prediction-versus-measurement comparison"
    ∷ "fail-closed empirical validation verdict"
    ∷ []
    )
    ( "comparison law accepted flag is false"
    ∷ "empirical adequacy cannot be inferred from digest equality alone"
    ∷ []
    )
    validationRequired
    terminalUnificationGuard
    "agda -i . -l standard-library DASHI/Promotion/EmpiricalRuntimeReplayAdapter.agda"

canonicalObservableAuthorityBridgeRows : List ObservableAuthorityBridgeRow
canonicalObservableAuthorityBridgeRows =
  finiteSMBookkeepingRow
  ∷ lagrangianNormalizationRow
  ∷ qftConstructionRow
  ∷ renormalizationPrescriptionRow
  ∷ scatteringAmplitudeRow
  ∷ crossSectionRow
  ∷ decayRateRow
  ∷ detectorUnfoldingRow
  ∷ covarianceRow
  ∷ holdoutRow
  ∷ pdgAuthorityRow
  ∷ atlasAuthorityRow
  ∷ cmsAuthorityRow
  ∷ hepDataAuthorityRow
  ∷ comparisonLawRow
  ∷ []

canonicalQFTObservableRows : List ObservableAuthorityBridgeRow
canonicalQFTObservableRows =
  finiteSMBookkeepingRow
  ∷ lagrangianNormalizationRow
  ∷ qftConstructionRow
  ∷ renormalizationPrescriptionRow
  ∷ scatteringAmplitudeRow
  ∷ []

canonicalEmpiricalValidationRows : List ObservableAuthorityBridgeRow
canonicalEmpiricalValidationRows =
  crossSectionRow
  ∷ decayRateRow
  ∷ detectorUnfoldingRow
  ∷ covarianceRow
  ∷ holdoutRow
  ∷ pdgAuthorityRow
  ∷ atlasAuthorityRow
  ∷ cmsAuthorityRow
  ∷ hepDataAuthorityRow
  ∷ []

canonicalTerminalComparisonRows : List ObservableAuthorityBridgeRow
canonicalTerminalComparisonRows =
  comparisonLawRow
  ∷ []

canonicalRecomposedBridgeRows : List ObservableAuthorityBridgeRow
canonicalRecomposedBridgeRows =
  appendRows
    canonicalQFTObservableRows
    (appendRows
      canonicalEmpiricalValidationRows
      canonicalTerminalComparisonRows)

canonicalBridgeRowCount : Nat
canonicalBridgeRowCount = listCount canonicalObservableAuthorityBridgeRows

canonicalQFTObservableRowCount : Nat
canonicalQFTObservableRowCount = listCount canonicalQFTObservableRows

canonicalEmpiricalValidationRowCount : Nat
canonicalEmpiricalValidationRowCount =
  listCount canonicalEmpiricalValidationRows

canonicalTerminalComparisonRowCount : Nat
canonicalTerminalComparisonRowCount =
  listCount canonicalTerminalComparisonRows

canonicalBridgeRowCountIsFifteen :
  canonicalBridgeRowCount ≡ 15
canonicalBridgeRowCountIsFifteen = refl

canonicalQFTObservableRowCountIsFive :
  canonicalQFTObservableRowCount ≡ 5
canonicalQFTObservableRowCountIsFive = refl

canonicalEmpiricalValidationRowCountIsNine :
  canonicalEmpiricalValidationRowCount ≡ 9
canonicalEmpiricalValidationRowCountIsNine = refl

canonicalTerminalComparisonRowCountIsOne :
  canonicalTerminalComparisonRowCount ≡ 1
canonicalTerminalComparisonRowCountIsOne = refl

canonicalRecomposedBridgeRowsCountMatches :
  listCount canonicalRecomposedBridgeRows ≡ canonicalBridgeRowCount
canonicalRecomposedBridgeRowsCountMatches = refl

------------------------------------------------------------------------
-- Guard surface.

data GuardInput : Set where
  finiteRepresentationInput : GuardInput
  lagrangianNormalizationInput : GuardInput
  qftConstructionInput : GuardInput
  renormalizationInput : GuardInput
  amplitudeInput : GuardInput
  crossSectionInput : GuardInput
  decayRateInput : GuardInput
  unfoldingInput : GuardInput
  covarianceInput : GuardInput
  holdoutInput : GuardInput
  pdgAuthorityInput : GuardInput
  atlasAuthorityInput : GuardInput
  cmsAuthorityInput : GuardInput
  hepDataAuthorityInput : GuardInput
  comparisonLawInput : GuardInput

record PromotionGuardStatus : Set₁ where
  field
    guardLabel : String
    guard : ObservablePromotionGuard
    requiredInputs : List GuardInput
    guardInputCount : Nat
    guardInputCountMatches :
      guardInputCount ≡ listCount requiredInputs
    blockingRows : List ObservableAuthorityBridgeRow
    blockingRowCount : Nat
    blockingRowCountMatches :
      blockingRowCount ≡ listCount blockingRows
    promoted : Bool
    promotedIsFalse :
      promoted ≡ false
    falseReason : String

open PromotionGuardStatus public

qftObservablePromotionGuardStatus : PromotionGuardStatus
qftObservablePromotionGuardStatus =
  record
    { guardLabel = "QFT observable promotion"
    ; guard = qftObservablePromotionGuard
    ; requiredInputs =
        finiteRepresentationInput
        ∷ lagrangianNormalizationInput
        ∷ qftConstructionInput
        ∷ renormalizationInput
        ∷ amplitudeInput
        ∷ []
    ; guardInputCount = 5
    ; guardInputCountMatches = refl
    ; blockingRows = canonicalQFTObservableRows
    ; blockingRowCount = canonicalQFTObservableRowCount
    ; blockingRowCountMatches = refl
    ; promoted = false
    ; promotedIsFalse = refl
    ; falseReason =
        "finite bookkeeping lacks normalized Lagrangian, QFT construction, renormalization, and amplitude authority receipts"
    }

empiricalValidationGuardStatus : PromotionGuardStatus
empiricalValidationGuardStatus =
  record
    { guardLabel = "empirical validation"
    ; guard = empiricalValidationGuard
    ; requiredInputs =
        crossSectionInput
        ∷ decayRateInput
        ∷ unfoldingInput
        ∷ covarianceInput
        ∷ holdoutInput
        ∷ pdgAuthorityInput
        ∷ atlasAuthorityInput
        ∷ cmsAuthorityInput
        ∷ hepDataAuthorityInput
        ∷ []
    ; guardInputCount = 9
    ; guardInputCountMatches = refl
    ; blockingRows = canonicalEmpiricalValidationRows
    ; blockingRowCount = canonicalEmpiricalValidationRowCount
    ; blockingRowCountMatches = refl
    ; promoted = false
    ; promotedIsFalse = refl
    ; falseReason =
        "comparison-ready public measurement, covariance, unfolding, and holdout authority are not accepted"
    }

terminalUnificationGuardStatus : PromotionGuardStatus
terminalUnificationGuardStatus =
  record
    { guardLabel = "terminal unification"
    ; guard = terminalUnificationGuard
    ; requiredInputs =
        finiteRepresentationInput
        ∷ lagrangianNormalizationInput
        ∷ qftConstructionInput
        ∷ renormalizationInput
        ∷ amplitudeInput
        ∷ crossSectionInput
        ∷ decayRateInput
        ∷ unfoldingInput
        ∷ covarianceInput
        ∷ holdoutInput
        ∷ pdgAuthorityInput
        ∷ atlasAuthorityInput
        ∷ cmsAuthorityInput
        ∷ hepDataAuthorityInput
        ∷ comparisonLawInput
        ∷ []
    ; guardInputCount = 15
    ; guardInputCountMatches = refl
    ; blockingRows = canonicalObservableAuthorityBridgeRows
    ; blockingRowCount = canonicalBridgeRowCount
    ; blockingRowCountMatches = refl
    ; promoted = false
    ; promotedIsFalse = refl
    ; falseReason =
        "terminal unification cannot consume empirical observables while QFT observable and empirical validation guards remain false"
    }

canonicalPromotionGuardStatuses : List PromotionGuardStatus
canonicalPromotionGuardStatuses =
  qftObservablePromotionGuardStatus
  ∷ empiricalValidationGuardStatus
  ∷ terminalUnificationGuardStatus
  ∷ []

canonicalPromotionGuardStatusCount : Nat
canonicalPromotionGuardStatusCount =
  listCount canonicalPromotionGuardStatuses

canonicalPromotionGuardStatusCountIsThree :
  canonicalPromotionGuardStatusCount ≡ 3
canonicalPromotionGuardStatusCountIsThree = refl

------------------------------------------------------------------------
-- Terminal receipt.

record StandardModelObservableAuthorityBridgeReceipt : Setω where
  field
    receiptLabel : String
    finiteSMModuleNames : List String
    empiricalRuntimeModuleNames : List String
    publicAuthorityModuleNames : List String
    bridgeRows : List ObservableAuthorityBridgeRow
    bridgeRowCount : Nat
    bridgeRowCountMatches :
      bridgeRowCount ≡ listCount bridgeRows
    qftObservableRows : List ObservableAuthorityBridgeRow
    qftObservableRowCount : Nat
    qftObservableRowCountMatches :
      qftObservableRowCount ≡ listCount qftObservableRows
    empiricalValidationRows : List ObservableAuthorityBridgeRow
    empiricalValidationRowCount : Nat
    empiricalValidationRowCountMatches :
      empiricalValidationRowCount ≡ listCount empiricalValidationRows
    terminalComparisonRows : List ObservableAuthorityBridgeRow
    terminalComparisonRowCount : Nat
    terminalComparisonRowCountMatches :
      terminalComparisonRowCount ≡ listCount terminalComparisonRows
    guardStatuses : List PromotionGuardStatus
    guardStatusCount : Nat
    guardStatusCountMatches :
      guardStatusCount ≡ listCount guardStatuses
    qftObservablePromoted : Bool
    qftObservablePromotedIsFalse :
      qftObservablePromoted ≡ false
    empiricalValidationPromoted : Bool
    empiricalValidationPromotedIsFalse :
      empiricalValidationPromoted ≡ false
    terminalUnificationPromoted : Bool
    terminalUnificationPromotedIsFalse :
      terminalUnificationPromoted ≡ false
    comparisonLawAccepted : Bool
    comparisonLawAcceptedIsFalse :
      comparisonLawAccepted ≡ false
    bridgeBoundary : List String

open StandardModelObservableAuthorityBridgeReceipt public

canonicalStandardModelObservableAuthorityBridgeReceipt :
  StandardModelObservableAuthorityBridgeReceipt
canonicalStandardModelObservableAuthorityBridgeReceipt =
  record
    { receiptLabel =
        "canonical Standard Model observable authority bridge"
    ; finiteSMModuleNames =
        "DASHI.Promotion.StandardModelFiniteRepresentationNarrowing"
        ∷ "DASHI.Promotion.StandardModelFiniteAnomalyHyperchargeCheck"
        ∷ "DASHI.Promotion.StandardModelTerminalObligations"
        ∷ []
    ; empiricalRuntimeModuleNames =
        "DASHI.Promotion.EmpiricalRuntimeReplayAdapter"
        ∷ "DASHI.Promotion.EmpiricalReplayAcceptanceCriteria"
        ∷ "DASHI.Physics.Closure.HEPDataEmpiricalResidualBridgeCore"
        ∷ []
    ; publicAuthorityModuleNames =
        "DASHI.Constants.Registry"
        ∷ "DASHI.Physics.Closure.HEPDataObservableSchema"
        ∷ "DASHI.Physics.Closure.HEPDataObservableDefinitionReceipt"
        ∷ "DASHI.Physics.Closure.HEPDataEmpiricalAuthorityReceiptCollation"
        ∷ "DASHI.Physics.Closure.HEPDataCMSSMP20003ExternalSourceAuthorityReceipt"
        ∷ []
    ; bridgeRows =
        canonicalObservableAuthorityBridgeRows
    ; bridgeRowCount =
        canonicalBridgeRowCount
    ; bridgeRowCountMatches =
        refl
    ; qftObservableRows =
        canonicalQFTObservableRows
    ; qftObservableRowCount =
        canonicalQFTObservableRowCount
    ; qftObservableRowCountMatches =
        refl
    ; empiricalValidationRows =
        canonicalEmpiricalValidationRows
    ; empiricalValidationRowCount =
        canonicalEmpiricalValidationRowCount
    ; empiricalValidationRowCountMatches =
        refl
    ; terminalComparisonRows =
        canonicalTerminalComparisonRows
    ; terminalComparisonRowCount =
        canonicalTerminalComparisonRowCount
    ; terminalComparisonRowCountMatches =
        refl
    ; guardStatuses =
        canonicalPromotionGuardStatuses
    ; guardStatusCount =
        canonicalPromotionGuardStatusCount
    ; guardStatusCountMatches =
        refl
    ; qftObservablePromoted =
        false
    ; qftObservablePromotedIsFalse =
        refl
    ; empiricalValidationPromoted =
        false
    ; empiricalValidationPromotedIsFalse =
        refl
    ; terminalUnificationPromoted =
        false
    ; terminalUnificationPromotedIsFalse =
        refl
    ; comparisonLawAccepted =
        false
    ; comparisonLawAcceptedIsFalse =
        refl
    ; bridgeBoundary =
        "this receipt records obligations and canonical rows only"
        ∷ "it does not construct a normalized Standard Model Lagrangian"
        ∷ "it does not construct a QFT, renormalized amplitude, cross section, or decay rate"
        ∷ "it does not accept PDG, ATLAS, CMS, or HEPData authority tokens"
        ∷ "it does not accept covariance, holdout, comparison, empirical validation, or terminal unification"
        ∷ []
    }

receiptBridgeRowCountIsFifteen :
  bridgeRowCount canonicalStandardModelObservableAuthorityBridgeReceipt ≡ 15
receiptBridgeRowCountIsFifteen = refl

receiptGuardStatusCountIsThree :
  guardStatusCount canonicalStandardModelObservableAuthorityBridgeReceipt ≡ 3
receiptGuardStatusCountIsThree = refl

receiptQFTObservablePromotionIsFalse :
  qftObservablePromoted canonicalStandardModelObservableAuthorityBridgeReceipt
  ≡
  false
receiptQFTObservablePromotionIsFalse = refl

receiptEmpiricalValidationPromotionIsFalse :
  empiricalValidationPromoted canonicalStandardModelObservableAuthorityBridgeReceipt
  ≡
  false
receiptEmpiricalValidationPromotionIsFalse = refl

receiptTerminalUnificationPromotionIsFalse :
  terminalUnificationPromoted canonicalStandardModelObservableAuthorityBridgeReceipt
  ≡
  false
receiptTerminalUnificationPromotionIsFalse = refl
