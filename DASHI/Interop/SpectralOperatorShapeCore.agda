module DASHI.Interop.SpectralOperatorShapeCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable spectral/Hodge/operator shape core.
--
-- This module is intentionally independent of the concrete PNF graph and
-- Hodge topology modules.  It only records finite symbolic cell references,
-- operator tags, signed-weight/co-ordinate kinds, and receipt gates.  The
-- signed residual Laplacian is the first implementable layer; higher Hodge
-- layers remain diagnostic-only and fail-closed.

data CellDimension : Set where
  zeroCellDimension : CellDimension
  oneCellDimension : CellDimension
  twoCellDimension : CellDimension

data ZeroCellRef : Set where
  zeroCellRef : Nat → ZeroCellRef
  zeroCellFallback : ZeroCellRef

data OneCellRef : Set where
  oneCellRef : Nat → OneCellRef
  residualOneCellFallback : OneCellRef
  transportOneCellFallback : OneCellRef
  oneCellFallback : OneCellRef

data TwoCellRef : Set where
  twoCellRef : Nat → TwoCellRef
  triangleTwoCellFallback : TwoCellRef
  twoCellFallback : TwoCellRef

data OperatorTag : Set where
  signedResidualLaplacianOperator :
    OperatorTag

  hodgeBoundaryOperator :
    OperatorTag

  hodgeDiagnosticOperator :
    OperatorTag

  spectralCoordinateOperator :
    OperatorTag

data LaplacianKind : Set where
  signedResidualGraphLaplacian0 :
    LaplacianKind

  hodgeLaplacian1Diagnostic :
    LaplacianKind

  hodgeLaplacian2Diagnostic :
    LaplacianKind

data SignedWeightKind : Set where
  unsignedResidualWeight :
    SignedWeightKind

  positiveResidualWeight :
    SignedWeightKind

  negativeContradictionWeight :
    SignedWeightKind

  diagnosticSignedIncidenceWeight :
    SignedWeightKind

data SpectralCoordinateKind : Set where
  residualSeverityCoordinate :
    SpectralCoordinateKind

  signedFrustrationCoordinate :
    SpectralCoordinateKind

  hodgeCycleDiagnosticCoordinate :
    SpectralCoordinateKind

  hodgeCavityDiagnosticCoordinate :
    SpectralCoordinateKind

data DiagnosticGate : Set where
  implementableSignedResidualGate :
    DiagnosticGate

  diagnosticOnlyFailClosedGate :
    DiagnosticGate

------------------------------------------------------------------------
-- Canonical shape functions.

operatorTagForLaplacian :
  LaplacianKind →
  OperatorTag
operatorTagForLaplacian signedResidualGraphLaplacian0 =
  signedResidualLaplacianOperator
operatorTagForLaplacian hodgeLaplacian1Diagnostic =
  hodgeDiagnosticOperator
operatorTagForLaplacian hodgeLaplacian2Diagnostic =
  hodgeDiagnosticOperator

cellDimensionForLaplacian :
  LaplacianKind →
  CellDimension
cellDimensionForLaplacian signedResidualGraphLaplacian0 =
  zeroCellDimension
cellDimensionForLaplacian hodgeLaplacian1Diagnostic =
  oneCellDimension
cellDimensionForLaplacian hodgeLaplacian2Diagnostic =
  twoCellDimension

signedWeightKindForLaplacian :
  LaplacianKind →
  SignedWeightKind
signedWeightKindForLaplacian signedResidualGraphLaplacian0 =
  negativeContradictionWeight
signedWeightKindForLaplacian hodgeLaplacian1Diagnostic =
  diagnosticSignedIncidenceWeight
signedWeightKindForLaplacian hodgeLaplacian2Diagnostic =
  diagnosticSignedIncidenceWeight

spectralCoordinateKindForLaplacian :
  LaplacianKind →
  SpectralCoordinateKind
spectralCoordinateKindForLaplacian signedResidualGraphLaplacian0 =
  signedFrustrationCoordinate
spectralCoordinateKindForLaplacian hodgeLaplacian1Diagnostic =
  hodgeCycleDiagnosticCoordinate
spectralCoordinateKindForLaplacian hodgeLaplacian2Diagnostic =
  hodgeCavityDiagnosticCoordinate

diagnosticGateForLaplacian :
  LaplacianKind →
  DiagnosticGate
diagnosticGateForLaplacian signedResidualGraphLaplacian0 =
  implementableSignedResidualGate
diagnosticGateForLaplacian hodgeLaplacian1Diagnostic =
  diagnosticOnlyFailClosedGate
diagnosticGateForLaplacian hodgeLaplacian2Diagnostic =
  diagnosticOnlyFailClosedGate

isHigherHodgeDiagnostic :
  LaplacianKind →
  Bool
isHigherHodgeDiagnostic signedResidualGraphLaplacian0 =
  false
isHigherHodgeDiagnostic hodgeLaplacian1Diagnostic =
  true
isHigherHodgeDiagnostic hodgeLaplacian2Diagnostic =
  true

isSignedResidualFirstLayer :
  LaplacianKind →
  Bool
isSignedResidualFirstLayer signedResidualGraphLaplacian0 =
  true
isSignedResidualFirstLayer hodgeLaplacian1Diagnostic =
  false
isSignedResidualFirstLayer hodgeLaplacian2Diagnostic =
  false

canonicalSpectralOperatorShapeStatement :
  String
canonicalSpectralOperatorShapeStatement =
  "Signed residual graph Laplacian is the first implementable finite operator shape; richer Hodge Laplacians are diagnostic-only, fail-closed receipts and grant no semantic, policy, legal, runtime, or continuum authority."

------------------------------------------------------------------------
-- Receipt boundary.

data SpectralOperatorShapePromotion : Set where

spectralOperatorShapePromotionImpossible :
  SpectralOperatorShapePromotion →
  ⊥
spectralOperatorShapePromotionImpossible ()

data SpectralOperatorShapeComponent : Set where
  zeroOneTwoCellReferenceComponent :
    SpectralOperatorShapeComponent

  operatorTagComponent :
    SpectralOperatorShapeComponent

  signedResidualLaplacianFirstComponent :
    SpectralOperatorShapeComponent

  signedWeightKindComponent :
    SpectralOperatorShapeComponent

  spectralCoordinateKindComponent :
    SpectralOperatorShapeComponent

  hodgeDiagnosticFailClosedComponent :
    SpectralOperatorShapeComponent

canonicalSpectralOperatorShapeComponents :
  List SpectralOperatorShapeComponent
canonicalSpectralOperatorShapeComponents =
  zeroOneTwoCellReferenceComponent
  ∷ operatorTagComponent
  ∷ signedResidualLaplacianFirstComponent
  ∷ signedWeightKindComponent
  ∷ spectralCoordinateKindComponent
  ∷ hodgeDiagnosticFailClosedComponent
  ∷ []

record SpectralOperatorShapeReceipt : Set where
  field
    laplacianKind :
      LaplacianKind

    operatorTag :
      OperatorTag

    operatorTagIsCanonical :
      operatorTag ≡ operatorTagForLaplacian laplacianKind

    actsOnCellDimension :
      CellDimension

    actsOnCellDimensionIsCanonical :
      actsOnCellDimension ≡ cellDimensionForLaplacian laplacianKind

    zeroCellReference :
      ZeroCellRef

    oneCellReference :
      OneCellRef

    twoCellReference :
      TwoCellRef

    signedWeightKind :
      SignedWeightKind

    signedWeightKindIsCanonical :
      signedWeightKind ≡ signedWeightKindForLaplacian laplacianKind

    spectralCoordinateKind :
      SpectralCoordinateKind

    spectralCoordinateKindIsCanonical :
      spectralCoordinateKind
      ≡
      spectralCoordinateKindForLaplacian laplacianKind

    signedResidualLaplacianFirst :
      Bool

    signedResidualLaplacianFirstIsCanonical :
      signedResidualLaplacianFirst
      ≡
      isSignedResidualFirstLayer laplacianKind

    diagnosticGate :
      DiagnosticGate

    diagnosticGateIsCanonical :
      diagnosticGate ≡ diagnosticGateForLaplacian laplacianKind

    higherHodgeDiagnosticOnly :
      Bool

    higherHodgeDiagnosticOnlyIsCanonical :
      higherHodgeDiagnosticOnly ≡ isHigherHodgeDiagnostic laplacianKind

    higherHodgeDiagnosticFailClosed :
      Bool

    higherHodgeDiagnosticFailClosedIsTrue :
      higherHodgeDiagnosticFailClosed ≡ true

    higherHodgeDiagnosticGrantsAuthority :
      Bool

    higherHodgeDiagnosticGrantsAuthorityIsFalse :
      higherHodgeDiagnosticGrantsAuthority ≡ false

    semanticTruthPromotion :
      Bool

    semanticTruthPromotionIsFalse :
      semanticTruthPromotion ≡ false

    runtimeEvidencePromotion :
      Bool

    runtimeEvidencePromotionIsFalse :
      runtimeEvidencePromotion ≡ false

    continuumSpectralPromotion :
      Bool

    continuumSpectralPromotionIsFalse :
      continuumSpectralPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ canonicalSpectralOperatorShapeStatement

    components :
      List SpectralOperatorShapeComponent

    componentsAreCanonical :
      components ≡ canonicalSpectralOperatorShapeComponents

    promotionFlags :
      List SpectralOperatorShapePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open SpectralOperatorShapeReceipt public

mkSpectralOperatorShapeReceipt :
  (kind : LaplacianKind) →
  SpectralOperatorShapeReceipt
mkSpectralOperatorShapeReceipt kind =
  record
    { laplacianKind =
        kind
    ; operatorTag =
        operatorTagForLaplacian kind
    ; operatorTagIsCanonical =
        refl
    ; actsOnCellDimension =
        cellDimensionForLaplacian kind
    ; actsOnCellDimensionIsCanonical =
        refl
    ; zeroCellReference =
        zeroCellFallback
    ; oneCellReference =
        oneCellFallback
    ; twoCellReference =
        twoCellFallback
    ; signedWeightKind =
        signedWeightKindForLaplacian kind
    ; signedWeightKindIsCanonical =
        refl
    ; spectralCoordinateKind =
        spectralCoordinateKindForLaplacian kind
    ; spectralCoordinateKindIsCanonical =
        refl
    ; signedResidualLaplacianFirst =
        isSignedResidualFirstLayer kind
    ; signedResidualLaplacianFirstIsCanonical =
        refl
    ; diagnosticGate =
        diagnosticGateForLaplacian kind
    ; diagnosticGateIsCanonical =
        refl
    ; higherHodgeDiagnosticOnly =
        isHigherHodgeDiagnostic kind
    ; higherHodgeDiagnosticOnlyIsCanonical =
        refl
    ; higherHodgeDiagnosticFailClosed =
        true
    ; higherHodgeDiagnosticFailClosedIsTrue =
        refl
    ; higherHodgeDiagnosticGrantsAuthority =
        false
    ; higherHodgeDiagnosticGrantsAuthorityIsFalse =
        refl
    ; semanticTruthPromotion =
        false
    ; semanticTruthPromotionIsFalse =
        refl
    ; runtimeEvidencePromotion =
        false
    ; runtimeEvidencePromotionIsFalse =
        refl
    ; continuumSpectralPromotion =
        false
    ; continuumSpectralPromotionIsFalse =
        refl
    ; statement =
        canonicalSpectralOperatorShapeStatement
    ; statementIsCanonical =
        refl
    ; components =
        canonicalSpectralOperatorShapeComponents
    ; componentsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

canonicalSignedResidualLaplacianReceipt :
  SpectralOperatorShapeReceipt
canonicalSignedResidualLaplacianReceipt =
  mkSpectralOperatorShapeReceipt signedResidualGraphLaplacian0

canonicalHodge1DiagnosticReceipt :
  SpectralOperatorShapeReceipt
canonicalHodge1DiagnosticReceipt =
  mkSpectralOperatorShapeReceipt hodgeLaplacian1Diagnostic

canonicalHodge2DiagnosticReceipt :
  SpectralOperatorShapeReceipt
canonicalHodge2DiagnosticReceipt =
  mkSpectralOperatorShapeReceipt hodgeLaplacian2Diagnostic

canonicalHodgeDiagnosticReceipts :
  List SpectralOperatorShapeReceipt
canonicalHodgeDiagnosticReceipts =
  canonicalHodge1DiagnosticReceipt
  ∷ canonicalHodge2DiagnosticReceipt
  ∷ []

canonicalSignedResidualLaplacianIsFirst :
  signedResidualLaplacianFirst canonicalSignedResidualLaplacianReceipt
  ≡
  true
canonicalSignedResidualLaplacianIsFirst =
  refl

canonicalHodge1DiagnosticIsFailClosed :
  higherHodgeDiagnosticFailClosed canonicalHodge1DiagnosticReceipt
  ≡
  true
canonicalHodge1DiagnosticIsFailClosed =
  refl

canonicalHodge2DiagnosticIsFailClosed :
  higherHodgeDiagnosticFailClosed canonicalHodge2DiagnosticReceipt
  ≡
  true
canonicalHodge2DiagnosticIsFailClosed =
  refl

spectralOperatorShapeGenericReceipt :
  SpectralOperatorShapeReceipt →
  GenericReceipt.GenericReceipt
spectralOperatorShapeGenericReceipt receipt =
  GenericReceipt.mkNonPromotingReceipt
    "spectral operator shape core"
    "DASHI.Interop.SpectralOperatorShapeCore"
    "canonicalSignedResidualLaplacianReceipt"
    (statement receipt)
    "higher Hodge operator shapes remain diagnostic-only and no spectral operator row grants semantic, runtime, continuum, or policy authority"
    "agda -i . DASHI/Interop/SpectralOperatorShapeCore.agda"

canonicalSpectralOperatorShapeGenericReceipts :
  List GenericReceipt.GenericReceipt
canonicalSpectralOperatorShapeGenericReceipts =
  spectralOperatorShapeGenericReceipt canonicalSignedResidualLaplacianReceipt
  ∷ spectralOperatorShapeGenericReceipt canonicalHodge1DiagnosticReceipt
  ∷ spectralOperatorShapeGenericReceipt canonicalHodge2DiagnosticReceipt
  ∷ []

canonicalSpectralOperatorShapeGenericReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting
    canonicalSpectralOperatorShapeGenericReceipts
canonicalSpectralOperatorShapeGenericReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting
    canonicalSpectralOperatorShapeGenericReceipts
