module DASHI.Physics.Closure.NSCollapseQMovingBoundaryTransportIdentityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Q(t) moving-boundary transport identity receipt.
--
-- This module records the Reynolds transport bookkeeping for a quantity
-- Q(t) defined on the moving boundary surface partial Omega_K(t).  The
-- receipt names the transport identity itself, the normal-velocity and
-- Jacobian correction, the tangential divergence term, the advective flux,
-- the boundary regularity prerequisites, the target bound dQ/dt <= C Q,
-- and the open geometric constants that still block a closed estimate.
--
-- The receipt is fail-closed: QGronwall stays false and Clay stays false.

data NSCollapseQMovingBoundaryTransportIdentityStatus : Set where
  qMovingBoundaryTransportIdentityRecorded_noPromotion :
    NSCollapseQMovingBoundaryTransportIdentityStatus

canonicalNSCollapseQMovingBoundaryTransportIdentityStatus :
  NSCollapseQMovingBoundaryTransportIdentityStatus
canonicalNSCollapseQMovingBoundaryTransportIdentityStatus =
  qMovingBoundaryTransportIdentityRecorded_noPromotion

data NSCollapseQMovingBoundaryTransportIdentityStage : Set where
  qFunctionalOnMovingBoundaryRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  reynoldsTransportOnPartialOmegaRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  normalVelocityAndJacobianCorrectionRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  tangentialDivergenceRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  advectiveFluxRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  boundaryRegularityPrerequisitesRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  openGeometricConstantsRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  targetBoundByCQRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  qGronwallFailClosedRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

  clayFailClosedRecorded :
    NSCollapseQMovingBoundaryTransportIdentityStage

canonicalNSCollapseQMovingBoundaryTransportIdentityStages :
  List NSCollapseQMovingBoundaryTransportIdentityStage
canonicalNSCollapseQMovingBoundaryTransportIdentityStages =
  qFunctionalOnMovingBoundaryRecorded
  ∷ reynoldsTransportOnPartialOmegaRecorded
  ∷ normalVelocityAndJacobianCorrectionRecorded
  ∷ tangentialDivergenceRecorded
  ∷ advectiveFluxRecorded
  ∷ boundaryRegularityPrerequisitesRecorded
  ∷ openGeometricConstantsRecorded
  ∷ targetBoundByCQRecorded
  ∷ qGronwallFailClosedRecorded
  ∷ clayFailClosedRecorded
  ∷ []

data NSCollapseQMovingBoundaryTransportIdentityTerm : Set where
  qDensityTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  reynoldsTransportSurfaceTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  normalVelocityJacobianTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  tangentialDivergenceTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  advectiveFluxTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  boundaryRegularityPrerequisitesTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  openGeometricConstantsTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  targetBoundByCQTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  qGronwallFailClosedTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

  clayFailClosedTerm :
    NSCollapseQMovingBoundaryTransportIdentityTerm

canonicalNSCollapseQMovingBoundaryTransportIdentityTerms :
  List NSCollapseQMovingBoundaryTransportIdentityTerm
canonicalNSCollapseQMovingBoundaryTransportIdentityTerms =
  qDensityTerm
  ∷ reynoldsTransportSurfaceTerm
  ∷ normalVelocityJacobianTerm
  ∷ tangentialDivergenceTerm
  ∷ advectiveFluxTerm
  ∷ boundaryRegularityPrerequisitesTerm
  ∷ openGeometricConstantsTerm
  ∷ targetBoundByCQTerm
  ∷ qGronwallFailClosedTerm
  ∷ clayFailClosedTerm
  ∷ []

data NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite :
  Set where
  movingBoundaryChartIsRegularEnoughForTransport :
    NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite

  boundaryNormalTraceIsAvailable :
    NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite

  surfaceMeasureDifferentiationIsAdmissible :
    NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite

  tangentialDifferentiationIsLegitimate :
    NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite

  advectiveFluxIsIntegrableOnTheBoundary :
    NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite

  traceTheoremInputIsAvailable :
    NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite

canonicalNSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisites :
  List NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite
canonicalNSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisites =
  movingBoundaryChartIsRegularEnoughForTransport
  ∷ boundaryNormalTraceIsAvailable
  ∷ surfaceMeasureDifferentiationIsAdmissible
  ∷ tangentialDifferentiationIsLegitimate
  ∷ advectiveFluxIsIntegrableOnTheBoundary
  ∷ traceTheoremInputIsAvailable
  ∷ []

data NSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstant : Set where
  boundarySpeedConstant :
    NSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstant

  jacobianCorrectionConstant :
    NSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstant

  tangentialGeometryConstant :
    NSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstant

  transportExtensionConstant :
    NSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstant

canonicalNSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstants :
  List NSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstant
canonicalNSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstants =
  boundarySpeedConstant
  ∷ jacobianCorrectionConstant
  ∷ tangentialGeometryConstant
  ∷ transportExtensionConstant
  ∷ []

data NSCollapseQMovingBoundaryTransportIdentityBlocker : Set where
  boundaryRegularityConstantsStillOpen :
    NSCollapseQMovingBoundaryTransportIdentityBlocker

  geometricConstantsNotFixed :
    NSCollapseQMovingBoundaryTransportIdentityBlocker

  sharpBoundaryEstimateNotClosed :
    NSCollapseQMovingBoundaryTransportIdentityBlocker

  qGronwallAbsorptionNotProved :
    NSCollapseQMovingBoundaryTransportIdentityBlocker

  clayPromotionUnavailable :
    NSCollapseQMovingBoundaryTransportIdentityBlocker

canonicalNSCollapseQMovingBoundaryTransportIdentityBlockers :
  List NSCollapseQMovingBoundaryTransportIdentityBlocker
canonicalNSCollapseQMovingBoundaryTransportIdentityBlockers =
  boundaryRegularityConstantsStillOpen
  ∷ geometricConstantsNotFixed
  ∷ sharpBoundaryEstimateNotClosed
  ∷ qGronwallAbsorptionNotProved
  ∷ clayPromotionUnavailable
  ∷ []

record NSCollapseQMovingBoundaryTransportIdentityLedgerCounts : Set where
  field
    stageCount :
      Nat

    termCount :
      Nat

    boundaryRegularityPrerequisiteCount :
      Nat

    openGeometryConstantCount :
      Nat

    blockerCount :
      Nat

open NSCollapseQMovingBoundaryTransportIdentityLedgerCounts public

canonicalNSCollapseQMovingBoundaryTransportIdentityLedgerCounts :
  NSCollapseQMovingBoundaryTransportIdentityLedgerCounts
canonicalNSCollapseQMovingBoundaryTransportIdentityLedgerCounts = record
  { stageCount = 10
  ; termCount = 10
  ; boundaryRegularityPrerequisiteCount = 6
  ; openGeometryConstantCount = 4
  ; blockerCount = 5
  }

data NSCollapseQMovingBoundaryTransportIdentityPromotion : Set where

nsCollapseQMovingBoundaryTransportIdentityPromotionImpossibleHere :
  NSCollapseQMovingBoundaryTransportIdentityPromotion →
  ⊥
nsCollapseQMovingBoundaryTransportIdentityPromotionImpossibleHere ()

transportIdentityText : String
transportIdentityText =
  "Q(t) is recorded on the moving boundary partial Omega_K(t) as a boundary integral that must be differentiated with Reynolds transport."

reynoldsTransportText : String
reynoldsTransportText =
  "Reynolds transport on partial Omega_K(t): d/dt Q(t) expands into the surface time derivative, the moving-boundary normal-velocity/Jacobian correction, the tangential divergence contribution, and the advective flux term."

normalVelocityJacobianText : String
normalVelocityJacobianText =
  "Normal velocity/Jacobian term: the boundary motion contributes a normal-speed factor together with the surface-measure Jacobian correction."

tangentialDivergenceText : String
tangentialDivergenceText =
  "Tangential divergence term: div_tau on the moving surface is tracked separately from the normal transport correction."

advectiveFluxText : String
advectiveFluxText =
  "Advective flux: the boundary advection contribution is named and recorded rather than absorbed into the geometric term."

boundaryRegularityPrerequisitesDescriptionText : String
boundaryRegularityPrerequisitesDescriptionText =
  "Boundary regularity prerequisites: a transport-admissible moving boundary, trace control, tangential differentiation, and integrable boundary flux are required before any estimate can be claimed."

targetBoundByCQText : String
targetBoundByCQText =
  "Target bound: dQ/dt <= C Q, with C treated as a geometric constant placeholder rather than a closed estimate."

openGeometricConstantsText : String
openGeometricConstantsText =
  "Open geometric constants: the boundary-speed, Jacobian, tangential-geometry, and transport-extension constants remain unspecified at the receipt level."

qGronwallText : String
qGronwallText =
  "QGronwall is fail-closed: the receipt records the dQ/dt <= C Q target but does not promote it to a proved Gronwall closure."

clayText : String
clayText =
  "Clay remains false: no Clay Navier-Stokes promotion is attached to this moving-boundary transport receipt."

canonicalNSCollapseQMovingBoundaryTransportIdentityReceiptBoundary : List String
canonicalNSCollapseQMovingBoundaryTransportIdentityReceiptBoundary =
  "Q(t) is tracked as a moving-boundary transport quantity on partial Omega_K(t)"
  ∷ "Reynolds transport is recorded explicitly, including the normal velocity/Jacobian correction"
  ∷ "Tangential divergence and advective flux are separated in the ledger"
  ∷ "Boundary regularity prerequisites are required before the transport identity can support any estimate"
  ∷ "The target bound dQ/dt <= C Q is recorded, but C is not fixed here"
  ∷ "Open geometric constants remain open"
  ∷ "QGronwall stays false"
  ∷ "Clay stays false"
  ∷ []

record NSCollapseQMovingBoundaryTransportIdentityReceipt : Setω where
  field
    status :
      NSCollapseQMovingBoundaryTransportIdentityStatus

    statusIsCanonical :
      status ≡ canonicalNSCollapseQMovingBoundaryTransportIdentityStatus

    ledgerCounts :
      NSCollapseQMovingBoundaryTransportIdentityLedgerCounts

    ledgerCountsIsCanonical :
      ledgerCounts ≡ canonicalNSCollapseQMovingBoundaryTransportIdentityLedgerCounts

    stageLedger :
      List NSCollapseQMovingBoundaryTransportIdentityStage

    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSCollapseQMovingBoundaryTransportIdentityStages

    termLedger :
      List NSCollapseQMovingBoundaryTransportIdentityTerm

    termLedgerIsCanonical :
      termLedger ≡ canonicalNSCollapseQMovingBoundaryTransportIdentityTerms

    boundaryRegularityPrerequisites :
      List NSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisite

    boundaryRegularityPrerequisitesIsCanonical :
      boundaryRegularityPrerequisites
      ≡
      canonicalNSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisites

    openGeometryConstants :
      List NSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstant

    openGeometryConstantsIsCanonical :
      openGeometryConstants
      ≡
      canonicalNSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstants

    blockers :
      List NSCollapseQMovingBoundaryTransportIdentityBlocker

    blockersIsCanonical :
      blockers ≡ canonicalNSCollapseQMovingBoundaryTransportIdentityBlockers

    transportIdentity :
      String

    transportIdentityIsCanonical :
      transportIdentity ≡ transportIdentityText

    reynoldsTransportFormula :
      String

    reynoldsTransportFormulaIsCanonical :
      reynoldsTransportFormula ≡ reynoldsTransportText

    normalVelocityJacobianTermText :
      String

    normalVelocityJacobianTermTextIsCanonical :
      normalVelocityJacobianTermText ≡ normalVelocityJacobianText

    tangentialDivergenceTermText :
      String

    tangentialDivergenceTermTextIsCanonical :
      tangentialDivergenceTermText ≡ tangentialDivergenceText

    advectiveFluxTermText :
      String

    advectiveFluxTermTextIsCanonical :
      advectiveFluxTermText ≡ advectiveFluxText

    boundaryRegularityPrerequisitesText :
      String

    boundaryRegularityPrerequisitesTextIsCanonical :
      boundaryRegularityPrerequisitesText ≡ boundaryRegularityPrerequisitesDescriptionText

    targetBoundByCQ :
      String

    targetBoundByCQIsCanonical :
      targetBoundByCQ ≡ targetBoundByCQText

    openGeometricConstantsDescription :
      String

    openGeometricConstantsDescriptionIsCanonical :
      openGeometricConstantsDescription ≡ openGeometricConstantsText

    qGronwall :
      Bool

    qGronwallIsFalse :
      qGronwall ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSCollapseQMovingBoundaryTransportIdentityPromotion

    promotionsAreEmpty :
      promotions ≡ []

    qGronwallTextValue :
      String

    qGronwallTextValueIsCanonical :
      qGronwallTextValue ≡ qGronwallText

    clayTextValue :
      String

    clayTextValueIsCanonical :
      clayTextValue ≡ clayText

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalNSCollapseQMovingBoundaryTransportIdentityReceiptBoundary

open NSCollapseQMovingBoundaryTransportIdentityReceipt public

canonicalNSCollapseQMovingBoundaryTransportIdentityReceipt :
  NSCollapseQMovingBoundaryTransportIdentityReceipt
canonicalNSCollapseQMovingBoundaryTransportIdentityReceipt =
  record
    { status =
        canonicalNSCollapseQMovingBoundaryTransportIdentityStatus
    ; statusIsCanonical =
        refl
    ; ledgerCounts =
        canonicalNSCollapseQMovingBoundaryTransportIdentityLedgerCounts
    ; ledgerCountsIsCanonical =
        refl
    ; stageLedger =
        canonicalNSCollapseQMovingBoundaryTransportIdentityStages
    ; stageLedgerIsCanonical =
        refl
    ; termLedger =
        canonicalNSCollapseQMovingBoundaryTransportIdentityTerms
    ; termLedgerIsCanonical =
        refl
    ; boundaryRegularityPrerequisites =
        canonicalNSCollapseQMovingBoundaryTransportIdentityBoundaryRegularityPrerequisites
    ; boundaryRegularityPrerequisitesIsCanonical =
        refl
    ; openGeometryConstants =
        canonicalNSCollapseQMovingBoundaryTransportIdentityOpenGeometryConstants
    ; openGeometryConstantsIsCanonical =
        refl
    ; blockers =
        canonicalNSCollapseQMovingBoundaryTransportIdentityBlockers
    ; blockersIsCanonical =
        refl
    ; transportIdentity =
        transportIdentityText
    ; transportIdentityIsCanonical =
        refl
    ; reynoldsTransportFormula =
        reynoldsTransportText
    ; reynoldsTransportFormulaIsCanonical =
        refl
    ; normalVelocityJacobianTermText =
        normalVelocityJacobianText
    ; normalVelocityJacobianTermTextIsCanonical =
        refl
    ; tangentialDivergenceTermText =
        tangentialDivergenceText
    ; tangentialDivergenceTermTextIsCanonical =
        refl
    ; advectiveFluxTermText =
        advectiveFluxText
    ; advectiveFluxTermTextIsCanonical =
        refl
    ; boundaryRegularityPrerequisitesText =
        boundaryRegularityPrerequisitesDescriptionText
    ; boundaryRegularityPrerequisitesTextIsCanonical =
        refl
    ; targetBoundByCQ =
        targetBoundByCQText
    ; targetBoundByCQIsCanonical =
        refl
    ; openGeometricConstantsDescription =
        openGeometricConstantsText
    ; openGeometricConstantsDescriptionIsCanonical =
        refl
    ; qGronwall =
        false
    ; qGronwallIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; qGronwallTextValue =
        qGronwallText
    ; qGronwallTextValueIsCanonical =
        refl
    ; clayTextValue =
        clayText
    ; clayTextValueIsCanonical =
        refl
    ; receiptBoundary =
        canonicalNSCollapseQMovingBoundaryTransportIdentityReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

nsCollapseQMovingBoundaryTransportIdentityKeepsQGronwallFalse :
  qGronwall canonicalNSCollapseQMovingBoundaryTransportIdentityReceipt ≡ false
nsCollapseQMovingBoundaryTransportIdentityKeepsQGronwallFalse =
  refl

nsCollapseQMovingBoundaryTransportIdentityKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSCollapseQMovingBoundaryTransportIdentityReceipt
  ≡
  false
nsCollapseQMovingBoundaryTransportIdentityKeepsClayFalse =
  refl
