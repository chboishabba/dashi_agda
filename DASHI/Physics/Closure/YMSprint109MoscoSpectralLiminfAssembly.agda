module DASHI.Physics.Closure.YMSprint109MoscoSpectralLiminfAssembly where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMSprint108MoscoNoPollutionBridge
  as Mosco108
import DASHI.Physics.Closure.YMSprint108SpectralGapTransport
  as SpectralTransport108
import DASHI.Physics.Closure.YMSprint108TransferLowerBoundAssembly
  as TransferAssembly108
import DASHI.Physics.Closure.YMSprint108UniformFormLowerBound
  as UniformForm108

------------------------------------------------------------------------
-- Sprint 109 Mosco spectral-liminf assembly.
--
-- This module is the high-level assembly lane for the Sprint109
-- Mosco/spectral-liminf package.  It deliberately imports only stable
-- Sprint108 receipts and records intended Sprint109 subpackages by concrete
-- names and module-path strings, so parallel Sprint109 workers can create
-- their own modules without import races.
--
-- The route is:
--
--   lower semicontinuity of closed forms
--     + recovery/core density
--     + a fail-closed no-bottom-pollution support lane
--     -> spectral liminf for the physical bottom and first threshold
--     -> transfer of the finite uniform gap to the continuum gap target.
--
-- This assembly is deliberately weaker than the corrected H3a/H3b
-- no-spectral-pollution theorem.  Mosco liminf plus compactness is a
-- necessary support route toward the continuum interface, but it is
-- insufficient for no-spectral-pollution.  The corrected split is explicit:
--
--   * H3a is transfer-matrix / norm-resolvent convergence on T_N restricted
--     to the vacuum-orthogonal sector.
--   * H3b is RP.4 / OS vacuum-projection continuity for the limiting vacuum.
--   * No-spectral-pollution depends on H3a + H3b, not on Mosco alone.
--
-- The receipt is fail-closed.  It records the route and the exact open
-- theorem flags, but it does not promote Clay Yang-Mills and does not claim
-- the continuum spectral gap theorem.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

assemblyReceiptRecorded : Bool
assemblyReceiptRecorded = true

moscoSpectralLiminfTheoremProvedHere : Bool
moscoSpectralLiminfTheoremProvedHere = false

continuumGapTransportTheoremProvedHere : Bool
continuumGapTransportTheoremProvedHere = false

clayContinuumMassGapPromotedHere : Bool
clayContinuumMassGapPromotedHere = false

normResolventTransferTheoremClosedHere : Bool
normResolventTransferTheoremClosedHere = false

vacuumProjectionContinuityClosedHere : Bool
vacuumProjectionContinuityClosedHere = false

noSpectralPollutionFromH3aH3bClosedHere : Bool
noSpectralPollutionFromH3aH3bClosedHere = false

moscoNecessaryButInsufficientRecorded : Bool
moscoNecessaryButInsufficientRecorded = true

lowerSemicontinuityClosedHere : Bool
lowerSemicontinuityClosedHere =
  Mosco108.lowerSemicontinuityProvedHere

recoverySequenceClosedHere : Bool
recoverySequenceClosedHere =
  Mosco108.recoverySequenceConstructedHere

noBottomPollutionClosedHere : Bool
noBottomPollutionClosedHere =
  Mosco108.noBottomSpectrumPollutionProvedHere

spectralLiminfClosedHere : Bool
spectralLiminfClosedHere =
  Mosco108.liminfSpectralLowerBoundProvedHere

uniformFormLowerBoundClosedHere : Bool
uniformFormLowerBoundClosedHere =
  UniformForm108.uniformFormLowerBoundTheoremProved

spectralGapTransportClosedHere : Bool
spectralGapTransportClosedHere =
  SpectralTransport108.transportTheoremProvedHere

transferLowerBoundAssemblyClosedHere : Bool
transferLowerBoundAssemblyClosedHere =
  TransferAssembly108.transferLowerBoundTheoremProvedHere

mosco108Path : String
mosco108Path =
  "DASHI/Physics/Closure/YMSprint108MoscoNoPollutionBridge.agda"

uniformForm108Path : String
uniformForm108Path =
  "DASHI/Physics/Closure/YMSprint108UniformFormLowerBound.agda"

spectralTransport108Path : String
spectralTransport108Path =
  "DASHI/Physics/Closure/YMSprint108SpectralGapTransport.agda"

transferAssembly108Path : String
transferAssembly108Path =
  "DASHI/Physics/Closure/YMSprint108TransferLowerBoundAssembly.agda"

intendedLowerSemicontinuityModuleName : String
intendedLowerSemicontinuityModuleName =
  "DASHI.Physics.Closure.YMSprint109MoscoLowerSemicontinuity"

intendedRecoveryModuleName : String
intendedRecoveryModuleName =
  "DASHI.Physics.Closure.YMSprint109MoscoRecoveryCore"

intendedNoBottomPollutionModuleName : String
intendedNoBottomPollutionModuleName =
  "DASHI.Physics.Closure.YMSprint109NoBottomPollution"

intendedSpectralLiminfModuleName : String
intendedSpectralLiminfModuleName =
  "DASHI.Physics.Closure.YMSprint109SpectralLiminf"

intendedGapTransportModuleName : String
intendedGapTransportModuleName =
  "DASHI.Physics.Closure.YMSprint109GapTransport"

intendedH3aModuleName : String
intendedH3aModuleName =
  "DASHI.Physics.Closure.YMSprint109VacuumOrthogonalTransferNormResolvent"

intendedH3bModuleName : String
intendedH3bModuleName =
  "DASHI.Physics.Closure.YMSprint109RP4OSVacuumProjectionContinuity"

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c_transfer * m_eff(a) * a transports to a positive continuum physical Hamiltonian gap"

assemblyStatementText : String
assemblyStatementText =
  "Sprint109 assembles Mosco lower semicontinuity, recovery, and no-bottom-pollution support statuses into a spectral-liminf and gap-transport route, but this route is strictly weaker than the corrected H3a/H3b no-spectral-pollution theorem."

lowerSemicontinuityStepText : String
lowerSemicontinuityStepText =
  "Closed-form lower semicontinuity supplies the Mosco liminf inequality on weak finite-energy approximants."

recoveryStepText : String
recoveryStepText =
  "Recovery/core density supplies approximants for continuum physical-domain vectors without increasing limiting form energy."

noBottomPollutionStepText : String
noBottomPollutionStepText =
  "No-bottom-pollution is a support lane only: it excludes a narrow class of spurious nonphysical finite spectral branches, but it does not replace H3a vacuum-orthogonal transfer convergence or H3b vacuum-projection continuity."

spectralLiminfStepText : String
spectralLiminfStepText =
  "The Mosco liminf plus no-bottom-pollution support package gives a spectral liminf boundary for bottom and first-threshold values, but this boundary is necessary only and is not H3a norm-resolvent / transfer-matrix convergence."

gapTransportStepText : String
gapTransportStepText =
  "Spectral liminf and the Sprint108 uniform form ledger are the route to transport the finite transfer lower bound to the continuum gap target, without closing H3a, without closing H3b, and therefore without closing no-spectral-pollution on the vacuum-orthogonal sector."

h3aOutsideAssemblyText : String
h3aOutsideAssemblyText =
  "Outside this file: H3a is the transfer-matrix / norm-resolvent convergence theorem on T_N restricted to the vacuum-orthogonal sector; Mosco liminf, compactness, and no-bottom-pollution support do not prove it."

h3bOutsideAssemblyText : String
h3bOutsideAssemblyText =
  "Outside this file: H3b is RP.4 / OS vacuum-projection continuity for the limiting vacuum; this assembly does not close that compatibility step."

noSpectralPollutionBoundaryText : String
noSpectralPollutionBoundaryText =
  "Corrected boundary: no-spectral-pollution depends on H3a + H3b. Mosco liminf is necessary support, but insufficient on its own."

failClosedBoundaryText : String
failClosedBoundaryText =
  "All theorem and Clay-promotion flags remain false. This assembly records a Mosco spectral-liminf route only; it does not certify H3a transfer-matrix / norm-resolvent convergence, does not certify H3b RP.4 / OS vacuum-projection continuity, and therefore does not close the corrected no-spectral-pollution theorem."

data AssemblyLane : Set where
  lower-semicontinuity-lane :
    AssemblyLane
  recovery-core-lane :
    AssemblyLane
  no-bottom-pollution-lane :
    AssemblyLane
  spectral-liminf-lane :
    AssemblyLane
  gap-transport-lane :
    AssemblyLane
  h3a-vacuum-orthogonal-transfer-lane :
    AssemblyLane
  h3b-vacuum-projection-continuity-lane :
    AssemblyLane

data AssemblyStatus : Set where
  imported-sprint108-support :
    AssemblyStatus
  intended-sprint109-package :
    AssemblyStatus
  required-open :
    AssemblyStatus
  route-assembled :
    AssemblyStatus
  theorem-fail-closed :
    AssemblyStatus
  nonpromotion-boundary :
    AssemblyStatus

record Sprint108SupportReceipts : Setω where
  constructor mkSprint108SupportReceipts
  field
    moscoNoPollutionReceipt :
      Mosco108.YMSprint108MoscoNoPollutionBridgeReceipt
    uniformFormReceipt :
      UniformForm108.YMSprint108UniformFormLowerBoundReceipt
    spectralGapTransportReceipt :
      SpectralTransport108.YMSprint108SpectralGapTransportReceipt
    transferLowerBoundAssemblyReceipt :
      TransferAssembly108.YMSprint108TransferLowerBoundAssemblyReceipt
    moscoModulePath :
      String
    uniformFormModulePath :
      String
    spectralTransportModulePath :
      String
    transferAssemblyModulePath :
      String
    importsRestrictedToSprint108 :
      Bool

record IntendedSprint109Subpackage : Set where
  constructor mkIntendedSprint109Subpackage
  field
    lane :
      AssemblyLane
    moduleName :
      String
    statement :
      String
    requiredForSpectralLiminf :
      Bool
    requiredForGapTransport :
      Bool
    provedHere :
      Bool
    status :
      AssemblyStatus

record MoscoToSpectralLiminfRoute : Set where
  constructor mkMoscoToSpectralLiminfRoute
  field
    lowerSemicontinuity :
      IntendedSprint109Subpackage
    recoveryCore :
      IntendedSprint109Subpackage
    noBottomPollution :
      IntendedSprint109Subpackage
    spectralLiminf :
      IntendedSprint109Subpackage
    lowerSemicontinuityClosed :
      Bool
    recoverySequenceClosed :
      Bool
    noBottomPollutionClosed :
      Bool
    spectralLiminfClosed :
      Bool
    routeAssembled :
      Bool
    theoremProvedHere :
      Bool
    status :
      AssemblyStatus

record SpectralGapTransportRoute : Set where
  constructor mkSpectralGapTransportRoute
  field
    gapTransport :
      IntendedSprint109Subpackage
    targetFormula :
      String
    uniformFormLowerBoundClosed :
      Bool
    sprint108SpectralTransportClosed :
      Bool
    sprint108TransferAssemblyClosed :
      Bool
    spectralLiminfInputClosed :
      Bool
    gapTransportTheoremProvedHere :
      Bool
    status :
      AssemblyStatus

record CorrectedNoSpectralPollutionBoundary : Set where
  constructor mkCorrectedNoSpectralPollutionBoundary
  field
    h3aModuleName :
      String
    h3bModuleName :
      String
    h3aStatement :
      String
    h3bStatement :
      String
    noSpectralPollutionBoundary :
      String
    moscoNecessaryButInsufficient :
      Bool
    h3aClosedHere :
      Bool
    h3bClosedHere :
      Bool
    noSpectralPollutionClosedHere :
      Bool
    status :
      AssemblyStatus

record FailClosedTheoremFlags : Set where
  constructor mkFailClosedTheoremFlags
  field
    moscoSpectralLiminfTheoremProved :
      Bool
    moscoSpectralLiminfTheoremProvedIsFalse :
      moscoSpectralLiminfTheoremProved ≡ false
    continuumGapTransportTheoremProved :
      Bool
    continuumGapTransportTheoremProvedIsFalse :
      continuumGapTransportTheoremProved ≡ false
    clayContinuumMassGapPromoted :
      Bool
    clayContinuumMassGapPromotedIsFalse :
      clayContinuumMassGapPromoted ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    normResolventTransferTheoremClosed :
      Bool
    normResolventTransferTheoremClosedIsFalse :
      normResolventTransferTheoremClosed ≡ false
    vacuumProjectionContinuityClosed :
      Bool
    vacuumProjectionContinuityClosedIsFalse :
      vacuumProjectionContinuityClosed ≡ false
    noSpectralPollutionFromH3aH3bClosed :
      Bool
    noSpectralPollutionFromH3aH3bClosedIsFalse :
      noSpectralPollutionFromH3aH3bClosed ≡ false
    h3aBoundaryStatement :
      String
    h3bBoundaryStatement :
      String
    noSpectralPollutionBoundaryStatement :
      String
    boundaryStatement :
      String
    status :
      AssemblyStatus

record AssemblyRouteStatus : Set where
  constructor mkAssemblyRouteStatus
  field
    targetFormula :
      String
    assemblyStatement :
      String
    moscoToSpectralLiminf :
      MoscoToSpectralLiminfRoute
    spectralGapTransport :
      SpectralGapTransportRoute
    correctedNoSpectralPollutionBoundary :
      CorrectedNoSpectralPollutionBoundary
    failClosedFlags :
      FailClosedTheoremFlags
    routeLedger :
      List String
    receiptRecorded :
      Bool
    status :
      AssemblyStatus

record YMSprint109MoscoSpectralLiminfAssemblyReceipt : Setω where
  field
    sprint108Support :
      Sprint108SupportReceipts
    routeStatus :
      AssemblyRouteStatus
    receiptRecorded :
      Bool
    moscoSpectralLiminfTheoremProvedHereFlag :
      Bool
    moscoSpectralLiminfTheoremProvedHereIsFalse :
      moscoSpectralLiminfTheoremProvedHereFlag ≡ false
    continuumGapTransportTheoremProvedHereFlag :
      Bool
    continuumGapTransportTheoremProvedHereIsFalse :
      continuumGapTransportTheoremProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    canonicalReceiptName :
      String

open YMSprint109MoscoSpectralLiminfAssemblyReceipt public

canonicalSprint108SupportReceipts : Sprint108SupportReceipts
canonicalSprint108SupportReceipts =
  mkSprint108SupportReceipts
    Mosco108.canonicalYMSprint108MoscoNoPollutionBridgeReceipt
    UniformForm108.canonicalYMSprint108UniformFormLowerBoundReceipt
    SpectralTransport108.canonicalYMSprint108SpectralGapTransportReceipt
    TransferAssembly108.canonicalYMSprint108TransferLowerBoundAssemblyReceipt
    mosco108Path
    uniformForm108Path
    spectralTransport108Path
    transferAssembly108Path
    true

canonicalLowerSemicontinuitySubpackage : IntendedSprint109Subpackage
canonicalLowerSemicontinuitySubpackage =
  mkIntendedSprint109Subpackage
    lower-semicontinuity-lane
    intendedLowerSemicontinuityModuleName
    lowerSemicontinuityStepText
    true
    true
    lowerSemicontinuityClosedHere
    required-open

canonicalRecoverySubpackage : IntendedSprint109Subpackage
canonicalRecoverySubpackage =
  mkIntendedSprint109Subpackage
    recovery-core-lane
    intendedRecoveryModuleName
    recoveryStepText
    true
    true
    recoverySequenceClosedHere
    required-open

canonicalNoBottomPollutionSubpackage : IntendedSprint109Subpackage
canonicalNoBottomPollutionSubpackage =
  mkIntendedSprint109Subpackage
    no-bottom-pollution-lane
    intendedNoBottomPollutionModuleName
    noBottomPollutionStepText
    true
    true
    noBottomPollutionClosedHere
    required-open

canonicalSpectralLiminfSubpackage : IntendedSprint109Subpackage
canonicalSpectralLiminfSubpackage =
  mkIntendedSprint109Subpackage
    spectral-liminf-lane
    intendedSpectralLiminfModuleName
    spectralLiminfStepText
    true
    true
    spectralLiminfClosedHere
    required-open

canonicalGapTransportSubpackage : IntendedSprint109Subpackage
canonicalGapTransportSubpackage =
  mkIntendedSprint109Subpackage
    gap-transport-lane
    intendedGapTransportModuleName
    gapTransportStepText
    false
    true
    continuumGapTransportTheoremProvedHere
    required-open

canonicalCorrectedNoSpectralPollutionBoundary :
  CorrectedNoSpectralPollutionBoundary
canonicalCorrectedNoSpectralPollutionBoundary =
  mkCorrectedNoSpectralPollutionBoundary
    intendedH3aModuleName
    intendedH3bModuleName
    h3aOutsideAssemblyText
    h3bOutsideAssemblyText
    noSpectralPollutionBoundaryText
    moscoNecessaryButInsufficientRecorded
    normResolventTransferTheoremClosedHere
    vacuumProjectionContinuityClosedHere
    noSpectralPollutionFromH3aH3bClosedHere
    theorem-fail-closed

canonicalMoscoToSpectralLiminfRoute : MoscoToSpectralLiminfRoute
canonicalMoscoToSpectralLiminfRoute =
  mkMoscoToSpectralLiminfRoute
    canonicalLowerSemicontinuitySubpackage
    canonicalRecoverySubpackage
    canonicalNoBottomPollutionSubpackage
    canonicalSpectralLiminfSubpackage
    lowerSemicontinuityClosedHere
    recoverySequenceClosedHere
    noBottomPollutionClosedHere
    spectralLiminfClosedHere
    true
    moscoSpectralLiminfTheoremProvedHere
    route-assembled

canonicalSpectralGapTransportRoute : SpectralGapTransportRoute
canonicalSpectralGapTransportRoute =
  mkSpectralGapTransportRoute
    canonicalGapTransportSubpackage
    targetFormulaText
    uniformFormLowerBoundClosedHere
    spectralGapTransportClosedHere
    transferLowerBoundAssemblyClosedHere
    spectralLiminfClosedHere
    continuumGapTransportTheoremProvedHere
    route-assembled

canonicalFailClosedTheoremFlags : FailClosedTheoremFlags
canonicalFailClosedTheoremFlags =
  mkFailClosedTheoremFlags
    moscoSpectralLiminfTheoremProvedHere
    refl
    continuumGapTransportTheoremProvedHere
    refl
    clayContinuumMassGapPromotedHere
    refl
    clayYangMillsPromoted
    refl
    normResolventTransferTheoremClosedHere
    refl
    vacuumProjectionContinuityClosedHere
    refl
    noSpectralPollutionFromH3aH3bClosedHere
    refl
    h3aOutsideAssemblyText
    h3bOutsideAssemblyText
    noSpectralPollutionBoundaryText
    failClosedBoundaryText
    theorem-fail-closed

canonicalAssemblyRouteStatus : AssemblyRouteStatus
canonicalAssemblyRouteStatus =
  mkAssemblyRouteStatus
    targetFormulaText
    assemblyStatementText
    canonicalMoscoToSpectralLiminfRoute
    canonicalSpectralGapTransportRoute
    canonicalCorrectedNoSpectralPollutionBoundary
    canonicalFailClosedTheoremFlags
    (assemblyStatementText
      ∷ lowerSemicontinuityStepText
      ∷ recoveryStepText
      ∷ noBottomPollutionStepText
      ∷ spectralLiminfStepText
      ∷ gapTransportStepText
      ∷ h3aOutsideAssemblyText
      ∷ h3bOutsideAssemblyText
      ∷ noSpectralPollutionBoundaryText
      ∷ failClosedBoundaryText
      ∷ [])
    assemblyReceiptRecorded
    route-assembled

canonicalYMSprint109MoscoSpectralLiminfAssemblyReceipt :
  YMSprint109MoscoSpectralLiminfAssemblyReceipt
canonicalYMSprint109MoscoSpectralLiminfAssemblyReceipt =
  record
    { sprint108Support =
        canonicalSprint108SupportReceipts
    ; routeStatus =
        canonicalAssemblyRouteStatus
    ; receiptRecorded =
        assemblyReceiptRecorded
    ; moscoSpectralLiminfTheoremProvedHereFlag =
        moscoSpectralLiminfTheoremProvedHere
    ; moscoSpectralLiminfTheoremProvedHereIsFalse =
        refl
    ; continuumGapTransportTheoremProvedHereFlag =
        continuumGapTransportTheoremProvedHere
    ; continuumGapTransportTheoremProvedHereIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    ; clayYangMillsPromotedHereIsFalse =
        refl
    ; canonicalReceiptName =
        "canonicalYMSprint109MoscoSpectralLiminfAssemblyReceipt"
    }

canonicalReceipt : YMSprint109MoscoSpectralLiminfAssemblyReceipt
canonicalReceipt =
  canonicalYMSprint109MoscoSpectralLiminfAssemblyReceipt

canonicalReceiptRecorded : Bool
canonicalReceiptRecorded =
  receiptRecorded canonicalReceipt

canonicalReceiptMoscoSpectralLiminfTheoremIsFalse :
  moscoSpectralLiminfTheoremProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptMoscoSpectralLiminfTheoremIsFalse =
  refl

canonicalReceiptContinuumGapTransportTheoremIsFalse :
  continuumGapTransportTheoremProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptContinuumGapTransportTheoremIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl
