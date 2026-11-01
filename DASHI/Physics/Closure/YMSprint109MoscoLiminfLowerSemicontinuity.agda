module DASHI.Physics.Closure.YMSprint109MoscoLiminfLowerSemicontinuity where

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
-- Sprint 109 Mosco liminf and lower-semicontinuity ledger.
--
-- This module sharpens the lower-semicontinuity side of the Sprint108
-- Mosco/no-pollution package.  It does not prove Mosco convergence or the
-- spectral lower-bound theorem.  Instead it records the exact lower-bound
-- path that must be supplied before the transfer lower-bound assembly can be
-- promoted:
--
--   weak compactness at bounded finite energy
--   lower semicontinuity of the closed quadratic form
--   liminf control of bottom spectral values
--   exclusion of lower-edge spectral pollution
--   compatibility with the uniform transfer constants

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

receiptRecorded : Bool
receiptRecorded = true

moscoLowerSemicontinuityProvedHere : Bool
moscoLowerSemicontinuityProvedHere = false

liminfSpectralLowerBoundProvedHere : Bool
liminfSpectralLowerBoundProvedHere = false

transferLiminfLowerBoundPathClosedHere : Bool
transferLiminfLowerBoundPathClosedHere = false

lowerEdgeNoPollutionProvedHere : Bool
lowerEdgeNoPollutionProvedHere = false

uniformConstantCompatibilityProvedHere : Bool
uniformConstantCompatibilityProvedHere = false

sprint108MoscoLowerSemicontinuityClosed : Bool
sprint108MoscoLowerSemicontinuityClosed =
  Mosco108.lowerSemicontinuityProvedHere

sprint108LiminfSpectralClosed : Bool
sprint108LiminfSpectralClosed =
  Mosco108.liminfSpectralLowerBoundProvedHere

sprint108AssemblyClosed : Bool
sprint108AssemblyClosed =
  TransferAssembly108.transferLowerBoundTheoremProvedHere

sprint108UniformFormClosed : Bool
sprint108UniformFormClosed =
  UniformForm108.uniformFormLowerBoundTheoremProved

sprint108SpectralTransportClosed : Bool
sprint108SpectralTransportClosed =
  SpectralTransport108.transportTheoremProvedHere

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c_transfer * m_eff(a) * a"

closedFormLiminfStatementText : String
closedFormLiminfStatementText =
  "For every weakly convergent bounded-energy lattice sequence, the continuum closed quadratic form is bounded above by the liminf of the finite transfer forms."

spectralLiminfStatementText : String
spectralLiminfStatementText =
  "The bottom spectral values in the non-vacuum physical sector must satisfy a liminf lower bound compatible with the continuum Hamiltonian lower edge."

weakCompactnessRequirementText : String
weakCompactnessRequirementText =
  "Supply a common physical Hilbert carrier and prove weak compactness for normalized finite-energy transfer-form sequences."

closedFormRequirementText : String
closedFormRequirementText =
  "Identify the closed semibounded continuum quadratic form and prove lower semicontinuity on the Mosco liminf domain."

domainIdentificationRequirementText : String
domainIdentificationRequirementText =
  "Prove that finite transfer form domains converge to the physical continuum form domain without losing gauge-sector constraints."

spectralProjectionRequirementText : String
spectralProjectionRequirementText =
  "Control spectral projections near the lower edge so approximate finite eigenvectors have continuum physical weak limits."

noLowerEdgePollutionRequirementText : String
noLowerEdgePollutionRequirementText =
  "Exclude spurious finite-transfer spectral branches converging below the continuum physical lower edge."

uniformConstantsRequirementText : String
uniformConstantsRequirementText =
  "Preserve c_transfer, the a-window, and the effective-mass normalization through the liminf spectral passage."

blockedBecauseText : String
blockedBecauseText =
  "Sprint109 records the liminf route but lacks DASHI-native weak compactness, closed-form lower semicontinuity, and lower-edge no-pollution proofs."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "All theorem and Clay promotion flags remain false; this receipt is a lower-bound status ledger, not a continuum mass-gap proof."

sprint108MoscoPath : String
sprint108MoscoPath =
  "DASHI/Physics/Closure/YMSprint108MoscoNoPollutionBridge.agda"

sprint108UniformFormPath : String
sprint108UniformFormPath =
  "DASHI/Physics/Closure/YMSprint108UniformFormLowerBound.agda"

sprint108SpectralTransportPath : String
sprint108SpectralTransportPath =
  "DASHI/Physics/Closure/YMSprint108SpectralGapTransport.agda"

sprint108AssemblyPath : String
sprint108AssemblyPath =
  "DASHI/Physics/Closure/YMSprint108TransferLowerBoundAssembly.agda"

data LiminfLowerBoundStatus : Set where
  imported-sprint108-boundary :
    LiminfLowerBoundStatus
  required-weak-compactness :
    LiminfLowerBoundStatus
  required-closed-form-liminf :
    LiminfLowerBoundStatus
  required-domain-identification :
    LiminfLowerBoundStatus
  required-spectral-liminf :
    LiminfLowerBoundStatus
  required-no-lower-edge-pollution :
    LiminfLowerBoundStatus
  required-uniform-constant-compatibility :
    LiminfLowerBoundStatus
  theorem-open :
    LiminfLowerBoundStatus
  nonpromotion-boundary :
    LiminfLowerBoundStatus

data LiminfLane : Set where
  weak-compactness-lane :
    LiminfLane
  closed-form-lower-semicontinuity-lane :
    LiminfLane
  domain-identification-lane :
    LiminfLane
  spectral-liminf-lane :
    LiminfLane
  no-lower-edge-pollution-lane :
    LiminfLane
  uniform-transfer-compatibility-lane :
    LiminfLane

canonicalLiminfLanes : List LiminfLane
canonicalLiminfLanes =
  weak-compactness-lane
  ∷ closed-form-lower-semicontinuity-lane
  ∷ domain-identification-lane
  ∷ spectral-liminf-lane
  ∷ no-lower-edge-pollution-lane
  ∷ uniform-transfer-compatibility-lane
  ∷ []

canonicalAnalyticRequirements : List String
canonicalAnalyticRequirements =
  weakCompactnessRequirementText
  ∷ closedFormRequirementText
  ∷ domainIdentificationRequirementText
  ∷ spectralProjectionRequirementText
  ∷ noLowerEdgePollutionRequirementText
  ∷ uniformConstantsRequirementText
  ∷ []

record Sprint108LiminfSupply : Setω where
  constructor mkSprint108LiminfSupply
  field
    moscoNoPollutionReceipt :
      Mosco108.YMSprint108MoscoNoPollutionBridgeReceipt
    uniformFormReceipt :
      UniformForm108.YMSprint108UniformFormLowerBoundReceipt
    spectralTransportReceipt :
      SpectralTransport108.YMSprint108SpectralGapTransportReceipt
    transferAssemblyReceipt :
      TransferAssembly108.YMSprint108TransferLowerBoundAssemblyReceipt
    moscoModulePath :
      String
    uniformFormModulePath :
      String
    spectralTransportModulePath :
      String
    transferAssemblyModulePath :
      String
    sprint108MoscoLiminfImported :
      Bool
    sprint108AssemblyImported :
      Bool
    importedClayFlagsKeptFalse :
      Bool

record WeakCompactnessRequirement : Set where
  constructor mkWeakCompactnessRequirement
  field
    lane :
      LiminfLane
    requirement :
      String
    neededForLowerSemicontinuity :
      Bool
    neededForSpectralLiminf :
      Bool
    provedHere :
      Bool
    status :
      LiminfLowerBoundStatus

record ClosedFormLowerSemicontinuityStatus : Set where
  constructor mkClosedFormLowerSemicontinuityStatus
  field
    lane :
      LiminfLane
    statement :
      String
    sprint108Closed :
      Bool
    closedContinuumFormIdentified :
      Bool
    lowerSemicontinuityProvedHere :
      Bool
    requiredForTargetFormula :
      Bool
    status :
      LiminfLowerBoundStatus

record DomainIdentificationStatus : Set where
  constructor mkDomainIdentificationStatus
  field
    lane :
      LiminfLane
    requirement :
      String
    physicalGaugeSectorPreserved :
      Bool
    commonCarrierConstructedHere :
      Bool
    finiteDomainsConvergeHere :
      Bool
    status :
      LiminfLowerBoundStatus

record SpectralLiminfLowerBoundStatus : Set where
  constructor mkSpectralLiminfLowerBoundStatus
  field
    lane :
      LiminfLane
    statement :
      String
    sprint108Closed :
      Bool
    followsFromFormLiminf :
      Bool
    requiresSpectralProjectionControl :
      Bool
    provedHere :
      Bool
    theoremFlag :
      Bool
    status :
      LiminfLowerBoundStatus

record LowerEdgeNoPollutionStatus : Set where
  constructor mkLowerEdgeNoPollutionStatus
  field
    lane :
      LiminfLane
    requirement :
      String
    sprint108NoPollutionClosed :
      Bool
    strongResolventAloneEnough :
      Bool
    compactnessTightnessNeeded :
      Bool
    provedHere :
      Bool
    status :
      LiminfLowerBoundStatus

record UniformTransferCompatibilityStatus : Set where
  constructor mkUniformTransferCompatibilityStatus
  field
    lane :
      LiminfLane
    targetFormula :
      String
    requirement :
      String
    importedSprint108UniformFormClosed :
      Bool
    importedSprint108SpectralTransportClosed :
      Bool
    cTransferPreservedHere :
      Bool
    aWindowPreservedHere :
      Bool
    effectiveMassNormalizationPreservedHere :
      Bool
    status :
      LiminfLowerBoundStatus

record BlockedGapRecord : Set where
  constructor mkBlockedGapRecord
  field
    blocked :
      Bool
    reason :
      String
    theoremStillOpen :
      Bool
    analyticRequirements :
      List String
    status :
      LiminfLowerBoundStatus

record TransferLowerBoundPathStatus : Set where
  constructor mkTransferLowerBoundPathStatus
  field
    targetFormula :
      String
    moscoLowerSemicontinuityClosed :
      Bool
    spectralLiminfClosed :
      Bool
    noLowerEdgePollutionClosed :
      Bool
    uniformConstantCompatibilityClosed :
      Bool
    importedSprint108TransferAssemblyClosed :
      Bool
    pathClosedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    status :
      LiminfLowerBoundStatus

record YMSprint109MoscoLiminfLowerSemicontinuityReceipt : Setω where
  field
    sprint108Supply :
      Sprint108LiminfSupply
    liminfLanes :
      List LiminfLane
    weakCompactness :
      WeakCompactnessRequirement
    closedFormLowerSemicontinuity :
      ClosedFormLowerSemicontinuityStatus
    domainIdentification :
      DomainIdentificationStatus
    spectralLiminfLowerBound :
      SpectralLiminfLowerBoundStatus
    lowerEdgeNoPollution :
      LowerEdgeNoPollutionStatus
    uniformTransferCompatibility :
      UniformTransferCompatibilityStatus
    blockedGap :
      BlockedGapRecord
    transferLowerBoundPath :
      TransferLowerBoundPathStatus
    receiptRecordedHere :
      Bool
    moscoLowerSemicontinuityProvedHereFlag :
      Bool
    moscoLowerSemicontinuityProvedHereFlagIsFalse :
      moscoLowerSemicontinuityProvedHereFlag ≡ false
    liminfSpectralLowerBoundProvedHereFlag :
      Bool
    liminfSpectralLowerBoundProvedHereFlagIsFalse :
      liminfSpectralLowerBoundProvedHereFlag ≡ false
    transferLiminfLowerBoundPathClosedHereFlag :
      Bool
    transferLiminfLowerBoundPathClosedHereFlagIsFalse :
      transferLiminfLowerBoundPathClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    evidenceLedger :
      List String

open YMSprint109MoscoLiminfLowerSemicontinuityReceipt public

canonicalSprint108LiminfSupply : Sprint108LiminfSupply
canonicalSprint108LiminfSupply =
  mkSprint108LiminfSupply
    Mosco108.canonicalYMSprint108MoscoNoPollutionBridgeReceipt
    UniformForm108.canonicalYMSprint108UniformFormLowerBoundReceipt
    SpectralTransport108.canonicalYMSprint108SpectralGapTransportReceipt
    TransferAssembly108.canonicalYMSprint108TransferLowerBoundAssemblyReceipt
    sprint108MoscoPath
    sprint108UniformFormPath
    sprint108SpectralTransportPath
    sprint108AssemblyPath
    true
    true
    true

canonicalWeakCompactnessRequirement : WeakCompactnessRequirement
canonicalWeakCompactnessRequirement =
  mkWeakCompactnessRequirement
    weak-compactness-lane
    weakCompactnessRequirementText
    true
    true
    false
    required-weak-compactness

canonicalClosedFormLowerSemicontinuityStatus :
  ClosedFormLowerSemicontinuityStatus
canonicalClosedFormLowerSemicontinuityStatus =
  mkClosedFormLowerSemicontinuityStatus
    closed-form-lower-semicontinuity-lane
    closedFormLiminfStatementText
    sprint108MoscoLowerSemicontinuityClosed
    false
    moscoLowerSemicontinuityProvedHere
    true
    required-closed-form-liminf

canonicalDomainIdentificationStatus : DomainIdentificationStatus
canonicalDomainIdentificationStatus =
  mkDomainIdentificationStatus
    domain-identification-lane
    domainIdentificationRequirementText
    true
    false
    false
    required-domain-identification

canonicalSpectralLiminfLowerBoundStatus :
  SpectralLiminfLowerBoundStatus
canonicalSpectralLiminfLowerBoundStatus =
  mkSpectralLiminfLowerBoundStatus
    spectral-liminf-lane
    spectralLiminfStatementText
    sprint108LiminfSpectralClosed
    true
    true
    liminfSpectralLowerBoundProvedHere
    liminfSpectralLowerBoundProvedHere
    required-spectral-liminf

canonicalLowerEdgeNoPollutionStatus : LowerEdgeNoPollutionStatus
canonicalLowerEdgeNoPollutionStatus =
  mkLowerEdgeNoPollutionStatus
    no-lower-edge-pollution-lane
    noLowerEdgePollutionRequirementText
    Mosco108.noBottomSpectrumPollutionProvedHere
    false
    true
    lowerEdgeNoPollutionProvedHere
    required-no-lower-edge-pollution

canonicalUniformTransferCompatibilityStatus :
  UniformTransferCompatibilityStatus
canonicalUniformTransferCompatibilityStatus =
  mkUniformTransferCompatibilityStatus
    uniform-transfer-compatibility-lane
    targetFormulaText
    uniformConstantsRequirementText
    sprint108UniformFormClosed
    sprint108SpectralTransportClosed
    uniformConstantCompatibilityProvedHere
    uniformConstantCompatibilityProvedHere
    uniformConstantCompatibilityProvedHere
    required-uniform-constant-compatibility

canonicalBlockedGapRecord : BlockedGapRecord
canonicalBlockedGapRecord =
  mkBlockedGapRecord
    true
    blockedBecauseText
    true
    canonicalAnalyticRequirements
    theorem-open

canonicalTransferLowerBoundPathStatus : TransferLowerBoundPathStatus
canonicalTransferLowerBoundPathStatus =
  mkTransferLowerBoundPathStatus
    targetFormulaText
    moscoLowerSemicontinuityProvedHere
    liminfSpectralLowerBoundProvedHere
    lowerEdgeNoPollutionProvedHere
    uniformConstantCompatibilityProvedHere
    sprint108AssemblyClosed
    transferLiminfLowerBoundPathClosedHere
    clayYangMillsPromoted
    theorem-open

canonicalYMSprint109MoscoLiminfLowerSemicontinuityReceipt :
  YMSprint109MoscoLiminfLowerSemicontinuityReceipt
canonicalYMSprint109MoscoLiminfLowerSemicontinuityReceipt =
  record
    { sprint108Supply =
        canonicalSprint108LiminfSupply
    ; liminfLanes =
        canonicalLiminfLanes
    ; weakCompactness =
        canonicalWeakCompactnessRequirement
    ; closedFormLowerSemicontinuity =
        canonicalClosedFormLowerSemicontinuityStatus
    ; domainIdentification =
        canonicalDomainIdentificationStatus
    ; spectralLiminfLowerBound =
        canonicalSpectralLiminfLowerBoundStatus
    ; lowerEdgeNoPollution =
        canonicalLowerEdgeNoPollutionStatus
    ; uniformTransferCompatibility =
        canonicalUniformTransferCompatibilityStatus
    ; blockedGap =
        canonicalBlockedGapRecord
    ; transferLowerBoundPath =
        canonicalTransferLowerBoundPathStatus
    ; receiptRecordedHere =
        receiptRecorded
    ; moscoLowerSemicontinuityProvedHereFlag =
        moscoLowerSemicontinuityProvedHere
    ; moscoLowerSemicontinuityProvedHereFlagIsFalse =
        refl
    ; liminfSpectralLowerBoundProvedHereFlag =
        liminfSpectralLowerBoundProvedHere
    ; liminfSpectralLowerBoundProvedHereFlagIsFalse =
        refl
    ; transferLiminfLowerBoundPathClosedHereFlag =
        transferLiminfLowerBoundPathClosedHere
    ; transferLiminfLowerBoundPathClosedHereFlagIsFalse =
        refl
    ; clayYangMillsPromotedHere =
        clayYangMillsPromoted
    ; clayYangMillsPromotedHereIsFalse =
        refl
    ; evidenceLedger =
        targetFormulaText
        ∷ closedFormLiminfStatementText
        ∷ spectralLiminfStatementText
        ∷ weakCompactnessRequirementText
        ∷ closedFormRequirementText
        ∷ domainIdentificationRequirementText
        ∷ spectralProjectionRequirementText
        ∷ noLowerEdgePollutionRequirementText
        ∷ uniformConstantsRequirementText
        ∷ blockedBecauseText
        ∷ nonPromotionBoundaryText
        ∷ []
    }

canonicalReceipt : YMSprint109MoscoLiminfLowerSemicontinuityReceipt
canonicalReceipt =
  canonicalYMSprint109MoscoLiminfLowerSemicontinuityReceipt

canonicalReceiptMoscoLowerSemicontinuityNotProved :
  moscoLowerSemicontinuityProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptMoscoLowerSemicontinuityNotProved =
  refl

canonicalReceiptLiminfSpectralLowerBoundNotProved :
  liminfSpectralLowerBoundProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptLiminfSpectralLowerBoundNotProved =
  refl

canonicalReceiptTransferPathNotClosed :
  transferLiminfLowerBoundPathClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptTransferPathNotClosed =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl
