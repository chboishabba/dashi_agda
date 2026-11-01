module DASHI.Physics.Closure.YMSprint119TransferCalculusAllObligationsReducer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint108LogGeneratorCalculusBridge
  as Log108
import DASHI.Physics.Closure.YMSprint108SpectralGapTransport
  as Spectral108
import DASHI.Physics.Closure.YMSprint108TransferLowerBoundAssembly
  as Transfer108
import DASHI.Physics.Closure.YMSprint108UniformFormLowerBound
  as Form108
import DASHI.Physics.Closure.YMSprint109TransferLowerBoundCriticalAssembly
  as Critical109
import DASHI.Physics.Closure.YMSprint117TransferReadinessObligationReducer
  as Reducer117
import DASHI.Physics.Closure.YMSprint118TransferCalculusReadinessAggregator
  as Aggregator118

------------------------------------------------------------------------
-- Sprint119 transfer-calculus all-obligations reducer.
--
-- This reducer keeps the transfer-calculus package separate from the stronger
-- continuum-transfer chain.  Uniform form bounds, logarithmic functional
-- calculus, spectral transport, and finite transfer assemblies feed a Mosco /
-- readiness package, but they do not by themselves guarantee survival of the
-- continuum gap.  The stronger obligations are named explicitly:
--
--   H3a : trace / norm-resolvent control on the vacuum-orthogonal sector.
--   H3b : vacuum-projection continuity for the limiting vacuum.
--   NSP : no-spectral-pollution, downstream of H3a + H3b.
--
-- The surface remains fail-closed: no transfer theorem, continuum mass gap,
-- or Clay Yang-Mills promotion is proved here.

sprintNumber : Nat
sprintNumber = 119

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint119TransferCalculusAllObligationsReducer.agda"

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

transferCalculusAllObligationsReducerRecorded : Bool
transferCalculusAllObligationsReducerRecorded = true

transferCalculusPackageAssembledHere : Bool
transferCalculusPackageAssembledHere = true

transferCalculusRowsNormalizedHere : Bool
transferCalculusRowsNormalizedHere = true

allTransferCalculusObligationsClosedHere : Bool
allTransferCalculusObligationsClosedHere = false

transferLowerBoundReadyHere : Bool
transferLowerBoundReadyHere = false

transferLowerBoundTheoremProvedHere : Bool
transferLowerBoundTheoremProvedHere = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

uniformFormLowerBoundClosedHere : Bool
uniformFormLowerBoundClosedHere =
  Aggregator118.uniformFormLowerBoundClosedHere

logGeneratorCalculusClosedHere : Bool
logGeneratorCalculusClosedHere =
  Aggregator118.logGeneratorCalculusClosedHere

spectralTransportClosedHere : Bool
spectralTransportClosedHere =
  Aggregator118.spectralTransportClosedHere

transferAssemblyClosedHere : Bool
transferAssemblyClosedHere =
  Aggregator118.transferAssemblyClosedHere

criticalLowerBoundAssemblyClosedHere : Bool
criticalLowerBoundAssemblyClosedHere =
  Aggregator118.criticalLowerBoundAssemblyClosedHere

sprint117ReadinessReducerClosedHere : Bool
sprint117ReadinessReducerClosedHere =
  Aggregator118.reducerReadinessClosedHere

sprint118AggregatorClosedHere : Bool
sprint118AggregatorClosedHere =
  Aggregator118.allTransferCalculusObligationsClosedHere

h3aTraceNormResolventClosedHere : Bool
h3aTraceNormResolventClosedHere = false

h3bVacuumProjectionContinuityClosedHere : Bool
h3bVacuumProjectionContinuityClosedHere = false

noSpectralPollutionClosedHere : Bool
noSpectralPollutionClosedHere = false

sprint108UniformFormSourcePath : String
sprint108UniformFormSourcePath =
  "DASHI/Physics/Closure/YMSprint108UniformFormLowerBound.agda"

sprint108LogGeneratorSourcePath : String
sprint108LogGeneratorSourcePath =
  "DASHI/Physics/Closure/YMSprint108LogGeneratorCalculusBridge.agda"

sprint108SpectralTransportSourcePath : String
sprint108SpectralTransportSourcePath =
  "DASHI/Physics/Closure/YMSprint108SpectralGapTransport.agda"

sprint108TransferAssemblySourcePath : String
sprint108TransferAssemblySourcePath =
  "DASHI/Physics/Closure/YMSprint108TransferLowerBoundAssembly.agda"

sprint109CriticalAssemblySourcePath : String
sprint109CriticalAssemblySourcePath =
  "DASHI/Physics/Closure/YMSprint109TransferLowerBoundCriticalAssembly.agda"

sprint117ReducerSourcePath : String
sprint117ReducerSourcePath =
  "DASHI/Physics/Closure/YMSprint117TransferReadinessObligationReducer.agda"

sprint118AggregatorSourcePath : String
sprint118AggregatorSourcePath =
  "DASHI/Physics/Closure/YMSprint118TransferCalculusReadinessAggregator.agda"

uniformFormResolutionText : String
uniformFormResolutionText =
  "Resolve the uniform form lower-bound gate by inhabiting uniform coercivity, constant independence, normalization windows, and the closed lower-bound theorem."

logGeneratorResolutionText : String
logGeneratorResolutionText =
  "Resolve the log-generator gate by inhabiting the common-core logarithmic functional calculus, spectral mapping, positivity, and closure of the generator package."

spectralTransportResolutionText : String
spectralTransportResolutionText =
  "Resolve spectral transport by controlling threshold transport, isolated bottom-sector survival, no-collapse transport, and the finite spectral margin."

transferAssemblyResolutionText : String
transferAssemblyResolutionText =
  "Resolve transfer assembly by closing the finite transfer lower-bound theorem once the analytic form, calculus, and spectral transport gates are inhabited."

criticalAssemblyResolutionText : String
criticalAssemblyResolutionText =
  "Resolve the critical lower-bound assembly without promoting downstream continuum claims; this is still finite-level readiness data."

sprint117ReducerResolutionText : String
sprint117ReducerResolutionText =
  "Resolve the Sprint117 readiness reducer by discharging common-carrier, compactness, lower-semicontinuity, recovery, weak-compactness, uniform-form, log-generator, and spectral-transport obligations."

h3aTraceNormResolventResolutionText : String
h3aTraceNormResolventResolutionText =
  "Resolve H3a by proving trace / norm-resolvent control of the vacuum-orthogonal transfer matrices; Mosco liminf and readiness data are not enough to preserve the gap."

h3bVacuumProjectionContinuityResolutionText : String
h3bVacuumProjectionContinuityResolutionText =
  "Resolve H3b by proving vacuum-projection continuity for the limiting OS vacuum, downstream of H3a and RP.4."

noSpectralPollutionResolutionText : String
noSpectralPollutionResolutionText =
  "Resolve no-spectral-pollution only after H3a and H3b, using the stronger transfer control to exclude spurious continuum spectrum below the finite margin."

finalBoundaryResolutionText : String
finalBoundaryResolutionText =
  "Final boundary remains fail-closed: transfer-calculus and readiness rows are normalized, but H3a trace / norm-resolvent control, H3b vacuum-projection continuity, downstream no-spectral-pollution, transfer theorem closure, continuum mass gap, and Clay promotion remain false."

data ObligationTier : Set where
  finite-transfer-tier :
    ObligationTier
  readiness-tier :
    ObligationTier
  h3a-tier :
    ObligationTier
  h3b-tier :
    ObligationTier
  no-spectral-pollution-tier :
    ObligationTier
  final-boundary-tier :
    ObligationTier

data NormalizedTransferCalculusGate : Set where
  uniform-form-lower-bound-gate :
    NormalizedTransferCalculusGate
  log-generator-functional-calculus-gate :
    NormalizedTransferCalculusGate
  spectral-transport-gate :
    NormalizedTransferCalculusGate
  transfer-assembly-gate :
    NormalizedTransferCalculusGate
  critical-lower-bound-assembly-gate :
    NormalizedTransferCalculusGate
  sprint117-readiness-reducer-gate :
    NormalizedTransferCalculusGate
  h3a-trace-norm-resolvent-gate :
    NormalizedTransferCalculusGate
  h3b-vacuum-projection-continuity-gate :
    NormalizedTransferCalculusGate
  downstream-no-spectral-pollution-gate :
    NormalizedTransferCalculusGate
  final-fail-closed-boundary-gate :
    NormalizedTransferCalculusGate

data NormalizedRowStatus : Set where
  finite-package-open :
    NormalizedRowStatus
  readiness-package-open :
    NormalizedRowStatus
  stronger-h3a-open :
    NormalizedRowStatus
  stronger-h3b-open :
    NormalizedRowStatus
  downstream-after-h3a-h3b :
    NormalizedRowStatus
  final-nonpromotion-boundary :
    NormalizedRowStatus

record ImportedCanonicalReceipts : Setω where
  constructor mkImportedCanonicalReceipts
  field
    uniformFormReceipt :
      Form108.YMSprint108UniformFormLowerBoundReceipt
    logGeneratorReceipt :
      Log108.YMSprint108LogGeneratorCalculusBridgeReceipt
    spectralTransportReceipt :
      Spectral108.YMSprint108SpectralGapTransportReceipt
    transferAssemblyReceipt :
      Transfer108.YMSprint108TransferLowerBoundAssemblyReceipt
    criticalAssemblyReceipt :
      Critical109.YMSprint109TransferLowerBoundCriticalAssemblyReceipt
    sprint117ReducerReceipt :
      Reducer117.YMSprint117TransferReadinessObligationReducerReceipt
    sprint118AggregatorReceipt :
      Aggregator118.YMSprint118TransferCalculusReadinessAggregatorReceipt
    receiptsImported :
      Bool

record UpstreamClosureFlags : Set where
  constructor mkUpstreamClosureFlags
  field
    uniformFormLowerBoundClosed :
      Bool
    uniformFormLowerBoundClosedIsFalse :
      uniformFormLowerBoundClosed ≡ false
    logGeneratorCalculusClosed :
      Bool
    logGeneratorCalculusClosedIsFalse :
      logGeneratorCalculusClosed ≡ false
    spectralTransportClosed :
      Bool
    spectralTransportClosedIsFalse :
      spectralTransportClosed ≡ false
    transferAssemblyClosed :
      Bool
    transferAssemblyClosedIsFalse :
      transferAssemblyClosed ≡ false
    criticalLowerBoundAssemblyClosed :
      Bool
    criticalLowerBoundAssemblyClosedIsFalse :
      criticalLowerBoundAssemblyClosed ≡ false
    sprint117ReadinessReducerClosed :
      Bool
    sprint117ReadinessReducerClosedIsFalse :
      sprint117ReadinessReducerClosed ≡ false
    sprint118AllObligationsClosed :
      Bool
    sprint118AllObligationsClosedIsFalse :
      sprint118AllObligationsClosed ≡ false
    h3aClosed :
      Bool
    h3aClosedIsFalse :
      h3aClosed ≡ false
    h3bClosed :
      Bool
    h3bClosedIsFalse :
      h3bClosed ≡ false
    noSpectralPollutionClosed :
      Bool
    noSpectralPollutionClosedIsFalse :
      noSpectralPollutionClosed ≡ false

record NormalizedObligationRow : Set where
  constructor mkNormalizedObligationRow
  field
    gate :
      NormalizedTransferCalculusGate
    tier :
      ObligationTier
    status :
      NormalizedRowStatus
    sourcePath :
      String
    requiredResolution :
      String
    canonicalReceiptImported :
      Bool
    requiredBeforeTransferLowerBound :
      Bool
    upstreamFlag :
      Bool
    upstreamFlagIsFalse :
      upstreamFlag ≡ false
    rowNormalized :
      Bool

record ReducerPackageAssembly : Set where
  constructor mkReducerPackageAssembly
  field
    sourcePaths :
      List String
    requiredResolutions :
      List String
    upstreamFlags :
      UpstreamClosureFlags
    rows :
      List NormalizedObligationRow
    rowCount :
      Nat
    reducerRecorded :
      Bool
    packageAssembled :
      Bool
    rowsNormalized :
      Bool
    allObligationsClosedHereFlag :
      Bool
    allObligationsClosedHereIsFalse :
      allObligationsClosedHereFlag ≡ false
    transferLowerBoundReadyHereFlag :
      Bool
    transferLowerBoundReadyHereIsFalse :
      transferLowerBoundReadyHereFlag ≡ false

record FinalReducerBoundary : Set where
  constructor mkFinalReducerBoundary
  field
    boundaryResolution :
      String
    h3aClosedHereFlag :
      Bool
    h3aClosedHereIsFalse :
      h3aClosedHereFlag ≡ false
    h3bClosedHereFlag :
      Bool
    h3bClosedHereIsFalse :
      h3bClosedHereFlag ≡ false
    noSpectralPollutionClosedHereFlag :
      Bool
    noSpectralPollutionClosedHereIsFalse :
      noSpectralPollutionClosedHereFlag ≡ false
    allTransferCalculusObligationsClosedHereFlag :
      Bool
    allTransferCalculusObligationsClosedHereIsFalse :
      allTransferCalculusObligationsClosedHereFlag ≡ false
    transferLowerBoundReadyHereFlag :
      Bool
    transferLowerBoundReadyHereIsFalse :
      transferLowerBoundReadyHereFlag ≡ false
    transferLowerBoundTheoremProvedHereFlag :
      Bool
    transferLowerBoundTheoremProvedHereIsFalse :
      transferLowerBoundTheoremProvedHereFlag ≡ false
    continuumMassGapProvedHereFlag :
      Bool
    continuumMassGapProvedHereIsFalse :
      continuumMassGapProvedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    finalStatus :
      NormalizedRowStatus

record YMSprint119TransferCalculusAllObligationsReducerReceipt : Setω where
  constructor mkYMSprint119TransferCalculusAllObligationsReducerReceipt
  field
    sprint :
      Nat
    evidencePath :
      String
    importedCanonicalReceipts :
      ImportedCanonicalReceipts
    packageAssembly :
      ReducerPackageAssembly
    normalizedRows :
      List NormalizedObligationRow
    rowStatuses :
      List NormalizedRowStatus
    finalBoundary :
      FinalReducerBoundary
    sourcePaths :
      List String
    requiredResolutions :
      List String
    evidenceLedger :
      List String
    reducerRecorded :
      Bool
    packageAssembled :
      Bool
    rowsNormalized :
      Bool
    allTransferCalculusObligationsClosedHereFlag :
      Bool
    allTransferCalculusObligationsClosedHereIsFalse :
      allTransferCalculusObligationsClosedHereFlag ≡ false
    transferLowerBoundReadyHereFlag :
      Bool
    transferLowerBoundReadyHereIsFalse :
      transferLowerBoundReadyHereFlag ≡ false
    transferLowerBoundTheoremProvedHereFlag :
      Bool
    transferLowerBoundTheoremProvedHereIsFalse :
      transferLowerBoundTheoremProvedHereFlag ≡ false
    continuumMassGapProvedHereFlag :
      Bool
    continuumMassGapProvedHereIsFalse :
      continuumMassGapProvedHereFlag ≡ false
    h3aTraceNormResolventClosedHereFlag :
      Bool
    h3aTraceNormResolventClosedHereIsFalse :
      h3aTraceNormResolventClosedHereFlag ≡ false
    h3bVacuumProjectionContinuityClosedHereFlag :
      Bool
    h3bVacuumProjectionContinuityClosedHereIsFalse :
      h3bVacuumProjectionContinuityClosedHereFlag ≡ false
    noSpectralPollutionClosedHereFlag :
      Bool
    noSpectralPollutionClosedHereIsFalse :
      noSpectralPollutionClosedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false

open YMSprint119TransferCalculusAllObligationsReducerReceipt public

canonicalImportedCanonicalReceipts : ImportedCanonicalReceipts
canonicalImportedCanonicalReceipts =
  mkImportedCanonicalReceipts
    Form108.canonicalReceipt
    Log108.canonicalReceipt
    Spectral108.canonicalReceipt
    Transfer108.canonicalReceipt
    Critical109.canonicalReceipt
    Reducer117.canonicalReceipt
    Aggregator118.canonicalReceipt
    true

canonicalUpstreamClosureFlags : UpstreamClosureFlags
canonicalUpstreamClosureFlags =
  mkUpstreamClosureFlags
    uniformFormLowerBoundClosedHere
    refl
    logGeneratorCalculusClosedHere
    refl
    spectralTransportClosedHere
    refl
    transferAssemblyClosedHere
    refl
    criticalLowerBoundAssemblyClosedHere
    refl
    sprint117ReadinessReducerClosedHere
    refl
    sprint118AggregatorClosedHere
    refl
    h3aTraceNormResolventClosedHere
    refl
    h3bVacuumProjectionContinuityClosedHere
    refl
    noSpectralPollutionClosedHere
    refl

uniformFormNormalizedRow : NormalizedObligationRow
uniformFormNormalizedRow =
  mkNormalizedObligationRow
    uniform-form-lower-bound-gate
    finite-transfer-tier
    finite-package-open
    sprint108UniformFormSourcePath
    uniformFormResolutionText
    true
    true
    uniformFormLowerBoundClosedHere
    refl
    true

logGeneratorNormalizedRow : NormalizedObligationRow
logGeneratorNormalizedRow =
  mkNormalizedObligationRow
    log-generator-functional-calculus-gate
    finite-transfer-tier
    finite-package-open
    sprint108LogGeneratorSourcePath
    logGeneratorResolutionText
    true
    true
    logGeneratorCalculusClosedHere
    refl
    true

spectralTransportNormalizedRow : NormalizedObligationRow
spectralTransportNormalizedRow =
  mkNormalizedObligationRow
    spectral-transport-gate
    finite-transfer-tier
    finite-package-open
    sprint108SpectralTransportSourcePath
    spectralTransportResolutionText
    true
    true
    spectralTransportClosedHere
    refl
    true

transferAssemblyNormalizedRow : NormalizedObligationRow
transferAssemblyNormalizedRow =
  mkNormalizedObligationRow
    transfer-assembly-gate
    finite-transfer-tier
    finite-package-open
    sprint108TransferAssemblySourcePath
    transferAssemblyResolutionText
    true
    true
    transferAssemblyClosedHere
    refl
    true

criticalAssemblyNormalizedRow : NormalizedObligationRow
criticalAssemblyNormalizedRow =
  mkNormalizedObligationRow
    critical-lower-bound-assembly-gate
    finite-transfer-tier
    finite-package-open
    sprint109CriticalAssemblySourcePath
    criticalAssemblyResolutionText
    true
    true
    criticalLowerBoundAssemblyClosedHere
    refl
    true

sprint117ReducerNormalizedRow : NormalizedObligationRow
sprint117ReducerNormalizedRow =
  mkNormalizedObligationRow
    sprint117-readiness-reducer-gate
    readiness-tier
    readiness-package-open
    sprint117ReducerSourcePath
    sprint117ReducerResolutionText
    true
    true
    sprint117ReadinessReducerClosedHere
    refl
    true

h3aTraceNormResolventRow : NormalizedObligationRow
h3aTraceNormResolventRow =
  mkNormalizedObligationRow
    h3a-trace-norm-resolvent-gate
    h3a-tier
    stronger-h3a-open
    sprint118AggregatorSourcePath
    h3aTraceNormResolventResolutionText
    true
    true
    h3aTraceNormResolventClosedHere
    refl
    true

h3bVacuumProjectionContinuityRow : NormalizedObligationRow
h3bVacuumProjectionContinuityRow =
  mkNormalizedObligationRow
    h3b-vacuum-projection-continuity-gate
    h3b-tier
    stronger-h3b-open
    modulePath
    h3bVacuumProjectionContinuityResolutionText
    true
    true
    h3bVacuumProjectionContinuityClosedHere
    refl
    true

noSpectralPollutionRow : NormalizedObligationRow
noSpectralPollutionRow =
  mkNormalizedObligationRow
    downstream-no-spectral-pollution-gate
    no-spectral-pollution-tier
    downstream-after-h3a-h3b
    modulePath
    noSpectralPollutionResolutionText
    true
    true
    noSpectralPollutionClosedHere
    refl
    true

finalBoundaryNormalizedRow : NormalizedObligationRow
finalBoundaryNormalizedRow =
  mkNormalizedObligationRow
    final-fail-closed-boundary-gate
    final-boundary-tier
    final-nonpromotion-boundary
    modulePath
    finalBoundaryResolutionText
    true
    true
    allTransferCalculusObligationsClosedHere
    refl
    true

canonicalNormalizedRows : List NormalizedObligationRow
canonicalNormalizedRows =
  uniformFormNormalizedRow
  ∷ logGeneratorNormalizedRow
  ∷ spectralTransportNormalizedRow
  ∷ transferAssemblyNormalizedRow
  ∷ criticalAssemblyNormalizedRow
  ∷ sprint117ReducerNormalizedRow
  ∷ h3aTraceNormResolventRow
  ∷ h3bVacuumProjectionContinuityRow
  ∷ noSpectralPollutionRow
  ∷ finalBoundaryNormalizedRow
  ∷ []

canonicalRowStatuses : List NormalizedRowStatus
canonicalRowStatuses =
  finite-package-open
  ∷ finite-package-open
  ∷ finite-package-open
  ∷ finite-package-open
  ∷ finite-package-open
  ∷ readiness-package-open
  ∷ stronger-h3a-open
  ∷ stronger-h3b-open
  ∷ downstream-after-h3a-h3b
  ∷ final-nonpromotion-boundary
  ∷ []

canonicalSourcePaths : List String
canonicalSourcePaths =
  modulePath
  ∷ sprint108UniformFormSourcePath
  ∷ sprint108LogGeneratorSourcePath
  ∷ sprint108SpectralTransportSourcePath
  ∷ sprint108TransferAssemblySourcePath
  ∷ sprint109CriticalAssemblySourcePath
  ∷ sprint117ReducerSourcePath
  ∷ sprint118AggregatorSourcePath
  ∷ []

canonicalRequiredResolutions : List String
canonicalRequiredResolutions =
  uniformFormResolutionText
  ∷ logGeneratorResolutionText
  ∷ spectralTransportResolutionText
  ∷ transferAssemblyResolutionText
  ∷ criticalAssemblyResolutionText
  ∷ sprint117ReducerResolutionText
  ∷ h3aTraceNormResolventResolutionText
  ∷ h3bVacuumProjectionContinuityResolutionText
  ∷ noSpectralPollutionResolutionText
  ∷ finalBoundaryResolutionText
  ∷ []

canonicalReducerPackageAssembly : ReducerPackageAssembly
canonicalReducerPackageAssembly =
  mkReducerPackageAssembly
    canonicalSourcePaths
    canonicalRequiredResolutions
    canonicalUpstreamClosureFlags
    canonicalNormalizedRows
    10
    transferCalculusAllObligationsReducerRecorded
    transferCalculusPackageAssembledHere
    transferCalculusRowsNormalizedHere
    allTransferCalculusObligationsClosedHere
    refl
    transferLowerBoundReadyHere
    refl

canonicalFinalReducerBoundary : FinalReducerBoundary
canonicalFinalReducerBoundary =
  mkFinalReducerBoundary
    finalBoundaryResolutionText
    h3aTraceNormResolventClosedHere
    refl
    h3bVacuumProjectionContinuityClosedHere
    refl
    noSpectralPollutionClosedHere
    refl
    allTransferCalculusObligationsClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl
    final-nonpromotion-boundary

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  uniformFormResolutionText
  ∷ logGeneratorResolutionText
  ∷ spectralTransportResolutionText
  ∷ transferAssemblyResolutionText
  ∷ criticalAssemblyResolutionText
  ∷ sprint117ReducerResolutionText
  ∷ h3aTraceNormResolventResolutionText
  ∷ h3bVacuumProjectionContinuityResolutionText
  ∷ noSpectralPollutionResolutionText
  ∷ finalBoundaryResolutionText
  ∷ []

canonicalYMSprint119TransferCalculusAllObligationsReducerReceipt :
  YMSprint119TransferCalculusAllObligationsReducerReceipt
canonicalYMSprint119TransferCalculusAllObligationsReducerReceipt =
  mkYMSprint119TransferCalculusAllObligationsReducerReceipt
    sprintNumber
    modulePath
    canonicalImportedCanonicalReceipts
    canonicalReducerPackageAssembly
    canonicalNormalizedRows
    canonicalRowStatuses
    canonicalFinalReducerBoundary
    canonicalSourcePaths
    canonicalRequiredResolutions
    canonicalEvidenceLedger
    transferCalculusAllObligationsReducerRecorded
    transferCalculusPackageAssembledHere
    transferCalculusRowsNormalizedHere
    allTransferCalculusObligationsClosedHere
    refl
    transferLowerBoundReadyHere
    refl
    transferLowerBoundTheoremProvedHere
    refl
    continuumMassGapProvedHere
    refl
    h3aTraceNormResolventClosedHere
    refl
    h3bVacuumProjectionContinuityClosedHere
    refl
    noSpectralPollutionClosedHere
    refl
    clayYangMillsPromoted
    refl

canonicalReceipt :
  YMSprint119TransferCalculusAllObligationsReducerReceipt
canonicalReceipt =
  canonicalYMSprint119TransferCalculusAllObligationsReducerReceipt

finalReceipt :
  YMSprint119TransferCalculusAllObligationsReducerReceipt
finalReceipt =
  canonicalReceipt

canonicalReceiptAllTransferCalculusObligationsClosedHereIsFalse :
  allTransferCalculusObligationsClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptAllTransferCalculusObligationsClosedHereIsFalse =
  refl

canonicalReceiptTransferLowerBoundReadyHereIsFalse :
  transferLowerBoundReadyHereFlag canonicalReceipt ≡ false
canonicalReceiptTransferLowerBoundReadyHereIsFalse =
  refl

canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse :
  transferLowerBoundTheoremProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptTransferLowerBoundTheoremProvedHereIsFalse =
  refl

canonicalReceiptContinuumMassGapProvedHereIsFalse :
  continuumMassGapProvedHereFlag canonicalReceipt ≡ false
canonicalReceiptContinuumMassGapProvedHereIsFalse =
  refl

canonicalReceiptH3aTraceNormResolventClosedHereIsFalse :
  h3aTraceNormResolventClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptH3aTraceNormResolventClosedHereIsFalse =
  refl

canonicalReceiptH3bVacuumProjectionContinuityClosedHereIsFalse :
  h3bVacuumProjectionContinuityClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptH3bVacuumProjectionContinuityClosedHereIsFalse =
  refl

canonicalReceiptNoSpectralPollutionClosedHereIsFalse :
  noSpectralPollutionClosedHereFlag canonicalReceipt ≡ false
canonicalReceiptNoSpectralPollutionClosedHereIsFalse =
  refl

canonicalReceiptClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalReceiptClayYangMillsPromotedIsFalse =
  refl
