module DASHI.Physics.CondensedMatter.MATBGTHFSelfConsistencyObstructionReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record THFSelfConsistencyObstructionReceipt : Set where
  constructor thf-self-consistency-obstruction-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    sourceDOI : String
    targetFilling : String
    kmax004V0BestResidual : String
    kmax004V45BestResidual : String
    kmax008V45BestResidual : String
    cutoffSensitivityObserved : Bool
    notationSensitivityObserved : Bool
    assertionsPassed : Bool

open THFSelfConsistencyObstructionReceipt public

canonicalTHFSelfConsistencyObstructionReceipt : THFSelfConsistencyObstructionReceipt
canonicalTHFSelfConsistencyObstructionReceipt =
  thf-self-consistency-obstruction-receipt
    "scripts/matbg_thf_self_consistency_obstruction.py"
    "Docs/evidence/matbg_thf_self_consistency_obstruction_2026-10-16.json"
    "532d92811cf27c5a3a7d423c3de361b2fe91f9da0061a0caab2a7b5cf08fef8d"
    "10.1038/s41586-026-10378-x"
    "0.5"
    "0.3711765887520629"
    "0.6548573409329657"
    "0.13281777311953444"
    true true true

record THFSelfConsistencyObstructionBoundary : Set where
  constructor thf-self-consistency-obstruction-boundary
  field
    sourceEquationsNumericallyInstantiated : Bool
    finiteQuadratureExecuted : Bool
    unresolvedCutoffSensitivityExposed : Bool
    unresolvedVYNotationSensitivityExposed : Bool
    fullSourceFaithfulSelfConsistencyPaid : Bool
    qtmExperimentalFitPaid : Bool
    sameSampleEntropyPaid : Bool

open THFSelfConsistencyObstructionBoundary public

canonicalTHFSelfConsistencyObstructionBoundary : THFSelfConsistencyObstructionBoundary
canonicalTHFSelfConsistencyObstructionBoundary =
  thf-self-consistency-obstruction-boundary true true true true false false false

record THFSelfConsistencyObstructionAttributionBoundary : Set where
  constructor thf-self-consistency-obstruction-attribution-boundary
  field
    xiaoOwnsSourceEquationsAndParameters : Bool
    dashiOwnsFiniteQuadratureAndObstructionReceipt : Bool
    failedCoarseClosureDoesNotRefuteSourceModel : Bool
    numericalSensitivityDoesNotLicenseVEqualsY : Bool
    obstructionReceiptDoesNotCreateExperimentalAuthority : Bool

open THFSelfConsistencyObstructionAttributionBoundary public

canonicalTHFSelfConsistencyObstructionAttributionBoundary : THFSelfConsistencyObstructionAttributionBoundary
canonicalTHFSelfConsistencyObstructionAttributionBoundary =
  thf-self-consistency-obstruction-attribution-boundary true true true true true
