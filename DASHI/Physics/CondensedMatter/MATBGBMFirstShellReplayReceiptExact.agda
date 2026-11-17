module DASHI.Physics.CondensedMatter.MATBGBMFirstShellReplayReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EXECUTION RECEIPT, NOT THEOREM AUTHORITY
--
-- The deterministic Python artifact executes the 8-band/first-honeycomb-shell
-- BM reconstruction. It is a numerical DASHI receipt over source equations,
-- not the full converged plane-wave model and not experimental evidence.
------------------------------------------------------------------------

record FirstShellReplayReceipt : Set where
  constructor first-shell-replay-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    bmSourceDOI : String
    qtmRatioSourceDOI : String
    analyticVelocityRatioAtAlpha045 : String
    numericVelocityRatioAtAlpha045 : String
    analyticNumericAbsError : String
    equalTunnellingMagicVelocityRatio : String
    qtmRatioMagicVelocityRatio : String
    equalZeroModeError : String
    qtmRatioZeroModeError : String
    hermiticityError : String
    assertionsPassed : Bool

open FirstShellReplayReceipt public

canonicalFirstShellReplayReceipt : FirstShellReplayReceipt
canonicalFirstShellReplayReceipt =
  first-shell-replay-receipt
    "scripts/matbg_bm_first_shell_replay.py"
    "Docs/evidence/matbg_bm_first_shell_replay_2026-10-16.json"
    "684d5530d79a1441166a821c1459041c55cd80027e8f41793960632305486489"
    "10.1073/pnas.1108174108"
    "10.1038/s41586-026-10378-x"
    "0.17720090293453725"
    "0.17720090284870016"
    "8.583708743792329e-11"
    "3.3374763554324673e-07"
    "1.52754935854381e-07"
    "3.892417595082818e-16"
    "5.36771454185332e-16"
    "0.0"
    true

record FirstShellReplayBoundary : Set where
  constructor first-shell-replay-boundary
  field
    firstShellNumericalExecutionPaid : Bool
    sourceAnalyticVelocityParityPaid : Bool
    qtmRatioFixtureExecuted : Bool
    exactScriptHashRecorded : Bool
    fullPlaneWaveConvergencePaid : Bool
    absoluteSampleTunnellingScalePaid : Bool
    interactingSelfEnergyPaid : Bool
    qtmDataReplayPaid : Bool
    sameSampleEntropyPaid : Bool
    agdaKernelReceiptPaid : Bool

open FirstShellReplayBoundary public

canonicalFirstShellReplayBoundary : FirstShellReplayBoundary
canonicalFirstShellReplayBoundary =
  first-shell-replay-boundary
    true true true true
    false false false false false false

record ReplayAttributionBoundary : Set where
  constructor replay-attribution-boundary
  field
    bmOwnsFirstShellAndAnalyticSourceRole : Bool
    xiaoOwnsReportedW0W1Fit : Bool
    dashiOwnsReconstructionAndExecutionReceipt : Bool
    numericalParityDoesNotReattributeSourceScience : Bool
    numericalExecutionDoesNotCreateExperiment : Bool

open ReplayAttributionBoundary public

canonicalReplayAttributionBoundary : ReplayAttributionBoundary
canonicalReplayAttributionBoundary =
  replay-attribution-boundary true true true true true
