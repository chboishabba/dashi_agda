module DASHI.Physics.CondensedMatter.MATBGBMPlaneWaveReplayReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record PlaneWaveReplayReceipt : Set where
  constructor plane-wave-replay-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    bmSourceDOI : String
    xiaoRatioSourceDOI : String
    implementationCrosscheck : String
    shell2BandwidthEV : String
    shell3BandwidthEV : String
    shell4BandwidthEV : String
    shell2Dimension : String
    shell3Dimension : String
    shell4Dimension : String
    relaxedMinimumThetaDeg : String
    relaxedMinimumBandwidthEV : String
    assertionsPassed : Bool

open PlaneWaveReplayReceipt public

canonicalPlaneWaveReplayReceipt : PlaneWaveReplayReceipt
canonicalPlaneWaveReplayReceipt =
  plane-wave-replay-receipt
    "scripts/matbg_bm_plane_wave_replay.py"
    "Docs/evidence/matbg_bm_plane_wave_replay_2026-10-16.json"
    "8558c6e9c048acbe4142524dbd824648815cd3251692bc1756c071d4e8f5259a"
    "10.1073/pnas.1108174108"
    "10.1038/s41586-026-10378-x"
    "R-Carrasco/tbg-simulator (MIT), inspected as an external implementation cross-check; DASHI reconstruction written independently"
    "0.04008548338121812"
    "0.027903563960662826"
    "0.0278976317849461"
    "56" "132" "228"
    "1.084999999999999"
    "0.0009274612896131532"
    true

record PlaneWaveReplayBoundary : Set where
  constructor plane-wave-replay-boundary
  field
    reciprocalLatticeExecutionPaid : Bool
    hermiticityChecksPaid : Bool
    shell3To4ConvergencePaid : Bool
    relaxedMagicAngleCrosscheckPaid : Bool
    xiaoRatioCoordinateUsed : Bool
    xiaoAbsoluteSampleCalibrationPaid : Bool
    interactingSelfEnergyPaid : Bool
    qtmDataReplayPaid : Bool
    sameSampleEntropyPaid : Bool
    agdaKernelReceiptPaid : Bool

open PlaneWaveReplayBoundary public

canonicalPlaneWaveReplayBoundary : PlaneWaveReplayBoundary
canonicalPlaneWaveReplayBoundary =
  plane-wave-replay-boundary
    true true true true true
    false false false false false

record PlaneWaveAttributionBoundary : Set where
  constructor plane-wave-attribution-boundary
  field
    bmOwnsContinuumScientificSourceRole : Bool
    xiaoOwnsReportedRatio : Bool
    externalSimulatorOwnsItsIndependentImplementation : Bool
    dashiOwnsIndependentReconstructionAndReceipt : Bool
    crosscheckDoesNotTransferExternalCodeAuthorship : Bool
    numericalConvergenceDoesNotCreateSameSampleExperiment : Bool

open PlaneWaveAttributionBoundary public

canonicalPlaneWaveAttributionBoundary : PlaneWaveAttributionBoundary
canonicalPlaneWaveAttributionBoundary =
  plane-wave-attribution-boundary true true true true true true
