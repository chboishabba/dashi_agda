module DASHI.Physics.CondensedMatter.MATBGQuantumGeometryReplayReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record QuantumGeometryReplayReceipt : Set where
  constructor quantum-geometry-replay-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    bmSourceDOI : String
    sotaInspirationDOI : String
    shell3TraceMetric : String
    shell4TraceMetric : String
    shell4TracedBerryCurvature : String
    scanMinimumTraceMetric : String
    scanMaximumTraceMetric : String
    assertionsPassed : Bool

open QuantumGeometryReplayReceipt public

canonicalQuantumGeometryReplayReceipt : QuantumGeometryReplayReceipt
canonicalQuantumGeometryReplayReceipt =
  quantum-geometry-replay-receipt
    "scripts/matbg_bm_quantum_geometry.py"
    "Docs/evidence/matbg_bm_quantum_geometry_2026-10-16.json"
    "6538c8628f3bcffe0adb19cc55ebd1e355b85e168200a6f4663061d6dd72c6dc"
    "10.1073/pnas.1108174108"
    "10.1038/s41467-026-74848-6"
    "2.9265860289675167"
    "2.927082700067621"
    "-4.830198063352983e-13"
    "2.6090576996110237"
    "55.23293896045926"
    true

record QuantumGeometryBoundary : Set where
  constructor quantum-geometry-boundary
  field
    rankTwoCentralProjectorPaid : Bool
    projectorGeometryExecutionPaid : Bool
    shell3To4MetricConvergencePaid : Bool
    tracedBerryNearZeroNumericalReceiptPaid : Bool
    coarseMetricInhomogeneityPaid : Bool
    experimentalQuantumMetricCalibrationPaid : Bool
    interactingQuantumGeometryPaid : Bool
    sameSampleSuperconductivityWeldPaid : Bool
    chernNumberPaid : Bool
    agdaKernelReceiptPaid : Bool

open QuantumGeometryBoundary public

canonicalQuantumGeometryBoundary : QuantumGeometryBoundary
canonicalQuantumGeometryBoundary =
  quantum-geometry-boundary
    true true true true true
    false false false false false

record QuantumGeometryAttributionBoundary : Set where
  constructor quantum-geometry-attribution-boundary
  field
    bmOwnsSingleParticleModelSourceRole : Bool
    later2026QuantumGeometryPaperIsInspirationOnly : Bool
    laterATQGPaperIsNotMATBGSameObject : Bool
    dashiOwnsProjectorComputationAndReceipt : Bool
    numericalQuantumGeometryDoesNotCreateExperimentalCalibration : Bool

open QuantumGeometryAttributionBoundary public

canonicalQuantumGeometryAttributionBoundary : QuantumGeometryAttributionBoundary
canonicalQuantumGeometryAttributionBoundary =
  quantum-geometry-attribution-boundary true true true true true
