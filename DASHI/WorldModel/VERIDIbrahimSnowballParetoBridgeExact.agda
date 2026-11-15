module DASHI.WorldModel.VERIDIbrahimSnowballParetoBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.WorldModel.VERIDExperimentProofSearchBridgeExact as VERID
import DASHI.Core.SnowballAtomWrongTypeScaleInvariantExact as Snowball
import DASHI.Core.LiteralFrontierSchedulerExact as Scheduler
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Pareto
import DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact as Ibrahim

------------------------------------------------------------------------
-- The VERID consumer is a concrete, optional snowball target. Historical
-- Ibrahim first-link data are NOT laboratory results and do not license
-- physical action. Reuse their same-object/provenance/priority discipline.
------------------------------------------------------------------------

record VERIDSourceCandidate : Set where
  constructor veridSourceCandidate
  field
    sourceReference : String
    objectReference : String
    claimReference : String
    dependencyReference : String
    physicalCalibrationReference : String

open VERIDSourceCandidate public

record VERIDConsumerFrontier : Set₁ where
  constructor veridConsumerFrontier
  field
    source : VERIDSourceCandidate
    move : Scheduler.LiteralFrontierMove
    disposition : Scheduler.LiteralMoveOutcome move
    laboratoryConsumerReference : String
    evidenceCeilingReference : String

open VERIDConsumerFrontier public

canonicalSnowballBoundary : Snowball.SnowballAcquisitionPaymentBoundary
canonicalSnowballBoundary =
  Snowball.canonicalSnowballAcquisitionPaymentBoundary

canonicalParetoBoundary : Pareto.ProofSearchExperimentalParetoBoundary
canonicalParetoBoundary =
  Pareto.canonicalProofSearchExperimentalParetoBoundary

canonicalSchedulerBoundary : Scheduler.LiteralFrontierSchedulerBoundary
canonicalSchedulerBoundary =
  Scheduler.canonicalLiteralFrontierSchedulerBoundary

ibrahimMetadataIsNotPhysicalAuthority : Ibrahim.ParetoFrontierLeaf
ibrahimMetadataIsNotPhysicalAuthority = Ibrahim.metadataCleanup

------------------------------------------------------------------------
-- Literal current frontier: discrimination is a redirect, not theorem
-- closure or a hardware dispatch receipt.
------------------------------------------------------------------------

discriminatorMove : Scheduler.LiteralFrontierMove
discriminatorMove = Scheduler.literalFrontierMove
  Pareto.derivedExperimentalCoordinate
  "VERID consumer-relative unsafe coarse observer"
  "measure discriminating laboratory state coordinate"
  "same coarse state with different downstream action outcomes"
  "physical action admissibility at explicit state version"
  "symbolic two-world regression; no physical calibration"
  "measurement proposal; no actuator authority"
  "cost/risk/discrimination comparison remains consumer-relative"

discriminatorRedirect : Scheduler.LiteralMoveOutcome discriminatorMove
discriminatorRedirect = Scheduler.redirected
  (Scheduler.redirectedLiteralMove
    true refl
    "calibrated measurement and global consumer sufficiency outstanding"
    "retain symbolic discriminator separately from empirical receipts"
    "refine the observer, then rerun safety and actionability checks")

canonicalVERIDFrontier : VERIDConsumerFrontier
canonicalVERIDFrontier = veridConsumerFrontier
  (veridSourceCandidate
    "Google VERID paper: empirical demonstration source"
    "paper versus simulator versus robot execution trace"
    "bounded aqueous demonstration; not biological discovery"
    "instrument calibration and state snapshot remain open"
    "none in symbolic fixture")
  discriminatorMove
  discriminatorRedirect
  "laboratory-specific safe action prediction"
  "model-safe does not entail physical success or causal identification"
