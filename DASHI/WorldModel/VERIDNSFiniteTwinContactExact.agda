module DASHI.WorldModel.VERIDNSFiniteTwinContactExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitRHSTangentRound65Exact as Tangent
import DASHI.Core.TrajectoryResidueExact as Residue
import DASHI.WorldModel.VERIDExperimentProofSearchBridgeExact as Experiment
import DASHI.WorldModel.VERIDIbrahimSnowballParetoBridgeExact as Frontier

------------------------------------------------------------------------
-- Owner-preserving bridge from the existing literal finite Galerkin RHS
-- and path-sensitive observer calculus to a separately executed numerical
-- simulator. Structural imports do NOT certify a numerical solver against
-- the Agda RHS or a finite approximation against continuum Navier-Stokes.
------------------------------------------------------------------------

finiteRHSCoordinateRetentionBoundary : Bool
finiteRHSCoordinateRetentionBoundary =
  Tangent.round65CanonicalOrbitGalerkinRHSPointwiseTangent

finiteRHSCoordinateRetentionIsTrue :
  finiteRHSCoordinateRetentionBoundary ≡ true
finiteRHSCoordinateRetentionIsTrue =
  Tangent.round65CanonicalOrbitGalerkinRHSPointwiseTangentIsTrue

trajectoryHistoryOwner : Residue.TrajectoryResidueBoundary
trajectoryHistoryOwner = Residue.canonicalTrajectoryResidueBoundary

literalExperimentalFrontier : Frontier.VERIDConsumerFrontier
literalExperimentalFrontier = Frontier.canonicalVERIDFrontier

------------------------------------------------------------------------
-- Numerical comparison receipts must stay different from physical receipts.
------------------------------------------------------------------------

record NSNumericalTwinContact : Set where
  constructor nsNumericalTwinContact
  field
    formalRHSReference : String
    modelSolverDigest : String
    comparisonSolverDigest : String
    measuredDiscrepancyReference : String
    timeGridAndCutoffReference : String
    identicalSolverCode : Bool
    physicallyValidated : Bool
    continuumAuthority : Bool
