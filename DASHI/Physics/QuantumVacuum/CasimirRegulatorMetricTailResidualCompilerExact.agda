module DASHI.Physics.QuantumVacuum.CasimirRegulatorMetricTailResidualCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.CasimirResidualCauchyToLimitExact as Residual
import DASHI.Physics.QuantumVacuum.CasimirResidualConvergenceRouteBidiExact as Route
import DASHI.Physics.QuantumVacuum.CasimirRegulatorMetricTailReceiptExact as Tail

------------------------------------------------------------------------
-- PROOF-BEARING METRIC TAIL -> LITERAL CASIMIR RESIDUAL LIMIT
------------------------------------------------------------------------

record ProofBearingResidualMetricTailWeld
    (P : Metric.ParameterisedMetricLimitProblem)
    (T : Tail.ProofBearingMetricTail P) : Set₁ where
  field
    residualAt : Nat → Spine.Carrier Residual.Real
    sequence : Spine.Sequence Residual.Real

    sequenceIsResidual : ∀ n →
      Spine._≈_ Residual.Real
        (Spine.sequenceAt Residual.Real sequence n)
        (residualAt n)

    ParameterWitness : Set
    parameterWitness : ParameterWitness

    candidate : Spine.Carrier Residual.Real

    SameLiteralResidualTrajectory : Set
    sameLiteralResidualTrajectoryEvidence : SameLiteralResidualTrajectory

    SameCandidateAsRenormalisedEnergy : Set
    sameCandidateAsRenormalisedEnergyEvidence :
      SameCandidateAsRenormalisedEnergy

    metricTailToBishopConvergence :
      Metric.PointwiseMetricConvergence P →
      SameLiteralResidualTrajectory →
      SameCandidateAsRenormalisedEnergy →
      Spine.ConvergesTo Residual.Real sequence candidate

    reading : String

open ProofBearingResidualMetricTailWeld public

asLegacyDirectResidualMetricLimit :
  ∀ {P} {T : Tail.ProofBearingMetricTail P} →
  ProofBearingResidualMetricTailWeld P T →
  Route.DirectResidualMetricLimit
asLegacyDirectResidualMetricLimit {P} {T} W = record
  { Route.residualAt = residualAt W
  ; Route.sequence = sequence W
  ; Route.sequenceIsResidual = sequenceIsResidual W
  ; Route.metricProblem = P
  ; Route.metricConvergence = Tail.asPointwiseMetricConvergence T
  ; Route.ParameterWitness = ParameterWitness W
  ; Route.parameterWitness = parameterWitness W
  ; Route.candidate = candidate W
  ; Route.sameLiteralResidualTrajectory = SameLiteralResidualTrajectory W
  ; Route.sameCandidateLimit = SameCandidateAsRenormalisedEnergy W
  ; Route.directMetricTailImpliesBishopConvergence = λ convergence →
      metricTailToBishopConvergence W
        convergence
        (sameLiteralResidualTrajectoryEvidence W)
        (sameCandidateAsRenormalisedEnergyEvidence W)
  ; Route.reading = reading W
  }

compileProofBearingDirectResidualLimit :
  ∀ {P} {T : Tail.ProofBearingMetricTail P} →
  ProofBearingResidualMetricTailWeld P T →
  Route.ResidualLimitResult
compileProofBearingDirectResidualLimit W =
  Route.compileResidualLimit
    (Route.viaDirectMetricTail
      (asLegacyDirectResidualMetricLimit W))

------------------------------------------------------------------------
-- Reverse search: only three local facts remain after the actual tail theorem.
------------------------------------------------------------------------

record ReverseProofBearingResidualTailObligations : Set where
  field
    literalResidualTrajectoryIdentification : Set
    renormalisedCandidateIdentification : Set
    metricToBishopConvergenceTransport : Set
    reading : String

open ReverseProofBearingResidualTailObligations public

data LegacyBareSameObjectLabelsSufficeForProofBearingCompiler : Set where

legacyLabelsDoNotSupplyEvidence :
  LegacyBareSameObjectLabelsSufficeForProofBearingCompiler → ⊥
legacyLabelsDoNotSupplyEvidence ()

record Status : Set where
  field
    proofBearingMetricTailConsumed : Bool
    trajectoryWeldProofBearing : Bool
    candidateWeldProofBearing : Bool
    directResidualLimitCompilerOwned : Bool
    concreteTailBoundClosed : Bool

    proofBearingMetricTailConsumedIsTrue : proofBearingMetricTailConsumed ≡ true
    trajectoryWeldProofBearingIsTrue : trajectoryWeldProofBearing ≡ true
    candidateWeldProofBearingIsTrue : candidateWeldProofBearing ≡ true
    directResidualLimitCompilerOwnedIsTrue : directResidualLimitCompilerOwned ≡ true
    concreteTailBoundClosedIsFalse : concreteTailBoundClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { proofBearingMetricTailConsumed = true
  ; trajectoryWeldProofBearing = true
  ; candidateWeldProofBearing = true
  ; directResidualLimitCompilerOwned = true
  ; concreteTailBoundClosed = false
  ; proofBearingMetricTailConsumedIsTrue = refl
  ; trajectoryWeldProofBearingIsTrue = refl
  ; candidateWeldProofBearingIsTrue = refl
  ; directResidualLimitCompilerOwnedIsTrue = refl
  ; concreteTailBoundClosedIsFalse = refl
  }
