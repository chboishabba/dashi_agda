module DASHI.Biology.CausalEstimatorAsymptoticProofDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Biology.CausalEstimatorMetricConsistencyExact as MetricConsistency
import DASHI.Biology.CausalEstimatorFiniteDispersionExact as FiniteDispersion

------------------------------------------------------------------------
-- ASYMPTOTIC FRONTIER
--
-- The introspective search has exhausted the source-native owners currently
-- visible for this causal-estimator lane.  Ordinary metric consistency reuses
-- MetricConvergenceKernelBidiExact; finite expectation, unbiasedness, variance
-- and MSE are exact rational constructions.  No owner was found for the exact
-- application-specific probability/distribution theorem needed to promote
-- convergence in probability, weak/distributional convergence, or asymptotic
-- normality.  This module records that as proof debt rather than manufacturing
-- a Gaussian/probability layer.
------------------------------------------------------------------------

data AsymptoticResidual : Set where
  convergenceInProbabilitySemantics : AsymptoticResidual
  distributionalConvergenceSemantics : AsymptoticResidual
  asymptoticNormalityTheorem : AsymptoticResidual
  standardErrorLimitCalibration : AsymptoticResidual

data AsymptoticProducerClass : Set where
  probabilityMeasureOwner : AsymptoticProducerClass
  distributionConvergenceOwner : AsymptoticProducerClass
  estimatorLimitTheoremOwner : AsymptoticProducerClass
  calibrationTheoremOwner : AsymptoticProducerClass

producerForResidual : AsymptoticResidual → AsymptoticProducerClass
producerForResidual convergenceInProbabilitySemantics = probabilityMeasureOwner
producerForResidual distributionalConvergenceSemantics = distributionConvergenceOwner
producerForResidual asymptoticNormalityTheorem = estimatorLimitTheoremOwner
producerForResidual standardErrorLimitCalibration = calibrationTheoremOwner

------------------------------------------------------------------------
-- Current exact selected debt.
--
-- For an arbitrary causal estimator, asymptotic normality is not available
-- merely from finite unbiasedness, finite variance, or metric consistency.
-- Until a same-estimator theorem/source is identified and aligned, the exact
-- application claim remains mathematical debt under the canonical router.
------------------------------------------------------------------------

selectedAsymptoticDebtRoute : Debt.ProofDebtRoutingReceipt
selectedAsymptoticDebtRoute =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.novelOpen
    Debt.notTranscribed
    Debt.uncertified
    Debt.sourceOnly
    Debt.mathematicalDebt
    refl

selectedAsymptoticDebtIsMathematical :
  Debt.routedDebt selectedAsymptoticDebtRoute ≡ Debt.mathematicalDebt
selectedAsymptoticDebtIsMathematical = refl

selectedAsymptoticSchedulerAction :
  Debt.scheduleAction
    (Debt.routedDebt selectedAsymptoticDebtRoute)
    (Debt.statementStatus selectedAsymptoticDebtRoute)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.researchMathematics
selectedAsymptoticSchedulerAction = refl

------------------------------------------------------------------------
-- Existing closed coordinates retained as witnesses to the introspective cut.
------------------------------------------------------------------------

metricConsistencyBoundary :
  MetricConsistency.CausalEstimatorMetricConsistencyBoundary
metricConsistencyBoundary =
  MetricConsistency.canonicalCausalEstimatorMetricConsistencyBoundary

finiteDispersionBoundary :
  FiniteDispersion.CausalEstimatorFiniteDispersionBoundary
finiteDispersionBoundary =
  FiniteDispersion.canonicalCausalEstimatorFiniteDispersionBoundary

introspectiveBoundary : Introspective.IntrospectiveProofLoopBoundary
introspectiveBoundary = Introspective.canonicalIntrospectiveProofLoopBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MetricConsistencyMeansProbabilityConsistencyPermission : Set where

data FiniteVarianceMeansAsymptoticNormalityPermission : Set where

data FiniteUnbiasednessMeansCLTPermission : Set where

data MissingOwnerMayBeReportedClosedPermission : Set where

data MathematicalDebtMayBeCalledCertificationDebtPermission : Set where

metricConsistencyDoesNotBecomeProbabilityConsistency :
  MetricConsistencyMeansProbabilityConsistencyPermission → ⊥
metricConsistencyDoesNotBecomeProbabilityConsistency ()

finiteVarianceDoesNotBecomeAsymptoticNormality :
  FiniteVarianceMeansAsymptoticNormalityPermission → ⊥
finiteVarianceDoesNotBecomeAsymptoticNormality ()

finiteUnbiasednessDoesNotBecomeCLT :
  FiniteUnbiasednessMeansCLTPermission → ⊥
finiteUnbiasednessDoesNotBecomeCLT ()

missingAsymptoticOwnerCannotBeReportedClosed :
  MissingOwnerMayBeReportedClosedPermission → ⊥
missingAsymptoticOwnerCannotBeReportedClosed ()

mathematicalDebtCannotBeRelabelledCertificationDebt :
  MathematicalDebtMayBeCalledCertificationDebtPermission → ⊥
mathematicalDebtCannotBeRelabelledCertificationDebt ()

record CausalEstimatorCompletionFrontier : Set where
  constructor causal-estimator-completion-frontier
  field
    finiteExpectationClosed : Bool
    finiteUnbiasednessClosed : Bool
    finiteVarianceAndMSEClosed : Bool
    metricConsistencyShapeClosed : Bool
    convergenceInProbabilityClosed : Bool
    distributionalConvergenceClosed : Bool
    asymptoticNormalityClosed : Bool
    standardErrorLimitCalibrationClosed : Bool
    currentDebtIsMathematicalOrSourceTheoremOwnership : Bool
    certificationDebtClaimedForMissingMathematics : Bool

canonicalCausalEstimatorCompletionFrontier :
  CausalEstimatorCompletionFrontier
canonicalCausalEstimatorCompletionFrontier =
  causal-estimator-completion-frontier
    true true true true
    false false false false
    true false
