module DASHI.Physics.YangMills.YMClaySUNMatrixR445R320SameCovarianceExact where

------------------------------------------------------------------------
-- R445 -> R320: ACTUAL REAL SU(N) SIX-PLANE GIBBS -> R278 COVARIANCE.
--
-- This composes original existing carriers, not another model:
--   original periodic SU(N) matrix six-positive-plane Wilson/Gibbs source
--   -> canonical normalized finite physical expectations (R445)
--   -> exactly those finite expectation measures (CMP119/R278)
--   -> selected real connected-covariance convergence compiler.
--
-- Source-first mathematical limitations:
-- - CMP116 mixed-source differentiated logZ/rooted-shell decay is NOT
--   inferred from bare covariance convergence.
-- - this n=3 side-four sequence is fixed-volume; it does not become a
--   four-dimensional scaling limit by naming the cutoff Nat.
-- - the same OS reconstructed Hamiltonian and spectral gap remain unpaid.
--
-- Balaban CMP116 (1988), DOI 10.1007/BF01239022; Wilson (1974),
-- DOI 10.1103/PhysRevD.10.2445; Osterwalder-Schrader CMP 42
-- (1975), DOI 10.1007/BF01608978. Previous DASHI R278/R320 owner credit
-- retained; new source-specific instantiation owned by DASHI.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSameFamilyR443R445Exact as Family
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

originalSUNR278Measure :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division}
    (source : Family.SUNOriginalWilsonFiniteFamily
      theory traceData exponential
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (algebra : OS2.CylinderOSAlgebra
      (Native.SUNSideFourLinks N theory → ℝ)) →
  Gram.PhysicalMeasureConvergenceData
    (Carrier.ExpectationMeasure (Native.SUNSideFourLinks N theory → ℝ))
    (Native.SUNSideFourLinks N theory → ℝ) ℝ
originalSUNR278Measure source algebra =
  Carrier.cmp119PhysicalMeasureConvergenceDataFromFamily
    (Family.sameOriginalFiniteMeasureFamily source) algebra

originalSUNR278FiniteSameExpectation :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division}
    (source : Family.SUNOriginalWilsonFiniteFamily
      theory traceData exponential
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (algebra : OS2.CylinderOSAlgebra
      (Native.SUNSideFourLinks N theory → ℝ))
    cutoff observable →
  Gram.expectation
    (Gram.operations (originalSUNR278Measure source algebra))
    (Gram.measureSequence (originalSUNR278Measure source algebra) cutoff)
    observable
  ≡ Limit.finiteExpectation
      (Family.sameOriginalFiniteMeasureFamily source) cutoff observable
originalSUNR278FiniteSameExpectation source algebra cutoff observable = refl

originalSUNR278ContinuumSameLimit :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division}
    (source : Family.SUNOriginalWilsonFiniteFamily
      theory traceData exponential
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (algebra : OS2.CylinderOSAlgebra
      (Native.SUNSideFourLinks N theory → ℝ))
    observable →
  Gram.expectation
    (Gram.operations (originalSUNR278Measure source algebra))
    (Gram.continuumMeasure (originalSUNR278Measure source algebra))
    observable
  ≡ Limit.limitExpectation
      (Family.sameOriginalFiniteMeasureFamily source) observable
originalSUNR278ContinuumSameLimit source algebra observable = refl

originalSUNRealCovarianceExtension :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division}
    (source : Family.SUNOriginalWilsonFiniteFamily
      theory traceData exponential
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (algebra : OS2.CylinderOSAlgebra
      (Native.SUNSideFourLinks N theory → ℝ))
    (laws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit) →
  R278.ScalarCovarianceConvergenceExtension
    (originalSUNR278Measure source algebra)
originalSUNRealCovarianceExtension source algebra laws =
  Cov.realCovarianceExtensionFromFamily
    (Family.sameOriginalFiniteMeasureFamily source) algebra laws
