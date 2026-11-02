module DASHI.Physics.YangMills.YMClaySUNMatrixSameFamilyR443R445Exact where

------------------------------------------------------------------------
-- R443->R445: SAME ORIGINAL REAL SU(N) MATRIX-LINK GIBBS CUT-OFF FAMILY.
--
-- The finite Wilson action, gauge value, density and partition function now
-- depend definitionally on the SAME native signed-link SU(N) matrix field,
-- original six positive plaquettes and the one selected product-Haar
-- functional per cutoff. No rational-point Haar or auxiliary siteGauge
-- integration is substituted.
--
-- R445's canonical finite-expectation owner is reused; the remaining source
-- inputs have mathematical content: actual full product SU(N) Haar and its
-- integration laws, a nonzero selected partition, and a variable-scale
-- *physical* continuum/projection measure. This n=3 family has fixed
-- side-four geometry even when its beta varies: it is NOT a UV continuum.
--
-- Wilson (1974), Bałaban (CMP 99, 1985, DOI 10.1007/BF01466594),
-- R443/R445 and original DASHI owners retain attribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact as Gibbs
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

-- Only real SU(N) matrix fields are allowed; these inputs are not rational
-- quaternion configurations. All cutoffs share one fixed lattice carrier.
record SUNOriginalWilsonFiniteFamily
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient) : Set₁ where
  field
    beta : Nat → ℝ
    productHaar :
      Nat →
      (Native.SUNSideFourLinks N theory → ℝ) → ℝ

    -- The measure is NOT a new arbitrary field. It is definitionally the
    -- literal original six-plane SU(N) Gibbs source at every cutoff.
    actualIntegrationLaws : ∀ cutoff →
      Finite.PhysicalFiniteMeasureIntegrationLaws
        (Gibbs.nativeSUNFiniteGibbsMeasure
          theory traceData exponential (beta cutoff)
          (productHaar cutoff) (Quotient.divide quotient))

    actualPartitionNonzero : ∀ cutoff →
      Quotient.Nonzero quotient
        (Physical.partitionFunction
          (Gibbs.nativeSUNFiniteGibbsMeasure
            theory traceData exponential (beta cutoff)
            (productHaar cutoff) (Quotient.divide quotient)))

open SUNOriginalWilsonFiniteFamily public

finitePhysicalMeasure :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division} →
  (source : SUNOriginalWilsonFiniteFamily
    theory traceData exponential
    {sequenceLimit = sequenceLimit} limitLaws quotient division) →
  Nat → Physical.PhysicalFiniteYMMeasure (Native.SUNSideFourLinks N theory) ℝ
finitePhysicalMeasure {theory = theory} {traceData = traceData}
    {exponential = exponential} {quotient = quotient} source cutoff =
  Gibbs.nativeSUNFiniteGibbsMeasure
    theory traceData exponential (beta source cutoff)
    (productHaar source cutoff) (Quotient.divide quotient)

-- Reuse canonical finite-normalized and selected-expectation compiler.
-- No second continuum object, no measure equality assumption.
sameOriginalFiniteMeasureFamily :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division} →
  SUNOriginalWilsonFiniteFamily
    theory traceData exponential
    {sequenceLimit = sequenceLimit} limitLaws quotient division →
  Limit.FinitePhysicalNormalizedFamily
    (Native.SUNSideFourLinks N theory)
    {sequenceLimit = sequenceLimit} limitLaws quotient division
sameOriginalFiniteMeasureFamily source = record
  { Limit.FinitePhysicalNormalizedFamily.finiteMeasure =
      finitePhysicalMeasure source
  ; Limit.FinitePhysicalNormalizedFamily.integrationLaws =
      actualIntegrationLaws source
  ; Limit.FinitePhysicalNormalizedFamily.partitionNonzero =
      actualPartitionNonzero source
  }

-- Partition is DEFINITIONALLY the Haar integral of the original SU(N)
-- six-plane exponential on this very same finite configuration.
originalSixPartitionSameObject :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division}
    (source : SUNOriginalWilsonFiniteFamily
      theory traceData exponential
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    cutoff →
  Physical.partitionFunction (finitePhysicalMeasure source cutoff)
  ≡ productHaar source cutoff
      (Gibbs.nativeSUNWilsonGibbsDensity
        theory traceData exponential (beta source cutoff))
originalSixPartitionSameObject source cutoff = refl

-- This provides the literal canonical R445 cutoff expectation; it does
-- not assert that the selected real sequence converges physically.
originalSixFiniteExpectation :
  ∀ {Matrix Complex : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    {traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory}
    {exponential : Exp.StrictPositiveRealExponential}
    {sequenceLimit limitLaws quotient division}
    (source : SUNOriginalWilsonFiniteFamily
      theory traceData exponential
      {sequenceLimit = sequenceLimit} limitLaws quotient division)
    (cutoff : Nat)
    (observable : Native.SUNSideFourLinks N theory → ℝ) →
  ℝ
originalSixFiniteExpectation source cutoff observable =
  Limit.finiteExpectation (sameOriginalFiniteMeasureFamily source)
    cutoff observable
