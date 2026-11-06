module DASHI.Physics.YangMills.YMClayE1OriginalSUNFiniteCylinderLawsExact where

------------------------------------------------------------------------
-- E1: finite normalized state laws of the ACTUAL variable-size SU(N)
-- Wilson/Haar family, reusing the existing normalized physical numerator
-- algebra AT EACH distinct cutoff carrier.
--
-- The only finite-source inputs below are actual integration laws and
-- original partition nonvanishing. There are NO independent finite
-- normalization/linearity/positivity assumptions.
--
-- This is finite mathematics. It does not assert a physical continuum
-- limit, clustering, spectral gap, noncollapse, or all compact simple G.
-- The real arithmetic is the repository's explicit non-safe axiom socket.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClayE1OriginalSUNDependentCylinderExact as Native
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws) quotient)
  where

  nativeMeasure :
    (n : Nat) →
    Physical.PhysicalFiniteYMMeasure
      (Native.ActualLinks theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient) n) ℝ
  nativeMeasure = Native.actualOriginalWilsonMeasureAt
    theory traceData exponential beta oneLink bilateral
    (Quotient.divide quotient)

  nativeExpectation :
    (n : Nat) →
    Native.Cylinder theory traceData exponential beta oneLink
      bilateral (Quotient.divide quotient) → ℝ
  nativeExpectation = Native.actualOriginalWilsonCylinderExpectation
    theory traceData exponential beta oneLink bilateral
    (Quotient.divide quotient)

  record ActualNativeFiniteIntegration : Set₁ where
    field
      integrals : ∀ n →
        Finite.PhysicalFiniteMeasureIntegrationLaws
          (nativeMeasure n)

      nonzero : ∀ n →
        Quotient.Nonzero quotient
          (Physical.partitionFunction (nativeMeasure n))

  open ActualNativeFiniteIntegration public

  -- Existing finite-cylinder normalized laws apply at any ONE n by
  -- making an irrelevant constant family at that fixed link carrier.
  -- The actual source across n is STILL the varying nativeMeasure.
  fixedCutoffFiniteLaws :
    ActualNativeFiniteIntegration →
    (n : Nat) →
    Limit.FinitePhysicalNormalizedFamily
      (Native.ActualLinks theory traceData exponential beta
        oneLink bilateral (Quotient.divide quotient) n)
      limitLaws quotient division
  fixedCutoffFiniteLaws source n = record
    { Limit.FinitePhysicalNormalizedFamily.finiteMeasure =
        λ _ → nativeMeasure n
    ; Limit.FinitePhysicalNormalizedFamily.integrationLaws =
        λ _ → integrals source n
    ; Limit.FinitePhysicalNormalizedFamily.partitionNonzero =
        λ _ → nonzero source n
    }

  -- Notice: finiteExpectation (fixedCutoffFiniteLaws source n) zero
  -- is definitionally the true original Wilson normalized expectation
  -- at cutoff n, because the quotient/divide are the same function.
  nativeExpectationZero :
    (source : ActualNativeFiniteIntegration) →
    ∀ n →
    nativeExpectation n
      (Native.zeroCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient))
    ≡ 0ℝ
  nativeExpectationZero source n =
    Limit.finiteExpectationZero (fixedCutoffFiniteLaws source n) zero

  nativeExpectationOne :
    (source : ActualNativeFiniteIntegration) →
    ∀ n →
    nativeExpectation n
      (Native.oneCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient))
    ≡ 1ℝ
  nativeExpectationOne source n =
    Limit.finiteExpectationOne (fixedCutoffFiniteLaws source n) zero

  nativeExpectationAdd :
    (source : ActualNativeFiniteIntegration) →
    ∀ n left right →
    nativeExpectation n
      (Native.addCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient) left right)
    ≡ nativeExpectation n left +ℝ nativeExpectation n right
  nativeExpectationAdd source n left right =
    Limit.finiteExpectationAdd (fixedCutoffFiniteLaws source n)
      zero (λ links → left n links) (λ links → right n links)

  nativeExpectationScale :
    (source : ActualNativeFiniteIntegration) →
    ∀ n scalar cylinder →
    nativeExpectation n
      (Native.scaleCylinder theory traceData exponential beta oneLink
        bilateral (Quotient.divide quotient) scalar cylinder)
    ≡ scalar *ℝ nativeExpectation n cylinder
  nativeExpectationScale source n scalar cylinder =
    Limit.finiteExpectationScale (fixedCutoffFiniteLaws source n)
      zero scalar (λ links → cylinder n links)

  nativeExpectationPositive :
    (source : ActualNativeFiniteIntegration) →
    ∀ n cylinder →
    (∀ links → 0ℝ ≤ℝ cylinder n links) →
    0ℝ ≤ℝ nativeExpectation n cylinder
  nativeExpectationPositive source n cylinder positive =
    Limit.finiteExpectationPositive (fixedCutoffFiniteLaws source n)
      zero (λ links → cylinder n links) positive
