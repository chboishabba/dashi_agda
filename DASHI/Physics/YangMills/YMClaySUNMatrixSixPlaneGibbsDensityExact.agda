module DASHI.Physics.YangMills.YMClaySUNMatrixSixPlaneGibbsDensityExact where

------------------------------------------------------------------------
-- R443: ACTUAL SUN MATRIX-LINK SIX POSITIVE-PLANE WILSON/GIBBS DENSITY.
--
-- Use the genuine SU(N) MATRIX link type already owned by SUNMatrixCarrier,
-- the ORIGINAL positive plaquettes and signed native holonomy, and existing
-- real finite-sum owner. This is not the rational SU2 surrogate.
--
-- Density exp(-beta * sum_{x,mu<nu}(1-ReTr_N U_p)) is here DEFINED from
-- the same native six-positive-plane Wilson source, rather than supplied by
-- an unconstrained 'density = Gibbs' equality. A positive exponential
-- implementation from the existing standard real-analysis owner gives
-- strict positivity immediately. A link-Haar functional and actual uniform
-- continuum family remain separate mathematical requirements.
--
-- Original: K. Wilson, Phys. Rev. D 10 (1974), 2445-2459,
-- DOI 10.1103/PhysRevD.10.2445; Bałaban, CMP 99 (1985), 75-102,
-- DOI 10.1007/BF01466594. DASHI owns the source-specific matrix weld.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _-ℝ_; _*ℝ_; -ℝ_; _<ℝ_)
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

sumFourReal : (Hodge.Index4 → ℝ) → ℝ
sumFourReal term =
  term Hodge.index0 +ℝ
    (term Hodge.index1 +ℝ
      (term Hodge.index2 +ℝ (term Hodge.index3 +ℝ 0ℝ)))

sumSitesReal : (Hodge.Site4 → ℝ) → ℝ
sumSitesReal term =
  sumFourReal (λ x0 →
    sumFourReal (λ x1 →
      sumFourReal (λ x2 →
        sumFourReal (λ x3 →
          term (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))))))

nativeSUNSixWilsonDeficitAt :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory) →
  Native.SUNSideFourLinks N theory → Hodge.Site4 → ℝ
nativeSUNSixWilsonDeficitAt theory traceData links site =
  Sums.realSum (Plaquette.ownedPeriodicPlaquettes site)
    (λ p → 1ℝ -ℝ Trace.matrixWilsonValue traceData
      (Native.sunPositivePlaquetteHolonomy theory links p))

nativeSUNSixWilsonDeficit :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory) →
  Native.SUNSideFourLinks N theory → ℝ
nativeSUNSixWilsonDeficit theory traceData links =
  sumSitesReal (nativeSUNSixWilsonDeficitAt theory traceData links)

nativeSUNWilsonAction :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (beta : ℝ) →
  Native.SUNSideFourLinks N theory → ℝ
nativeSUNWilsonAction theory traceData beta links =
  beta *ℝ nativeSUNSixWilsonDeficit theory traceData links

-- The Euclidean Gibbs density now has a literal body on the actual
-- source-group lattice. Only the real exponential mathematics is imported.
nativeSUNWilsonGibbsDensity :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ) →
  Native.SUNSideFourLinks N theory → ℝ
nativeSUNWilsonGibbsDensity theory traceData exponential beta links =
  Exp.expReal exponential
    (-ℝ nativeSUNWilsonAction theory traceData beta links)

nativeSUNWilsonGibbsDensityStrictlyPositive :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ) (links : Native.SUNSideFourLinks N theory) →
  0ℝ <ℝ nativeSUNWilsonGibbsDensity theory traceData exponential beta links
nativeSUNWilsonGibbsDensityStrictlyPositive
    theory traceData exponential beta links =
  Exp.expPositive exponential
    (-ℝ nativeSUNWilsonAction theory traceData beta links)

-- A candidate physical finite measure must supply a H A A R integral and
-- a partition NORMALIZATION. These are not trivial finite sums: the space
-- (SU(N))^(4*256) is continuous for any fixed finite lattice.
-- Density identification itself is definitional rather than postulated.
nativeSUNFiniteGibbsMeasure :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (productHaar :
      (Native.SUNSideFourLinks N theory → ℝ) → ℝ)
    (divide : ℝ → ℝ → ℝ) →
  Physical.PhysicalFiniteYMMeasure (Native.SUNSideFourLinks N theory) ℝ
nativeSUNFiniteGibbsMeasure theory traceData exponential beta productHaar divide =
  record
    { Physical.density =
        nativeSUNWilsonGibbsDensity theory traceData exponential beta
    ; Physical.haarIntegral = productHaar
    ; Physical.multiply = _*ℝ_
    ; Physical.divide = divide
    ; Physical.partitionFunction =
        productHaar
          (nativeSUNWilsonGibbsDensity theory traceData exponential beta)
    }

nativeSUNFiniteMeasureDensitySameObject :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (productHaar : (Native.SUNSideFourLinks N theory → ℝ) → ℝ)
    divide links →
  Physical.density
    (nativeSUNFiniteGibbsMeasure theory traceData exponential beta
      productHaar divide)
    links
  ≡ nativeSUNWilsonGibbsDensity theory traceData exponential beta links
nativeSUNFiniteMeasureDensitySameObject theory traceData exponential beta
    productHaar divide links = refl

nativeSUNFiniteMeasurePartitionSameObject :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : ℝ)
    (productHaar : (Native.SUNSideFourLinks N theory → ℝ) → ℝ)
    divide →
  Physical.partitionFunction
    (nativeSUNFiniteGibbsMeasure theory traceData exponential beta
      productHaar divide)
  ≡ productHaar
      (nativeSUNWilsonGibbsDensity theory traceData exponential beta)
nativeSUNFiniteMeasurePartitionSameObject
    theory traceData exponential beta productHaar divide = refl
