module DASHI.Physics.YangMills.YMClayOriginalVariableWilsonCovarianceSourceExact where

------------------------------------------------------------------------
-- Clay D1: ORIGINAL varying-cutoff 4D SU(N) Wilson covariance owner
--
-- This is the literal ℝ-valued Gibbs measure constructed on (n+1)^4
-- ORIGINAL periodic sites, with 4(n+1)^4 positive Wilson links, at
-- arbitrary n, not the auxiliary rational T5 physical-measure record
-- and not the frozen 1024-link n=3 test source.
--
-- We prove, on that actual source:
--  * normalized expectation is extensional for all cylinder tests;
--  * the finite Wilson connected covariance is symmetric;
--  * any gauge-invariant pair has a gauge-invariant product and
--    connected covariance under the source's original gauge action.
--
-- Product-Haar integral congruence is a THEOREM from the repository's
-- actual finite link-vector product, not a fresh finite measure axiom.
-- It does not imply cutoff/volume-uniform decay, a native ℝ→ℚ
-- T5 scalar weld, R333's physical spectrum, or a continuum limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _-ℝ_; *-comm)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClaySUNVariablePhysicalCutoffFamilyExact as Family
import DASHI.Physics.YangMills.YMClayE1OriginalSUNDependentCylinderExact as E1
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClaySUNMatrixProductHaarC3Exact as ProductCongruence
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (beta : Nat → ℝ)
    (oneLink : Product.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  Links : Nat → Set
  Links n = Family.linksAt
    theory traceData exponential beta oneLink bilateral divide n

  Test : Nat → Set
  Test n = Links n → ℝ

  measure : (n : Nat) → Physical.PhysicalFiniteYMMeasure (Links n) ℝ
  measure = Family.physicalFiniteCutoffMeasure
    theory traceData exponential beta oneLink bilateral divide

  expectation : (n : Nat) → Test n → ℝ
  expectation n = Physical.normalizedExpectation (measure n)

  -- This is a sourced ℝ-valued cylinder expectation at EVERY n:
  -- the product-Haar integral is the original bond-vector decoder.
  originalWilsonExpectationExtensional :
    (n : Nat) (left right : Test n) →
    (∀ links → left links ≡ right links) →
    expectation n left ≡ expectation n right
  originalWilsonExpectationExtensional n left right equal =
    cong
      (λ numerator → divide numerator
        (Physical.partitionFunction (measure n)))
      (ProductCongruence.productIntegralCongruent oneLink
        (λ vector →
          Physical.density (measure n)
            (Codec.decodeOriginalBonds (suc n) vector)
            *ℝ left
              (Codec.decodeOriginalBonds (suc n) vector))
        (λ vector →
          Physical.density (measure n)
            (Codec.decodeOriginalBonds (suc n) vector)
            *ℝ right
              (Codec.decodeOriginalBonds (suc n) vector))
        (λ vector →
          cong
            (λ value →
              Physical.density (measure n)
                (Codec.decodeOriginalBonds (suc n) vector)
                *ℝ value)
            (equal (Codec.decodeOriginalBonds (suc n) vector))))

  originalWilsonConnectedCovariance :
    (n : Nat) → Test n → Test n → ℝ
  originalWilsonConnectedCovariance n left right =
    expectation n (λ links → left links *ℝ right links)
      -ℝ
    (expectation n left *ℝ expectation n right)

  originalWilsonConnectedCovarianceSymmetric :
    (n : Nat) (left right : Test n) →
    originalWilsonConnectedCovariance n left right ≡
      originalWilsonConnectedCovariance n right left
  originalWilsonConnectedCovarianceSymmetric n left right =
    cong₂ _-ℝ_
      (originalWilsonExpectationExtensional n
        (λ links → left links *ℝ right links)
        (λ links → right links *ℝ left links)
        (λ links → *-comm (left links) (right links)))
      (*-comm (expectation n left) (expectation n right))

  -- E1 and D1 are now literally SAME changing physical Wilson
  -- measure for any cutoff-dependent original cylinder sections.
  -- The only data chosen is the original observable section itself.
  -- No rational T5 source or independent cumulant is inserted.
  OriginalCylinderSection : Set
  OriginalCylinderSection = (n : Nat) → Test n

  actualE1CylinderExpectation :
    (n : Nat) → OriginalCylinderSection → ℝ
  actualE1CylinderExpectation n cylinder =
    E1.actualOriginalWilsonCylinderExpectation
      theory traceData exponential beta oneLink bilateral divide
      n cylinder

  actualE1D1SameWilsonConnectedCovariance :
    (n : Nat)
    (left right : OriginalCylinderSection) →
    originalWilsonConnectedCovariance n (left n) (right n)
    ≡
    (actualE1CylinderExpectation n
      (λ cutoff links → left cutoff links *ℝ right cutoff links))
    -ℝ
    (actualE1CylinderExpectation n left
      *ℝ actualE1CylinderExpectation n right)
  actualE1D1SameWilsonConnectedCovariance n left right = refl

  originalGauge : (n : Nat) → Set
  originalGauge n = Family.gaugeAt
    theory traceData exponential beta oneLink bilateral divide n

  gaugeShift :
    (n : Nat) → originalGauge n → Test n → Test n
  gaugeShift n gamma test links =
    test (Variable.periodicSUNGaugeTransform theory n links gamma)

  originalGaugeInvariant : (n : Nat) → Test n → Set
  originalGaugeInvariant n test =
    ∀ gamma links → gaugeShift n gamma test links ≡ test links

  originalGaugeInvariantProduct :
    (n : Nat) (left right : Test n) →
    originalGaugeInvariant n left →
    originalGaugeInvariant n right →
    originalGaugeInvariant n
      (λ links → left links *ℝ right links)
  originalGaugeInvariantProduct n left right invLeft invRight gamma links =
    cong₂ _*ℝ_
      (invLeft gamma links)
      (invRight gamma links)

  -- E1: actual dependent GAUGE-INVARIANT source subalgebra.
  -- This is narrower than ALL cutoff sections and uses the literal
  -- (n+1)^4 periodic local gauge transformation at every n.
  OriginalGaugeInvariantSection : OriginalCylinderSection → Set
  OriginalGaugeInvariantSection cylinder =
    ∀ n → originalGaugeInvariant n (cylinder n)

  originalZeroCylinderSection : OriginalCylinderSection
  originalZeroCylinderSection n links = 0ℝ

  originalUnitCylinderSection : OriginalCylinderSection
  originalUnitCylinderSection n links = 1ℝ

  originalGaugeInvariantZeroCylinder :
    OriginalGaugeInvariantSection originalZeroCylinderSection
  originalGaugeInvariantZeroCylinder n gamma links = refl

  originalGaugeInvariantUnitCylinder :
    OriginalGaugeInvariantSection originalUnitCylinderSection
  originalGaugeInvariantUnitCylinder n gamma links = refl

  originalGaugeInvariantSectionAdd :
    (left right : OriginalCylinderSection) →
    OriginalGaugeInvariantSection left →
    OriginalGaugeInvariantSection right →
    OriginalGaugeInvariantSection
      (λ n links → left n links +ℝ right n links)
  originalGaugeInvariantSectionAdd left right invLeft invRight n gamma links =
    cong₂ _+ℝ_ (invLeft n gamma links) (invRight n gamma links)

  originalGaugeInvariantSectionScale :
    (scalar : ℝ) (cylinder : OriginalCylinderSection) →
    OriginalGaugeInvariantSection cylinder →
    OriginalGaugeInvariantSection
      (λ n links → scalar *ℝ cylinder n links)
  originalGaugeInvariantSectionScale scalar cylinder inv n gamma links =
    cong (λ value → scalar *ℝ value) (inv n gamma links)

  originalGaugeInvariantSectionProduct :
    (left right : OriginalCylinderSection) →
    OriginalGaugeInvariantSection left →
    OriginalGaugeInvariantSection right →
    OriginalGaugeInvariantSection
      (λ n links → left n links *ℝ right n links)
  originalGaugeInvariantSectionProduct left right invLeft invRight n =
    originalGaugeInvariantProduct n (left n) (right n)
      (invLeft n) (invRight n)

  -- Original ONE FIXED positive plaquette at the canonical origin:
  -- a genuinely support-local original SU(N) Wilson trace test on
  -- each varying periodic four-torus (NOT the extensive six-plane
  -- action sum). The same original theory and trace are used.
  originalOriginPositivePlaquetteAt :
    (n : Nat) → Plaquette.PeriodicPlaquette n
  originalOriginPositivePlaquetteAt n =
    Plaquette.periodicPlaquetteAt Blocks.zeroBlock Torus.zeroᵢ

  originalLocalPlaquetteTraceSection : OriginalCylinderSection
  originalLocalPlaquetteTraceSection n links =
    Trace.matrixWilsonValue traceData
      (Variable.periodicSUNPositivePlaquette theory n links
        (originalOriginPositivePlaquetteAt n))

  originalLocalPlaquetteTraceIsGaugeInvariantSection :
    OriginalGaugeInvariantSection originalLocalPlaquetteTraceSection
  originalLocalPlaquetteTraceIsGaugeInvariantSection n gamma links =
    Variable.periodicSUNPositivePlaquetteGaugeTrace
      theory traceData n links gamma
      (originalOriginPositivePlaquetteAt n)

  originalLocalPlaquetteProductIsGaugeInvariantSection :
    OriginalGaugeInvariantSection
      (λ n links →
        originalLocalPlaquetteTraceSection n links
        *ℝ originalLocalPlaquetteTraceSection n links)
  originalLocalPlaquetteProductIsGaugeInvariantSection =
    originalGaugeInvariantSectionProduct
      originalLocalPlaquetteTraceSection
      originalLocalPlaquetteTraceSection
      originalLocalPlaquetteTraceIsGaugeInvariantSection
      originalLocalPlaquetteTraceIsGaugeInvariantSection

  -- This LOCAL source is available to the E1 and D1 physical
  -- programmes at every finite cutoff, without inventing a new
  -- measure, trace, gauge algebra or cylinder-representation axiom.
  originalE1LocalPlaquetteConnectedCovarianceIsSameD1 :
    (n : Nat) →
    originalWilsonConnectedCovariance n
      (originalLocalPlaquetteTraceSection n)
      (originalLocalPlaquetteTraceSection n)
    ≡
    actualE1CylinderExpectation n
      (λ cutoff links →
        originalLocalPlaquetteTraceSection cutoff links
        *ℝ originalLocalPlaquetteTraceSection cutoff links)
    -ℝ
    (actualE1CylinderExpectation n originalLocalPlaquetteTraceSection
      *ℝ actualE1CylinderExpectation n originalLocalPlaquetteTraceSection)
  originalE1LocalPlaquetteConnectedCovarianceIsSameD1 n =
    actualE1D1SameWilsonConnectedCovariance n
      originalLocalPlaquetteTraceSection
      originalLocalPlaquetteTraceSection

  -- The existing original six-plaquette action density is the
  -- ACTUAL selected Wilson cylinder generator, at EVERY variable
  -- lattice size. No second arbitrary gauge test is introduced.
  originalSixPlaquetteDeficitSection : OriginalCylinderSection
  originalSixPlaquetteDeficitSection n links =
    Variable.periodicSUNSixDeficit theory traceData n links

  originalSixPlaquetteDeficitIsGaugeInvariantSection :
    OriginalGaugeInvariantSection originalSixPlaquetteDeficitSection
  originalSixPlaquetteDeficitIsGaugeInvariantSection n gamma links =
    Variable.periodicSUNSixDeficitGaugeInvariant
      theory traceData n links gamma

  originalSixPlaquetteDeficitSquareIsGaugeInvariantSection :
    OriginalGaugeInvariantSection
      (λ n links →
        originalSixPlaquetteDeficitSection n links
        *ℝ originalSixPlaquetteDeficitSection n links)
  originalSixPlaquetteDeficitSquareIsGaugeInvariantSection =
    originalGaugeInvariantSectionProduct
      originalSixPlaquetteDeficitSection
      originalSixPlaquetteDeficitSection
      originalSixPlaquetteDeficitIsGaugeInvariantSection
      originalSixPlaquetteDeficitIsGaugeInvariantSection

  -- In particular, the original E1 variance/covariance for the
  -- true six-plaquette Wilson deficit is definitionally the original
  -- D1 covariance at every cutoff, and its gauge sector is proved.
  originalE1SixDeficitCovarianceIsSameD1Source :
    (n : Nat) →
    originalWilsonConnectedCovariance n
      (originalSixPlaquetteDeficitSection n)
      (originalSixPlaquetteDeficitSection n)
    ≡
    actualE1CylinderExpectation n
      (λ cutoff links →
        originalSixPlaquetteDeficitSection cutoff links
        *ℝ originalSixPlaquetteDeficitSection cutoff links)
    -ℝ
    (actualE1CylinderExpectation n originalSixPlaquetteDeficitSection
      *ℝ actualE1CylinderExpectation n originalSixPlaquetteDeficitSection)
  originalE1SixDeficitCovarianceIsSameD1Source n =
    actualE1D1SameWilsonConnectedCovariance n
      originalSixPlaquetteDeficitSection
      originalSixPlaquetteDeficitSection

  -- Gauge-invariant ORIGINAL Wilson cylinder covariance is exactly
  -- gauge invariant at every changing physical cutoff.
  originalWilsonGaugeInvariantConnectedCovariance :
    (n : Nat) (left right : Test n) →
    originalGaugeInvariant n left →
    originalGaugeInvariant n right →
    ∀ gamma →
      originalWilsonConnectedCovariance n
        (gaugeShift n gamma left) (gaugeShift n gamma right)
      ≡ originalWilsonConnectedCovariance n left right
  originalWilsonGaugeInvariantConnectedCovariance
      n left right invLeft invRight gamma =
    cong₂ _-ℝ_
      (originalWilsonExpectationExtensional n
        (λ links →
          gaugeShift n gamma left links
          *ℝ gaugeShift n gamma right links)
        (λ links → left links *ℝ right links)
        (λ links →
          cong₂ _*ℝ_
            (invLeft gamma links)
            (invRight gamma links)))
      (cong₂ _*ℝ_
        (originalWilsonExpectationExtensional n
          (gaugeShift n gamma left) left (invLeft gamma))
        (originalWilsonExpectationExtensional n
          (gaugeShift n gamma right) right (invRight gamma)))

-- D1 is the unsolved UNIFORM quantitative localization of this
-- concrete original varying-cutoff covariance; the older R320/T5
-- consumer uses a rational scalar and requires a separate faithful
-- same-source real/rational transport, not just matching symbols.
