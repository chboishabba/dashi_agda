module DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact where

------------------------------------------------------------------------
-- R443: REAL/CERTIFIED SU(N) WILSON TRACE CLASS FUNCTION AND GAUGE WELD
--
-- Previous exact owner: SUNMatrixCarrier (certified SU(N) matrices) and
-- BalabanClayGate4PeriodicBondPathBianchiExact (original signed plaquettes).
-- This DASHI extension proves trace-conjugation invariance from the
-- matrix trace CYCLICITY equality, rather than assuming the desired gauge
-- invariance as an independent field. It then instantiates the original
-- periodic oriented-plaquette gauge-cancellation proof on SUN matrices.
--
-- No Haar measure, Wilson Gibbs partition, UV continuum or spectral gap.
-- Matrix theory and trace cyclicity are explicit external mathematical
-- conditions; neither is proved for unspecified complex matrix primitives.
--
-- Sources: K. Wilson, Phys. Rev. D 10 (1974) 2445-2459,
-- DOI 10.1103/PhysRevD.10.2445; T. Balaban, CMP 99 (1985) 75-102,
-- DOI 10.1007/BF01466594. Original DASHI source theorem owners retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Gauge
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.SUNWilsonClassFunction as OriginalSUNTrace
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClaySUNPeriodicWilsonDensityCoreExact as Density
import DASHI.Physics.YangMills.YMClaySide4C3CoreExact as Side4
import DASHI.Physics.YangMills.YMClaySide4SpatialC3WilsonNaturalityExact as Spatial

record SUNMatrixRealTrace
    {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) : Set₁ where
  field
    normalizedRealTrace : Matrix → Scalar
    traceCyclic : ∀ A B →
      normalizedRealTrace
        (SUN.multiplyM (SUN.operations theory) A B)
      ≡
      normalizedRealTrace
        (SUN.multiplyM (SUN.operations theory) B A)

open SUNMatrixRealTrace public

matrixWilsonValue :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex} →
  SUNMatrixRealTrace {Scalar = Scalar} theory → SUN.SUNMatrixElement theory → Scalar
matrixWilsonValue traceData U =
  normalizedRealTrace traceData (SUN.matrix U)

sunTraceCyclic :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (traceData : SUNMatrixRealTrace {Scalar = Scalar} theory) x y →
  matrixWilsonValue traceData (SUN.sunMultiply theory x y)
  ≡ matrixWilsonValue traceData (SUN.sunMultiply theory y x)
sunTraceCyclic traceData x y =
  traceCyclic traceData (SUN.matrix x) (SUN.matrix y)

sunTraceConjugationInvariant :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (traceData : SUNMatrixRealTrace {Scalar = Scalar} theory) h x →
  matrixWilsonValue traceData
    (Derived.conjugate (SUN.sunMatrixGroup theory) h x)
  ≡ matrixWilsonValue traceData x
sunTraceConjugationInvariant {theory = theory} traceData h x =
  let H = SUN.sunMatrixGroup theory in
  trans
    (sunTraceCyclic traceData
      (SUN.sunMultiply theory h x) (SUN.sunInverse theory h))
    (trans
      (cong (matrixWilsonValue traceData)
        (sym (Core.multiplyAssociative H (SUN.sunInverse theory h) h x)))
      (trans
        (cong
          (λ value → matrixWilsonValue traceData (SUN.sunMultiply theory value x))
          (Core.inverseLeft H h))
        (cong (matrixWilsonValue traceData) (Core.identityLeft H x))))

sunTraceClass :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (traceData : SUNMatrixRealTrace {Scalar = Scalar} theory) →
  Gauge.ClassFunction
    (SUN.sunMatrixGroup theory) (matrixWilsonValue traceData)
sunTraceClass traceData = record
  { conjugationInvariant =
      sunTraceConjugationInvariant traceData
  }

-- A real SUN link field on the ORIGINAL native n=3/side-four positive bonds
-- with arbitrary local site-gauge values. No rational surrogate is introduced.
sunGaugeRealization :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : Density.SUNPeriodicLinks theory Side4.three)
    (gamma : Bond.PeriodicSiteGauge Side4.three (SUN.SUNMatrixElement theory)) →
  Bond.PeriodicBondGaugeRealization Side4.three
    (SUN.SUNMatrixElement theory) (Density.periodicSUNLinkGroup theory)
sunGaugeRealization theory links gamma =
  Covariance.literalPeriodicBondGaugeRealization
    (Density.periodicSUNLinkGroup theory)
    (Geometry.periodicStepInverseLaws Side4.three)
    links gamma

-- Selected finite original positive plaquette, with actual inverse links,
-- has invariant real trace under arbitrary site gauge on SUN matrix group.
sunOriginalPlaquetteTraceGaugeInvariant :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : SUNMatrixRealTrace {Scalar = Scalar} theory)
    (links : Density.SUNPeriodicLinks theory Side4.three)
    (gamma : Bond.PeriodicSiteGauge Side4.three (SUN.SUNMatrixElement theory))
    (plaquette : Plaquette.PeriodicPlaquette Side4.three) →
  matrixWilsonValue traceData
    (Bond.transformedPathHolonomy
      (sunGaugeRealization theory links gamma)
      (Torus.first plaquette)
      (Bond.plaquetteBoundaryDirections (Torus.second plaquette)))
  ≡ matrixWilsonValue traceData
    (Bond.plaquetteHolonomyFromBonds
      (sunGaugeRealization theory links gamma) plaquette)
sunOriginalPlaquetteTraceGaugeInvariant theory traceData links gamma plaquette =
  trans
    (cong (matrixWilsonValue traceData)
      (Bond.plaquetteGaugeCancellation
        (Geometry.periodicPlaquetteClosure Side4.three)
        (sunGaugeRealization theory links gamma) plaquette))
    (sunTraceConjugationInvariant traceData (gamma (Torus.first plaquette))
      (Bond.plaquetteHolonomyFromBonds
        (sunGaugeRealization theory links gamma) plaquette))

-- This specialisation is only the universal positive-edge C3 theorem.
-- It transports signed plaquettes separately via SignedSUN, so there is no
-- accidental identification of a positive-only loop with its inverse edge.
sunSideFourWilsonC3 :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : SUNMatrixRealTrace {Scalar = Scalar} theory)
    (gaugeField : Gauge.GaugeField {G = SUN.SUNMatrixElement theory}
      Spatial.ForwardBond4) {start}
    (loop : Gauge.Path Spatial.ForwardBond4 start start) →
  Gauge.loopObservable (SUN.sunMatrixGroup theory)
    (matrixWilsonValue traceData)
    (Spatial.pullbackGaugeField gaugeField) loop
  ≡ Gauge.loopObservable (SUN.sunMatrixGroup theory)
    (matrixWilsonValue traceData) gaugeField (Spatial.rotatePath loop)
sunSideFourWilsonC3 theory traceData gaugeField loop =
  Spatial.wilsonC3Naturality
    (SUN.sunMatrixGroup theory) (matrixWilsonValue traceData) gaugeField loop

------------------------------------------------------------------------
-- Reuse the older canonical SUNWilsonClassFunction theorem owner instead
-- of maintaining a second distinct Wilson trace/class-function authority.
-- The older record requires trace conjugation invariance; above we DERIVE
-- it from matrix trace cyclicity and the existing group laws.
------------------------------------------------------------------------

asCanonicalSUNTraceAuthority :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex} →
  SUNMatrixRealTrace {Scalar = Scalar} theory →
  OriginalSUNTrace.SUNWilsonTraceAuthority
    {Scalar = Scalar} theory
asCanonicalSUNTraceAuthority traceData = record
  { normalizedRealTrace =
      matrixWilsonValue traceData
  ; traceConjugationInvariant =
      sunTraceConjugationInvariant traceData
  }

canonicalSUNWilsonClassFunctionAgreement :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (traceData : SUNMatrixRealTrace {Scalar = Scalar} theory)
    h x →
  OriginalSUNTrace.normalizedRealTrace
    (asCanonicalSUNTraceAuthority traceData)
    (Derived.conjugate (SUN.sunMatrixGroup theory) h x)
  ≡ OriginalSUNTrace.normalizedRealTrace
    (asCanonicalSUNTraceAuthority traceData) x
canonicalSUNWilsonClassFunctionAgreement traceData =
  OriginalSUNTrace.traceConjugationInvariant
    (asCanonicalSUNTraceAuthority traceData)
