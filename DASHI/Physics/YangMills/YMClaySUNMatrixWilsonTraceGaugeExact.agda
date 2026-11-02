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
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as SignedSUN
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
  SUNMatrixRealTrace theory → SUN.SUNMatrixElement theory → Scalar
matrixWilsonValue traceData U =
  normalizedRealTrace traceData (SUN.matrix U)

sunTraceCyclic :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (traceData : SUNMatrixRealTrace theory) x y →
  matrixWilsonValue traceData (SUN.sunMultiply theory x y)
  ≡ matrixWilsonValue traceData (SUN.sunMultiply theory y x)
sunTraceCyclic traceData x y =
  traceCyclic traceData (SUN.matrix x) (SUN.matrix y)

sunTraceConjugationInvariant :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    {theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex}
    (traceData : SUNMatrixRealTrace theory) h x →
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
    (traceData : SUNMatrixRealTrace theory) →
  Gauge.ClassFunction
    (SUN.sunMatrixGroup theory) (matrixWilsonValue traceData)
sunTraceClass traceData = record
  { Gauge.ClassFunction.conjugationInvariant =
      sunTraceConjugationInvariant traceData
  }

-- A real SUN link field on the ORIGINAL native n=3/side-four positive bonds
-- with arbitrary local site-gauge values. No rational surrogate is introduced.
sunGaugeRealization :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (links : SignedSUN.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory)) →
  Bond.PeriodicBondGaugeRealization Weld.three
    (SUN.SUNMatrixElement theory) (SignedSUN.sunExactSignedLinkGroup theory)
sunGaugeRealization theory links gamma =
  Covariance.literalPeriodicBondGaugeRealization
    (SignedSUN.sunExactSignedLinkGroup theory)
    (Geometry.periodicStepInverseLaws Weld.three)
    links gamma

-- Selected finite original positive plaquette, with actual inverse links,
-- has invariant real trace under arbitrary site gauge on SUN matrix group.
sunOriginalPlaquetteTraceGaugeInvariant :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : SUNMatrixRealTrace theory)
    (links : SignedSUN.SUNSideFourLinks N theory)
    (gamma : Bond.PeriodicSiteGauge Weld.three (SUN.SUNMatrixElement theory))
    (plaquette : Plaquette.PeriodicPlaquette Weld.three) →
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
        (Geometry.periodicPlaquetteClosure Weld.three)
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
    (traceData : SUNMatrixRealTrace theory)
    (field : Gauge.GaugeField {G = SUN.SUNMatrixElement theory}
      Spatial.ForwardBond4) {start}
    (loop : Gauge.Path Spatial.ForwardBond4 start start) →
  Gauge.loopObservable (SUN.sunMatrixGroup theory)
    (matrixWilsonValue traceData)
    (Spatial.pullbackGaugeField field) loop
  ≡ Gauge.loopObservable (SUN.sunMatrixGroup theory)
    (matrixWilsonValue traceData) field (Spatial.rotatePath loop)
sunSideFourWilsonC3 theory traceData field loop =
  Spatial.wilsonC3Naturality
    (SUN.sunMatrixGroup theory) (matrixWilsonValue traceData) field loop
