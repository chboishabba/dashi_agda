module DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact where

------------------------------------------------------------------------
-- ACTUAL REPO SOURCE: BALABAN RATIONAL SU2 BOND n=3 <-> SIDE-FOUR GRAPH.
--
-- PeriodicBlock n = Fourfold(CyclicIndex(suc n)).
-- Consequently n=3 means actual side four (suc 3 = 4).
--
-- The native rational SU2 configuration in
-- BalabanClayGate4RationalSU2BondCarrierExact ALREADY has exactly this
-- positive-bond carrier.  We produce a pointwise two-sided codec with the
-- new graph/path/C3 naturality theorem. This removes a *carrier convention*
-- bridge without claiming an unproved continuum physical measure or
-- identification of the separate su2 Lie TANGENT field as an SU2 link.
--
-- The older native rational SU2 bond convention is golden; no new group,
-- new gauge field physics, or renormalization operator is invented.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bonds
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Gauge
import DASHI.Physics.YangMills.YMClaySide4SpatialC3WilsonNaturalityExact as Spatial
import DASHI.Physics.YangMills.YMClaySide4RationalSU2C3WilsonTraceExact as Trace

three : Nat
three = suc (suc (suc zero))

nativeSiteIsSide4 : Hodge.Site4 ≡ Torus.periodicTorus4Definition (suc three)
nativeSiteIsSide4 = refl

nativePositiveBondIsSide4 :
  Bonds.PeriodicBondField three SU2.RationalUnitQuaternion
  ≡ Torus.BondField Torus.four SU2.RationalUnitQuaternion
nativePositiveBondIsSide4 = refl

graphFieldFromNativeBonds :
  ∀ {G : Set} →
  Bonds.PeriodicBondField three G →
  Gauge.GaugeField {G = G} Spatial.ForwardBond4
graphFieldFromNativeBonds bonds
    site .(Hodge.shiftForward axis site)
    (Spatial.forwardBond axis) =
  bonds (Torus.pair site axis)

nativeBondsFromGraphField :
  ∀ {G : Set} →
  Gauge.GaugeField {G = G} Spatial.ForwardBond4 →
  Bonds.PeriodicBondField three G
nativeBondsFromGraphField field (Torus.pair site axis) =
  field site (Hodge.shiftForward axis site) (Spatial.forwardBond axis)

nativeAfterGraphPointwise :
  ∀ {G : Set}
  (field : Gauge.GaugeField {G = G} Spatial.ForwardBond4)
  site axis →
  nativeBondsFromGraphField field (Torus.pair site axis)
  ≡ field site (Hodge.shiftForward axis site) (Spatial.forwardBond axis)
nativeAfterGraphPointwise field site axis = refl

graphAfterNativePointwise :
  ∀ {G : Set}
  (bonds : Bonds.PeriodicBondField three G)
  start finish (edge : Spatial.ForwardBond4 start finish) →
  graphFieldFromNativeBonds
    (nativeBondsFromGraphField (graphFieldFromNativeBonds bonds))
    start finish edge
  ≡ graphFieldFromNativeBonds bonds start finish edge
graphAfterNativePointwise bonds site .(Hodge.shiftForward axis site)
    (Spatial.forwardBond axis) = refl

nativeRoundTrip :
  ∀ {G : Set}
  (bonds : Bonds.PeriodicBondField three G) site axis →
  nativeBondsFromGraphField
    (graphFieldFromNativeBonds bonds) (Torus.pair site axis)
  ≡ bonds (Torus.pair site axis)
nativeRoundTrip bonds site axis = refl

-- A native rational SU2 BondData is not a fresh/free group wrapper:
-- it is the actual existing (links, siteGauge) carrier.
graphFieldFromActualNativeRationalSU2 :
  Native.RationalSU2BondData three →
  Trace.RationalSU2Side4Field
graphFieldFromActualNativeRationalSU2 dataSet =
  graphFieldFromNativeBonds (Native.links dataSet)

nativeRationalSU2SiteGauge :
  Native.RationalSU2BondData three →
  Trace.RationalSU2Side4Gauge
nativeRationalSU2SiteGauge dataSet =
  Native.siteGauge dataSet

-- The chosen C3 must act on the canonical native rational positive bonds
-- by the SAME four-dimensional spatial x/y/z permutation.
nativeForwardC3Bonds :
  ∀ {G : Set} →
  Bonds.PeriodicBondField three G →
  Bonds.PeriodicBondField three G
nativeForwardC3Bonds bonds (Torus.pair site axis) =
  bonds
    (Torus.pair (C3.spatialC3Site site) (C3.spatialC3Axis axis))

-- For arbitrary native group-valued bonds, the generic graph C3 pullback
-- equals the literal native positive-bond C3 action pointwise.
nativeGraphC3Square :
  ∀ {G : Set}
  (bonds : Bonds.PeriodicBondField three G)
  site axis →
  nativeBondsFromGraphField
    (Spatial.pullbackGaugeField (graphFieldFromNativeBonds bonds))
    (Torus.pair site axis)
  ≡ nativeForwardC3Bonds bonds (Torus.pair site axis)
nativeGraphC3Square bonds
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  Hodge.axis0 = refl
nativeGraphC3Square bonds
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  Hodge.axis1 = refl
nativeGraphC3Square bonds
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  Hodge.axis2 = refl
nativeGraphC3Square bonds
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  Hodge.axis3 = refl

-- Finite selected bond source: exact quaternion-normalised closed Wilson
-- observation is physical-graph C3 natural on Native.RationalSU2BondData 3.
nativeRationalSU2Side4C3Wilson :
  ∀ {start}
  (dataSet : Native.RationalSU2BondData three)
  (loop : Gauge.Path Spatial.ForwardBond4 start start) →
  Gauge.loopObservable
    Trace.rationalSU2Group SU2.realPart
    (Spatial.pullbackGaugeField
      (graphFieldFromActualNativeRationalSU2 dataSet)) loop
  ≡
  Gauge.loopObservable
    Trace.rationalSU2Group SU2.realPart
    (graphFieldFromActualNativeRationalSU2 dataSet)
    (Spatial.rotatePath loop)
nativeRationalSU2Side4C3Wilson dataSet loop =
  Trace.rationalSU2Side4WilsonC3Naturality
    (graphFieldFromActualNativeRationalSU2 dataSet) loop

nativeRationalSU2Side4C3GaugeWilson :
  ∀ {start}
  (dataSet : Native.RationalSU2BondData three)
  (loop : Gauge.Path Spatial.ForwardBond4 start start) →
  Gauge.loopObservable Trace.rationalSU2Group SU2.realPart
    (Gauge.gaugeAction Trace.rationalSU2Group
      (nativeRationalSU2SiteGauge dataSet)
      (Spatial.pullbackGaugeField
        (graphFieldFromActualNativeRationalSU2 dataSet))) loop
  ≡
  Gauge.loopObservable Trace.rationalSU2Group SU2.realPart
    (graphFieldFromActualNativeRationalSU2 dataSet)
    (Spatial.rotatePath loop)
nativeRationalSU2Side4C3GaugeWilson dataSet loop =
  Trace.rationalSU2Side4WilsonC3GaugeInvariant
    (nativeRationalSU2SiteGauge dataSet)
    (graphFieldFromActualNativeRationalSU2 dataSet) loop
