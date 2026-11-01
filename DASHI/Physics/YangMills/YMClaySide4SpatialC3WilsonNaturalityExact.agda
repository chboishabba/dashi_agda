module DASHI.Physics.YangMills.YMClaySide4SpatialC3WilsonNaturalityExact where

------------------------------------------------------------------------
-- LITERAL FINITE SIDE-FOUR YM GRAPH: SPATIAL C3 / POSITIVE BOND / WILSON
--
-- Reuse of actual existing source owners (NOT a new SU(2) claim):
--   CMP119FlatSide4SpatialC3FieldCovarianceExact
--   BalabanP33PeriodicFourDimensionalHodgeIdentityExact
--   CompactLieLatticeGauge
--
-- Novel small adapter: push the physical spatial xyz 1->2->3->1
-- permutation through the actual graph of forward bonds, path recursion,
-- arbitrary group-valued links, closed-loop holonomy and class functions.
--
-- The finite positive-bond graph has real periodic Site4 vertices,
-- not the 27-site jfine/Monster hyperfabric graph.  This is an actual
-- graph-and-gauge theorem on the SAME source-selected 4D lattice.
-- The abstract G need still be instantiated as selected SU(2)/SU(N)
-- and the selected CMP119/Wilson continuum measure remains unpaid.
--
-- Physical author/source ownership: K. Wilson (1974), T. Balaban
-- (1985), existing DASHI CMP119 and compact-Lie lattice-gauge proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
import DASHI.Physics.YangMills.CompactLieGroupCore as Group
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Gauge

------------------------------------------------------------------------
-- Use *literal* side-four site and side-four positive-bond incidence.
------------------------------------------------------------------------

data ForwardBond4 : Hodge.Site4 → Hodge.Site4 → Set where
  forwardBond : ∀ {site} (axis : Torus.Axis4) →
    ForwardBond4 site (Hodge.shiftForward axis site)

-- The old side-four C3 action fixes time and cycles axes 1,2,3.
-- Naturality is definitional after splitting the exact four-axis carrier.
spatialC3ShiftForward : ∀ axis site →
  Hodge.shiftForward
    (C3.spatialC3Axis axis)
    (C3.spatialC3Site site)
  ≡
  C3.spatialC3Site (Hodge.shiftForward axis site)
spatialC3ShiftForward Hodge.axis0
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3ShiftForward Hodge.axis1
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3ShiftForward Hodge.axis2
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl
spatialC3ShiftForward Hodge.axis3
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

rotateForwardBond :
  ∀ {start finish} → ForwardBond4 start finish →
  ForwardBond4
    (C3.spatialC3Site start)
    (C3.spatialC3Site finish)
rotateForwardBond {start = start} (forwardBond axis) =
  subst
    (ForwardBond4 (C3.spatialC3Site start))
    (spatialC3ShiftForward axis start)
    (forwardBond (C3.spatialC3Axis axis))

rotatePath :
  ∀ {start finish} →
  Gauge.Path ForwardBond4 start finish →
  Gauge.Path ForwardBond4
    (C3.spatialC3Site start)
    (C3.spatialC3Site finish)
rotatePath Gauge.empty = Gauge.empty
rotatePath (edge Gauge.▷ rest) =
  rotateForwardBond edge Gauge.▷ rotatePath rest

------------------------------------------------------------------------
-- The physical C3 acts by pullback on selected G-valued gauge fields.
------------------------------------------------------------------------

pullbackGaugeField :
  ∀ {G : Set} →
  Gauge.GaugeField {G = G} ForwardBond4 →
  Gauge.GaugeField {G = G} ForwardBond4
pullbackGaugeField field start finish edge =
  field
    (C3.spatialC3Site start)
    (C3.spatialC3Site finish)
    (rotateForwardBond edge)

pullbackGaugeTransformation :
  ∀ {G : Set} →
  Gauge.GaugeTransformation Hodge.Site4 G →
  Gauge.GaugeTransformation Hodge.Site4 G
pullbackGaugeTransformation gamma site =
  gamma (C3.spatialC3Site site)

-- Note: equality is pointwise. No function extensionality is assumed.
pullbackCommutesWithGaugeAction :
  ∀ {G : Set}
  (H : Group.Group G)
  (gamma : Gauge.GaugeTransformation Hodge.Site4 G)
  (field : Gauge.GaugeField ForwardBond4)
  start finish (edge : ForwardBond4 start finish) →
  Gauge.gaugeAction H
    (pullbackGaugeTransformation gamma)
    (pullbackGaugeField field) start finish edge
  ≡
  pullbackGaugeField
    (Gauge.gaugeAction H gamma field) start finish edge
pullbackCommutesWithGaugeAction H gamma field start finish edge = refl

-- The holonomy calculation itself is exactly the generic pre-existing
-- CompactLieLatticeGauge recursion; new mathematics is path/C3 naturality.
holonomyC3Naturality :
  ∀ {G : Set} {start finish}
  (H : Group.Group G)
  (field : Gauge.GaugeField ForwardBond4)
  (path : Gauge.Path ForwardBond4 start finish) →
  Gauge.holonomy H (pullbackGaugeField field) path
  ≡
  Gauge.holonomy H field (rotatePath path)
holonomyC3Naturality H field Gauge.empty = refl
holonomyC3Naturality H field (edge Gauge.▷ rest) =
  cong
    (Group.multiply H
      (pullbackGaugeField field _ _ edge))
    (holonomyC3Naturality H field rest)

-- Wilson functions commute with physical spatial-C3 path transport.
-- The loop itself moves; invariance on a FIXED loop also requires the
-- loop to be C3 invariant (or a separately selected loop-average).
wilsonC3Naturality :
  ∀ {G Scalar : Set} {start}
  (H : Group.Group G)
  (value : G → Scalar)
  (field : Gauge.GaugeField ForwardBond4)
  (loop : Gauge.Path ForwardBond4 start start) →
  Gauge.loopObservable H value (pullbackGaugeField field) loop
  ≡
  Gauge.loopObservable H value field (rotatePath loop)
wilsonC3Naturality H value field loop =
  cong value (holonomyC3Naturality H field loop)

-- Gauge invariance and C3 transport are compatible ON THE SAME finite
-- physical lattice; no Monster or generic coarse-fine identification.
wilsonC3GaugeInvariant :
  ∀ {G Scalar : Set} {start}
  (H : Group.Group G)
  (value : G → Scalar)
  (classValue : Gauge.ClassFunction H value)
  (gamma : Gauge.GaugeTransformation Hodge.Site4 G)
  (field : Gauge.GaugeField ForwardBond4)
  (loop : Gauge.Path ForwardBond4 start start) →
  Gauge.loopObservable H value
    (Gauge.gaugeAction H gamma (pullbackGaugeField field)) loop
  ≡
  Gauge.loopObservable H value field (rotatePath loop)
wilsonC3GaugeInvariant H value classValue gamma field loop =
  trans
    (Gauge.loopObservableGaugeInvariant
      H value classValue gamma (pullbackGaugeField field) loop)
    (wilsonC3Naturality H value field loop)
