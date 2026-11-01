module DASHI.Physics.YangMills.YMClaySide4RationalSU2C3WilsonTraceExact where

------------------------------------------------------------------------
-- ACTUAL RATIONAL SU2 QUATERNION ON THE ACTUAL SIDE-FOUR C3 GRAPH
--
-- Existing source owners:
--   BalabanClayGate4RationalSU2ExactGroupLaws: exact SU2 quaternion group
--   BalabanSU2RationalWilsonLargeFieldGapExact: unit quaternion/trace
--   CompactLieLatticeGauge: group-valued path gauge-covariance
--   CMP119FlatSide4SpatialC3FieldCovarianceExact: spatial side-four C3
--   YMClaySide4SpatialC3WilsonNaturalityExact: graph/map holonomy naturality
--
-- New exact source-specific theorem: a real-part normalised Wilson loop of
-- the literal rational SU2 link group is C3-natural and invariant under
-- *local* gauge transformations; the path is transported with C3.
--
-- Unlike the su2 Lie-tangent side-four stress module, links HERE are literal
-- rational norm-one group elements. We do not equate these configurations
-- with the CMP119 nonlinear generated-action measure or a Haar-completed
-- continuum compact SU2 group; ℚ-rational unit quaternions are not the
-- full compact real SU2 topology or its normalised Haar measure.
--
-- Trace cyclicity/conjugation are derived from existing quaternion group
-- fields and a one-line exact rational polynomial commutation.
--
-- Wilson (1974), Bałaban (1985), and existing DASHI original proof owners
-- retain credit. No theorem about Clay Yang–Mills mass gap is claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.CompactLieGroupCore as Group
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Gauge
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Q
import DASHI.Physics.YangMills.YMClaySide4SpatialC3WilsonNaturalityExact as Spatial

RationalSU2 : Set
RationalSU2 = SU2.RationalUnitQuaternion

rationalSU2Group : Group.Group RationalSU2
rationalSU2Group = record
  { Group.Group.identity = Q.identityRationalSU2
  ; Group.Group.multiply = Q.multiplyRationalSU2
  ; Group.Group.inverse = Q.inverseRationalSU2
  ; Group.Group.multiplyAssociative = Q.multiplyAssociative
  ; Group.Group.identityLeft = Q.identityLeft
  ; Group.Group.identityRight = Q.identityRight
  ; Group.Group.inverseLeft = Q.inverseLeft
  ; Group.Group.inverseRight = Q.inverseRight
  }

rationalTraceCyclic : ∀ left right →
  SU2.realPart (Q.multiplyRationalSU2 left right)
  ≡ SU2.realPart (Q.multiplyRationalSU2 right left)
rationalTraceCyclic left right =
  ℚRing.solve-∀
    (SU2.realPart left)
    (SU2.imagI left)
    (SU2.imagJ left)
    (SU2.imagK left)
    (SU2.realPart right)
    (SU2.imagI right)
    (SU2.imagJ right)
    (SU2.imagK right)

-- Derived, not merely assumed: normalized SU2 trace is a class function.
rationalTraceConjugationInvariant : ∀ h x →
  SU2.realPart (Derived.conjugate rationalSU2Group h x)
  ≡ SU2.realPart x
rationalTraceConjugationInvariant h x =
  trans
    (rationalTraceCyclic (Q.multiplyRationalSU2 h x)
      (Q.inverseRationalSU2 h))
    (trans
      (cong SU2.realPart
        (sym
          (Q.multiplyAssociative (Q.inverseRationalSU2 h) h x)))
      (trans
        (cong
          (λ value → SU2.realPart (Q.multiplyRationalSU2 value x))
          (Q.inverseLeft h))
        (cong SU2.realPart (Q.identityLeft x))))

rationalSU2WilsonTraceClass :
  Gauge.ClassFunction rationalSU2Group SU2.realPart
rationalSU2WilsonTraceClass = record
  { Gauge.ClassFunction.conjugationInvariant =
      rationalTraceConjugationInvariant }

-- Explicit physical source: periodic side-four positive bond link fields
-- (unrestricted rational unit-quaternion assignments at every positive edge).
RationalSU2Side4Field : Set
RationalSU2Side4Field =
  Gauge.GaugeField {G = RationalSU2} Spatial.ForwardBond4

RationalSU2Side4Gauge : Set
RationalSU2Side4Gauge =
  Gauge.GaugeTransformation Hodge.Site4 RationalSU2

rationalSU2Side4WilsonC3Naturality :
  ∀ {start}
  (field : RationalSU2Side4Field)
  (loop : Gauge.Path Spatial.ForwardBond4 start start) →
  Gauge.loopObservable rationalSU2Group SU2.realPart
    (Spatial.pullbackGaugeField field) loop
  ≡
  Gauge.loopObservable rationalSU2Group SU2.realPart
    field (Spatial.rotatePath loop)
rationalSU2Side4WilsonC3Naturality field loop =
  Spatial.wilsonC3Naturality rationalSU2Group SU2.realPart field loop

-- Both symmetries use the same exact rational SU2 group carrier and actual
-- C3-positive-bond transport; the local gauge action is not called C3.
rationalSU2Side4WilsonC3GaugeInvariant :
  ∀ {start}
  (gamma : RationalSU2Side4Gauge)
  (field : RationalSU2Side4Field)
  (loop : Gauge.Path Spatial.ForwardBond4 start start) →
  Gauge.loopObservable rationalSU2Group SU2.realPart
    (Gauge.gaugeAction rationalSU2Group gamma
      (Spatial.pullbackGaugeField field)) loop
  ≡
  Gauge.loopObservable rationalSU2Group SU2.realPart
    field (Spatial.rotatePath loop)
rationalSU2Side4WilsonC3GaugeInvariant gamma field loop =
  Spatial.wilsonC3GaugeInvariant
    rationalSU2Group SU2.realPart rationalSU2WilsonTraceClass
    gamma field loop
