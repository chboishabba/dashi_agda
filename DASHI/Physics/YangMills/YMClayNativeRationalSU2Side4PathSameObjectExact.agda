module DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4PathSameObjectExact where

------------------------------------------------------------------------
-- HIGHEST-ALPHA SELECTED WILSON SAME-OBJECT PATH SEAM (SIDE-FOUR, n=3)
--
-- This is the actual n=3 RationalSU2BondData -> existing signed-word
-- pathHolonomy link, not an unrelated SU2 quaternion convention.
--
-- Existing native owners:
-- BalabanClayT2PeriodicAdjacencyBFSExact, ...BondPathBianchiExact,
-- ...RationalSU2BondCarrierExact, BalabanP33PeriodicFourDimensionalHodge-
-- IdentityExact, CompactLieLatticeGauge and the new native C3 carrier weld.
--
-- This states a precise POSITIVE-WORD subalgebra same-object theorem.
-- Arbitrarily signed Wilson paths require the inverse-edge extension,
-- and the group-valued rational carrier remains different from the
-- continuum Haar SU2 physical measure (R445), not promoted here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adj
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Q
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Gauge
import DASHI.Physics.YangMills.YMClaySide4SpatialC3WilsonNaturalityExact as Spatial
import DASHI.Physics.YangMills.YMClaySide4RationalSU2C3WilsonTraceExact as Trace
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld

-- The cyclic successor used by the actual native bond parser is the
-- literal Hodge side-four shift. No new finite graph is invented.
side4CyclicSuccessorIsHodge :
  ∀ (index : Hodge.Index4) →
  Adj.cyclicSuccessor index ≡ Hodge.next4 index
side4CyclicSuccessorIsHodge Torus.zeroᵢ = refl
side4CyclicSuccessorIsHodge (Torus.sucᵢ Torus.zeroᵢ) = refl
side4CyclicSuccessorIsHodge
  (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
side4CyclicSuccessorIsHodge
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

nativePositiveStepEqualsHodge :
  ∀ axis site →
  Bond.positiveStep {n = Weld.three} site axis
  ≡ Hodge.shiftForward axis site
nativePositiveStepEqualsHodge Hodge.axis0
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  rewrite side4CyclicSuccessorIsHodge x0 = refl
nativePositiveStepEqualsHodge Hodge.axis1
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  rewrite side4CyclicSuccessorIsHodge x1 = refl
nativePositiveStepEqualsHodge Hodge.axis2
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  rewrite side4CyclicSuccessorIsHodge x2 = refl
nativePositiveStepEqualsHodge Hodge.axis3
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  rewrite side4CyclicSuccessorIsHodge x3 = refl

-- Erasure is unambiguous: each typed step is already an exact adjacent
-- positive bond, not an arbitrary pair of endpoints.
positivePathWord :
  ∀ {start finish} →
  Gauge.Path Spatial.ForwardBond4 start finish →
  List Signed.SignedAxis4
positivePathWord Gauge.empty = []
positivePathWord (Spatial.forwardBond axis Gauge.▷ rest) =
  Bond.positiveDirection axis ∷ positivePathWord rest

-- Same native source: the graph-gauge recursion equals the actual existing
-- periodic rational SU2 pathHolonomy with the erased positive signed word.
nativeGraphHolonomyEqualsExistingPathHolonomy :
  ∀ {start finish}
  (dataSet : Native.RationalSU2BondData Weld.three)
  (path : Gauge.Path Spatial.ForwardBond4 start finish) →
  Gauge.holonomy Trace.rationalSU2Group
    (Weld.graphFieldFromActualNativeRationalSU2 dataSet) path
  ≡
  Bond.pathHolonomy (Native.realization dataSet)
    start (positivePathWord path)
nativeGraphHolonomyEqualsExistingPathHolonomy dataSet Gauge.empty = refl
nativeGraphHolonomyEqualsExistingPathHolonomy
  {start = start} dataSet
  (Spatial.forwardBond axis Gauge.▷ rest)
  rewrite nativePositiveStepEqualsHodge axis start =
  cong
    (Q.multiplyRationalSU2
      (Native.links dataSet (Torus.pair start axis)))
    (nativeGraphHolonomyEqualsExistingPathHolonomy dataSet rest)

-- A real SU2 trace equality on the SAME selected finite n=3 bond carrier;
-- this is the Wilson observable already used by the R445 native path algebra
-- once the observer is chosen to be this positive signed word.
nativeGraphWilsonEqualsExistingPathWilson :
  ∀ {start finish}
  (dataSet : Native.RationalSU2BondData Weld.three)
  (path : Gauge.Path Spatial.ForwardBond4 start finish) →
  SU2.realPart
    (Gauge.holonomy Trace.rationalSU2Group
      (Weld.graphFieldFromActualNativeRationalSU2 dataSet) path)
  ≡
  SU2.realPart
    (Bond.pathHolonomy (Native.realization dataSet)
      start (positivePathWord path))
nativeGraphWilsonEqualsExistingPathWilson dataSet path =
  cong SU2.realPart
    (nativeGraphHolonomyEqualsExistingPathHolonomy dataSet path)
