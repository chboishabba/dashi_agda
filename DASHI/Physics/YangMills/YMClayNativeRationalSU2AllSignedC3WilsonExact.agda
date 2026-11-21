module DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact where

------------------------------------------------------------------------
-- PAY THE NATIVE SIGNED-PATH C3 CUT, INCLUDING INVERSE LINKS.
--
-- Reuse: BalabanClayGate4RationalSU2BondCarrierExact's literal
-- PeriodicBondGaugeRealization/pathHolonomy on SU2 norm-one quaternions,
-- existing adjacency (both +/- steps), CMP119 4D spatial C3 lattice,
-- and the n=3/side-four same-carrier code in
-- YMClayNativeRationalSU2Side4C3CarrierWeldExact.
--
-- For any signed word w and actual existing RationalSU2BondData 3:
--
--   Hol_{C3*bonds}(x,w) = Hol_bonds(C3 x, C3 w).
--
-- This is a genuine full inverse-edge/n=3 same-object Wilson-loop
-- transport on the selected native finite rational group-valued carrier.
-- Only the spatial C3 action is used; internal local gauge transformations
-- are separate and already proven by the native Bond gauge telescope.
--
-- This does NOT establish finite SU2 Haar/Wilson Gibbs invariance,
-- physical continuum source, or Clay mass gap.
--
-- Sources: Wilson (1974), Bałaban's original 1985 lattice work, and
-- native DASHI SU2/periodic-bond proof owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Q
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld

-- Signed coordinate action. It preserves the orientation sign but permutes
-- time-fixed spatial coordinates exactly as the existing CMP119 source.
c3SignedDirection : Signed.SignedAxis4 → Signed.SignedAxis4
c3SignedDirection (Torus.pair axis orientation) =
  Torus.pair (C3.spatialC3Axis axis) orientation

-- C3 commutes with the actual native periodic signed adjacency, even on
-- inverse steps. No hypothetical edge-action structure is supplied.
c3SignedStepNaturality :
  ∀ (site : Hodge.Site4) (direction : Signed.SignedAxis4) →
  Bond.walkStep (C3.spatialC3Site site) (c3SignedDirection direction)
  ≡ C3.spatialC3Site (Bond.walkStep site direction)
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis0 true) = refl
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis0 false) = refl
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis1 true) = refl
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis1 false) = refl
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis2 true) = refl
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis2 false) = refl
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis3 true) = refl
c3SignedStepNaturality
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3))
  (Torus.pair Hodge.axis3 false) = refl

-- The same existing n=3 rational unit-quaternion carrier, with links
-- C3-pulled back, and site gauge pulled back on the literal Site4.
c3NativeData :
  Native.RationalSU2BondData Weld.three →
  Native.RationalSU2BondData Weld.three
c3NativeData dataSet = record
  { Native.RationalSU2BondData.links =
      Weld.nativeForwardC3Bonds (Native.links dataSet)
  ; Native.RationalSU2BondData.siteGauge =
      λ site → Native.siteGauge dataSet (C3.spatialC3Site site)
  }

c3NativeOrientedLink :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
  site direction →
  Bond.orientedLink (Native.realization (c3NativeData dataSet)) site direction
  ≡
  Bond.orientedLink (Native.realization dataSet)
    (C3.spatialC3Site site) (c3SignedDirection direction)
c3NativeOrientedLink dataSet site (Torus.pair axis true) = refl
c3NativeOrientedLink dataSet site (Torus.pair axis false) =
  cong
    (λ movedSite →
      Q.inverseRationalSU2
        (Native.links dataSet
          (Torus.pair movedSite (C3.spatialC3Axis axis))))
    (sym
      (c3SignedStepNaturality site
        (Torus.pair axis false)))

c3NativeSignedPathHolonomy :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
  site (directions : List Signed.SignedAxis4) →
  Bond.pathHolonomy (Native.realization (c3NativeData dataSet))
    site directions
  ≡
  Bond.pathHolonomy (Native.realization dataSet)
    (C3.spatialC3Site site)
    (map c3SignedDirection directions)
c3NativeSignedPathHolonomy dataSet site [] = refl
c3NativeSignedPathHolonomy dataSet site (direction ∷ directions) =
  trans
    (cong
      (λ first →
        Q.multiplyRationalSU2 first
          (Bond.pathHolonomy
            (Native.realization (c3NativeData dataSet))
            (Bond.walkStep site direction) directions))
      (c3NativeOrientedLink dataSet site direction))
    (trans
      (cong
        (Q.multiplyRationalSU2
          (Bond.orientedLink (Native.realization dataSet)
            (C3.spatialC3Site site) (c3SignedDirection direction)))
        (c3NativeSignedPathHolonomy dataSet
          (Bond.walkStep site direction) directions))
      (cong
        (λ nextSite →
          Q.multiplyRationalSU2
            (Bond.orientedLink (Native.realization dataSet)
              (C3.spatialC3Site site) (c3SignedDirection direction))
            (Bond.pathHolonomy (Native.realization dataSet)
              nextSite (map c3SignedDirection directions)))
        (sym (c3SignedStepNaturality site direction))))

-- The literal real-part / normalized SU2 Wilson observation is C3-natural
-- for ALL existing native signed words, including inverse oriented links.
c3NativeSignedWilson :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
  site (directions : List Signed.SignedAxis4) →
  SU2.realPart
    (Bond.pathHolonomy
      (Native.realization (c3NativeData dataSet)) site directions)
  ≡
  SU2.realPart
    (Bond.pathHolonomy (Native.realization dataSet)
      (C3.spatialC3Site site)
      (map c3SignedDirection directions))
c3NativeSignedWilson dataSet site directions =
  cong SU2.realPart
    (c3NativeSignedPathHolonomy dataSet site directions)
