module DASHI.Physics.YangMills.YMClaySide4C3CoreExact where

------------------------------------------------------------------------
-- Sources: T. Balaban, Commun. Math. Phys. 99 (1985) 75--102,
-- DOI 10.1007/BF01466594; K. Wilson, Phys. Rev. D 10 (1974) 2445--2459,
-- DOI 10.1103/PhysRevD.10.2445.
--
-- DASHI contribution: a lightweight carrier for the literal side-four
-- positive-bond C3 relabelling. The definitions reproduce the finite
-- Torus/axis data used by the heavier Weld module, but do not import the
-- rational Hodge/LDL certificate chain. No new physical claim is made.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

three : Nat
three = suc (suc (suc zero))

Index4 : Set
Index4 = Torus.CyclicIndex (suc three)

next4 : Index4 → Index4
next4 Torus.zeroᵢ = Torus.sucᵢ Torus.zeroᵢ
next4 (Torus.sucᵢ Torus.zeroᵢ) =
  Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)
next4 (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) =
  Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))
next4 (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = Torus.zeroᵢ

SideFourSite : Set
SideFourSite = Torus.periodicTorus4Definition (suc three)

shiftForward : Torus.Axis4 → SideFourSite → SideFourSite
shiftForward Torus.zeroᵢ
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair (next4 x0) x1) (Torus.pair x2 x3)
shiftForward (Torus.sucᵢ Torus.zeroᵢ)
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair x0 (next4 x1)) (Torus.pair x2 x3)
shiftForward (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair x0 x1) (Torus.pair (next4 x2) x3)
shiftForward (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair x0 x1) (Torus.pair x2 (next4 x3))

axis0 axis1 axis2 axis3 : Torus.Axis4
axis0 = Torus.zeroᵢ
axis1 = Torus.sucᵢ Torus.zeroᵢ
axis2 = Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)
axis3 = Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))

spatialC3Axis : Torus.Axis4 → Torus.Axis4
spatialC3Axis Torus.zeroᵢ = axis0
spatialC3Axis (Torus.sucᵢ Torus.zeroᵢ) = axis2
spatialC3Axis (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = axis3
spatialC3Axis (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = axis1

spatialC3Site : SideFourSite → SideFourSite
spatialC3Site
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair x0 x3) (Torus.pair x1 x2)

inverseSpatialC3Axis : Torus.Axis4 → Torus.Axis4
inverseSpatialC3Axis Torus.zeroᵢ = axis0
inverseSpatialC3Axis (Torus.sucᵢ Torus.zeroᵢ) = axis3
inverseSpatialC3Axis (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = axis1
inverseSpatialC3Axis (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = axis2

spatialC3AxisAfterInverse : ∀ axis →
  spatialC3Axis (inverseSpatialC3Axis axis) ≡ axis
spatialC3AxisAfterInverse Torus.zeroᵢ = refl
spatialC3AxisAfterInverse (Torus.sucᵢ Torus.zeroᵢ) = refl
spatialC3AxisAfterInverse (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
spatialC3AxisAfterInverse
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

inverseSpatialC3AxisAfter : ∀ axis →
  inverseSpatialC3Axis (spatialC3Axis axis) ≡ axis
inverseSpatialC3AxisAfter Torus.zeroᵢ = refl
inverseSpatialC3AxisAfter (Torus.sucᵢ Torus.zeroᵢ) = refl
inverseSpatialC3AxisAfter (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
inverseSpatialC3AxisAfter
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

inverseSpatialC3Site : SideFourSite → SideFourSite
inverseSpatialC3Site
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) =
  Torus.pair (Torus.pair x0 x2) (Torus.pair x3 x1)

spatialC3SiteAfterInverse : ∀ site →
  spatialC3Site (inverseSpatialC3Site site) ≡ site
spatialC3SiteAfterInverse
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

inverseSpatialC3SiteAfter : ∀ site →
  inverseSpatialC3Site (spatialC3Site site) ≡ site
inverseSpatialC3SiteAfter
  (Torus.pair (Torus.pair x0 x1) (Torus.pair x2 x3)) = refl

nativeForwardC3Bonds :
  ∀ {G : Set} →
  Bond.PeriodicBondField three G →
  Bond.PeriodicBondField three G
nativeForwardC3Bonds bonds (Torus.pair site axis) =
  bonds (Torus.pair (spatialC3Site site) (spatialC3Axis axis))
