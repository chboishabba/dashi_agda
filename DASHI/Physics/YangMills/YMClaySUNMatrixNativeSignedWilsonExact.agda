module DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact where

------------------------------------------------------------------------
-- R443: ORIGINAL FOUR-DIMENSIONAL PERIODIC SIGNED BONDS ON SU(N) MATRICES
--
-- This is a *new DASHI same-object extension*, not the compact Haar
-- construction. It consumes the original certified SU(N) matrix group from
-- SUNMatrixCarrier and the ORIGINAL Balaban periodic positive/negative bond
-- words. It does not substitute a rational quaternion or Lie tangent.
--
-- Physical source: K. Wilson, Phys. Rev. D 10 (1974) 2445-2459,
-- DOI: 10.1103/PhysRevD.10.2445.
-- T. Balaban, "Averaging Operations for Lattice Gauge Theories",
-- CMP 98 (1985), 17-51, DOI: 10.1007/BF01211042.
-- Existing DASHI group, signed-geometry and physical C3 authors retain
-- original proof ownership. No SU(N) analytic compactness, Haar, UV or
-- continuum gap is proved by this module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Covariance
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact as SignedC3
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as SpatialC3

-- A general group has the two extra inverse laws required by the
-- original signed-bond source. Derive them; do not assume a second group.
inverseOfProduct :
  ∀ {G : Set} (H : Core.Group G) x y →
  Core.inverse H (Core.multiply H x y)
  ≡ Core.multiply H (Core.inverse H y) (Core.inverse H x)
inverseOfProduct H x y =
  sym (Derived.rightInverseUnique H
    (Core.multiply H (Core.inverse H y) (Core.inverse H x))
    (trans
      (Core.multiplyAssociative H x y
        (Core.multiply H (Core.inverse H y) (Core.inverse H x)))
      (trans
        (cong (Core.multiply H x)
          (sym (Core.multiplyAssociative H y
            (Core.inverse H y) (Core.inverse H x))))
        (trans
          (cong (Core.multiply H x)
            (cong (λ z → Core.multiply H z (Core.inverse H x))
              (Core.inverseRight H y)))
          (trans
            (cong (Core.multiply H x)
              (Core.identityLeft H (Core.inverse H x)))
            (Core.inverseRight H x))))))

toExactSignedBondGroup :
  ∀ {G : Set} → Core.Group G → Bond.ExactLinkGroup G
toExactSignedBondGroup H = record
  { Bond.ExactLinkGroup.identity = Core.identity H
  ; Bond.ExactLinkGroup.multiply = Core.multiply H
  ; Bond.ExactLinkGroup.inverse = Core.inverse H
  ; Bond.ExactLinkGroup.multiplyAssociative = Core.multiplyAssociative H
  ; Bond.ExactLinkGroup.identityLeft = Core.identityLeft H
  ; Bond.ExactLinkGroup.identityRight = Core.identityRight H
  ; Bond.ExactLinkGroup.inverseLeft = Core.inverseLeft H
  ; Bond.ExactLinkGroup.inverseRight = Core.inverseRight H
  ; Bond.ExactLinkGroup.inverseProduct = inverseOfProduct H
  ; Bond.ExactLinkGroup.inverseInverse = Derived.inverseInvolutive H
  }

-- The full native SU(N) matrix carrier (provided the certified matrix theory
-- is instantiated over COMPLEX matrices). The matrix theory is an imported
-- genuine group-law authority; it does not assert physical Haar existence.
SUNSideFourLinks :
  ∀ {Matrix Complex : Set} (N : Nat) →
  SUN.CertifiedSUNMatrixTheory N Matrix Complex → Set
SUNSideFourLinks N theory =
  Bond.PeriodicBondField Weld.three (SUN.SUNMatrixElement theory)

sunExactSignedLinkGroup :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  Bond.ExactLinkGroup (SUN.SUNMatrixElement theory)
sunExactSignedLinkGroup theory =
  toExactSignedBondGroup (SUN.sunMatrixGroup theory)

sunSignedRealization :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  SUNSideFourLinks N theory →
  Bond.PeriodicBondGaugeRealization Weld.three
    (SUN.SUNMatrixElement theory) (sunExactSignedLinkGroup theory)
sunSignedRealization theory bonds =
  Covariance.literalPeriodicBondGaugeRealization
    (sunExactSignedLinkGroup theory)
    (Geometry.periodicStepInverseLaws Weld.three)
    bonds
    (λ _ → SUN.sunIdentity theory)

sunSignedPathHolonomy :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  SUNSideFourLinks N theory →
  Torus.periodicTorus4Definition (Agda.Builtin.Nat.suc Weld.three) →
  List Signed.SignedAxis4 →
  SUN.SUNMatrixElement theory
sunSignedPathHolonomy theory bonds site word =
  Bond.pathHolonomy (sunSignedRealization theory bonds) site word

sunPositivePlaquetteHolonomy :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  SUNSideFourLinks N theory →
  Plaquette.PeriodicPlaquette Weld.three →
  SUN.SUNMatrixElement theory
sunPositivePlaquetteHolonomy theory bonds plaquette =
  Bond.plaquetteHolonomyFromBonds (sunSignedRealization theory bonds) plaquette

sunC3Bonds :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex) →
  SUNSideFourLinks N theory →
  SUNSideFourLinks N theory
sunC3Bonds theory = Weld.nativeForwardC3Bonds

-- Signed edge naturality uses the earlier *geometric* result; its proof does
-- not depend on rational quaternions and is valid for any certified group.
sunSignedC3OrientedLink :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  bonds site direction →
  Bond.orientedLink
    (sunSignedRealization theory (sunC3Bonds theory bonds)) site direction
  ≡ Bond.orientedLink (sunSignedRealization theory bonds)
      (SpatialC3.spatialC3Site site)
      (SignedC3.c3SignedDirection direction)
sunSignedC3OrientedLink theory bonds site (Torus.pair axis Agda.Builtin.Bool.true) =
  refl
sunSignedC3OrientedLink theory bonds site (Torus.pair axis Agda.Builtin.Bool.false) =
  cong (SUN.sunInverse theory)
    (sym (SignedC3.c3SignedStepNaturality site
      (Torus.pair axis Agda.Builtin.Bool.false)))

sunSignedC3Holonomy :
  ∀ {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  bonds site (directions : List Signed.SignedAxis4) →
  sunSignedPathHolonomy theory (sunC3Bonds theory bonds) site directions
  ≡ sunSignedPathHolonomy theory bonds
      (SpatialC3.spatialC3Site site)
      (map SignedC3.c3SignedDirection directions)
sunSignedC3Holonomy theory bonds site [] = refl
sunSignedC3Holonomy theory bonds site (direction ∷ directions) =
  trans
    (cong
      (λ first →
        SUN.sunMultiply theory first
          (sunSignedPathHolonomy theory (sunC3Bonds theory bonds)
            (Bond.walkStep site direction) directions))
      (sunSignedC3OrientedLink theory bonds site direction))
    (trans
      (cong
        (SUN.sunMultiply theory
          (Bond.orientedLink (sunSignedRealization theory bonds)
            (SpatialC3.spatialC3Site site)
            (SignedC3.c3SignedDirection direction)))
        (sunSignedC3Holonomy theory bonds
          (Bond.walkStep site direction) directions))
      (cong
        (λ nextSite →
          SUN.sunMultiply theory
            (Bond.orientedLink (sunSignedRealization theory bonds)
              (SpatialC3.spatialC3Site site)
              (SignedC3.c3SignedDirection direction))
            (sunSignedPathHolonomy theory bonds
              nextSite (map SignedC3.c3SignedDirection directions)))
        (sym (SignedC3.c3SignedStepNaturality site direction))))

sunSignedC3Wilson :
  ∀ {Matrix Complex Scalar : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  (wilsonValue : SUN.SUNMatrixElement theory → Scalar)
  bonds site directions →
  wilsonValue
    (sunSignedPathHolonomy theory (sunC3Bonds theory bonds) site directions)
  ≡ wilsonValue
    (sunSignedPathHolonomy theory bonds
      (SpatialC3.spatialC3Site site)
      (map SignedC3.c3SignedDirection directions))
sunSignedC3Wilson theory wilsonValue bonds site directions =
  cong wilsonValue (sunSignedC3Holonomy theory bonds site directions)
