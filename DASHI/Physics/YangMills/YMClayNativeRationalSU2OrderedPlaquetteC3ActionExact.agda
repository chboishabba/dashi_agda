module DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact where

------------------------------------------------------------------------
-- LITERAL RATIONAL SU2/WILSON FOUR-TORUS: ORDERED PLAQUETTE C3 SUM
--
-- A genuinely *finite physical-link* action, not an invented jCoarse/fine
-- gauge model. It sums real-part Wilson trace over ALL 256 sites and
-- ALL 4x4 ordered coordinate-pair loops, including diagonal backtracking.
-- The ordered sum differs by a known convention from canonical six
-- UNORDERED plaquette action; this file deliberately does NOT assert their
-- equality or proper coupling/constant normalization without proof.
--
-- Complete signed-word C3 naturality is imported from
-- YMClayNativeRationalSU2AllSignedC3WilsonExact; the exact n=3 rational
-- quaternion carrier is from the original DASHI SU2 bond module.
--
-- The sum is invariant under spatial C3 via two nested four-axis
-- reindexings and the finite 3-cycle of site-coordinate sums.
-- No input measure or Haar integration is constructed; this supplies
-- the group-valued Wilson ACTION half of R443 on an explicit finite
-- ordered source, not the genuine continuum Gibbs/Haar/Clay conclusion.
--
-- Primary theory: K. Wilson (1974), T. Bałaban (1985); all previous
-- source theorem ownership remains with its original authors.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Data.Rational.Base as ℚ using (ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact as SignedC3

-- All oriented plaquettes of the 4D periodic bond lattice: a,b,-a,-b.
-- Duplicate inverse orientations and diagonal identity terms are retained.
orientedOrderedPlaquetteWord : Torus.Axis4 → Torus.Axis4 →
  List Signed.SignedAxis4 
orientedOrderedPlaquetteWord a b =
  Bond.positiveDirection a ∷
  Bond.positiveDirection b ∷
  Bond.negativeDirection a ∷
  Bond.negativeDirection b ∷ []

-- Native signed-word type is reused without introducing any parallel carrier.

c3PlaquetteWord :
  ∀ a b →
  map SignedC3.c3SignedDirection (orientedOrderedPlaquetteWord a b)
  ≡ orientedOrderedPlaquetteWord
      (C3.spatialC3Axis a) (C3.spatialC3Axis b)
c3PlaquetteWord a b = refl

orderedWilsonPlaquette :
  Native.RationalSU2BondData Weld.three →
  Hodge.Site4 → Torus.Axis4 → Torus.Axis4 → ℚ
orderedWilsonPlaquette dataSet site a b =
  SU2.realPart
    (Bond.pathHolonomy (Native.realization dataSet)
      site (orientedOrderedPlaquetteWord a b))

orderedWilsonPlaquetteC3 :
  ∀ dataSet site a b →
  orderedWilsonPlaquette (SignedC3.c3NativeData dataSet) site a b
  ≡
  orderedWilsonPlaquette dataSet
    (C3.spatialC3Site site)
    (C3.spatialC3Axis a) (C3.spatialC3Axis b)
orderedWilsonPlaquetteC3 dataSet site a b =
  trans
    (SignedC3.c3NativeSignedWilson dataSet site
      (orientedOrderedPlaquetteWord a b))
    (cong
      (λ directions →
        SU2.realPart
          (Bond.pathHolonomy (Native.realization dataSet)
            (C3.spatialC3Site site) directions))
      (c3PlaquetteWord a b))

-- Exact 4-element reindexing; the cyclic spatial permutation fixes axis 0.
sumIndexC3 :
  ∀ (term : Torus.Axis4 → ℚ) →
  Hodge.sumIndex4 (λ axis → term (C3.spatialC3Axis axis))
  ≡ Hodge.sumIndex4 term
sumIndexC3 term =
  ℚRing.solve-∀
    (term Hodge.axis0) (term Hodge.axis1)
    (term Hodge.axis2) (term Hodge.axis3)

-- Existing Hodge.sumIndex4 does not expose this 16-term Fubini law;
-- it is an exact polynomial-identity consequence, not analytic Fubini.
sumIndexSwap :
  ∀ (term : Hodge.Index4 → Hodge.Index4 → ℚ) →
  Hodge.sumIndex4 (λ x → Hodge.sumIndex4 (λ y → term x y))
  ≡
  Hodge.sumIndex4 (λ y → Hodge.sumIndex4 (λ x → term x y))
sumIndexSwap f =
  ℚRing.solve-∀
    (f Hodge.axis0 Hodge.axis0)
    (f Hodge.axis0 Hodge.axis1)
    (f Hodge.axis0 Hodge.axis2)
    (f Hodge.axis0 Hodge.axis3)
    (f Hodge.axis1 Hodge.axis0)
    (f Hodge.axis1 Hodge.axis1)
    (f Hodge.axis1 Hodge.axis2)
    (f Hodge.axis1 Hodge.axis3)
    (f Hodge.axis2 Hodge.axis0)
    (f Hodge.axis2 Hodge.axis1)
    (f Hodge.axis2 Hodge.axis2)
    (f Hodge.axis2 Hodge.axis3)
    (f Hodge.axis3 Hodge.axis0)
    (f Hodge.axis3 Hodge.axis1)
    (f Hodge.axis3 Hodge.axis2)
    (f Hodge.axis3 Hodge.axis3)

-- Actual 3-cycle (x1,x2,x3)->(x3,x1,x2) on side-four site sums,
-- using only the existing nested exact finite-sum owner.
sumSitesSpatialC3 :
  ∀ (term : Hodge.Site4 → ℚ) →
  Hodge.sumSites (λ site → term (C3.spatialC3Site site))
  ≡ Hodge.sumSites term
sumSitesSpatialC3 term =
  Hodge.sumIndex4Cong _ _ (λ x0 →
    trans
      (Hodge.sumIndex4Cong _ _ (λ x1 →
        sumIndexSwap
          (λ x2 x3 →
            term (Torus.pair (Torus.pair x0 x3)
              (Torus.pair x1 x2)))))
      (sumIndexSwap
        (λ x1 x3 →
          Hodge.sumIndex4 (λ x2 →
            term (Torus.pair (Torus.pair x0 x3)
              (Torus.pair x1 x2))))))

-- The actual selected n=3 rational-SU2 *ordered* plaquette real-trace
-- sum is a source-defined finite gauge-action observable.
orderedWilsonAction :
  Native.RationalSU2BondData Weld.three → ℚ
orderedWilsonAction dataSet =
  Hodge.sumSites
    (λ site → Hodge.sumIndex4
      (λ a → Hodge.sumIndex4
        (λ b → orderedWilsonPlaquette dataSet site a b)))

orderedWilsonActionSpatialC3Invariant :
  ∀ dataSet →
  orderedWilsonAction (SignedC3.c3NativeData dataSet)
  ≡ orderedWilsonAction dataSet
orderedWilsonActionSpatialC3Invariant dataSet =
  trans
    (Hodge.sumSitesCong _ _ (λ site →
      Hodge.sumIndex4Cong _ _ (λ a →
        Hodge.sumIndex4Cong _ _ (λ b →
          orderedWilsonPlaquetteC3 dataSet site a b))))
    (trans
      (Hodge.sumSitesCong _ _ (λ site →
        trans
          (Hodge.sumIndex4Cong _ _ (λ a →
            sumIndexC3
              (λ b →
                orderedWilsonPlaquette dataSet
                  (C3.spatialC3Site site)
                  (C3.spatialC3Axis a) b)))
          (sumIndexC3
            (λ a → Hodge.sumIndex4 (λ b →
              orderedWilsonPlaquette dataSet
                (C3.spatialC3Site site) a b)))))
      (sumSitesSpatialC3
        (λ site → Hodge.sumIndex4
          (λ a → Hodge.sumIndex4
            (λ b → orderedWilsonPlaquette dataSet site a b)))))
