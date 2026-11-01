module DASHI.Physics.YangMills.YMClayNativeSixPlaneC3SourceReductionExact where

------------------------------------------------------------------------
-- R443-SIX: ACTUAL SIX-PLAQUETTE FINITE PHYSICAL-WILSON C3 MAX-CUT
--
-- Reuse:
--   * original native PositivePlane4 / ownedPeriodicPlaquettes,
--   * actual n=3 rational SU2 norm-one link source,
--   * all signed C3 path transport (not a 369 analogy),
--   * native six-plane -> ordered word equality, and
--   * exact 4D side-four finite-sum reindexing.
--
-- Important logical boundary: on the original 6-plane convention C3 sends
--   01 -> 02; 02 -> 03; 03 -> 01;
--   12 -> 23; 13 -> 21; 23 -> 31.
-- So TWO source-specific *orientation-reversal* equalities, not a second
-- whole measure, are all that remains for this exact C3 action theorem.
-- The existing exact norm-one quaternion four-factor inverse proof is the
-- algebraic donor; attaching that to the physical four-site contour is the
-- remaining orientation geometry proof, exposed here as a narrow witness.
--
-- This file does NOT assume Haar invariance, asymptotic freedom, continuum
-- OS positivity, or a Yang-Mills mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.Foundations.CMP119FlatSide4SpatialC3FieldCovarianceExact as C3
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact as SignedC3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact as Ordered
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six

-- The actual old native six positive-plane real trace, unfolded only into
-- its exact source-backed six geometric terms.
sixPhysicalAt :
  Native.RationalSU2BondData Weld.three →
  Hodge.Site4 → ℚ
sixPhysicalAt dataSet site =
  Ordered.orderedWilsonPlaquette dataSet site Hodge.axis0 Hodge.axis1
  + (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis0 Hodge.axis2
  + (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis0 Hodge.axis3
  + (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis1 Hodge.axis2
  + (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis1 Hodge.axis3
  + (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis2 Hodge.axis3
  + 0ℚ)))))

nativeSixPlaneAtIsLiteralSix :
  ∀ dataSet site →
  Six.nativeSixPlaneTraceSumAt dataSet site ≡ sixPhysicalAt dataSet site
nativeSixPlaneAtIsLiteralSix dataSet site = refl

-- Only two reversed selected spatial planes occur after a cyclic spatial
-- rotation. Avoid a larger unjustified (or separately selected) symmetry.
record NativeSixC3Orientation
    (dataSet : Native.RationalSU2BondData Weld.three) : Set where
  field
    reverse21 : ∀ site →
      Ordered.orderedWilsonPlaquette dataSet site Hodge.axis2 Hodge.axis1
      ≡ Ordered.orderedWilsonPlaquette dataSet site Hodge.axis1 Hodge.axis2
    reverse31 : ∀ site →
      Ordered.orderedWilsonPlaquette dataSet site Hodge.axis3 Hodge.axis1
      ≡ Ordered.orderedWilsonPlaquette dataSet site Hodge.axis1 Hodge.axis3

open NativeSixC3Orientation public

-- The exactly six original physical source terms are invariant under C3
-- once precisely those two on-source orientation witnesses are supplied.
nativeSixC3At :
  ∀ dataSet →
  NativeSixC3Orientation dataSet →
  ∀ site →
  sixPhysicalAt (SignedC3.c3NativeData dataSet) site
  ≡ sixPhysicalAt dataSet
      (C3.spatialC3Site site)
nativeSixC3At dataSet orientation site
  rewrite Ordered.orderedWilsonPlaquetteC3 dataSet site Hodge.axis0 Hodge.axis1
        | Ordered.orderedWilsonPlaquetteC3 dataSet site Hodge.axis0 Hodge.axis2
        | Ordered.orderedWilsonPlaquetteC3 dataSet site Hodge.axis0 Hodge.axis3
        | Ordered.orderedWilsonPlaquetteC3 dataSet site Hodge.axis1 Hodge.axis2
        | Ordered.orderedWilsonPlaquetteC3 dataSet site Hodge.axis1 Hodge.axis3
        | Ordered.orderedWilsonPlaquetteC3 dataSet site Hodge.axis2 Hodge.axis3
        | reverse21 orientation
            (C3.spatialC3Site site)
        | reverse31 orientation
            (C3.spatialC3Site site)
  = ℚRing.solve-∀
      (Ordered.orderedWilsonPlaquette dataSet
        (C3.spatialC3Site site)
        Hodge.axis0 Hodge.axis1)
      (Ordered.orderedWilsonPlaquette dataSet
        (C3.spatialC3Site site)
        Hodge.axis0 Hodge.axis2)
      (Ordered.orderedWilsonPlaquette dataSet
        (C3.spatialC3Site site)
        Hodge.axis0 Hodge.axis3)
      (Ordered.orderedWilsonPlaquette dataSet
        (C3.spatialC3Site site)
        Hodge.axis1 Hodge.axis2)
      (Ordered.orderedWilsonPlaquette dataSet
        (C3.spatialC3Site site)
        Hodge.axis1 Hodge.axis3)
      (Ordered.orderedWilsonPlaquette dataSet
        (C3.spatialC3Site site)
        Hodge.axis2 Hodge.axis3)

nativeSixC3Summed :
  ∀ dataSet →
  NativeSixC3Orientation dataSet →
  Six.sixPlanePhysicalTraceAction (SignedC3.c3NativeData dataSet)
  ≡ Six.sixPlanePhysicalTraceAction dataSet
nativeSixC3Summed dataSet orientation =
  trans
    (Hodge.sumSitesCong _ _
      (λ site → trans
        (nativeSixPlaneAtIsLiteralSix
          (SignedC3.c3NativeData dataSet) site)
        (nativeSixC3At dataSet orientation site)))
    (trans
      (Ordered.sumSitesSpatialC3
        (sixPhysicalAt dataSet))
      (Hodge.sumSitesCong _ _
        (λ site → sym (nativeSixPlaneAtIsLiteralSix dataSet site))))
