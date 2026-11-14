module DASHI.Physics.YangMills.YMClayNativeSixPlaneC3ActualPhysicalSourceExact where

-- R443-SIX: CLOSED ON THE ACTUAL NATIVE SIX-PLANE RATIONAL SU2 SOURCE.
-- Previous owners: Wilson (1974), Balaban (1985), DASHI native signed-path
-- inverse theorem and periodic positive-plane closure. Not Haar/continuum.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans; sym)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as Inverse
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Quaternion
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact as Ordered
import DASHI.Physics.YangMills.YMClayNativeSixPlaneC3SourceReductionExact as Reduction
import DASHI.Physics.YangMills.YMClayNativeRationalSU2AllSignedC3WilsonExact as SignedC3
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six
import DASHI.Physics.YangMills.YMClayNativeRationalSU2FourFactorReversalExact as Reversal

-- Reverse-opposite of each of the six ORIGINAL source plaquette words is
-- precisely the swapped-axis oriented word, with the SAME starting site.
inversePositivePlaneIsSwappedWord :
  ∀ (plane : Plaquette.PositivePlane4) →
  Inverse.reverseOpposite (Bond.plaquetteBoundaryDirections plane)
  ≡ Ordered.orientedOrderedPlaquetteWord
      (Torus.second (Plaquette.planeAxes plane))
      (Torus.first (Plaquette.planeAxes plane))
inversePositivePlaneIsSwappedWord Torus.zeroᵢ = refl
inversePositivePlaneIsSwappedWord (Torus.sucᵢ Torus.zeroᵢ) = refl
inversePositivePlaneIsSwappedWord
  (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
inversePositivePlaneIsSwappedWord
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl
inversePositivePlaneIsSwappedWord
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ
    (Torus.sucᵢ Torus.zeroᵢ)))) = refl
inversePositivePlaneIsSwappedWord
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ
    (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))))) = refl

-- The physical plaquette closure rewrites the reverse-opposite theorem's
-- terminal site back to exactly the original plaquette basepoint.
swappedPositivePlaquetteIsInverse :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
    (site : Hodge.Site4)
    (plane : Plaquette.PositivePlane4) →
  Bond.pathHolonomy (Native.realization dataSet) site
    (Ordered.orientedOrderedPlaquetteWord
      (Torus.second (Plaquette.planeAxes plane))
      (Torus.first (Plaquette.planeAxes plane)))
  ≡ Quaternion.inverseRationalSU2
      (Native.rationalSU2PlaquetteHolonomy dataSet
        (Torus.pair site plane))
swappedPositivePlaquetteIsInverse dataSet site plane =
  trans
    (cong
      (Bond.pathHolonomy (Native.realization dataSet) site)
      (sym (inversePositivePlaneIsSwappedWord plane)))
    (subst
      (λ start →
        Bond.pathHolonomy (Native.realization dataSet) start
          (Inverse.reverseOpposite (Bond.plaquetteBoundaryDirections plane))
        ≡ Quaternion.inverseRationalSU2
            (Native.rationalSU2PlaquetteHolonomy dataSet
              (Torus.pair site plane)))
      (Bond.plaquetteCloses
        (Geometry.periodicPlaquetteClosure Weld.three) site plane)
      (Inverse.pathHolonomyReverseOpposite
        (Geometry.periodicStepInverseLaws Weld.three)
        (Native.realization dataSet) site
        (Bond.plaquetteBoundaryDirections plane)))

swappedPositivePlaquetteTrace :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
    (site : Hodge.Site4)
    (plane : Plaquette.PositivePlane4) →
  Ordered.orderedWilsonPlaquette dataSet site
    (Torus.second (Plaquette.planeAxes plane))
    (Torus.first (Plaquette.planeAxes plane))
  ≡ Ordered.orderedWilsonPlaquette dataSet site
    (Torus.first (Plaquette.planeAxes plane))
    (Torus.second (Plaquette.planeAxes plane))
swappedPositivePlaquetteTrace dataSet site plane =
  trans
    (cong SU2.realPart
      (swappedPositivePlaquetteIsInverse dataSet site plane))
    (trans
      (Reversal.realTraceInverse
        (Native.rationalSU2PlaquetteHolonomy dataSet
          (Torus.pair site plane)))
      (Six.nativeSixPlaneTraceIsOrdered dataSet site plane))

nativeSelectedSixOrientation :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) →
  Reduction.NativeSixC3Orientation dataSet
nativeSelectedSixOrientation dataSet = record
  { Reduction.NativeSixC3Orientation.reverse21 =
      λ site → swappedPositivePlaquetteTrace dataSet site
        (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))
  ; Reduction.NativeSixC3Orientation.reverse31 =
      λ site → swappedPositivePlaquetteTrace dataSet site
        (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ
          (Torus.sucᵢ Torus.zeroᵢ))))
  }

-- Actual six-positive-plane native rational SU2 Wilson action C3 symmetry:
-- no new mathematical proposition remains in the six-plane *finite*
-- orientation geometry, conditional only on correctness of Agda typechecking.
nativeSixPositiveWilsonActionSpatialC3 :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) →
  Six.sixPlanePhysicalTraceAction (SignedC3.c3NativeData dataSet)
  ≡ Six.sixPlanePhysicalTraceAction dataSet
nativeSixPositiveWilsonActionSpatialC3 dataSet =
  Reduction.nativeSixC3Summed dataSet
    (nativeSelectedSixOrientation dataSet)
