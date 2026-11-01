module DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact where

------------------------------------------------------------------------
-- CANONICAL SIX (mu<nu) PLAQUETTE SAME-OBJECT CONSUMER.
--
-- Reuse actual existing sources, no parallel plaquette carrier:
--
--   BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact.PositivePlane4
--   BalabanClayGate4PeriodicBondPathBianchiExact.plaquetteBoundaryDirections
--   BalabanClayGate4RationalSU2BondCarrierExact.rationalSU2PlaquetteHolonomy
--
-- The new sixteen ordered-axis-pair C3 theorem is a useful analytic finite
-- parent, but *six* physical positive planes are separately owned.
-- Here we identify the actual native six-plane contour/holonomy with the
-- previously built native real SU2 rational oriented word term. This is a
-- genuine same-object finite Wilson observable, not a toy identification.
--
-- It does NOT claim six-plane *summed action* C3 invariance from the sixteen
-- ordered-sum proof: that additional implication requires reverse orientation
-- symmetry and the correct diagonal/multiplicity identity.
--
-- Primary: Wilson, "Confinement of Quarks" (1974); Bałaban (1985), and
-- previous DASHI native six-plane/P33 proof owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact as Ordered

-- The native existing plaquette word IS the source six-positive-plane
-- specialisation of the 16 ordered-word constructor.
nativeSixPlaneBoundaryIsOrdered :
  ∀ (plane : Plaquette.PositivePlane4) →
  Bond.plaquetteBoundaryDirections plane
  ≡
  Ordered.orientedOrderedPlaquetteWord
    (Torus.first (Plaquette.planeAxes plane))
    (Torus.second (Plaquette.planeAxes plane))
nativeSixPlaneBoundaryIsOrdered plane = refl

-- Existing native rational SU2 plaquette HOLONOMY itself is identical
-- to the real selected n=3 ordered graph-transport source convention.
nativeSixPlaneHolonomyIsOrdered :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
    (site : Hodge.Site4) (plane : Plaquette.PositivePlane4) →
  Native.rationalSU2PlaquetteHolonomy dataSet
    (Torus.pair site plane)
  ≡
  Bond.pathHolonomy (Native.realization dataSet)
    site
    (Ordered.orientedOrderedPlaquetteWord
      (Torus.first (Plaquette.planeAxes plane))
      (Torus.second (Plaquette.planeAxes plane)))
nativeSixPlaneHolonomyIsOrdered dataSet site plane =
  cong
    (Bond.pathHolonomy (Native.realization dataSet) site)
    (nativeSixPlaneBoundaryIsOrdered plane)

nativeSixPlaneTraceIsOrdered :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
    (site : Hodge.Site4) (plane : Plaquette.PositivePlane4) →
  SU2.realPart
    (Native.rationalSU2PlaquetteHolonomy dataSet (Torus.pair site plane))
  ≡
  Ordered.orderedWilsonPlaquette dataSet site
    (Torus.first (Plaquette.planeAxes plane))
    (Torus.second (Plaquette.planeAxes plane))
nativeSixPlaneTraceIsOrdered dataSet site plane =
  cong SU2.realPart
    (nativeSixPlaneHolonomyIsOrdered dataSet site plane)

nativeSixPlaneTraceSumAt :
  Native.RationalSU2BondData Weld.three → Hodge.Site4 → ℚ
nativeSixPlaneTraceSumAt dataSet site =
  SU2.sumMap (Plaquette.ownedPeriodicPlaquettes site)
    (λ plaquette →
      SU2.realPart (Native.rationalSU2PlaquetteHolonomy dataSet plaquette))

sixPlanePhysicalTraceAction :
  Native.RationalSU2BondData Weld.three → ℚ
sixPlanePhysicalTraceAction dataSet =
  Hodge.sumSites (nativeSixPlaneTraceSumAt dataSet)

sixPlaneSumMapCong :
  ∀ {A : Set}
    (values : List A) (left right : A → ℚ) →
  (∀ item → left item ≡ right item) →
  SU2.sumMap values left ≡ SU2.sumMap values right
sixPlaneSumMapCong [] left right pointwise = refl
sixPlaneSumMapCong (item ∷ rest) left right pointwise
  rewrite pointwise item
        | sixPlaneSumMapCong rest left right pointwise = refl

-- This exact trace sum is on the original six-plaq-on-native-SU2 carrier.
-- Do not equate it with the 16-ordered sum or an actual Gibbs/Haar probability.
nativeSixPlaneTraceSumEqualsOrderedSixSubfamily :
  ∀ dataSet site →
  nativeSixPlaneTraceSumAt dataSet site
  ≡
  SU2.sumMap (Plaquette.ownedPeriodicPlaquettes site)
    (λ plaquette →
      Ordered.orderedWilsonPlaquette dataSet site
        (Torus.first (Plaquette.planeAxes (Torus.second plaquette)))
        (Torus.second (Plaquette.planeAxes (Torus.second plaquette))))
nativeSixPlaneTraceSumEqualsOrderedSixSubfamily dataSet site =
  sixPlaneSumMapCong _ _ _
    (λ (Torus.pair here plane) →
      nativeSixPlaneTraceIsOrdered dataSet here plane)
