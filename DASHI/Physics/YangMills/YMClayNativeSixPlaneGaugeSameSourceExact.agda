module DASHI.Physics.YangMills.YMClayNativeSixPlaneGaugeSameSourceExact where

------------------------------------------------------------------------
-- ORIGINAL periodic positive-six-plane Wilson gauge invariance.
--
-- Compose existing source owners:
--   BalabanClayGate4RationalSU2BondCarrierExact:
--     rationalSU2PlaquetteGaugeCancellation (for ALL periodic n)
--   YMClaySide4RationalSU2C3WilsonTraceExact:
--     rationalTraceConjugationInvariant
--   YMClayNativeRationalSU2SixPlaneSameSourceExact:
--     exact ORIGINAL positive six-plane sum (n = 3, L = 4).
--
-- This is a same-original-link algebraic gauge weld. No new group,
-- no new trace, no synthetic gauge assumption and no Haar.
-- The original SUN matrix, Bishop real, integrals and continuum
-- remain distinct, not coerced to this rational proposition.
--
-- Attribution: Wilson/Balaban; previous DASHI original finite
-- periodic bond, SU2 and six-plane theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.YMClaySide4RationalSU2C3WilsonTraceExact as Class
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld

originalTransformedPlaquetteTrace :
  ∀ {n} (dataSet : Native.RationalSU2BondData n) →
  Plaquette.PeriodicPlaquette n → ℚ
originalTransformedPlaquetteTrace dataSet plaquette =
  SU2.realPart
    (Bond.transformedPathHolonomy (Native.realization dataSet)
      (Torus.first plaquette)
      (Bond.plaquetteBoundaryDirections (Torus.second plaquette)))

-- Original rational plaquette, all n, with its OWN gauge transformation.
originalPlaquetteTraceGaugeInvariant :
  ∀ {n} (dataSet : Native.RationalSU2BondData n)
    (plaquette : Plaquette.PeriodicPlaquette n) →
  originalTransformedPlaquetteTrace dataSet plaquette
  ≡ SU2.realPart
      (Native.rationalSU2PlaquetteHolonomy dataSet plaquette)
originalPlaquetteTraceGaugeInvariant dataSet plaquette =
  trans
    (cong SU2.realPart
      (Native.rationalSU2PlaquetteGaugeCancellation dataSet plaquette))
    (Class.rationalTraceConjugationInvariant
      (Native.siteGauge dataSet (Torus.first plaquette))
      (Native.rationalSU2PlaquetteHolonomy dataSet plaquette))

-- At the ORIGINAL side-four source, apply the theorem to the literal
-- six positive planes; never confuse with sixteen ordered-axis pairs.
nativeTransformedSixPlaneTraceSumAt :
  Native.RationalSU2BondData Weld.three → Hodge.Site4 → ℚ
nativeTransformedSixPlaneTraceSumAt dataSet site =
  SU2.sumMap (Plaquette.ownedPeriodicPlaquettes site)
    (originalTransformedPlaquetteTrace dataSet)

nativeSixPlaneGaugeInvariantAt :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) site →
  nativeTransformedSixPlaneTraceSumAt dataSet site
  ≡ Six.nativeSixPlaneTraceSumAt dataSet site
nativeSixPlaneGaugeInvariantAt dataSet site =
  Six.sixPlaneSumMapCong _ _ _
    (originalPlaquetteTraceGaugeInvariant dataSet)

nativeTransformedSixPlaneTraceAction :
  Native.RationalSU2BondData Weld.three → ℚ
nativeTransformedSixPlaneTraceAction dataSet =
  Hodge.sumSites (nativeTransformedSixPlaneTraceSumAt dataSet)

-- Fully reduced original six-plane, full four-dimensional site sum.
nativeSixPlaneGaugeInvariant :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) →
  nativeTransformedSixPlaneTraceAction dataSet
  ≡ Six.sixPlanePhysicalTraceAction dataSet
nativeSixPlaneGaugeInvariant dataSet =
  Hodge.sumSitesCong _ _
    (nativeSixPlaneGaugeInvariantAt dataSet)
