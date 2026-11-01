module DASHI.Physics.YangMills.YMClayNativeSixPlaneOrderedIdentityExact where

------------------------------------------------------------------------
-- R443 SIX-PLANE CONVENTION: EXACT 16-ORDERED VS ORIGINAL SIX-SOURCE.
--
-- For each side-four site on the ORIGINAL n=3 norm-one rational SU2 links:
--   Σ_{a,b=0..3} Re Tr(U_ab)/2
--     = 2·Σ_{a<b} Re Tr(U_ab)/2 + 4 .
--
-- There are four diagonal ordered terms: every +a,+a,-a,-a path is
-- the two-edge prefix followed by its reverse-opposite, so native
-- holonomy = 1 and normalized real trace = 1. The remaining 12 terms
-- are precisely the six original positive planes and their six inverse
-- orientations, already proved equal by the native inverse-path theorem.
--
-- No physical coupling beta, plaquette action normalisation or compact
-- Haar measure is silently supplied; 1-ReTr, rather than ReTr alone,
-- is the usual Wilson action deficit convention.
--
-- Attribution: Wilson (1974), Balaban (1985); older native geometry,
-- reverse-path, finite-sum and ring algebra remain their own owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Signed
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Q
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as Inverse
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeRationalSU2OrderedPlaquetteC3ActionExact as Ordered
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six
import DASHI.Physics.YangMills.YMClayNativeSixPlaneC3SourceReductionExact as Reduction
import DASHI.Physics.YangMills.YMClayNativeSixPlaneC3ActualPhysicalSourceExact as Source

twoPositive : ∀ axis → List Signed.SignedAxis4
twoPositive axis = Bond.positiveDirection axis ∷ Bond.positiveDirection axis ∷ []

diagonalWordIsReverseOpposite :
  ∀ axis →
  Ordered.orientedOrderedPlaquetteWord axis axis
  ≡ Inverse._++_ (twoPositive axis) (Inverse.reverseOpposite (twoPositive axis))
diagonalWordIsReverseOpposite axis = refl

-- Exact diagonal plaquette is the identity in the original SU2 link group,
-- using source-native path append, inverse and group inverse-right proofs.
nativeDiagonalHolonomyIdentity :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three)
  site axis →
  Bond.pathHolonomy (Native.realization dataSet) site
    (Ordered.orientedOrderedPlaquetteWord axis axis)
  ≡ Q.identityRationalSU2
nativeDiagonalHolonomyIdentity dataSet site axis =
  trans
    (cong (Bond.pathHolonomy (Native.realization dataSet) site)
      (diagonalWordIsReverseOpposite axis))
    (trans
      (Inverse.holonomyAppend
        (Native.realization dataSet) site
        (twoPositive axis) (Inverse.reverseOpposite (twoPositive axis)))
      (trans
        (cong
          (Q.multiplyRationalSU2
            (Bond.pathHolonomy (Native.realization dataSet) site
              (twoPositive axis)))
          (Inverse.pathHolonomyReverseOpposite
            (Geometry.periodicStepInverseLaws Weld.three)
            (Native.realization dataSet) site (twoPositive axis)))
        (Q.inverseRight
          (Bond.pathHolonomy (Native.realization dataSet) site
            (twoPositive axis)))))

nativeDiagonalTraceIsOne :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) site axis →
  Ordered.orderedWilsonPlaquette dataSet site axis axis ≡ 1ℚ
nativeDiagonalTraceIsOne dataSet site axis =
  cong SU2.realPart (nativeDiagonalHolonomyIdentity dataSet site axis)

fourℚ : ℚ
fourℚ = 1ℚ + (1ℚ + (1ℚ + 1ℚ))

-- The universally quantified 16↔6 formula, on the actual native source.
orderedAtIsTwiceSixPlusDiagonal :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) site →
  Hodge.sumIndex4
    (λ a → Hodge.sumIndex4
      (λ b → Ordered.orderedWilsonPlaquette dataSet site a b))
  ≡ Reduction.sixPhysicalAt dataSet site
      + (Reduction.sixPhysicalAt dataSet site + fourℚ)
orderedAtIsTwiceSixPlusDiagonal dataSet site
  rewrite nativeDiagonalTraceIsOne dataSet site Hodge.axis0
        | nativeDiagonalTraceIsOne dataSet site Hodge.axis1
        | nativeDiagonalTraceIsOne dataSet site Hodge.axis2
        | nativeDiagonalTraceIsOne dataSet site Hodge.axis3
        | Source.swappedPositivePlaquetteTrace dataSet site Torus.zeroᵢ
        | Source.swappedPositivePlaquetteTrace dataSet site
            (Torus.sucᵢ Torus.zeroᵢ)
        | Source.swappedPositivePlaquetteTrace dataSet site
            (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))
        | Source.swappedPositivePlaquetteTrace dataSet site
            (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))
        | Source.swappedPositivePlaquetteTrace dataSet site
            (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ
              (Torus.sucᵢ Torus.zeroᵢ))))
        | Source.swappedPositivePlaquetteTrace dataSet site
            (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ
              (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))))
  = ℚRing.solve-∀
      (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis0 Hodge.axis1)
      (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis0 Hodge.axis2)
      (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis0 Hodge.axis3)
      (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis1 Hodge.axis2)
      (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis1 Hodge.axis3)
      (Ordered.orderedWilsonPlaquette dataSet site Hodge.axis2 Hodge.axis3)

-- The physical 16-ordered site-sum equals the SIX ORIGINAL SOURCE
-- plaquettes counted twice plus four trivial diagonal plaquettes per site.
-- This is a universal finite source identity; no Wilson beta chosen here.
orderedActionIsSixSourceTwicePlusDiagonal :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) →
  Ordered.orderedWilsonAction dataSet
  ≡ Hodge.sumSites
      (λ site →
        Six.nativeSixPlaneTraceSumAt dataSet site
          + (Six.nativeSixPlaneTraceSumAt dataSet site + fourℚ))
orderedActionIsSixSourceTwicePlusDiagonal dataSet =
  Hodge.sumSitesCong _ _
    (λ site → trans
      (orderedAtIsTwiceSixPlusDiagonal dataSet site)
      (cong
        (λ six → six + (six + fourℚ))
        (sym (Reduction.nativeSixPlaneAtIsLiteralSix dataSet site))))

------------------------------------------------------------------------
-- Physical Wilson action convention: sum of (1 - normalized real trace)
-- instead of the trace sum itself. Exact finite-site normalization:
-- sixteen ORDERED deficits = twice the SIX original positive-plane deficits.
-- The four diagonal loops contribute zero Wilson deficit (holonomy 1).
------------------------------------------------------------------------

sixℚ : ℚ
sixℚ = 1ℚ + (1ℚ + (1ℚ + (1ℚ + (1ℚ + 1ℚ))))

sixteenℚ : ℚ
sixteenℚ = (sixℚ + sixℚ) + fourℚ

sixPhysicalDeficitAt :
  Native.RationalSU2BondData Weld.three → Hodge.Site4 → ℚ
sixPhysicalDeficitAt dataSet site =
  sixℚ - Six.nativeSixPlaneTraceSumAt dataSet site

orderedDeficitAt :
  Native.RationalSU2BondData Weld.three → Hodge.Site4 → ℚ
orderedDeficitAt dataSet site =
  sixteenℚ -
    Hodge.sumIndex4 (λ a →
      Hodge.sumIndex4 (λ b →
        Ordered.orderedWilsonPlaquette dataSet site a b))

orderedDeficitAtIsTwiceSixDeficit :
  ∀ (dataSet : Native.RationalSU2BondData Weld.three) site →
  orderedDeficitAt dataSet site
  ≡ sixPhysicalDeficitAt dataSet site
      + sixPhysicalDeficitAt dataSet site
orderedDeficitAtIsTwiceSixDeficit dataSet site
  rewrite Reduction.nativeSixPlaneAtIsLiteralSix dataSet site
        | orderedAtIsTwiceSixPlusDiagonal dataSet site
  = ℚRing.solve-∀ (Reduction.sixPhysicalAt dataSet site)
