module DASHI.Physics.Closure.NSTriadKNNestedDominantCommonHatReuseRound339Exact where

------------------------------------------------------------------------
-- ROUND339 / SAME-OBJECT REUSE OF THE EXISTING RESONANT DOMINANT COMMON HAT
--
-- R338 says not to rediscover finite-band support.  R63 already proves that
-- EVERY literal resonant PhysicalTriadIncidence has a constructed dominant
-- dyadic common hat with at most two adjacent active shells.
--
-- A literal R329 nested cell contains TWO actual physical triads:
--
--   inner : a + b = p,
--   outer : p + q = k,
--
-- with the inner output definitionally/receipt-wise identified with the outer
-- forcing leg.  Therefore both layers inherit R63's existing common-hat theorem
-- directly on the SAME objects.  No new support ontology is introduced.
--
-- Important boundary: two local hats do not yet prove that the composed
-- heat-weighted shell OPERATOR has a bandwidth-one TT* kernel.  Composition may
-- couple the two support fibres through the shared p leg.  The remaining work
-- is precisely to transport these already-constructed local hats through the
-- literal nested operator realization demanded by R338.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNResonantDominantCommonHatRound63Exact as R63

F : C3.RealField _
F = Rational.rationalRealField

innerDominantCommonHat :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  R63.ResonantDominantCommonHat (R329.inner C)
innerDominantCommonHat E I O system S L H W C =
  R63.resonantDominantCommonHat (R329.inner C)

outerDominantCommonHat :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  R63.ResonantDominantCommonHat (R329.outer C)
outerDominantCommonHat E I O system S L H W C =
  R63.resonantDominantCommonHat (R329.outer C)

record NestedDominantCommonHatCarrier
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F)
    (C : R329.StrongLowLiteralNestedCell E I O system S L H W) : Set where
  constructor nested-dominant-common-hat-carrier
  field
    innerHat : R63.ResonantDominantCommonHat (R329.inner C)
    outerHat : R63.ResonantDominantCommonHat (R329.outer C)

open NestedDominantCommonHatCarrier public

nestedDominantCommonHatCarrier :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  NestedDominantCommonHatCarrier E I O system S L H W C
nestedDominantCommonHatCarrier E I O system S L H W C =
  nested-dominant-common-hat-carrier
    (innerDominantCommonHat E I O system S L H W C)
    (outerDominantCommonHat E I O system S L H W C)

round339InnerCommonHatInheritedFromR63 : Bool
round339InnerCommonHatInheritedFromR63 = true

round339OuterCommonHatInheritedFromR63 : Bool
round339OuterCommonHatInheritedFromR63 = true

round339NestedCellUsesLiteralR329Triads : Bool
round339NestedCellUsesLiteralR329Triads = true

round339TwoLocalHatsAloneProveComposedTTStarBandwidthOne : Bool
round339TwoLocalHatsAloneProveComposedTTStarBandwidthOne = false

round339NestedOperatorSupportTransportClosed : Bool
round339NestedOperatorSupportTransportClosed = false

round339PackageAClosed : Bool
round339PackageAClosed = false

round339ClayPromotion : Bool
round339ClayPromotion = false

round339TwoLocalHatsAloneProveComposedTTStarBandwidthOneIsFalse :
  round339TwoLocalHatsAloneProveComposedTTStarBandwidthOne ≡ false
round339TwoLocalHatsAloneProveComposedTTStarBandwidthOneIsFalse = refl

round339PackageAClosedIsFalse : round339PackageAClosed ≡ false
round339PackageAClosedIsFalse = refl

round339ClayPromotionIsFalse : round339ClayPromotion ≡ false
round339ClayPromotionIsFalse = refl
