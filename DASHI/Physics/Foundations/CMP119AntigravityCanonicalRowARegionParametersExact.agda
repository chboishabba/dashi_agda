{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowARegionParametersExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_)

import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA

------------------------------------------------------------------------
-- SAME-OBJECT S4a CONSTRUCTOR
--
-- Do not choose an arbitrary repository coupling cap and later prove that it
-- equals the Row-A cap.  Construct the preferred YM4 region parameter package
-- with that cap definitionally.
------------------------------------------------------------------------

canonicalRowARegionParameters :
  RowA.FiniteQuarticResponseConstants →
  ℚ → ℚ → ℚ →
  RG.YM4RGRegionParameters
canonicalRowARegionParameters rowA smallFieldCap largeFieldCap covarianceCap =
  RG.regionParameters
    (RowA.canonicalQuarticResponseGamma rowA)
    smallFieldCap
    largeFieldCap
    covarianceCap

canonicalRowARegionCouplingCap :
  ∀ rowA smallFieldCap largeFieldCap covarianceCap →
  RG.couplingCap
    (canonicalRowARegionParameters
      rowA smallFieldCap largeFieldCap covarianceCap)
  ≡ RowA.canonicalQuarticResponseGamma rowA
canonicalRowARegionCouplingCap rowA smallFieldCap largeFieldCap covarianceCap =
  refl

canonicalRowARegionCouplingCapAtMostOne :
  ∀ rowA smallFieldCap largeFieldCap covarianceCap →
  RG.couplingCap
    (canonicalRowARegionParameters
      rowA smallFieldCap largeFieldCap covarianceCap)
  ≤ 1ℚ
canonicalRowARegionCouplingCapAtMostOne rowA smallFieldCap largeFieldCap covarianceCap =
  RowA.canonicalQuarticResponseGammaAtMostOne rowA

repositoryCapEqualityRequiredOnPreferredRoute : Bool
repositoryCapEqualityRequiredOnPreferredRoute = false

repositoryCapEqualityRequiredOnPreferredRouteIsFalse :
  repositoryCapEqualityRequiredOnPreferredRoute ≡ false
repositoryCapEqualityRequiredOnPreferredRouteIsFalse = refl
