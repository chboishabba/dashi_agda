module DASHI.Physics.Closure.NSTriadKNR571CenteredAlignedComplementExact where

------------------------------------------------------------------------
-- R571 / CENTERED ALIGNED COMPLEMENT
--
-- Purpose:
--   expose the aligned P-Q companion of the existing anti-parallel
--   normalized-direction identity used around R467, specialized to the
--   centered shift p = k + y, q = k - y.
--
-- Source status:
--   This owner is intentionally small and fail-closed.  It records the exact
--   algebraic target and the resulting angular second-moment consequence, but
--   does not fabricate the carrier-specific normalized-direction identity.
--   The live analytic frontier remains the ordered radial/angular payment used
--   by Gate-A coordinate A2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

------------------------------------------------------------------------
-- A least-privilege scalar interface for the aligned complement.
--
-- The intended physical interpretation is
--
--   radiusP       = |p|
--   radiusQ       = |q|
--   alignedDefect = ||P - Q||²
--   shiftRadiusSq = |p-q|² = 4 |y|²
--
-- and the exact identity
--
--   (|p|-|q|)² + |p||q| ||P-Q||² = |p-q|².
------------------------------------------------------------------------

record CenteredAlignedComplementData : Set where
  field
    radiusP : ℚ
    radiusQ : ℚ
    alignedDefect : ℚ
    shiftRadiusSq : ℚ

    radiusPNonnegative : 0ℚ ≤ radiusP
    radiusQNonnegative : 0ℚ ≤ radiusQ
    alignedDefectNonnegative : 0ℚ ≤ alignedDefect

    alignedComplementIdentity :
      ((radiusP + (- radiusQ)) * (radiusP + (- radiusQ)))
        + (radiusP * radiusQ) * alignedDefect
      ≡ shiftRadiusSq

    alignedAngularTermBelowShift :
      (radiusP * radiusQ) * alignedDefect ≤ shiftRadiusSq

open CenteredAlignedComplementData public

------------------------------------------------------------------------
-- Centered-shift specialization surface.
--
-- The literal Fourier owner should instantiate `shiftRadiusSq` with 4|y|².
-- Keeping that identification separate prevents this file from silently
-- reintroducing square roots or a second norm carrier.
------------------------------------------------------------------------

record CenteredShiftAlignedComplement : Set where
  field
    base : CenteredAlignedComplementData
    yRadiusSq : ℚ
    centeredShiftRadiusMeaning :
      CenteredAlignedComplementData.shiftRadiusSq base
      ≡ (1ℚ + 1ℚ) * (1ℚ + 1ℚ) * yRadiusSq

open CenteredShiftAlignedComplement public

centeredAngularSecondMomentPayment :
  (D : CenteredShiftAlignedComplement) →
  let B = CenteredShiftAlignedComplement.base D
  in
  (CenteredAlignedComplementData.radiusP B
    * CenteredAlignedComplementData.radiusQ B)
    * CenteredAlignedComplementData.alignedDefect B
  ≤ (1ℚ + 1ℚ) * (1ℚ + 1ℚ)
      * CenteredShiftAlignedComplement.yRadiusSq D
centeredAngularSecondMomentPayment D
  rewrite CenteredShiftAlignedComplement.centeredShiftRadiusMeaning D =
  CenteredAlignedComplementData.alignedAngularTermBelowShift
    (CenteredShiftAlignedComplement.base D)

------------------------------------------------------------------------
-- Status / firewall.
------------------------------------------------------------------------

roundR571CenteredAlignedComplementInterfaceWritten : Bool
roundR571CenteredAlignedComplementInterfaceWritten = true

roundR571CenteredAlignedAngularPaymentDerived : Bool
roundR571CenteredAlignedAngularPaymentDerived = true

roundR571LiteralNormalizedDirectionIdentityInhabitedHere : Bool
roundR571LiteralNormalizedDirectionIdentityInhabitedHere = false

roundR571A2UniformCurvatureClosedHere : Bool
roundR571A2UniformCurvatureClosedHere = false

roundR571CenteredAlignedComplementInterfaceWrittenIsTrue :
  roundR571CenteredAlignedComplementInterfaceWritten ≡ true
roundR571CenteredAlignedComplementInterfaceWrittenIsTrue = refl

roundR571LiteralNormalizedDirectionIdentityInhabitedHereIsFalse :
  roundR571LiteralNormalizedDirectionIdentityInhabitedHere ≡ false
roundR571LiteralNormalizedDirectionIdentityInhabitedHereIsFalse = refl

roundR571A2UniformCurvatureClosedHereIsFalse :
  roundR571A2UniformCurvatureClosedHere ≡ false
roundR571A2UniformCurvatureClosedHereIsFalse = refl
