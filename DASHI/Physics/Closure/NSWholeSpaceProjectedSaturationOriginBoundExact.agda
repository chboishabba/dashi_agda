module DASHI.Physics.Closure.NSWholeSpaceProjectedSaturationOriginBoundExact where

------------------------------------------------------------------------
-- A / COMPLETE LOCAL LOW-FREQUENCY SATURATION PAYMENT
--
-- Compose:
--
--   1. literal Bishop divergence-form convection,
--   2. literal Bishop Leray contraction,
--   3. projected Gram quadratic output bound,
--   4. centered-resolvent saturation K(a,s) <= 1/a,
--   5. a(xi)=nu |xi|^2.
--
-- On every punctured output frequency and every nonnegative centered residual:
--
--   K(nu |xi|^2,s) * Gram_P(xi)
--     <= nu^{-1}
--        ( |u_a(eta)|^2 |u_a(zeta)|^2
--        + |u_b(eta)|^2 |u_b(zeta)|^2 ).
--
-- There is NO singular power of |xi| on the right.  This is the local
-- whole-space origin theorem the A lane actually needs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayProjectionExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedGramQuadraticMajorantExact as Projected
import DASHI.Physics.Closure.NSTriadKNEuclideanRawGramQuadraticMajorantExact as Raw
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpaceCenteredResolventSaturationExact as Saturation
import DASHI.Physics.Closure.NSWholeSpaceSaturationOriginCancellationExact as Origin

record WholeSpaceProjectedSaturationCell : Set where
  constructor whole-space-projected-saturation-cell
  field
    viscosity : BishopReal.ℝ
    viscosityPositive :
      BishopReal._<_ BishopReal.0ℝ viscosity

    output : Leray.PuncturedFrequency

    residual : BishopReal.ℝ
    residualNonnegative :
      BishopReal.NonNegative residual

    aEta aZeta bEta bZeta : Physical.BishopComplex3

open WholeSpaceProjectedSaturationCell public

radiusSquared :
  WholeSpaceProjectedSaturationCell → BishopReal.ℝ
radiusSquared D =
  Heat.frequencyNormSquared
    (Leray.frequency (output D))

radiusSquaredPositive :
  (D : WholeSpaceProjectedSaturationCell) →
  BishopReal._<_ BishopReal.0ℝ (radiusSquared D)
radiusSquaredPositive D =
  Leray.normSquaredPositive (output D)

heatRate :
  WholeSpaceProjectedSaturationCell → BishopReal.ℝ
heatRate D =
  BishopReal._*_
    (viscosity D)
    (radiusSquared D)

heatRatePositive :
  (D : WholeSpaceProjectedSaturationCell) →
  BishopReal._<_ BishopReal.0ℝ (heatRate D)
heatRatePositive D =
  let
    nuPos = BishopP.0<x⇒posx (viscosityPositive D)
    qPos = BishopP.0<x⇒posx (radiusSquaredPositive D)
  in
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y nuPos qPos)

heatPlusResidualPositive :
  (D : WholeSpaceProjectedSaturationCell) →
  BishopReal._<_ BishopReal.0ℝ
    (BishopReal._+_ (heatRate D) (residual D))
heatPlusResidualPositive D =
  let
    residualOrder =
      BishopP.nonNegx⇒0≤x (residualNonnegative D)

    heatBelowSum :
      BishopReal._≤_
        (heatRate D)
        (BishopReal._+_ (heatRate D) (residual D))
    heatBelowSum =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm
          (BishopP.+-identityʳ (heatRate D)))
        (BishopP.+-monoʳ-≤
          (heatRate D)
          residualOrder)
  in
  BishopP.<-≤-trans
    (heatRatePositive D)
    heatBelowSum

gram :
  WholeSpaceProjectedSaturationCell → BishopReal.ℝ
gram D =
  Projected.projectedGram
    (output D)
    (aEta D) (aZeta D)
    (bEta D) (bZeta D)

majorant :
  WholeSpaceProjectedSaturationCell → BishopReal.ℝ
majorant D =
  Raw.rawGramStateMajorant
    (aEta D) (aZeta D)
    (bEta D) (bZeta D)

majorantNonnegative :
  (D : WholeSpaceProjectedSaturationCell) →
  BishopReal.NonNegative (majorant D)
majorantNonnegative D =
  Raw.rawGramStateMajorantNonnegative
    (aEta D) (aZeta D)
    (bEta D) (bZeta D)

gramQuadraticBound :
  (D : WholeSpaceProjectedSaturationCell) →
  BishopReal._≤_
    (gram D)
    (BishopReal._*_
      (radiusSquared D)
      (majorant D))
gramQuadraticBound D =
  Projected.projectedGramQuadraticMajorant
    (output D)
    (aEta D) (aZeta D)
    (bEta D) (bZeta D)

originCell :
  WholeSpaceProjectedSaturationCell →
  Origin.SaturatedPhysicalOriginCell
originCell D =
  Origin.saturated-physical-origin-cell
    (viscosity D)
    (radiusSquared D)
    (viscosityPositive D)
    (radiusSquaredPositive D)
    (residual D)
    (residualNonnegative D)
    (heatPlusResidualPositive D)
    (gram D)
    (majorant D)
    (majorantNonnegative D)
    (gramQuadraticBound D)

centeredResolventKernel :
  WholeSpaceProjectedSaturationCell → BishopReal.ℝ
centeredResolventKernel D =
  Saturation.kernel
    (Origin.saturationInputs (originCell D))

viscosityNonzero :
  (D : WholeSpaceProjectedSaturationCell) →
  BishopReal._≄0 (viscosity D)
viscosityNonzero D =
  Heat.Reciprocal.xNonzero (viscosityPositive D)

viscosityInverse :
  WholeSpaceProjectedSaturationCell → BishopReal.ℝ
viscosityInverse D =
  BishopInverse._⁻¹
    (viscosity D)
    (viscosityNonzero D)

projectedSaturationOriginBound :
  (D : WholeSpaceProjectedSaturationCell) →
  BishopReal._≤_
    (BishopReal._*_
      (centeredResolventKernel D)
      (gram D))
    (BishopReal._*_
      (viscosityInverse D)
      (majorant D))
projectedSaturationOriginBound D =
  Origin.saturatedOriginBound (originCell D)

------------------------------------------------------------------------
-- This closes the local low-frequency singularity.  Remaining whole-space A
-- work is global/integral:
--
--   * instantiate this cell from the continuous interaction/kernel record,
--   * prove the state majorant integrable on the signed convolution carrier,
--   * use high-frequency second-order branch + low-frequency saturation branch,
--   * compile the resulting signed critical barrier into whole-space
--     continuation.
------------------------------------------------------------------------

wholeSpaceProjectedSaturationOriginBoundClosed : Bool
wholeSpaceProjectedSaturationOriginBoundClosed = true

lowFrequencyNeedsXiSixCompensation : Bool
lowFrequencyNeedsXiSixCompensation = false

lowFrequencyNeedsXiFourCompensation : Bool
lowFrequencyNeedsXiFourCompensation = false

lowFrequencyUsesOnlyQuadraticGramOutputFactor : Bool
lowFrequencyUsesOnlyQuadraticGramOutputFactor = true

signedLebesgueMajorantIntegrabilityClosedHere : Bool
signedLebesgueMajorantIntegrabilityClosedHere = false

clayPromotion : Bool
clayPromotion = false

wholeSpaceProjectedSaturationOriginBoundClosedIsTrue :
  wholeSpaceProjectedSaturationOriginBoundClosed ≡ true
wholeSpaceProjectedSaturationOriginBoundClosedIsTrue = refl

lowFrequencyNeedsXiSixCompensationIsFalse :
  lowFrequencyNeedsXiSixCompensation ≡ false
lowFrequencyNeedsXiSixCompensationIsFalse = refl

lowFrequencyUsesOnlyQuadraticGramOutputFactorIsTrue :
  lowFrequencyUsesOnlyQuadraticGramOutputFactor ≡ true
lowFrequencyUsesOnlyQuadraticGramOutputFactorIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
