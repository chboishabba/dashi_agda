module DASHI.Physics.Closure.NSWholeSpaceSaturationOriginCancellationExact where

------------------------------------------------------------------------
-- A / SATURATION BRANCH REMOVES THE WHOLE-SPACE ORIGIN SINGULARITY
--
-- Put q = |xi|^2 > 0 and a = nu q with nu > 0.  The low-frequency
-- centered-resolvent saturation branch supplies K <= a^{-1}.  Therefore any
-- physical Gram bound of the natural divergence-form size
--
--     gram <= q * M
--
-- yields
--
--     K * gram <= (nu q)^{-1} (q M) = nu^{-1} M.
--
-- This is strictly stronger at the origin than asking the second-order
-- curvature branch for six or four powers.  It needs exactly the two
-- output-frequency powers already exposed by the raw Gram.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSWholeSpaceR3RadialOriginCancellationExact as R3
import DASHI.Physics.Closure.NSWholeSpaceCenteredResolventSaturationExact as Saturation

record SaturatedPhysicalOriginCell : Set where
  constructor saturated-physical-origin-cell
  field
    viscosity radiusSquared : BishopReal.ℝ
    viscosityPositive :
      BishopReal._<_ BishopReal.0ℝ viscosity
    radiusSquaredPositive :
      BishopReal._<_ BishopReal.0ℝ radiusSquared

    residual : BishopReal.ℝ
    residualNonnegative :
      BishopReal.NonNegative residual
    heatPlusResidualPositive :
      BishopReal._<_ BishopReal.0ℝ
        (BishopReal._+_
          (BishopReal._*_ viscosity radiusSquared)
          residual)

    gram majorant : BishopReal.ℝ
    majorantNonnegative : BishopReal.NonNegative majorant
    gramCarriesOutputSquare :
      BishopReal._≤_
        gram
        (BishopReal._*_ radiusSquared majorant)

open SaturatedPhysicalOriginCell public

positiveRateData :
  SaturatedPhysicalOriginCell →
  R3.PositiveViscosityRadiusSquare
positiveRateData D =
  R3.positive-viscosity-radius-square
    (viscosity D)
    (radiusSquared D)
    (viscosityPositive D)
    (radiusSquaredPositive D)

saturationInputs :
  SaturatedPhysicalOriginCell →
  Saturation.SaturationInputs
saturationInputs D =
  Saturation.saturation-inputs
    (BishopReal._*_ (viscosity D) (radiusSquared D))
    (residual D)
    (R3.heatRatePositive (positiveRateData D))
    (residualNonnegative D)
    (heatPlusResidualPositive D)

outputInverse :
  SaturatedPhysicalOriginCell →
  BishopReal.ℝ
outputInverse D =
  BishopInverse._⁻¹
    (BishopReal._*_ (viscosity D) (radiusSquared D))
    (R3.heatRateNonzero (positiveRateData D))

viscosityInverse :
  SaturatedPhysicalOriginCell →
  BishopReal.ℝ
viscosityInverse D =
  BishopInverse._⁻¹
    (viscosity D)
    (R3.viscosityNonzero (positiveRateData D))

outputInverseNonnegative :
  (D : SaturatedPhysicalOriginCell) →
  BishopReal.NonNegative (outputInverse D)
outputInverseNonnegative D =
  BishopP.pos⇒nonNeg
    (BishopInverse.posx⇒posx⁻¹
      (R3.heatRateNonzero (positiveRateData D))
      (BishopP.0<x⇒posx (R3.heatRatePositive (positiveRateData D))))

kernelTimesGramBelowKernelMajorant :
  (D : SaturatedPhysicalOriginCell) →
  BishopReal._≤_
    (BishopReal._*_
      (Saturation.kernel (saturationInputs D))
      (gram D))
    (BishopReal._*_
      (Saturation.kernel (saturationInputs D))
      (BishopReal._*_ (radiusSquared D) (majorant D)))
kernelTimesGramBelowKernelMajorant D =
  BishopP.*-monoˡ-≤-nonNeg
    (gramCarriesOutputSquare D)
    (Saturation.kernelNonnegative (saturationInputs D))

outputMajorantNonnegative :
  (D : SaturatedPhysicalOriginCell) →
  BishopReal.NonNegative
    (BishopReal._*_ (radiusSquared D) (majorant D))
outputMajorantNonnegative D =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.pos⇒nonNeg
      (BishopP.0<x⇒posx (radiusSquaredPositive D)))
    (majorantNonnegative D)

kernelMajorantBelowOutputInverseMajorant :
  (D : SaturatedPhysicalOriginCell) →
  BishopReal._≤_
    (BishopReal._*_
      (Saturation.kernel (saturationInputs D))
      (BishopReal._*_ (radiusSquared D) (majorant D)))
    (BishopReal._*_
      (outputInverse D)
      (BishopReal._*_ (radiusSquared D) (majorant D)))
kernelMajorantBelowOutputInverseMajorant D =
  BishopP.*-monoʳ-≤-nonNeg
    (Saturation.kernelBelowOutputInverse (saturationInputs D))
    (outputMajorantNonnegative D)

outputInverseCancelsOutputSquare :
  (D : SaturatedPhysicalOriginCell) →
  BishopReal._≃_
    (BishopReal._*_
      (outputInverse D)
      (BishopReal._*_ (radiusSquared D) (majorant D)))
    (BishopReal._*_
      (viscosityInverse D)
      (majorant D))
outputInverseCancelsOutputSquare D =
  let
    rate = positiveRateData D
    inverseProduct = R3.inverseProductExact rate
    q = radiusSquared D
    iq =
      BishopInverse._⁻¹ q (R3.radiusSquaredNonzero rate)
    inu = viscosityInverse D
    qLaw =
      BishopInverse.*-inverseˡ
        q
        (R3.radiusSquaredNonzero rate)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congʳ inverseProduct)
    (BishopP.≃-trans
      (solve 3
        (λ n q' iq' →
          (n ⊗ iq') ⊗ (q' ⊗ majorant D)
          ⊜
          n ⊗ ((q' ⊗ iq') ⊗ majorant D))
        BishopP.≃-refl
        inu q iq)
      (BishopP.≃-trans
        (BishopP.*-congˡ
          (BishopP.*-congʳ qLaw))
        (let open BishopP.ℝ-Solver
         in solve 2
           (λ n m →
             n ⊗ (BishopReal.1ℝ ⊗ m)
             ⊜ n ⊗ m)
           BishopP.≃-refl
           inu (majorant D))))

saturatedOriginBound :
  (D : SaturatedPhysicalOriginCell) →
  BishopReal._≤_
    (BishopReal._*_
      (Saturation.kernel (saturationInputs D))
      (gram D))
    (BishopReal._*_
      (viscosityInverse D)
      (majorant D))
saturatedOriginBound D =
  BishopP.≤-trans
    (kernelTimesGramBelowKernelMajorant D)
    (BishopP.≤-trans
      (kernelMajorantBelowOutputInverseMajorant D)
      (BishopP.≤-respʳ-≃
        (outputInverseCancelsOutputSquare D)
        BishopP.≤-refl))

------------------------------------------------------------------------
-- This is the sharp low-frequency consumer.  The outstanding physical theorem
-- is now just the expected quadratic Gram estimate on the projected continuous
-- NS interaction:
--
--   Gram(xi,eta,...) <= |xi|^2 M(xi,eta,...),
--
-- with an integrable M after signed recombination.
------------------------------------------------------------------------

saturationOriginCancellationClosed : Bool
saturationOriginCancellationClosed = true

requiredOutputPowersAtOrigin : Bool
requiredOutputPowersAtOrigin = true

secondOrderCurvatureRequiredNearOrigin : Bool
secondOrderCurvatureRequiredNearOrigin = false

physicalProjectedGramQuadraticBoundClosedHere : Bool
physicalProjectedGramQuadraticBoundClosedHere = false

clayPromotion : Bool
clayPromotion = false

saturationOriginCancellationClosedIsTrue :
  saturationOriginCancellationClosed ≡ true
saturationOriginCancellationClosedIsTrue = refl

secondOrderCurvatureRequiredNearOriginIsFalse :
  secondOrderCurvatureRequiredNearOrigin ≡ false
secondOrderCurvatureRequiredNearOriginIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
