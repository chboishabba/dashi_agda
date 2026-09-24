module DASHI.Physics.Closure.NSWholeSpaceCenteredResolventSaturationExact where

------------------------------------------------------------------------
-- A / BISHOP-REAL CENTERED RESOLVENT SATURATION
--
-- Near xi = 0 the second-order curvature envelope 2/a^3 is the wrong branch.
-- The exact centered-resolvent coefficient is
--
--     K(a,s) = s (a+s)^(-1) a^(-1),
--
-- with a>0 and s>=0.  Since s <= a+s,
--
--     s (a+s)^(-1) <= 1,
--
-- hence
--
--     K(a,s) <= a^(-1).
--
-- This is the Bishop-real version of the rational two-envelope saturation
-- theorem.  It lives on the scalar carrier used by literal Euclidean A and
-- needs no spectral gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

record SaturationInputs : Set where
  constructor saturation-inputs
  field
    a s : BishopReal.ℝ
    aPositive : BishopReal._<_ BishopReal.0ℝ a
    sNonnegative : BishopReal.NonNegative s
    aPlusSPositive :
      BishopReal._<_ BishopReal.0ℝ (BishopReal._+_ a s)

open SaturationInputs public

aNonzero : (D : SaturationInputs) → BishopReal._≄0 (a D)
aNonzero D = Reciprocal.xNonzero (aPositive D)

aPlusSNonzero :
  (D : SaturationInputs) →
  BishopReal._≄0 (BishopReal._+_ (a D) (s D))
aPlusSNonzero D = Reciprocal.xNonzero (aPlusSPositive D)

invA : SaturationInputs → BishopReal.ℝ
invA D = BishopInverse._⁻¹ (a D) (aNonzero D)

invAPlusS : SaturationInputs → BishopReal.ℝ
invAPlusS D =
  BishopInverse._⁻¹
    (BishopReal._+_ (a D) (s D))
    (aPlusSNonzero D)

kernel : SaturationInputs → BishopReal.ℝ
kernel D =
  BishopReal._*_
    (BishopReal._*_ (s D) (invAPlusS D))
    (invA D)

invANonnegative :
  (D : SaturationInputs) →
  BishopReal.NonNegative (invA D)
invANonnegative D =
  BishopP.pos⇒nonNeg
    (BishopInverse.posx⇒posx⁻¹
      (aNonzero D)
      (BishopP.0<x⇒posx (aPositive D)))

invAPlusSNonnegative :
  (D : SaturationInputs) →
  BishopReal.NonNegative (invAPlusS D)
invAPlusSNonnegative D =
  BishopP.pos⇒nonNeg
    (BishopInverse.posx⇒posx⁻¹
      (aPlusSNonzero D)
      (BishopP.0<x⇒posx (aPlusSPositive D)))

sBelowAPlusS :
  (D : SaturationInputs) →
  BishopReal._≤_ (s D) (BishopReal._+_ (a D) (s D))
sBelowAPlusS D =
  let
    aNN = BishopP.pos⇒nonNeg (BishopP.0<x⇒posx (aPositive D))
    zeroBelowA = BishopP.nonNegx⇒0≤x aNN
    raised =
      BishopP.+-monoʳ-≤
        (s D)
        zeroBelowA
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (BishopP.+-identityˡ (s D)))
    (BishopP.≤-respʳ-≃
      (BishopP.+-comm (a D) (s D))
      raised)

defectFractionBelowOne :
  (D : SaturationInputs) →
  BishopReal._≤_
    (BishopReal._*_ (s D) (invAPlusS D))
    BishopReal.1ℝ
defectFractionBelowOne D =
  let
    scaled :
      BishopReal._≤_
        (BishopReal._*_ (s D) (invAPlusS D))
        (BishopReal._*_
          (BishopReal._+_ (a D) (s D))
          (invAPlusS D))
    scaled =
      BishopP.*-monoʳ-≤-nonNeg
        (sBelowAPlusS D)
        (invAPlusSNonnegative D)

    collapse =
      BishopInverse.*-inverseˡ
        (BishopReal._+_ (a D) (s D))
        (aPlusSNonzero D)
  in
  BishopP.≤-respʳ-≃ collapse scaled

kernelBelowOutputInverse :
  (D : SaturationInputs) →
  BishopReal._≤_ (kernel D) (invA D)
kernelBelowOutputInverse D =
  let
    scaled :
      BishopReal._≤_
        (BishopReal._*_
          (BishopReal._*_ (s D) (invAPlusS D))
          (invA D))
        (BishopReal._*_ BishopReal.1ℝ (invA D))
    scaled =
      BishopP.*-monoʳ-≤-nonNeg
        (defectFractionBelowOne D)
        (invANonnegative D)
  in
  BishopP.≤-respʳ-≃
    (BishopP.*-identityˡ (invA D))
    scaled

kernelNonnegative :
  (D : SaturationInputs) →
  BishopReal.NonNegative (kernel D)
kernelNonnegative D =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.nonNegx,y⇒nonNegx*y
      (sNonnegative D)
      (invAPlusSNonnegative D))
    (invANonnegative D)

------------------------------------------------------------------------
-- Low-frequency selection rule:
--   use saturation K <= 1/a near the origin;
--   reserve the a^-3 second-order curvature branch for regions where its
--   extra h^2 cancellation is actually advantageous.
------------------------------------------------------------------------

bishopRealSaturationEnvelopeClosed : Bool
bishopRealSaturationEnvelopeClosed = true

saturationNeedsSpectralGap : Bool
saturationNeedsSpectralGap = false

saturationCurvatureOrderAtOrigin : Bool
saturationCurvatureOrderAtOrigin = false

clayPromotion : Bool
clayPromotion = false

bishopRealSaturationEnvelopeClosedIsTrue :
  bishopRealSaturationEnvelopeClosed ≡ true
bishopRealSaturationEnvelopeClosedIsTrue = refl

saturationNeedsSpectralGapIsFalse :
  saturationNeedsSpectralGap ≡ false
saturationNeedsSpectralGapIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
