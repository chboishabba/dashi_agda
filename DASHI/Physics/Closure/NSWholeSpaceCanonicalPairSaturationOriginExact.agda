module DASHI.Physics.Closure.NSWholeSpaceCanonicalPairSaturationOriginExact where

------------------------------------------------------------------------
-- A / CANONICAL PUNCTURED PAIR SATURATION ORIGIN THEOREM
--
-- Build the low-frequency physical coefficient instead of accepting it as a
-- same-object input.
--
-- For a punctured output xi, positive viscosity nu, and nonnegative centered
-- residual s:
--
--   a       = nu |xi|^2
--   R_out   = a^{-1}
--   R_pair  = (a+s)^{-1}
--   C       = R_pair R_out s.
--
-- The canonical same-output projected Gram pair is built directly from
-- (xi,eta_alpha,eta_beta,t).  The centered correction is C times that signed
-- off-diagonal Gram.  Ring commutativity identifies C with the saturation
-- kernel s(a+s)^{-1}a^{-1}, so the existing local origin theorem gives
--
--   centeredCorrection <= nu^{-1} M.
--
-- No abstract physical-kernel resolvent fields, coefficient weld, Gram
-- positivity, absolute Gram observer, or directional second moment are needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayProjectionExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedGramPairCarrierRealizationExact as PairCarrier
import DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalProjectedGramPairExact as Pair
import DASHI.Physics.Closure.NSWholeSpaceProjectedSaturationOriginBoundExact as Origin

record CanonicalPairSaturationData
    {S : Canonical.CanonicalNSSemantics}
    (trajectory : Physical.EuclideanFourierTrajectory S)
    (fluid : Heat.PositiveViscosity) : Set₁ where
  constructor canonical-pair-saturation-data
  field
    point : Heat.PuncturedEuclideanFrequency
    alphaEta betaEta : Euclidean.R3Frequency
    time : Canonical.Time

    residual : BishopReal.ℝ
    residualNonnegative : BishopReal.NonNegative residual

open CanonicalPairSaturationData public

alphaInteraction :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  Euclidean.EuclideanInteraction
alphaInteraction D =
  PairCarrier.canonicalConvolutionInteraction
    (Heat.frequency (point D))
    (alphaEta D)

betaInteraction :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  Euclidean.EuclideanInteraction
betaInteraction D =
  PairCarrier.canonicalConvolutionInteraction
    (Heat.frequency (point D))
    (betaEta D)

canonicalProjectedPair :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  Pair.CanonicalProjectedGramPair trajectory (point D)
canonicalProjectedPair {trajectory = trajectory} D =
  Pair.canonical-projected-gram-pair
    (alphaInteraction D)
    (betaInteraction D)
    refl
    refl
    (time D)

heatRate :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
heatRate {fluid = fluid} D =
  Heat.viscousHeatRate fluid (Heat.frequency (point D))

heatRatePositive :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._<_ BishopReal.0ℝ (heatRate D)
heatRatePositive {fluid = fluid} D =
  Heat.viscousHeatRatePositive fluid (point D)

heatPlusResidualPositive :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._<_
    BishopReal.0ℝ
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

heatNonzero :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≄0 (heatRate D)
heatNonzero D =
  Reciprocal.xNonzero (heatRatePositive D)

heatPlusResidualNonzero :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≄0
    (BishopReal._+_ (heatRate D) (residual D))
heatPlusResidualNonzero D =
  Reciprocal.xNonzero (heatPlusResidualPositive D)

outputResolvent :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
outputResolvent D =
  BishopInverse._⁻¹ (heatRate D) (heatNonzero D)

pairResolvent :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
pairResolvent D =
  BishopInverse._⁻¹
    (BishopReal._+_ (heatRate D) (residual D))
    (heatPlusResidualNonzero D)

centeredCoefficient :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
centeredCoefficient D =
  BishopReal._*_
    (pairResolvent D)
    (BishopReal._*_
      (outputResolvent D)
      (residual D))

pairGram :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
pairGram D =
  Pair.pairGram (canonicalProjectedPair D)

centeredCorrection :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  BishopReal.ℝ
centeredCorrection D =
  BishopReal._*_
    (centeredCoefficient D)
    (pairGram D)

originCell :
  ∀ {S trajectory fluid} →
  CanonicalPairSaturationData
    {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid →
  Origin.WholeSpaceProjectedSaturationCell
originCell {fluid = fluid} D =
  let pair = canonicalProjectedPair D
  in
  Origin.whole-space-projected-saturation-cell
    (Heat.viscosity fluid)
    (Heat.viscosityPositive fluid)
    (Leray.punctured-frequency
      (Heat.frequency (point D))
      (Heat.normSquaredPositive (point D)))
    (residual D)
    (residualNonnegative D)
    (Physical.uEta (Pair.alphaCell pair))
    (Physical.uZeta (Pair.alphaCell pair))
    (Physical.uEta (Pair.betaCell pair))
    (Physical.uZeta (Pair.betaCell pair))

coefficientIsSaturationKernel :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≃_
    (centeredCoefficient D)
    (Origin.centeredResolventKernel (originCell D))
coefficientIsSaturationKernel D =
  let open BishopP.ℝ-Solver
  in
  solve 3
    (λ pairInv outInv s →
      pairInv ⊗ (outInv ⊗ s)
      ⊜
      (s ⊗ pairInv) ⊗ outInv)
    BishopP.≃-refl
    (pairResolvent D)
    (outputResolvent D)
    (residual D)

gramIsOriginGram :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≃_
    (pairGram D)
    (Origin.gram (originCell D))
gramIsOriginGram D =
  BishopP.≃-refl (pairGram D)

centeredCorrectionIsOriginProduct :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≃_
    (centeredCorrection D)
    (BishopReal._*_
      (Origin.centeredResolventKernel (originCell D))
      (Origin.gram (originCell D)))
centeredCorrectionIsOriginProduct D =
  BishopP.*-cong
    (coefficientIsSaturationKernel D)
    (gramIsOriginGram D)

canonicalPairSaturationOriginBound :
  ∀ {S trajectory fluid} →
  (D :
    CanonicalPairSaturationData
      {S} (trajectory : Physical.EuclideanFourierTrajectory S) fluid) →
  BishopReal._≤_
    (centeredCorrection D)
    (BishopReal._*_
      (Origin.viscosityInverse (originCell D))
      (Origin.majorant (originCell D)))
canonicalPairSaturationOriginBound D =
  BishopP.≤-respˡ-≃
    (centeredCorrectionIsOriginProduct D)
    (Origin.projectedSaturationOriginBound
      (originCell D))

canonicalPairResolventsConstructed : Bool
canonicalPairResolventsConstructed = true

centeredCoefficientWeldRequired : Bool
centeredCoefficientWeldRequired = false

abstractPhysicalKernelRequiredForOriginBound : Bool
abstractPhysicalKernelRequiredForOriginBound = false

offDiagonalGramPositivityRequired : Bool
offDiagonalGramPositivityRequired = false

directionalSecondMomentRequired : Bool
directionalSecondMomentRequired = false

clayPromotion : Bool
clayPromotion = false

canonicalPairResolventsConstructedIsTrue :
  canonicalPairResolventsConstructed ≡ true
canonicalPairResolventsConstructedIsTrue = refl

centeredCoefficientWeldRequiredIsFalse :
  centeredCoefficientWeldRequired ≡ false
centeredCoefficientWeldRequiredIsFalse = refl

abstractPhysicalKernelRequiredForOriginBoundIsFalse :
  abstractPhysicalKernelRequiredForOriginBound ≡ false
abstractPhysicalKernelRequiredForOriginBoundIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
