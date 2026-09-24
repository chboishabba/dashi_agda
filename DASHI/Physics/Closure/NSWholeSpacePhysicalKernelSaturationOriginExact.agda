module DASHI.Physics.Closure.NSWholeSpacePhysicalKernelSaturationOriginExact where

------------------------------------------------------------------------
-- A / PHYSICAL KERNEL LOW-FREQUENCY SATURATION COMPILER
--
-- This is the canonical near-origin branch.
--
-- Inputs:
--   * the exact off-diagonal projected Gram realization of gramScalar;
--   * nonnegativity of the literal centered residual;
--   * ONE same-object coefficient equality identifying
--
--       pairResolvent * outputResolvent * centeredResidual
--
--     with the Bishop-real saturation kernel
--
--       s / ((nu |xi|^2 + s) (nu |xi|^2)).
--
-- Output:
--
--   physicalCenteredResolventCorrection(kernel,I)
--      <= nu^{-1} M_{alpha beta}.
--
-- The signed Gram is never replaced by |Gram| and is never assumed
-- nonnegative.  No directional second-moment q-gain is used.  Thus the
-- continuous centered displacement need not shrink with the output frequency.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayProjectionExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalProjectedGramPairExact as Pair
import DASHI.Physics.Closure.NSWholeSpaceR3PhysicalKernelProjectedQWeldExact as GramWeld
import DASHI.Physics.Closure.NSWholeSpaceProjectedSaturationOriginBoundExact as SaturationBound
import DASHI.Physics.Closure.NSWholeSpaceCenteredResolventSaturationExact as Saturation
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

lerayPoint :
  Heat.PuncturedEuclideanFrequency →
  Leray.PuncturedFrequency
lerayPoint point =
  Leray.punctured-frequency
    (Heat.frequency point)
    (Heat.normSquaredPositive point)

record PhysicalKernelSaturationOriginWeld
    {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    (kernel : Physical.EuclideanPhysicalResolventKernel trajectory)
    (fluid : Heat.PositiveViscosity)
    (point : Heat.PuncturedEuclideanFrequency)
    (I : Euclidean.EuclideanInteraction) : Set₁ where
  constructor physical-kernel-saturation-origin-weld
  field
    projectedGramWeld :
      GramWeld.PhysicalKernelProjectedGramWeld
        kernel point I

    centeredResidualNonnegative :
      BishopReal.NonNegative
        (Physical.centeredResidual kernel I)

    heatPlusCenteredResidualPositive :
      BishopReal._<_
        BishopReal.0ℝ
        (BishopReal._+_
          (Heat.viscousHeatRate fluid (Heat.frequency point))
          (Physical.centeredResidual kernel I))

    centeredCoefficientIsSaturationKernel :
      BishopReal._≃_
        (BishopReal._*_
          (Physical.pairResolvent kernel I)
          (BishopReal._*_
            (Physical.outputResolvent kernel I)
            (Physical.centeredResidual kernel I)))
        (SaturationBound.centeredResolventKernel
          (SaturationBound.whole-space-projected-saturation-cell
            (Heat.viscosity fluid)
            (Heat.viscosityPositive fluid)
            (lerayPoint point)
            (Physical.centeredResidual kernel I)
            centeredResidualNonnegative
            (Physical.uEta
              (Pair.alphaCell
                (GramWeld.projectedPair projectedGramWeld)))
            (Physical.uZeta
              (Pair.alphaCell
                (GramWeld.projectedPair projectedGramWeld)))
            (Physical.uEta
              (Pair.betaCell
                (GramWeld.projectedPair projectedGramWeld)))
            (Physical.uZeta
              (Pair.betaCell
                (GramWeld.projectedPair projectedGramWeld)))))

open PhysicalKernelSaturationOriginWeld public

saturationCell :
  ∀ {S trajectory kernel fluid point I} →
  PhysicalKernelSaturationOriginWeld
    {S} {trajectory} kernel fluid point I →
  SaturationBound.WholeSpaceProjectedSaturationCell
saturationCell {kernel = kernel} {fluid = fluid} {point = point} weld =
  let pair = GramWeld.projectedPair (projectedGramWeld weld)
  in
  SaturationBound.whole-space-projected-saturation-cell
    (Heat.viscosity fluid)
    (Heat.viscosityPositive fluid)
    (lerayPoint point)
    (Physical.centeredResidual kernel I)
    (centeredResidualNonnegative weld)
    (Physical.uEta (Pair.alphaCell pair))
    (Physical.uZeta (Pair.alphaCell pair))
    (Physical.uEta (Pair.betaCell pair))
    (Physical.uZeta (Pair.betaCell pair))

kernelCorrectionAsSaturationProduct :
  ∀ {S trajectory kernel fluid point I} →
  (weld :
    PhysicalKernelSaturationOriginWeld
      {S} {trajectory} kernel fluid point I) →
  BishopReal._≃_
    (Physical.physicalCenteredResolventCorrection kernel I)
    (BishopReal._*_
      (SaturationBound.centeredResolventKernel (saturationCell weld))
      (SaturationBound.gram (saturationCell weld)))
kernelCorrectionAsSaturationProduct
    {kernel = kernel} {I = I} weld =
  let
    coefficient =
      centeredCoefficientIsSaturationKernel weld
    gram =
      GramWeld.gramScalarIsProjectedPairGram
        (projectedGramWeld weld)
    open BishopP.ℝ-Solver
    reassociate :
      BishopReal._≃_
        (Physical.physicalCenteredResolventCorrection kernel I)
        (BishopReal._*_
          (BishopReal._*_
            (Physical.pairResolvent kernel I)
            (BishopReal._*_
              (Physical.outputResolvent kernel I)
              (Physical.centeredResidual kernel I)))
          (Physical.gramScalar kernel I))
    reassociate =
      solve 4
        (λ p o s g →
          (p ⊗ o) ⊗ (s ⊗ g)
          ⊜
          (p ⊗ (o ⊗ s)) ⊗ g)
        BishopP.≃-refl
        (Physical.pairResolvent kernel I)
        (Physical.outputResolvent kernel I)
        (Physical.centeredResidual kernel I)
        (Physical.gramScalar kernel I)
  in
  BishopP.≃-trans
    reassociate
    (BishopP.*-cong coefficient gram)

physicalKernelSaturationOriginBound :
  ∀ {S trajectory kernel fluid point I} →
  (weld :
    PhysicalKernelSaturationOriginWeld
      {S} {trajectory} kernel fluid point I) →
  BishopReal._≤_
    (Physical.physicalCenteredResolventCorrection kernel I)
    (BishopReal._*_
      (SaturationBound.viscosityInverse (saturationCell weld))
      (SaturationBound.majorant (saturationCell weld)))
physicalKernelSaturationOriginBound weld =
  BishopP.≤-respˡ-≃
    (kernelCorrectionAsSaturationProduct weld)
    (SaturationBound.projectedSaturationOriginBound
      (saturationCell weld))

lowFrequencyPhysicalKernelSaturationCompilerClosed : Bool
lowFrequencyPhysicalKernelSaturationCompilerClosed = true

lowFrequencyDirectionalSecondMomentRequired : Bool
lowFrequencyDirectionalSecondMomentRequired = false

lowFrequencyGramPositivityRequired : Bool
lowFrequencyGramPositivityRequired = false

lowFrequencyAbsoluteGramObserverIntroduced : Bool
lowFrequencyAbsoluteGramObserverIntroduced = false

clayPromotion : Bool
clayPromotion = false

lowFrequencyPhysicalKernelSaturationCompilerClosedIsTrue :
  lowFrequencyPhysicalKernelSaturationCompilerClosed ≡ true
lowFrequencyPhysicalKernelSaturationCompilerClosedIsTrue = refl

lowFrequencyDirectionalSecondMomentRequiredIsFalse :
  lowFrequencyDirectionalSecondMomentRequired ≡ false
lowFrequencyDirectionalSecondMomentRequiredIsFalse = refl

lowFrequencyGramPositivityRequiredIsFalse :
  lowFrequencyGramPositivityRequired ≡ false
lowFrequencyGramPositivityRequiredIsFalse = refl

lowFrequencyAbsoluteGramObserverIntroducedIsFalse :
  lowFrequencyAbsoluteGramObserverIntroduced ≡ false
lowFrequencyAbsoluteGramObserverIntroducedIsFalse = refl
