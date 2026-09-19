module DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact where

------------------------------------------------------------------------
-- A / ACTUAL WHOLE-SPACE FOURIER OBJECT TYPES
--
-- This owner removes the "three arbitrary scalar flux functions" seam from
-- EuclideanSignedFluxData.  The whole-space realization now starts from:
--
--   * canonical constructive R^3 time/space semantics;
--   * literal continuous frequency xi, eta, zeta = xi-eta;
--   * a proof-relevant Fourier velocity trajectory;
--   * an output-Leray projected interaction cell;
--   * the Gram scalar and the two resolvent factors on THAT SAME interaction.
--
-- weighted/common/centered fluxes are definitions from those physical
-- ingredients.  The only remaining algebraic input is the exact pointwise
-- resolvent split on the concrete kernel, which is the Bishop/setoid analogue
-- of the already checked rational identity used in periodic B.
--
-- No lattice mode, Galerkin cutoff, finite fibre, or T^3 limit appears here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean

------------------------------------------------------------------------
-- Literal complex C^3 values over the canonical Bishop real carrier.
------------------------------------------------------------------------

record BishopComplex : Set where
  constructor bishop-complex
  field
    realPart imaginaryPart : BishopReal.ℝ

open BishopComplex public

record BishopComplex3 : Set where
  constructor bishop-complex3
  field
    cx cy cz : BishopComplex

open BishopComplex3 public

FourierVelocityHistory : Set
FourierVelocityHistory =
  Canonical.Time → Euclidean.R3Frequency → BishopComplex3

FourierPressureHistory : Set
FourierPressureHistory =
  Canonical.Time → Euclidean.R3Frequency → BishopComplex

FourierForcingHistory : Set
FourierForcingHistory =
  Canonical.Time → Euclidean.R3Frequency → BishopComplex3

------------------------------------------------------------------------
-- Fourier realization of one canonical physical-space trajectory.
------------------------------------------------------------------------

record EuclideanFourierTrajectory
    (S : Canonical.CanonicalNSSemantics) : Set₁ where
  field
    velocityPhysical : Canonical.VelocityHistory
    pressurePhysical : Canonical.PressureHistory

    velocityHat : FourierVelocityHistory
    pressureHat : FourierPressureHistory

    FourierTransformVelocity : Set
    FourierTransformPressure : Set

    velocityTransformExact : FourierTransformVelocity
    pressureTransformExact : FourierTransformPressure

    divergenceFreePhysical :
      Canonical.DivergenceFreeHistory S velocityPhysical

open EuclideanFourierTrajectory public

------------------------------------------------------------------------
-- One literal continuous triad cell after eliminating the delta constraint.
------------------------------------------------------------------------

record EuclideanProjectedInteraction
    {S : Canonical.CanonicalNSSemantics}
    (trajectory : EuclideanFourierTrajectory S) : Set₁ where
  field
    interaction : Euclidean.EuclideanInteraction
    time : Canonical.Time

    uEta :
      BishopComplex3
    uEtaExact :
      uEta
      ≡ velocityHat trajectory time
          (Euclidean.eta interaction)

    uZeta :
      BishopComplex3
    uZetaExact :
      uZeta
      ≡ velocityHat trajectory time
          (Euclidean.zeta interaction)

    rawConvolutionCell : BishopComplex3
    lerayProjectedCell : BishopComplex3

    RawInteractionMeaning : Set
    LerayProjectionMeaning : Set

    rawInteractionExact : RawInteractionMeaning
    lerayProjectionExact : LerayProjectionMeaning

open EuclideanProjectedInteraction public

------------------------------------------------------------------------
-- Physical signed resolvent kernel.
--
-- The scalar observables are now attached to an actual Fourier trajectory and
-- actual projected continuous interaction.  They are no longer three unrelated
-- functions accepted by EuclideanSignedFluxData.
------------------------------------------------------------------------

record EuclideanPhysicalResolventKernel
    {S : Canonical.CanonicalNSSemantics}
    (trajectory : EuclideanFourierTrajectory S) : Set₁ where
  field
    cell :
      Euclidean.EuclideanInteraction →
      EuclideanProjectedInteraction trajectory

    gramScalar :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    pairResolvent :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    outputResolvent :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    centeredResidual :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    pairResolventMeaning : Set
    outputResolventMeaning : Set
    centeredResidualMeaning : Set
    gramMeaning : Set

    pairResolventIsPhysical : pairResolventMeaning
    outputResolventIsPhysical : outputResolventMeaning
    centeredResidualIsPhysical : centeredResidualMeaning
    gramIsPhysical : gramMeaning

    pointwiseResolventGramSplit :
      (I : Euclidean.EuclideanInteraction) →
      BishopReal._*_
        (pairResolvent I)
        (gramScalar I)
      ≡
      BishopReal._-_
        (BishopReal._*_
          (outputResolvent I)
          (gramScalar I))
        (BishopReal._*_
          (BishopReal._*_
            (pairResolvent I)
            (outputResolvent I))
          (BishopReal._*_
            (centeredResidual I)
            (gramScalar I)))

open EuclideanPhysicalResolventKernel public

physicalWeightedFlux :
  ∀ {S} {trajectory : EuclideanFourierTrajectory S} →
  EuclideanPhysicalResolventKernel trajectory →
  Euclidean.EuclideanInteraction → BishopReal.ℝ
physicalWeightedFlux kernel I =
  BishopReal._*_
    (pairResolvent kernel I)
    (gramScalar kernel I)

physicalCommonResolventFlux :
  ∀ {S} {trajectory : EuclideanFourierTrajectory S} →
  EuclideanPhysicalResolventKernel trajectory →
  Euclidean.EuclideanInteraction → BishopReal.ℝ
physicalCommonResolventFlux kernel I =
  BishopReal._*_
    (outputResolvent kernel I)
    (gramScalar kernel I)

physicalCenteredResolventCorrection :
  ∀ {S} {trajectory : EuclideanFourierTrajectory S} →
  EuclideanPhysicalResolventKernel trajectory →
  Euclidean.EuclideanInteraction → BishopReal.ℝ
physicalCenteredResolventCorrection kernel I =
  BishopReal._*_
    (BishopReal._*_
      (pairResolvent kernel I)
      (outputResolvent kernel I))
    (BishopReal._*_
      (centeredResidual kernel I)
      (gramScalar kernel I))

physicalEuclideanSignedFluxData :
  ∀ {S} {trajectory : EuclideanFourierTrajectory S} →
  EuclideanPhysicalResolventKernel trajectory →
  Euclidean.EuclideanSignedFluxData
physicalEuclideanSignedFluxData kernel = record
  { Euclidean.weightedFluxR3 = physicalWeightedFlux kernel
  ; Euclidean.commonResolventFluxR3 = physicalCommonResolventFlux kernel
  ; Euclidean.centeredResolventCorrectionR3 =
      physicalCenteredResolventCorrection kernel
  ; Euclidean.pointwiseCenteredResolventSplitR3 =
      pointwiseResolventGramSplit kernel
  }

physicalFluxFieldsAreDerivedNotIndependent : Bool
physicalFluxFieldsAreDerivedNotIndependent = true

continuousTriadUsesXiEtaXiMinusEta : Bool
continuousTriadUsesXiEtaXiMinusEta = true

wholeSpaceFourierTrajectoryTypeFixed : Bool
wholeSpaceFourierTrajectoryTypeFixed = true

concreteFourierTransformImplementationClosedHere : Bool
concreteFourierTransformImplementationClosedHere = false

bishopLerayFormulaKernelClosedHere : Bool
bishopLerayFormulaKernelClosedHere = false

lowFrequencyAnalyticPaymentClosedHere : Bool
lowFrequencyAnalyticPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

physicalFluxFieldsAreDerivedNotIndependentIsTrue :
  physicalFluxFieldsAreDerivedNotIndependent ≡ true
physicalFluxFieldsAreDerivedNotIndependentIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
