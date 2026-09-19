module DASHI.Physics.Closure.NSTriadKNPhysicalCenteredResolventKernelEnvelopeExact where

------------------------------------------------------------------------
-- PHYSICAL SPECIALIZATION OF THE TWO-ENVELOPE CENTERED RESOLVENT KERNEL
--
-- On a nonzero literal periodic output fibre with positive viscosity,
--
--   a = nu |k|^2 > 0,
--   s_ab = (nu/2)(C_a + C_b) >= 0,
--   Lambda_ab = a + s_ab.
--
-- Therefore the exact coefficient of the centered R290 correction,
--
--   w_ab w_k s_ab,
--
-- is the generic kernel s/[a(a+s)].  This file constructs all positivity from
-- the physical carrier and imports the two exact analytic envelopes:
--
--   w_ab w_k s_ab <= w_k^2 s_ab,
--   w_ab w_k s_ab <= w_k.
--
-- The first is the Taylor/second-moment branch.  The second is the saturation
-- branch.  No fibre cardinality, absolute-value sum, cutoff factor, or Clay
-- promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; nonNegative; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalOutputRateNormalFormExact as OutputRate
import DASHI.Physics.Closure.NSTriadKNFixedOutputResolventCenteredDefectExact as Defect
import DASHI.Physics.Closure.NSTriadKNFixedOutputResolventGramFluxSplitExact as SplitOwner
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNCenteredResolventKernelEnvelopeExact as Kernel
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalKernelEnvelope
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module D = Defect.PhysicalResolventDefect physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  nu = Field30.viscosity physicalSystem

  halfPositive : 0ℚ < OutputRate.half
  halfPositive =
    let
      instance
        halfPositiveI : Positive OutputRate.half
        halfPositiveI = ℚP.normalize-pos 1 2
    in
    ℚP.positive⁻¹ OutputRate.half

  halfNonnegative : 0ℚ ≤ OutputRate.half
  halfNonnegative = ℚP.<⇒≤ halfPositive

  viscosityNonnegative : 0ℚ ≤ nu
  viscosityNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ nu)

  halfViscosityNonnegative : 0ℚ ≤ OutputRate.halfViscosity nu
  halfViscosityNonnegative =
    let
      instance
        halfNNI : NonNegative OutputRate.half
        halfNNI = nonNegative halfNonnegative
        nuNNI : NonNegative nu
        nuNNI = nonNegative viscosityNonnegative
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg OutputRate.half nu
    in
    ℚP.nonNegative⁻¹ (OutputRate.half * nu)

  centeredSquareNonnegative :
    (p q : Z3.FourierMode) →
    0ℚ ≤ Centered.centeredSquare E p q
  centeredSquareNonnegative
      (Z3.mode px py pz) (Z3.mode qx qy qz) =
    Rational.addNonnegative
      (Rational.addNonnegative
        (Rational.squareNonnegative
          (C3.embedInteger E px - C3.embedInteger E qx))
        (Rational.squareNonnegative
          (C3.embedInteger E py - C3.embedInteger E qy)))
      (Rational.squareNonnegative
        (C3.embedInteger E pz - C3.embedInteger E qz))

  pairCenteredResidualNonnegative :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    0ℚ ≤ D.pairCenteredResidual alpha beta
  pairCenteredResidualNonnegative alpha beta =
    let
      ca = Centered.centeredSquare E (Physical.p alpha) (Physical.q alpha)
      cb = Centered.centeredSquare E (Physical.p beta) (Physical.q beta)
      centeredNN =
        Rational.addNonnegative
          (centeredSquareNonnegative (Physical.p alpha) (Physical.q alpha))
          (centeredSquareNonnegative (Physical.p beta) (Physical.q beta))
      instance
        halfNuNNI : NonNegative (OutputRate.halfViscosity nu)
        halfNuNNI = nonNegative halfViscosityNonnegative
        centeredNNI : NonNegative (ca + cb)
        centeredNNI = nonNegative centeredNN
        productNNI =
          ℚP.nonNeg*nonNeg⇒nonNeg
            (OutputRate.halfViscosity nu) (ca + cb)
    in
    ℚP.nonNegative⁻¹
      (OutputRate.halfViscosity nu * (ca + cb))

  outputPairHeatRatePositive : Positive (D.outputPairHeatRate output)
  outputPairHeatRatePositive =
    let
      normPositive : Positive (C3.normSquared I output)
      normPositive = R400.normSquaredPositive E I output outputNonzero

      instance
        nuPositiveI : Positive nu
        nuPositiveI = viscosityPositive
        normPositiveI : Positive (C3.normSquared I output)
        normPositiveI = normPositive
        productPositiveI =
          ℚP.pos*pos⇒pos nu (C3.normSquared I output)

      exact :
        D.outputPairHeatRate output
        ≡ nu * C3.normSquared I output
      exact = solve (nu ∷ C3.normSquared I output ∷ [])
    in
    subst Positive (sym exact) productPositiveI

  pairRatePositive :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    Positive (D.physicalPairRate alpha beta)
  pairRatePositive alpha beta alphaOutput betaOutput =
    Rate.pairRatePositiveFromCellRates alpha beta
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero alpha alphaOutput)
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero beta betaOutput)

  correctionCoefficient :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    ℚ
  correctionCoefficient alpha beta alphaOutput betaOutput =
    let
      positive = pairRatePositive alpha beta alphaOutput betaOutput
    in
    D.pairResolvent alpha beta positive
      * D.outputResolvent output
      * D.pairCenteredResidual alpha beta

  physicalKernel :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    ℚ
  physicalKernel alpha beta =
    Kernel.centeredResolventKernel
      (D.outputPairHeatRate output)
      (D.pairCenteredResidual alpha beta)
      (ℚP.positive⁻¹ (D.outputPairHeatRate output))
      (Kernel.positivePlusNonnegative
        (ℚP.positive⁻¹ (D.outputPairHeatRate output))
        (pairCenteredResidualNonnegative alpha beta))
    where
    instance
      outputPositiveI : Positive (D.outputPairHeatRate output)
      outputPositiveI = outputPairHeatRatePositive

  correctionCoefficientIsPhysicalKernel :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (betaOutput : Physical.k beta ≡ output) →
    correctionCoefficient alpha beta alphaOutput betaOutput
    ≡ physicalKernel alpha beta
  correctionCoefficientIsPhysicalKernel
      alpha beta alphaOutput betaOutput =
    let
      a = D.outputPairHeatRate output
      s = D.pairCenteredResidual alpha beta
      pairRate = D.physicalPairRate alpha beta
      pairPositive = pairRatePositive alpha beta alphaOutput betaOutput
      aStrict = ℚP.positive⁻¹ a
      sNN = pairCenteredResidualNonnegative alpha beta
      sumStrict = Kernel.positivePlusNonnegative aStrict sNN

      split : pairRate ≡ a + s
      split =
        D.physicalPairRateSplitsAtOutput
          output alpha beta alphaOutput betaOutput

      pairReciprocal :
        D.pairResolvent alpha beta pairPositive
        ≡ Quotient.positiveReciprocal pairRate (ℚP.positive⁻¹ pairRate)
      pairReciprocal =
        trans
          (D.pairResolventMeaning alpha beta pairPositive)
          (R449.safeReciprocalIsPositiveReciprocal
            pairRate (ℚP.positive⁻¹ pairRate))

      outputReciprocal :
        D.outputResolvent output
        ≡ Quotient.positiveReciprocal a aStrict
      outputReciprocal =
        R449.safeReciprocalIsPositiveReciprocal a aStrict
    in
    rewrite pairReciprocal | outputReciprocal | split =
      solve
        ( s
        ∷ Quotient.positiveReciprocal (a + s) sumStrict
        ∷ Quotient.positiveReciprocal a aStrict
        ∷ [])

  correctionCoefficientBelowSmallDefect :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (betaOutput : Physical.k beta ≡ output) →
    correctionCoefficient alpha beta alphaOutput betaOutput
    ≤
    Kernel.smallDefectEnvelope
      (D.outputPairHeatRate output)
      (D.pairCenteredResidual alpha beta)
      (ℚP.positive⁻¹ (D.outputPairHeatRate output))
  correctionCoefficientBelowSmallDefect
      alpha beta alphaOutput betaOutput =
    subst
      (λ selected →
        selected
        ≤ Kernel.smallDefectEnvelope
            (D.outputPairHeatRate output)
            (D.pairCenteredResidual alpha beta)
            (ℚP.positive⁻¹ (D.outputPairHeatRate output)))
      (sym (correctionCoefficientIsPhysicalKernel
        alpha beta alphaOutput betaOutput))
      (Kernel.kernelBelowSmallDefectEnvelope
        (D.outputPairHeatRate output)
        (D.pairCenteredResidual alpha beta)
        (ℚP.positive⁻¹ (D.outputPairHeatRate output))
        (pairCenteredResidualNonnegative alpha beta))

  correctionCoefficientBelowSaturation :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (betaOutput : Physical.k beta ≡ output) →
    correctionCoefficient alpha beta alphaOutput betaOutput
    ≤
    Kernel.saturationEnvelope
      (D.outputPairHeatRate output)
      (ℚP.positive⁻¹ (D.outputPairHeatRate output))
  correctionCoefficientBelowSaturation
      alpha beta alphaOutput betaOutput =
    subst
      (λ selected →
        selected
        ≤ Kernel.saturationEnvelope
            (D.outputPairHeatRate output)
            (ℚP.positive⁻¹ (D.outputPairHeatRate output)))
      (sym (correctionCoefficientIsPhysicalKernel
        alpha beta alphaOutput betaOutput))
      (Kernel.kernelBelowSaturationEnvelope
        (D.outputPairHeatRate output)
        (D.pairCenteredResidual alpha beta)
        (ℚP.positive⁻¹ (D.outputPairHeatRate output))
        (pairCenteredResidualNonnegative alpha beta))

physicalCenteredResidualNonnegativeClosed : Bool
physicalCenteredResidualNonnegativeClosed = true

physicalCenteredResolventKernelIdentificationClosed : Bool
physicalCenteredResolventKernelIdentificationClosed = true

physicalSmallDefectEnvelopeClosed : Bool
physicalSmallDefectEnvelopeClosed = true

physicalSaturationEnvelopeClosed : Bool
physicalSaturationEnvelopeClosed = true

absoluteGramSummationClosedHere : Bool
absoluteGramSummationClosedHere = false

cutoffUniformSignedCorrectionPaymentClosedHere : Bool
cutoffUniformSignedCorrectionPaymentClosedHere = false

clayPromotion : Bool
clayPromotion = false

physicalCenteredResolventKernelIdentificationClosedIsTrue :
  physicalCenteredResolventKernelIdentificationClosed ≡ true
physicalCenteredResolventKernelIdentificationClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
