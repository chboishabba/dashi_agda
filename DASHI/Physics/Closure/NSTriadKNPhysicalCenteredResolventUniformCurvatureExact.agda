module DASHI.Physics.Closure.NSTriadKNPhysicalCenteredResolventUniformCurvatureExact where

------------------------------------------------------------------------
-- PERIODIC PHYSICAL UNIFORM CURVATURE: 2/(nu |k|^2)^3 <= 2/nu^3
--
-- The generic opposite-shift resolvent estimate has transport curvature
--
--   2 / a^3,     a = nu |k|^2.
--
-- On the canonical periodic Fourier normalization, every nonzero output obeys
--
--   1 <= |k|^2,
--
-- hence
--
--   nu <= a
--
-- for positive viscosity.  Reciprocal antitonicity therefore gives the
-- cutoff/output-independent curvature ceiling
--
--   2 / a^3 <= 2 / nu^3.
--
-- This closes the MULTIPLIER-CURVATURE uniformity issue for every nonzero
-- periodic output.  It does not pay the state derivative envelopes G2/G1, the
-- signed Gram aggregation, or the zero-mode semantic branch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputResolventCenteredDefectExact as Defect
import DASHI.Physics.Closure.NSTriadKNPhysicalCenteredResolventKernelEnvelopeExact as PhysicalKernel
import DASHI.Physics.Closure.NSTriadKNCenteredResolventOppositeShiftSecondOrderExact as Resolvent
import DASHI.Physics.Closure.NSTriadKNCenteredResolventSecondOrderEnvelopeExact as Envelope
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

F : C3.RealField _
F = Rational.rationalRealField

module UniformCurvature
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem) where

  nu : ℚ
  nu = Field30.viscosity physicalSystem

  nuPositive : 0ℚ < nu
  nuPositive = ℚP.positive⁻¹ nu

  nuNonnegative : 0ℚ ≤ nu
  nuNonnegative = ℚP.<⇒≤ nuPositive

  uniformTransportCurvature : ℚ
  uniformTransportCurvature =
    Envelope.two
      * Resolvent.inv nu * Resolvent.inv nu * Resolvent.inv nu

  module AtOutput
      (output : Z3.FourierMode)
      (outputNonzero : Z3.NonZeroMode output) where

    module D = Defect.PhysicalResolventDefect physicalSystem S
    module P =
      PhysicalKernel.PhysicalKernelEnvelope
        physicalSystem S viscosityPositive output outputNonzero

    a : ℚ
    a = D.outputPairHeatRate output

    aPositive : 0ℚ < a
    aPositive = ℚP.positive⁻¹ P.outputPairHeatRatePositive

    outputSquareAtLeastOne :
      1ℚ
      ≤ C3.normSquared
          (Field30.physicalInverseSquare physicalSystem) output
    outputSquareAtLeastOne =
      R450.nonzeroModeSquareAtLeastOne unitGap output outputNonzero

    outputPairHeatRateMeaning :
      a
      ≡ nu
        * C3.normSquared
            (Field30.physicalInverseSquare physicalSystem) output
    outputPairHeatRateMeaning =
      solve
        ( nu
        ∷ C3.normSquared
            (Field30.physicalInverseSquare physicalSystem) output
        ∷ [])

    viscosityBelowOutputPairHeatRate :
      nu ≤ a
    viscosityBelowOutputPairHeatRate =
      let
        square =
          C3.normSquared
            (Field30.physicalInverseSquare physicalSystem) output

        instance
          nuNNI : NonNegative nu
          nuNNI = nonNegative nuNonnegative

        scaled : nu * 1ℚ ≤ nu * square
        scaled =
          ℚP.*-monoˡ-≤-nonNeg nu outputSquareAtLeastOne
      in
      subst
        (nu ≤_)
        (sym outputPairHeatRateMeaning)
        (subst
          (nu ≤_)
          (ℚP.*-identityʳ nu)
          scaled)

    outputInverseBelowViscosityInverse :
      Resolvent.inv a ≤ Resolvent.inv nu
    outputInverseBelowViscosityInverse =
      Envelope.safeInvAntitone
        nu a nuPositive aPositive viscosityBelowOutputPairHeatRate

    outputTripleInverseBelowViscosityTriple :
      Resolvent.inv a * Resolvent.inv a * Resolvent.inv a
      ≤
      Resolvent.inv nu * Resolvent.inv nu * Resolvent.inv nu
    outputTripleInverseBelowViscosityTriple =
      Envelope.tripleInverseBound
        nu a a a
        nuPositive aPositive aPositive aPositive
        viscosityBelowOutputPairHeatRate
        viscosityBelowOutputPairHeatRate
        viscosityBelowOutputPairHeatRate

    outputTransportCurvature : ℚ
    outputTransportCurvature =
      Envelope.resolventTransportCurvature a

    outputTransportCurvatureBelowUniform :
      outputTransportCurvature ≤ uniformTransportCurvature
    outputTransportCurvatureBelowUniform =
      let
        twoNN = Envelope.twoNonnegative

        tripleBound =
          outputTripleInverseBelowViscosityTriple

        instance
          twoNNI : NonNegative Envelope.two
          twoNNI = nonNegative twoNN

        scaled :
          Envelope.two
            * (Resolvent.inv a * Resolvent.inv a * Resolvent.inv a)
          ≤
          Envelope.two
            * (Resolvent.inv nu * Resolvent.inv nu * Resolvent.inv nu)
        scaled =
          ℚP.*-monoˡ-≤-nonNeg Envelope.two tripleBound
      in
      subst
        (outputTransportCurvature ≤_)
        (solve
          (Envelope.two ∷ Resolvent.inv nu ∷ []))
        (subst
          (λ lhs →
            lhs
            ≤ Envelope.two
                * (Resolvent.inv nu * Resolvent.inv nu * Resolvent.inv nu))
          (solve
            (Envelope.two ∷ Resolvent.inv a ∷ []))
          scaled)

    uniformOppositeShiftMagnitudeEnvelope :
      (s h : ℚ) →
      (centerResidualNN : 0ℚ ≤ s) →
      (plusResidualNN : 0ℚ ≤ s + h) →
      (minusResidualNN : 0ℚ ≤ s - h) →
      ∣ Resolvent.centeredSecondDifference a s h ∣
      ≤
      h * h * uniformTransportCurvature
    uniformOppositeShiftMagnitudeEnvelope
        s h centerResidualNN plusResidualNN minusResidualNN =
      let
        local =
          Envelope.centeredResolventSecondOrderMagnitudeEnvelope
            a s h aPositive
            centerResidualNN plusResidualNN minusResidualNN

        hSquareNN : 0ℚ ≤ h * h
        hSquareNN = Rational.squareNonnegative h

        localCurvatureBound =
          outputTransportCurvatureBelowUniform

        scaled :
          h * h * outputTransportCurvature
          ≤ h * h * uniformTransportCurvature
        scaled =
          let
            instance
              hSquareNNI : NonNegative (h * h)
              hSquareNNI = nonNegative hSquareNN
          in
          ℚP.*-monoˡ-≤-nonNeg (h * h) localCurvatureBound

        localTargetMeaning :
          Envelope.two * h * h
            * Resolvent.inv a * Resolvent.inv a * Resolvent.inv a
          ≡ h * h * outputTransportCurvature
        localTargetMeaning =
          solve
            (Envelope.two ∷ h ∷ Resolvent.inv a ∷ [])
      in
      ℚP.≤-trans
        local
        (subst
          (_≤ h * h * uniformTransportCurvature)
          (sym localTargetMeaning)
          scaled)

periodicMultiplierCurvatureUniformInOutput : Bool
periodicMultiplierCurvatureUniformInOutput = true

periodicMultiplierCurvatureUniformInCutoff : Bool
periodicMultiplierCurvatureUniformInCutoff = true

uniformCurvatureDependsOnlyOnViscosity : Bool
uniformCurvatureDependsOnlyOnViscosity = true

stateDerivativeG2G1PaidHere : Bool
stateDerivativeG2G1PaidHere = false

signedGramAggregationPaidHere : Bool
signedGramAggregationPaidHere = false

zeroOutputBranchPaidHere : Bool
zeroOutputBranchPaidHere = false

clayPromotion : Bool
clayPromotion = false

periodicMultiplierCurvatureUniformInCutoffIsTrue :
  periodicMultiplierCurvatureUniformInCutoff ≡ true
periodicMultiplierCurvatureUniformInCutoffIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
