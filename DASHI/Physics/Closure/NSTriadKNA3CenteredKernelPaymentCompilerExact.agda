{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CenteredKernelPaymentCompilerExact where

------------------------------------------------------------------------
-- A3 / CENTERED KERNEL PAYMENT -> EXISTING SIGNED RATE PAYMENT
--
-- The exact normal form from NSTriadKNA3CenteredKernelNormalFormExact gives
--
--   4 * S_A3
--     = n * (-W(M,K_r)) + R * W(M,K).
--
-- Therefore the genuinely analytic payment can be stated directly on the
-- centered quadratic-kernel scalar:
--
--   n * (-W(M,K_r)) + R * W(M,K) <= 4 * residualBudget.
--
-- Since 4>0, this compiles exactly to the existing
-- FixedOutputSignedRateVectorPayment.
--
-- Helical laws/transversality are explicit inputs because the standalone A3
-- record stores only (system,S,output); the live trajectory supplies them via
-- its existing At.P certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; _<_; Positive)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as A3
import DASHI.Physics.Closure.NSTriadKNRateWeightedMixedHelicityKernelCollapseExact as RateKernel
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel

F : C3.RealField _
F = Rational.rationalRealField

four : ℚ
four = Kernel.four

two : ℚ
two = 1ℚ + 1ℚ

twoPositive : 0ℚ < two
twoPositive =
  ℚP.+-mono-<-<
    (ℚP.positive⁻¹ 1ℚ)
    (ℚP.positive⁻¹ 1ℚ)

fourPositive : 0ℚ < four
fourPositive =
  ℚP.+-mono-<-< twoPositive twoPositive

fourPositiveInstance : Positive four
fourPositiveInstance = ℚP.positive fourPositive

------------------------------------------------------------------------
-- Physical kernel scalar on exactly the A3 finite system.
------------------------------------------------------------------------

record FixedOutputCenteredKernelPayment
    (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (PhysicalField.physicalEmbedding system)
      (PhysicalField.physicalInverseSquare system)
      S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (PhysicalField.physicalEmbedding system)
      (PhysicalField.physicalInverseSquare system)
      S L H
      (Audit.velocity (PhysicalField.finiteSystem system)))
    (output : Z3.FourierMode) : Set where
  field
    residualBudget : ℚ

    centeredKernelPayment :
      let
        items = A3.physicalOutputItems system output
        mixed = A3.physicalMixedFold system S output
        rate = Rate.physicalCellRate system
        rho = Rate.physicalModalRate system
        n = Pair.natAsRational (length items)
        rateTotal = Pair.rateSum rate items

        weightedKernel =
          DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.foldVector
            (RateKernel.weightedIQuadraticKernel
              (RateKernel.physicalRateWeight rho)
              S
              (Audit.velocity (PhysicalField.finiteSystem system)))
            items

        kernel =
          DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.foldVector
            (R225.iQuadraticKernelCell
              S
              (Audit.velocity (PhysicalField.finiteSystem system)))
            items
      in
      n * (0ℚ - Work.coherentWork mixed weightedKernel)
        + rateTotal * Work.coherentWork mixed kernel
      ≤ four * residualBudget

open FixedOutputCenteredKernelPayment public

------------------------------------------------------------------------
-- Exact compiler.
------------------------------------------------------------------------

centeredKernelPaymentBuildsSignedRatePayment :
  ∀ {system S L H P output} →
  FixedOutputCenteredKernelPayment system S L H P output →
  A3.FixedOutputSignedRateVectorPayment system S output
centeredKernelPaymentBuildsSignedRatePayment
    {system} {S} {L} {H} {P} {output} payment =
  record
    { A3.FixedOutputSignedRateVectorPayment.residualBudget =
        residualBudget payment
    ; A3.FixedOutputSignedRateVectorPayment.signedRateVectorPayment =
        let
          items = A3.physicalOutputItems system output
          value = A3.physicalMixedValue system S
          mixed = A3.physicalMixedFold system S output
          rate = Rate.physicalCellRate system
          rho = Rate.physicalModalRate system
          signedA3 =
            0ℚ -
              DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact.pairDifferenceVectorWorkSum
                rate mixed value items
          budget = residualBudget payment

          normalForm :
            four * signedA3
            ≡
            let
              n = Pair.natAsRational (length items)
              rateTotal = Pair.rateSum rate items
              weightedKernel =
                DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.foldVector
                  (RateKernel.weightedIQuadraticKernel
                    (RateKernel.physicalRateWeight rho)
                    S
                    (Audit.velocity (PhysicalField.finiteSystem system)))
                  items
              kernel =
                DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.foldVector
                  (R225.iQuadraticKernelCell
                    S
                    (Audit.velocity (PhysicalField.finiteSystem system)))
                  items
            in
            n * (0ℚ - Work.coherentWork mixed weightedKernel)
              + rateTotal * Work.coherentWork mixed kernel
          normalForm =
            Kernel.fixedOutputSignedA3KernelCenteredNormalForm
              P rho
              (Audit.cutoff (PhysicalField.finiteSystem system))
              output

          scaledPayment :
            four * signedA3 ≤ four * budget
          scaledPayment =
            subst
              (λ left → left ≤ four * budget)
              (sym normalForm)
              (centeredKernelPayment payment)

          instance
            fourPos : Positive four
            fourPos = fourPositiveInstance
        in
        ℚP.*-cancelˡ-≤-pos four scaledPayment
    }

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

kernelCenteredPaymentCompilerClosed : Bool
kernelCenteredPaymentCompilerClosed = true

kernelCenteredPaymentIsPreferredA3ResearchInequality : Bool
kernelCenteredPaymentIsPreferredA3ResearchInequality = true

pairEnumerationRequiredInA3ResearchStatement : Bool
pairEnumerationRequiredInA3ResearchStatement = false

pointwiseR205RequiredInKernelPayment : Bool
pointwiseR205RequiredInKernelPayment = false

pointwiseLowerSeparationRequiredInKernelPayment : Bool
pointwiseLowerSeparationRequiredInKernelPayment = false

kernelCenteredPaymentCompilerClosedIsTrue :
  kernelCenteredPaymentCompilerClosed ≡ true
kernelCenteredPaymentCompilerClosedIsTrue = refl

kernelCenteredPaymentIsPreferredA3ResearchInequalityIsTrue :
  kernelCenteredPaymentIsPreferredA3ResearchInequality ≡ true
kernelCenteredPaymentIsPreferredA3ResearchInequalityIsTrue = refl

pairEnumerationRequiredInA3ResearchStatementIsFalse :
  pairEnumerationRequiredInA3ResearchStatement ≡ false
pairEnumerationRequiredInA3ResearchStatementIsFalse = refl

pointwiseR205RequiredInKernelPaymentIsFalse :
  pointwiseR205RequiredInKernelPayment ≡ false
pointwiseR205RequiredInKernelPaymentIsFalse = refl

pointwiseLowerSeparationRequiredInKernelPaymentIsFalse :
  pointwiseLowerSeparationRequiredInKernelPayment ≡ false
pointwiseLowerSeparationRequiredInKernelPaymentIsFalse = refl
