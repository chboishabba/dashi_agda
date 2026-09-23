{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CenteredFullGramNormalFormRound599Exact where

------------------------------------------------------------------------
-- ROUND599 / A3 CENTERED KERNEL -> COMPLETE DOUBLE-MIXED GRAM NORMAL FORM
--
-- R598/R596 put the weighted R406 side on the complete double-mixed Gram
-- carrier.  This module moves A3 onto that SAME carrier.
--
-- Let
--
--   D     = sum_alpha D_alpha              (double-mixed fold)
--   D_r   = sum_alpha r_alpha D_alpha      (rate-weighted double-mixed fold)
--   G     = W(D,D)
--   G_r   = W(D,D_r)
--   n     = fibre cardinality
--   R     = sum_alpha r_alpha.
--
-- The R225 / rate-weighted R225 collapses give
--
--   D   = 4 M,
--   D_r = K_r,
--   K   = D.
--
-- Therefore the existing centered-kernel A3 normal form
--
--   4 C_A3 = -n W(M,K_r) + R W(M,K)
--
-- becomes, division-free,
--
--   16 C_A3 = R G - n G_r.
--
-- No estimate, positivity, Cauchy bound, or pointwise separation is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate
import DASHI.Physics.Closure.NSTriadKNRateWeightedMixedHelicityKernelCollapseExact as RateKernel
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNA3CauchyFluxTangentMismatchRound598Exact as R598

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (output : Z3.FourierMode) where

  cutoff : Nat
  cutoff = Audit.cutoff (Field30.finiteSystem physicalSystem)

  velocity = Audit.velocityAt (Field30.finiteSystem physicalSystem)

  fibre = Output.physicalOutputFiber cutoff output

  mixed : C3.Complex3 F
  mixed =
    R224.foldVector (D1a.mixedProductCell S velocity) fibre

  doubleFold : C3.Complex3 F
  doubleFold =
    R224.foldVector (R225.doubleMixedCell S velocity) fibre

  kernel : C3.Complex3 F
  kernel =
    R224.foldVector (R225.iQuadraticKernelCell S velocity) fibre

  rho : Z3.FourierMode → ℚ
  rho = Rate.physicalModalRate physicalSystem

  rate = Pair.cellRate rho

  weightedKernel : C3.Complex3 F
  weightedKernel =
    R224.foldVector
      (RateKernel.weightedIQuadraticKernel
        (RateKernel.physicalRateWeight rho) S velocity)
      fibre

  n : ℚ
  n = Pair.natAsRational (length fibre)

  rateTotal : ℚ
  rateTotal = Pair.rateSum rate fibre

  signedA3 : ℚ
  signedA3 =
    0ℚ - Vector.pairDifferenceVectorWorkSum
      rate mixed (D1a.mixedProductCell S velocity) fibre

  selfKernelWork : ℚ
  selfKernelWork = Work.coherentWork mixed kernel

  weightedKernelWork : ℚ
  weightedKernelWork = Work.coherentWork mixed weightedKernel

  fullGram : ℚ
  fullGram = Work.coherentWork doubleFold doubleFold

  rightRateWeightedFullGram : ℚ
  rightRateWeightedFullGram =
    Work.coherentWork doubleFold weightedKernel

  doubleFoldIsFourMixed :
    doubleFold ≡ R225.fourCopies mixed
  doubleFoldIsFourMixed =
    R225.fixedOutputDoubleMixedSumIsFourPlusMinusSum
      S velocity cutoff output

  kernelIsFourMixed :
    kernel ≡ R225.fourCopies mixed
  kernelIsFourMixed =
    R225.fixedOutputQuadraticKernelIsFourMixedHelicityConvolution
      P cutoff output

  fullGramIsFourSelfKernelWork :
    fullGram ≡ Kernel.four * selfKernelWork
  fullGramIsFourSelfKernelWork =
    let
      fourMixed = R225.fourCopies mixed

      toFour :
        fullGram ≡ Work.coherentWork fourMixed fourMixed
      toFour =
        cong (λ x → Work.coherentWork x x) doubleFoldIsFourMixed

      fourRight :
        Work.coherentWork fourMixed fourMixed
        ≡ Kernel.four * Work.coherentWork fourMixed mixed
      fourRight =
        Kernel.workFourCopies fourMixed mixed

      symmetric :
        Work.coherentWork fourMixed mixed
        ≡ Work.coherentWork mixed fourMixed
      symmetric =
        R598.FixedOutput.coherentWorkSymmetric
          physicalSystem S L H P
          (Data.Rational.Base.positive 1ℚ)
          output
          (record {})
          fourMixed mixed
    in
    trans toFour
      (trans fourRight
        (trans
          (cong (Kernel.four *_) symmetric)
          (cong
            (Kernel.four *_)
            (cong (Work.coherentWork mixed) (sym kernelIsFourMixed)))))

  rightRateWeightedFullGramIsFourWeightedKernelWork :
    rightRateWeightedFullGram
    ≡ Kernel.four * weightedKernelWork
  rightRateWeightedFullGramIsFourWeightedKernelWork =
    trans
      (cong
        (λ left → Work.coherentWork left weightedKernel)
        doubleFoldIsFourMixed)
      (let
        fourMixed = R225.fourCopies mixed
        first =
          Kernel.workFourCopies weightedKernel mixed
        symmetry :
          Work.coherentWork fourMixed weightedKernel
          ≡ Work.coherentWork weightedKernel fourMixed
        symmetry =
          cong (Work.two *_)
            (DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact.realHermitianCrossSymmetric
              fourMixed weightedKernel)
        back :
          Work.coherentWork weightedKernel mixed
          ≡ Work.coherentWork mixed weightedKernel
        back =
          cong (Work.two *_)
            (DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact.realHermitianCrossSymmetric
              weightedKernel mixed)
      in
      trans symmetry
        (trans first (cong (Kernel.four *_) back)))

  centeredFullGramNormalForm :
    (Kernel.four * Kernel.four) * signedA3
    ≡ rateTotal * fullGram - n * rightRateWeightedFullGram
  centeredFullGramNormalForm
    rewrite Kernel.fixedOutputSignedA3KernelCenteredNormalForm
      P rho cutoff output
          | fullGramIsFourSelfKernelWork
          | rightRateWeightedFullGramIsFourWeightedKernelWork =
    solve
      ( n ∷ rateTotal
      ∷ selfKernelWork
      ∷ weightedKernelWork
      ∷ Kernel.four
      ∷ [])

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round599A3CenteredFullGramNormalFormClosed : Bool
round599A3CenteredFullGramNormalFormClosed = true

round599A3AndR596NowShareCompleteDoubleMixedGramCarrier : Bool
round599A3AndR596NowShareCompleteDoubleMixedGramCarrier = true

round599IntroducesEstimate : Bool
round599IntroducesEstimate = false

round599RemainingCoordinateIsDynamicCauchyFluxTangent : Bool
round599RemainingCoordinateIsDynamicCauchyFluxTangent = true

round599A3CenteredFullGramNormalFormClosedIsTrue :
  round599A3CenteredFullGramNormalFormClosed ≡ true
round599A3CenteredFullGramNormalFormClosedIsTrue = refl

round599A3AndR596NowShareCompleteDoubleMixedGramCarrierIsTrue :
  round599A3AndR596NowShareCompleteDoubleMixedGramCarrier ≡ true
round599A3AndR596NowShareCompleteDoubleMixedGramCarrierIsTrue = refl

round599IntroducesEstimateIsFalse :
  round599IntroducesEstimate ≡ false
round599IntroducesEstimateIsFalse = refl

round599RemainingCoordinateIsDynamicCauchyFluxTangentIsTrue :
  round599RemainingCoordinateIsDynamicCauchyFluxTangent ≡ true
round599RemainingCoordinateIsDynamicCauchyFluxTangentIsTrue = refl
