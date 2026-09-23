{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CauchyFluxTangentMismatchRound598Exact where

------------------------------------------------------------------------
-- ROUND598 / EXACT A3 <-> CAUCHY FLUX-TANGENT MISMATCH NORMAL FORM
--
-- R596 proves on the literal nonzero fixed-output fibre
--
--   4 * ForcingFull = FullGram + FluxTangentFull.
--
-- R597 plus the R225 complete-fibre collapse identifies
--
--   FullGram = 4 * W(M,K),
--
-- where K is the SAME unweighted quadratic-kernel fold appearing in the A3
-- centered-kernel normal form.
--
-- A3 already proves
--
--   4 * A3 = n * (-W(M,K_r)) + R * W(M,K).
--
-- Therefore exact rational algebra gives the division-free mismatch identity
--
--   R * (4 * ForcingFull) - 4 * (4 * A3)
--     = R * FluxTangentFull + 4*n*W(M,K_r).
--
-- No estimate is introduced.  This isolates the final representation
-- coordinate sharply: the Cauchy weighted Gram-tangent full square must be
-- related to the rate-weighted A3 kernel work.  The coherent self-work part is
-- already cancelled exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate
import DASHI.Physics.Closure.NSTriadKNRateWeightedMixedHelicityKernelCollapseExact as RateKernel
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNR567CauchyGramFluxNormalFormRound596Exact as R596
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as A3Kernel

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
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module C = R596.FixedOutput
    physicalSystem S viscosityPositive output outputNonzero

  cutoff : Nat
  cutoff = Audit.cutoff (Field30.finiteSystem physicalSystem)

  velocity = Audit.velocityAt (Field30.finiteSystem physicalSystem)

  fibre = Output.physicalOutputFiber cutoff output

  mixed : C3.Complex3 F
  mixed =
    R224.foldVector (D1a.mixedProductCell S velocity) fibre

  kernel : C3.Complex3 F
  kernel =
    R224.foldVector (R225.iQuadraticKernelCell S velocity) fibre

  rho : Z3.FourierMode → ℚ
  rho = Rate.physicalModalRate physicalSystem

  weightedKernel : C3.Complex3 F
  weightedKernel =
    R224.foldVector
      (RateKernel.weightedIQuadraticKernel
        (RateKernel.physicalRateWeight rho) S velocity)
      fibre

  rate = Pair.cellRate rho

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

  forcingFull : ℚ
  forcingFull = R543.fullSquareSum C.C.T.forcingPair fibre

  fluxTangentFull : ℚ
  fluxTangentFull =
    R543.fullSquareSum C.weightedFluxTangentPair fibre

  coherentWorkSymmetric :
    (left right : C3.Complex3 F) →
    Work.coherentWork left right ≡ Work.coherentWork right left
  coherentWorkSymmetric left right =
    cong (Work.two *_) (R287.realHermitianCrossSymmetric left right)

  four567IsA3Four : R567.four567 ≡ A3Kernel.four
  four567IsA3Four = solve []

  doubleFoldIsFourMixed :
    R224.foldVector C.doubleCell fibre ≡ R225.fourCopies mixed
  doubleFoldIsFourMixed =
    R225.fixedOutputDoubleMixedSumIsFourPlusMinusSum
      S velocity cutoff output

  kernelIsFourMixed :
    kernel ≡ R225.fourCopies mixed
  kernelIsFourMixed =
    R225.fixedOutputQuadraticKernelIsFourMixedHelicityConvolution
      P cutoff output

  fullGramIsFourSelfKernelWork :
    R543.fullSquareSum C.gramPair fibre
    ≡ A3Kernel.four * selfKernelWork
  fullGramIsFourSelfKernelWork =
    let
      fourMixed = R225.fourCopies mixed

      fullToFold =
        C.fullGramIsCoherentSelfWork

      foldToFour :
        Work.coherentWork
          (R224.foldVector C.doubleCell fibre)
          (R224.foldVector C.doubleCell fibre)
        ≡ Work.coherentWork fourMixed fourMixed
      foldToFour =
        cong₂ Work.coherentWork
          doubleFoldIsFourMixed doubleFoldIsFourMixed

      fourRight :
        Work.coherentWork fourMixed fourMixed
        ≡ A3Kernel.four * Work.coherentWork fourMixed mixed
      fourRight =
        A3Kernel.workFourCopies fourMixed mixed

      swap :
        Work.coherentWork fourMixed mixed
        ≡ Work.coherentWork mixed fourMixed
      swap = coherentWorkSymmetric fourMixed mixed

      fourToKernel :
        Work.coherentWork mixed fourMixed
        ≡ selfKernelWork
      fourToKernel =
        cong (Work.coherentWork mixed) (sym kernelIsFourMixed)
    in
    trans fullToFold
      (trans foldToFour
        (trans fourRight
          (trans
            (cong (A3Kernel.four *_) swap)
            (cong (A3Kernel.four *_) fourToKernel))))

  fourForcingFullIsFourSelfKernelPlusFlux :
    A3Kernel.four * forcingFull
    ≡ A3Kernel.four * selfKernelWork + fluxTangentFull
  fourForcingFullIsFourSelfKernelPlusFlux =
    trans
      (cong (_* forcingFull) four567IsA3Four |>sym)
      (trans
        C.fourForcingFullIsGramPlusFlux
        (cong
          (_+ fluxTangentFull)
          fullGramIsFourSelfKernelWork))
    where
    infix 0 _|>sym
    _|>sym : ∀ {a b : ℚ} → a ≡ b → b ≡ a
    _|>sym = sym

  a3CenteredKernelNormalForm :
    A3Kernel.four * signedA3
    ≡
    n * (0ℚ - weightedKernelWork)
      + rateTotal * selfKernelWork
  a3CenteredKernelNormalForm =
    A3Kernel.fixedOutputSignedA3KernelCenteredNormalForm
      P rho cutoff output

  cauchyA3MismatchNormalForm :
    rateTotal * (A3Kernel.four * forcingFull)
      - A3Kernel.four * (A3Kernel.four * signedA3)
    ≡
    rateTotal * fluxTangentFull
      + A3Kernel.four * n * weightedKernelWork
  cauchyA3MismatchNormalForm
    rewrite fourForcingFullIsFourSelfKernelPlusFlux
          | a3CenteredKernelNormalForm =
    solve
      ( rateTotal
      ∷ selfKernelWork
      ∷ fluxTangentFull
      ∷ n
      ∷ weightedKernelWork
      ∷ A3Kernel.four
      ∷ [])

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round598CauchyA3MismatchNormalFormClosed : Bool
round598CauchyA3MismatchNormalFormClosed = true

round598A3SelfWorkCoordinateCancelledExactly : Bool
round598A3SelfWorkCoordinateCancelledExactly = true

round598OnlyResidualIsFluxTangentPlusRateWeightedKernel : Bool
round598OnlyResidualIsFluxTangentPlusRateWeightedKernel = true

round598IntroducesEstimate : Bool
round598IntroducesEstimate = false

round598FluxTangentToRateWeightedKernelClosed : Bool
round598FluxTangentToRateWeightedKernelClosed = false

round598CauchyA3MismatchNormalFormClosedIsTrue :
  round598CauchyA3MismatchNormalFormClosed ≡ true
round598CauchyA3MismatchNormalFormClosedIsTrue = refl

round598A3SelfWorkCoordinateCancelledExactlyIsTrue :
  round598A3SelfWorkCoordinateCancelledExactly ≡ true
round598A3SelfWorkCoordinateCancelledExactlyIsTrue = refl

round598OnlyResidualIsFluxTangentPlusRateWeightedKernelIsTrue :
  round598OnlyResidualIsFluxTangentPlusRateWeightedKernel ≡ true
round598OnlyResidualIsFluxTangentPlusRateWeightedKernelIsTrue = refl

round598IntroducesEstimateIsFalse :
  round598IntroducesEstimate ≡ false
round598IntroducesEstimateIsFalse = refl

round598FluxTangentToRateWeightedKernelClosedIsFalse :
  round598FluxTangentToRateWeightedKernelClosed ≡ false
round598FluxTangentToRateWeightedKernelClosedIsFalse = refl
