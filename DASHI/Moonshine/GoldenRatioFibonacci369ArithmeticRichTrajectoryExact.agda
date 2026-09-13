module DASHI.Moonshine.GoldenRatioFibonacci369ArithmeticRichTrajectoryExact where

------------------------------------------------------------------------
-- SAME-OBJECT ARITHMETIC TRAJECTORY FOR THE RICH 3 / 6 / 9 / 27 FIBRE
--
-- The rich-fibre lift retains sign, defect magnitude and prime compression.
-- This owner now pays the first same-object arithmetic seam on an explicit
-- Fibonacci trajectory: 2/1 -> 3/2 -> 5/3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.GoldenRatioFibonacci369SheetVoxelBridgeExact as Fib369
import DASHI.Moonshine.GoldenRatioFibonacci369RichFibreLiftExact as Rich

------------------------------------------------------------------------
-- 1. Missing intermediate negative-defect state 3/2.
------------------------------------------------------------------------

phi3Over2PrimeFibre : Compression.PrimeCompressionFibre
phi3Over2PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 3 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 2 (SSP.negativeMultiplicity 1) ∷ [])
    []

phi3Over2Rich : Rich.RichDefectFibre
phi3Over2Rich =
  Rich.rich-defect-fibre 3 2 Triadic.negativeTrit 1 phi3Over2PrimeFibre

------------------------------------------------------------------------
-- 2. Typed one-step arithmetic transition.
------------------------------------------------------------------------

record RichFibStepReceipt (before after : Rich.RichDefectFibre) : Set where
  constructor rich-fib-step-receipt
  field
    numeratorUpdate :
      Rich.numerator after ≡ Rich.numerator before + Rich.denominator before
    denominatorUpdate :
      Rich.denominator after ≡ Rich.numerator before
    signFlips :
      Rich.defectSign after ≡ Triadic.negateTrit (Rich.defectSign before)
    magnitudePreserved :
      Rich.defectMagnitude after ≡ Rich.defectMagnitude before

step2Over1To3Over2 :
  RichFibStepReceipt Rich.phi2Over1Rich phi3Over2Rich
step2Over1To3Over2 =
  rich-fib-step-receipt refl refl refl refl

step3Over2To5Over3 :
  RichFibStepReceipt phi3Over2Rich Rich.phi5Over3Rich
step3Over2To5Over3 =
  rich-fib-step-receipt refl refl refl refl

------------------------------------------------------------------------
-- 3. Actual 9-sheet and 27-voxel use changing arithmetic payloads.
------------------------------------------------------------------------

actualComparison2To3 : Rich.RichComparisonSheet9
actualComparison2To3 =
  Rich.rich-comparison-sheet9 Rich.phi2Over1Rich phi3Over2Rich

actualComparison3To5 : Rich.RichComparisonSheet9
actualComparison3To5 =
  Rich.rich-comparison-sheet9 phi3Over2Rich Rich.phi5Over3Rich

actualComparison2To3Projects :
  Rich.observe9 actualComparison2To3
  ≡ (Triadic.positiveTrit , Triadic.negativeTrit)
actualComparison2To3Projects = refl

actualComparison3To5Projects :
  Rich.observe9 actualComparison3To5
  ≡ (Triadic.negativeTrit , Triadic.positiveTrit)
actualComparison3To5Projects = refl

actualVoxel2_3_5 : Rich.RichVoxel27
actualVoxel2_3_5 =
  Rich.rich-voxel27 Rich.phi2Over1Rich phi3Over2Rich Rich.phi5Over3Rich

actualVoxel2_3_5ProjectsToFibonacciVoxel :
  Rich.observe27 actualVoxel2_3_5
  ≡ Fib369.fibVoxel Triadic.positiveTrit
actualVoxel2_3_5ProjectsToFibonacciVoxel = refl

actualVoxelRetainsNormOneMagnitude :
  (Rich.defectMagnitude (Rich.step0 actualVoxel2_3_5) ≡ 1) ×
  (Rich.defectMagnitude (Rich.step1 actualVoxel2_3_5) ≡ 1) ×
  (Rich.defectMagnitude (Rich.step2 actualVoxel2_3_5) ≡ 1)
actualVoxelRetainsNormOneMagnitude = refl , refl , refl

------------------------------------------------------------------------
-- 4. Compression fibre changes even when coarse sign/magnitude follows a
--    simple law.  This is why the prime representation must remain in fibre.
------------------------------------------------------------------------

record ArithmeticCompressionSeparation : Set where
  constructor arithmetic-compression-separation
  field
    sameMagnitudeAcrossTrajectory : Bool
    signAlternatesAcrossTrajectory : Bool
    primeRepresentationMayChange : Bool
    coarse369ObserverDeterminesPrimeFactorisation : Bool

canonicalArithmeticCompressionSeparation : ArithmeticCompressionSeparation
canonicalArithmeticCompressionSeparation =
  arithmetic-compression-separation true true true false

------------------------------------------------------------------------
-- 5. Frontier after paying the explicit arithmetic weld.
------------------------------------------------------------------------

data ArithmeticRichResidual : Set where
  missingGenericRichFibStepProducer : ArithmeticRichResidual
  missingGenericPrimeFactorisationProducer : ArithmeticRichResidual
  missingCompressionCostTheorem : ArithmeticRichResidual
  missingSameBishopPhiLimitBridge : ArithmeticRichResidual

record ArithmeticRichFrontier : Set where
  constructor arithmetic-rich-frontier
  field
    explicitSameObjectArithmeticTrajectory : Bool
    richNineComparisonUsesActualNextState : Bool
    richTwentySevenVoxelUsesActualThreeStates : Bool
    normOneMagnitudeRetained : Bool
    primeCompressionRetainedPerState : Bool
    genericTrajectoryProducerComplete : Bool
    bishopPhiLimitPaid : Bool
    firstResidual : ArithmeticRichResidual

canonicalArithmeticRichFrontier : ArithmeticRichFrontier
canonicalArithmeticRichFrontier =
  arithmetic-rich-frontier
    true true true true true false false
    missingGenericRichFibStepProducer
