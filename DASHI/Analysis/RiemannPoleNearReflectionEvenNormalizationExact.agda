module DASHI.Analysis.RiemannPoleNearReflectionEvenNormalizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAnalyticComplexCharacterExtensionExact as Character
import DASHI.Analysis.RiemannAristotleReflectionPairKernelReturnExact as Reflection

------------------------------------------------------------------------
-- BACKWARD NORMALIZATION FROM THE LITERAL POLE REFLECTION CONSUMER
--
-- Source-pinned return:
--   K(a,delta;u) + K(-a,delta;u)
--     = 4 g(u) cosh(a u) cos(delta u).
--
-- H_X is responsible only for the target-relative complex character and its
-- even real projection cos(delta u).  The factor 4 g(u) cosh(a u), common
-- multiplicity, and literal pole taper remain kernel-side data.
------------------------------------------------------------------------

record PoleReflectionEvenNormalization
    (analytic : Analytic.AnalyticSubstrate)
    (H_X : Character.RiemannComplexCharacterExtension analytic) : Set₁ where
  constructor pole-reflection-even-normalization
  field
    Scalar : Set
    delta target source frequency height : Scalar

    poleTaperValue : Scalar
    coshHeightFrequency : Scalar
    cosineGapFrequency : Scalar
    multiply : Scalar → Scalar → Scalar
    fourTimes : Scalar → Scalar

    reflectionPairKernelValue : Scalar

    deltaIsLiteralOrdinateGap : Set
    cosineComesFromHXEvenProjection : Set

    kernelIdentity :
      reflectionPairKernelValue
      ≡ fourTimes
          (multiply poleTaperValue
            (multiply coshHeightFrequency cosineGapFrequency))

    literalPoleTaperPreserved : Set
    commonMultiplicityPreserved : Set
    oddSinhSinChannelCancelledBeforeMajorization : Set

    sourceTheoremName : String
    sourceTheoremMatchesReturn :
      sourceTheoremName ≡
      Reflection.leanTheoremName Reflection.canonicalReflectionPairKernelReturn

    normalizationReference : String

open PoleReflectionEvenNormalization public

record ReflectionEvenNormalizationBoundary : Set where
  constructor reflection-even-normalization-boundary
  field
    reflectionReturnOwnsFactorFour : Bool
    reflectionReturnOwnsFactorFourIsTrue : reflectionReturnOwnsFactorFour ≡ true

    reflectionReturnOwnsOddChannelCancellation : Bool
    reflectionReturnOwnsOddChannelCancellationIsTrue :
      reflectionReturnOwnsOddChannelCancellation ≡ true

    characterLawShouldAbsorbPoleCoshTaperFactor : Bool
    characterLawShouldAbsorbPoleCoshTaperFactorIsFalse :
      characterLawShouldAbsorbPoleCoshTaperFactor ≡ false

    normalizationReceiptClosed : Bool
    normalizationReceiptClosedIsFalse : normalizationReceiptClosed ≡ false

    reflectionSourceMachineCheckedInThisAgdaLane : Bool
    reflectionSourceMachineCheckedInThisAgdaLaneIsFalse :
      reflectionSourceMachineCheckedInThisAgdaLane ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalReflectionEvenNormalizationBoundary : ReflectionEvenNormalizationBoundary
canonicalReflectionEvenNormalizationBoundary =
  reflection-even-normalization-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
