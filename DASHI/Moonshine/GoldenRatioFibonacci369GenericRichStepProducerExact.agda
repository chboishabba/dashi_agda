module DASHI.Moonshine.GoldenRatioFibonacci369GenericRichStepProducerExact where

------------------------------------------------------------------------
-- GENERIC RICH FIBONACCI STEP PRODUCER
--
-- Arithmetic evolution (p,q) -> (p+q,p) is total.  Exact quadratic-defect
-- classification and signed-prime factorisation are explicit producer
-- authorities rather than hidden computation.  Coherence fields require those
-- producers to realise the already-proved Fibonacci defect involution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.QuadraticIrrationalSignedApproximationFibreExact as Quad
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.GoldenRatioFibonacci369RichFibreLiftExact as Rich

------------------------------------------------------------------------
-- 1. Magnitude projection from a proof-bearing golden-ratio defect.
------------------------------------------------------------------------

goldenDefectMagnitude :
  {p q : Nat} → Quad.GoldenRatioDefect p q → Nat
goldenDefectMagnitude (Quad.phiBelow delta eq) = delta
goldenDefectMagnitude (Quad.phiExact eq) = 0
goldenDefectMagnitude (Quad.phiAbove delta eq) = delta

------------------------------------------------------------------------
-- 2. Producer authority.
------------------------------------------------------------------------

record RichStepAuthority : Set₁ where
  field
    classify : (p q : Nat) → Quad.GoldenRatioDefect p q
    compress : (p q : Nat) → Compression.PrimeCompressionFibre

    stepSignCoherent :
      (p q : Nat) →
      Quad.goldenRatioTrit (classify (p + q) p)
      ≡ Triadic.negateTrit (Quad.goldenRatioTrit (classify p q))

    stepMagnitudeCoherent :
      (p q : Nat) →
      goldenDefectMagnitude (classify (p + q) p)
      ≡ goldenDefectMagnitude (classify p q)

open RichStepAuthority public

------------------------------------------------------------------------
-- 3. Canonical rich-state compiler and one-step producer.
------------------------------------------------------------------------

compileRich :
  RichStepAuthority → Nat → Nat → Rich.RichDefectFibre
compileRich A p q =
  Rich.rich-defect-fibre
    p q
    (Quad.goldenRatioTrit (classify A p q))
    (goldenDefectMagnitude (classify A p q))
    (compress A p q)

richFibStep :
  RichStepAuthority → Nat → Nat → Rich.RichDefectFibre
richFibStep A p q = compileRich A (p + q) p

richFibStepNumerator :
  (A : RichStepAuthority) (p q : Nat) →
  Rich.numerator (richFibStep A p q) ≡ p + q
richFibStepNumerator A p q = refl

richFibStepDenominator :
  (A : RichStepAuthority) (p q : Nat) →
  Rich.denominator (richFibStep A p q) ≡ p
richFibStepDenominator A p q = refl

richFibStepSignFlips :
  (A : RichStepAuthority) (p q : Nat) →
  Rich.defectSign (richFibStep A p q)
  ≡ Triadic.negateTrit (Rich.defectSign (compileRich A p q))
richFibStepSignFlips A p q = stepSignCoherent A p q

richFibStepMagnitudePreserved :
  (A : RichStepAuthority) (p q : Nat) →
  Rich.defectMagnitude (richFibStep A p q)
  ≡ Rich.defectMagnitude (compileRich A p q)
richFibStepMagnitudePreserved A p q = stepMagnitudeCoherent A p q

------------------------------------------------------------------------
-- 4. Same rich trajectory compiles directly to 9 and 27 observers.
------------------------------------------------------------------------

compileComparison :
  RichStepAuthority → Nat → Nat → Rich.RichComparisonSheet9
compileComparison A p q =
  Rich.rich-comparison-sheet9
    (compileRich A p q)
    (richFibStep A p q)

compileThreeStepVoxel :
  RichStepAuthority → Nat → Nat → Rich.RichVoxel27
compileThreeStepVoxel A p q =
  let
    s0 = compileRich A p q
    s1 = richFibStep A p q
    p1 = p + q
    q1 = p
    s2 = richFibStep A p1 q1
  in
  Rich.rich-voxel27 s0 s1 s2

compileComparisonProjectsToSignFlip :
  (A : RichStepAuthority) (p q : Nat) →
  Rich.observe9 (compileComparison A p q)
  ≡
  ( Rich.observe3 (compileRich A p q)
  , Triadic.negateTrit (Rich.observe3 (compileRich A p q)) )
compileComparisonProjectsToSignFlip A p q
  rewrite stepSignCoherent A p q = refl

------------------------------------------------------------------------
-- 5. Frontier.
------------------------------------------------------------------------

data GenericRichStepResidual : Set where
  missingCanonicalDefectClassifier : GenericRichStepResidual
  missingCanonicalPrimeCompressionProducer : GenericRichStepResidual
  missingSameBishopRatioConvergence : GenericRichStepResidual

record GenericRichStepFrontier : Set where
  constructor generic-rich-step-frontier
  field
    arithmeticStepGeneric : Bool
    richCompilerGeneric : Bool
    signCoherenceTyped : Bool
    magnitudeCoherenceTyped : Bool
    nineComparisonCompilerGeneric : Bool
    twentySevenVoxelCompilerGeneric : Bool
    canonicalAuthoritiesInstantiated : Bool
    firstResidual : GenericRichStepResidual

canonicalGenericRichStepFrontier : GenericRichStepFrontier
canonicalGenericRichStepFrontier =
  generic-rich-step-frontier
    true true true true true true false
    missingCanonicalDefectClassifier
