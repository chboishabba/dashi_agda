module DASHI.Foundations.PolynomialC3S3ReflectionParityLinearExact where

------------------------------------------------------------------------
-- ADDITIVE-F3 LINEARITY OF THE 7-EVEN + 4-ODD REFLECTION CHART.
-- Reuse exact Phase3 additive C3 algebra and the 11-class
-- quotient. All four pair operations are verified over 3^4=81
-- scalar cases, no postulates, no function-extensionality axiom.
-- This is the C2 Fourier diagonalisation over characteristic THREE;
-- it is not C3 averaging (which would require division by 3).
-- Classical sign representation and finite Fourier mathematics
-- retained as prior work; new bridge owns concrete field chart only.
-- SOURCE WRITTEN / KERNEL PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Base369 as Base
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as C3
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q
import DASHI.Foundations.PolynomialC3S3ReflectionParityFourierExact as Fourier

plusTruth : Base.TriTruth → Base.TriTruth → Base.TriTruth
plusTruth a b =
  Fourier.fromPhase (C3._+₃_ (Fourier.toPhase a) (Fourier.toPhase b))

plus11 : Q.Field11 → Q.Field11 → Q.Field11
plus11 f g o = plusTruth (f o) (g o)

plus7 : Q.Field7 → Q.Field7 → Q.Field7
plus7 f g s = plusTruth (f s) (g s)

plusOdd4 : Fourier.Odd4 → Fourier.Odd4 → Fourier.Odd4
plusOdd4 (Fourier.odd4 a b c d) (Fourier.odd4 e f g h) =
  Fourier.odd4
    (C3._+₃_ a e) (C3._+₃_ b f)
    (C3._+₃_ c g) (C3._+₃_ d h)

plusCoordinates :
  Fourier.EvenOddCoordinates → Fourier.EvenOddCoordinates →
  Fourier.EvenOddCoordinates
plusCoordinates x y =
  Fourier.evenOdd
    (plus7 (Fourier.even7 x) (Fourier.even7 y))
    (plusOdd4 (Fourier.odd4Coords x) (Fourier.odd4Coords y))

evenAverageAdditive :
  (a b c d : Base.TriTruth) →
  Fourier.evenAverage (plusTruth a c) (plusTruth b d) ≡
  plusTruth (Fourier.evenAverage a b) (Fourier.evenAverage c d)
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-low Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-mid Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-low Base.tri-high Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-low Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-mid Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-mid Base.tri-high Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-low Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-mid Base.tri-high Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-low Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-low Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-low Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-mid Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-mid Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-mid Base.tri-high = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-high Base.tri-low = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-high Base.tri-mid = refl
evenAverageAdditive Base.tri-high Base.tri-high Base.tri-high Base.tri-high = refl

oddHalfDifferenceAdditive :
  (a b c d : Base.TriTruth) →
  Fourier.oddHalfDifference (plusTruth a c) (plusTruth b d) ≡
  C3._+₃_ (Fourier.oddHalfDifference a b)
           (Fourier.oddHalfDifference c d)
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-low Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-mid Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-low Base.tri-high Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-low Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-mid Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-mid Base.tri-high Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-low Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-mid Base.tri-high Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-low Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-low Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-low Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-mid Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-mid Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-mid Base.tri-high = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-high Base.tri-low = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-high Base.tri-mid = refl
oddHalfDifferenceAdditive Base.tri-high Base.tri-high Base.tri-high Base.tri-high = refl

positiveReconstructionAdditive :
  (e f : Base.TriTruth) (a b : Phase.Phase3) →
  Fourier.reconstructPositive (plusTruth e f) (C3._+₃_ a b) ≡
  plusTruth (Fourier.reconstructPositive e a)
            (Fourier.reconstructPositive f b)
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-low Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-low Base.tri-high Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-low Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase2 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase0 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase0 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase0 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase1 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase1 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase1 Phase.phase2 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase2 Phase.phase0 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase2 Phase.phase1 = refl
positiveReconstructionAdditive Base.tri-high Base.tri-high Phase.phase2 Phase.phase2 = refl

negativeReconstructionAdditive :
  (e f : Base.TriTruth) (a b : Phase.Phase3) →
  Fourier.reconstructNegative (plusTruth e f) (C3._+₃_ a b) ≡
  plusTruth (Fourier.reconstructNegative e a)
            (Fourier.reconstructNegative f b)
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-low Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-mid Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-low Base.tri-high Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-low Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-mid Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-mid Base.tri-high Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-low Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-mid Phase.phase2 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase0 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase0 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase0 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase1 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase1 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase1 Phase.phase2 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase2 Phase.phase0 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase2 Phase.phase1 = refl
negativeReconstructionAdditive Base.tri-high Base.tri-high Phase.phase2 Phase.phase2 = refl

encodeEvenAdditiveAt :
  (f g : Q.Field11) (s : Shape.ShapeOrbit7) →
  Fourier.encodeEven (plus11 f g) s ≡
  plus7 (Fourier.encodeEven f) (Fourier.encodeEven g) s
encodeEvenAdditiveAt f g Shape.identityShape = refl
encodeEvenAdditiveAt f g Shape.threeCycleShape =
  evenAverageAdditive
    (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit)
    (g Q.cycleForwardOrbit) (g Q.cycleBackwardOrbit)
encodeEvenAdditiveAt f g Shape.transpositionShape = refl
encodeEvenAdditiveAt f g Shape.constantShape = refl
encodeEvenAdditiveAt f g Shape.rank2OneFixedShape =
  evenAverageAdditive
    (f Q.rank2OneFixedA) (f Q.rank2OneFixedB)
    (g Q.rank2OneFixedA) (g Q.rank2OneFixedB)
encodeEvenAdditiveAt f g Shape.rank2TwoFixedShape =
  evenAverageAdditive
    (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB)
    (g Q.rank2TwoFixedA) (g Q.rank2TwoFixedB)
encodeEvenAdditiveAt f g Shape.rank2TwoCycleShape =
  evenAverageAdditive
    (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB)
    (g Q.rank2TwoCycleA) (g Q.rank2TwoCycleB)

encodeOddAdditiveCycle :
  (f g : Q.Field11) →
  Fourier.cycleOdd (Fourier.encodeOdd (plus11 f g)) ≡
  C3._+₃_ (Fourier.cycleOdd (Fourier.encodeOdd f))
           (Fourier.cycleOdd (Fourier.encodeOdd g))
encodeOddAdditiveCycle f g =
  oddHalfDifferenceAdditive
    (f Q.cycleForwardOrbit) (f Q.cycleBackwardOrbit)
    (g Q.cycleForwardOrbit) (g Q.cycleBackwardOrbit)

encodeOddAdditiveOneFixed :
  (f g : Q.Field11) →
  Fourier.rank2OneFixedOdd (Fourier.encodeOdd (plus11 f g)) ≡
  C3._+₃_ (Fourier.rank2OneFixedOdd (Fourier.encodeOdd f))
           (Fourier.rank2OneFixedOdd (Fourier.encodeOdd g))
encodeOddAdditiveOneFixed f g =
  oddHalfDifferenceAdditive
    (f Q.rank2OneFixedA) (f Q.rank2OneFixedB)
    (g Q.rank2OneFixedA) (g Q.rank2OneFixedB)

encodeOddAdditiveTwoFixed :
  (f g : Q.Field11) →
  Fourier.rank2TwoFixedOdd (Fourier.encodeOdd (plus11 f g)) ≡
  C3._+₃_ (Fourier.rank2TwoFixedOdd (Fourier.encodeOdd f))
           (Fourier.rank2TwoFixedOdd (Fourier.encodeOdd g))
encodeOddAdditiveTwoFixed f g =
  oddHalfDifferenceAdditive
    (f Q.rank2TwoFixedA) (f Q.rank2TwoFixedB)
    (g Q.rank2TwoFixedA) (g Q.rank2TwoFixedB)

encodeOddAdditiveTwoCycle :
  (f g : Q.Field11) →
  Fourier.rank2TwoCycleOdd (Fourier.encodeOdd (plus11 f g)) ≡
  C3._+₃_ (Fourier.rank2TwoCycleOdd (Fourier.encodeOdd f))
           (Fourier.rank2TwoCycleOdd (Fourier.encodeOdd g))
encodeOddAdditiveTwoCycle f g =
  oddHalfDifferenceAdditive
    (f Q.rank2TwoCycleA) (f Q.rank2TwoCycleB)
    (g Q.rank2TwoCycleA) (g Q.rank2TwoCycleB)

decodeAdditiveAt :
  (x y : Fourier.EvenOddCoordinates) (o : Q.Orbit11) →
  Fourier.decodeEvenOdd (plusCoordinates x y) o ≡
  plus11 (Fourier.decodeEvenOdd x) (Fourier.decodeEvenOdd y) o
decodeAdditiveAt x y Q.identityOrbit = refl
decodeAdditiveAt x y Q.cycleForwardOrbit =
  positiveReconstructionAdditive
    (Fourier.even7 x Shape.threeCycleShape)
    (Fourier.even7 y Shape.threeCycleShape)
    (Fourier.cycleOdd (Fourier.odd4Coords x))
    (Fourier.cycleOdd (Fourier.odd4Coords y))
decodeAdditiveAt x y Q.cycleBackwardOrbit =
  negativeReconstructionAdditive
    (Fourier.even7 x Shape.threeCycleShape)
    (Fourier.even7 y Shape.threeCycleShape)
    (Fourier.cycleOdd (Fourier.odd4Coords x))
    (Fourier.cycleOdd (Fourier.odd4Coords y))
decodeAdditiveAt x y Q.transpositionOrbit = refl
decodeAdditiveAt x y Q.constantOrbit = refl
decodeAdditiveAt x y Q.rank2OneFixedA =
  positiveReconstructionAdditive
    (Fourier.even7 x Shape.rank2OneFixedShape)
    (Fourier.even7 y Shape.rank2OneFixedShape)
    (Fourier.rank2OneFixedOdd (Fourier.odd4Coords x))
    (Fourier.rank2OneFixedOdd (Fourier.odd4Coords y))
decodeAdditiveAt x y Q.rank2OneFixedB =
  negativeReconstructionAdditive
    (Fourier.even7 x Shape.rank2OneFixedShape)
    (Fourier.even7 y Shape.rank2OneFixedShape)
    (Fourier.rank2OneFixedOdd (Fourier.odd4Coords x))
    (Fourier.rank2OneFixedOdd (Fourier.odd4Coords y))
decodeAdditiveAt x y Q.rank2TwoFixedA =
  positiveReconstructionAdditive
    (Fourier.even7 x Shape.rank2TwoFixedShape)
    (Fourier.even7 y Shape.rank2TwoFixedShape)
    (Fourier.rank2TwoFixedOdd (Fourier.odd4Coords x))
    (Fourier.rank2TwoFixedOdd (Fourier.odd4Coords y))
decodeAdditiveAt x y Q.rank2TwoFixedB =
  negativeReconstructionAdditive
    (Fourier.even7 x Shape.rank2TwoFixedShape)
    (Fourier.even7 y Shape.rank2TwoFixedShape)
    (Fourier.rank2TwoFixedOdd (Fourier.odd4Coords x))
    (Fourier.rank2TwoFixedOdd (Fourier.odd4Coords y))
decodeAdditiveAt x y Q.rank2TwoCycleA =
  positiveReconstructionAdditive
    (Fourier.even7 x Shape.rank2TwoCycleShape)
    (Fourier.even7 y Shape.rank2TwoCycleShape)
    (Fourier.rank2TwoCycleOdd (Fourier.odd4Coords x))
    (Fourier.rank2TwoCycleOdd (Fourier.odd4Coords y))
decodeAdditiveAt x y Q.rank2TwoCycleB =
  negativeReconstructionAdditive
    (Fourier.even7 x Shape.rank2TwoCycleShape)
    (Fourier.even7 y Shape.rank2TwoCycleShape)
    (Fourier.rank2TwoCycleOdd (Fourier.odd4Coords x))
    (Fourier.rank2TwoCycleOdd (Fourier.odd4Coords y))

-- Together with the two-sided pointwise inverse laws in the original
-- reflection-Fourier owner, these give a constructive additive
-- group isomorphism of F3^11 and the seven+four additive carrier.
-- No independent vector-space scalar action is claimed beyond F3
-- addition; such an action can be reconstructed from this prime field.
