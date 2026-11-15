module DASHI.Moonshine.AbelBishopNewtonLiteralFirstStepFromTaylorExact where

------------------------------------------------------------------------
-- ACTUAL NATIVE-EXP NEWTON FIRST STEP FROM TWO SOURCE NUMERIC BOUNDS.
--
-- The original Newton centre is literal:
--   c = 31813/100000 + i*(133724/100000)
--   d = expC(c)-1
--   f = expC(c)-c
--   T(c) = c-f*d^-1
--
-- This module does not repackage first-step contraction as an input.
-- From ORIGINAL same-carrier Bishop normSq enclosures:
--   normSq(f)    <= (1/10000)^2
--   normSq(d^-1) <= (2/3)^2
-- it constructs the exact ORIGINAL
--   normSq(T(c)-c) <= (1/15000)^2
-- input to AbelBishopAnalyticNewtonContractionExact.
--
-- These two analytic source enclosures are still to be constructed
-- from the actual exp/cos/sin Taylor tails and positive denominator.
-- No claim of a completed local Newton contraction or Agda receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
import Inverse as BishopInverse
import Data.Rational.Unnormalised.Properties as RationalP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Moonshine.AbelBishopNewtonSelectedOperatorExact as Newton
import DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact as Constants
import DASHI.Moonshine.AbelBishopAnalyticNewtonContractionExact as Disk

centerResidualSquareUpper : BishopReal.ℝ
centerResidualSquareUpper = BishopReal._⋆ (+ 1 / 10000)

centerReciprocalUpper : BishopReal.ℝ
centerReciprocalUpper = BishopReal._⋆ (+ 2 / 3)

sourceNewtonResidual :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  Complex.BishopComplex
sourceNewtonResidual T =
  Newton.originalBishopExponentialDefect
    T Newton.selectedRationalNewtonCenter

sourceNewtonReciprocal :
  ∀ T →
  (nz : Reciprocal.BishopComplexNonzero
    (Newton.originalBishopNewtonDenominator T)) →
  Complex.BishopComplex
sourceNewtonReciprocal T nz =
  Reciprocal.reciprocalC
    (Newton.originalBishopNewtonDenominator T) nz

record OriginalBishopNewtonTaylorCenterEnclosures
    (T : Cartesian.BishopSetoidComplexTranscendentals)
    (nz : Reciprocal.BishopComplexNonzero
      (Newton.originalBishopNewtonDenominator T)) : Set where
  field
    -- Literal original expC(c)-c; not a surrogate complex exponential.
    expResidualSquared :
      BishopReal._≤_
        (Norm.normSqC (sourceNewtonResidual T))
        (Norm.square centerResidualSquareUpper)

    -- Literal source inverse of expC(c)-1.
    reciprocalSquared :
      BishopReal._≤_
        (Norm.normSqC (sourceNewtonReciprocal T nz))
        (Norm.square centerReciprocalUpper)

open OriginalBishopNewtonTaylorCenterEnclosures public

originalBishopSubtractSelfAfterCorrectionNormSquare :
  ∀ center correction →
  BishopReal._≃_
    (Norm.normSqC
      (Algebra._-C_
        (Algebra._-C_ center correction)
        center))
    (Norm.normSqC correction)
originalBishopSubtractSelfAfterCorrectionNormSquare
  (Complex.complex a b) (Complex.complex c d) =
  let open BishopP.ℝ-Solver in
  solve 4
    (λ a′ b′ c′ d′ →
      (((a′ ⊖ c′) ⊖ a′) ⊗ ((a′ ⊖ c′) ⊖ a′))
        ⊕ (((b′ ⊖ d′) ⊖ b′) ⊗ ((b′ ⊖ d′) ⊖ b′))
      ⊜ ((c′ ⊗ c′) ⊕ (d′ ⊗ d′)))
    BishopP.≃-refl a b c d

originalBishopFirstStepSquareIsResidualProduct :
  ∀ T nz →
  BishopReal._≃_
    (Disk.originalBishopNewtonIncrementSquare T nz zero)
    (BishopReal._*_
      (Norm.normSqC (sourceNewtonResidual T))
      (Norm.normSqC (sourceNewtonReciprocal T nz)))
originalBishopFirstStepSquareIsResidualProduct T nz =
  BishopP.≃-trans
    (originalBishopSubtractSelfAfterCorrectionNormSquare
      Newton.selectedRationalNewtonCenter
      (Algebra._*C_
        (sourceNewtonResidual T)
        (sourceNewtonReciprocal T nz)))
    (Norm.normSqMultiply
      (sourceNewtonResidual T)
      (sourceNewtonReciprocal T nz))

originalBishopSelectedFirstStepBoundConstant :
  BishopReal._≃_
    (BishopReal._*_
      (Norm.square centerResidualSquareUpper)
      (Norm.square centerReciprocalUpper))
    (Norm.square Constants.bishopSelectedNewtonIncrementConstant)
originalBishopSelectedFirstStepBoundConstant =
  let open BishopP.ℝ-Solver in
  solve 0
    ((((Κ (+ 1 / 10000)) ⊗ (Κ (+ 1 / 10000)))
        ⊗ ((Κ (+ 2 / 3)) ⊗ (Κ (+ 2 / 3))))
      ⊜ ((Κ (+ 1 / 15000)) ⊗ (Κ (+ 1 / 15000))))
    BishopP.≃-refl

originalBishopFirstStepBoundFromActualSourceEnclosures :
  ∀ T nz →
  OriginalBishopNewtonTaylorCenterEnclosures T nz →
  BishopReal._≤_
    (Disk.originalBishopNewtonIncrementSquare T nz zero)
    (Norm.square Constants.bishopSelectedNewtonIncrementConstant)
originalBishopFirstStepBoundFromActualSourceEnclosures
  T nz center =
  BishopP.≤-respˡ-≃
    (originalBishopFirstStepSquareIsResidualProduct T nz)
    (BishopP.≤-respʳ-≃
      originalBishopSelectedFirstStepBoundConstant
      (BishopP.*-mono-≤
        (Upper.normSquareNonnegative (sourceNewtonResidual T))
        (Upper.normSquareNonnegative (sourceNewtonReciprocal T nz))
        (expResidualSquared center)
        (reciprocalSquared center)))

-- Upgrade the existing original disk-contraction record, replacing its
-- first-step premise by literal expC Taylor and reciprocal enclosures.
originalBishopNewtonContractionFromSourceCenter :
  ∀ T nz →
  (∀ z →
    Disk.originalBishopSelectedNewtonDisk z →
    Disk.originalBishopSelectedNewtonDisk
      (Newton.originalBishopNewtonOperator T nz z)) →
  (∀ z w →
    Disk.originalBishopSelectedNewtonDisk z →
    Disk.originalBishopSelectedNewtonDisk w →
    BishopReal._≤_
      (Disk.originalBishopSquaredDistance
        (Newton.originalBishopNewtonOperator T nz z)
        (Newton.originalBishopNewtonOperator T nz w))
      (BishopReal._*_
        (Norm.square Constants.bishopSelectedNewtonRatio)
        (Disk.originalBishopSquaredDistance z w))) →
  OriginalBishopNewtonTaylorCenterEnclosures T nz →
  Disk.OriginalBishopAnalyticNewtonContraction T nz
originalBishopNewtonContractionFromSourceCenter
  T nz invariant contractive center = record
    { Disk.originalNewtonMapsDisk = invariant
    ; Disk.originalNewtonSquaredContraction = contractive
    ; Disk.originalNewtonFirstStepSquared =
        originalBishopFirstStepBoundFromActualSourceEnclosures
          T nz center
    }


------------------------------------------------------------------------
-- DENOMINATOR LOWER ENCLOSURE -> ACTUAL RECIPROCAL UPPER ENCLOSURE.
-- This uses original Bishop inverse multiplication (d*d^-1≈1), not a
-- separate reciprocal estimate oracle.
------------------------------------------------------------------------

centerDenominatorSquareLower : BishopReal.ℝ
centerDenominatorSquareLower =
  BishopReal._⋆ (+ 9 / 4)

centerDenominatorInverseSquareUpper : BishopReal.ℝ
centerDenominatorInverseSquareUpper =
  BishopReal._⋆ (+ 4 / 9)

centerDenominatorInverseSquareUpperNonnegative :
  BishopReal.NonNegative centerDenominatorInverseSquareUpper
centerDenominatorInverseSquareUpperNonnegative =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx
      (BishopP.p<q⇒p⋆<q⋆
        0ℚᵘ (+ 4 / 9)
        (RationalP.positive⁻¹ (+ 4 / 9))))

centerInverseUpperAsSquare :
  BishopReal._≃_
    centerDenominatorInverseSquareUpper
    (Norm.square centerReciprocalUpper)
centerInverseUpperAsSquare =
  let open BishopP.ℝ-Solver in
  solve 0
    (Κ (+ 4 / 9)
      ⊜ ((Κ (+ 2 / 3)) ⊗ (Κ (+ 2 / 3))))
    BishopP.≃-refl

originalBishopReciprocalNormFromActualDenominatorLower :
  ∀ T nz →
  BishopReal._≤_
    centerDenominatorSquareLower
    (Norm.normSqC (Newton.originalBishopNewtonDenominator T)) →
  BishopReal._≤_
    (Norm.normSqC (sourceNewtonReciprocal T nz))
    (Norm.square centerReciprocalUpper)
originalBishopReciprocalNormFromActualDenominatorLower
  T nz denominatorLower =
  let
    den = Newton.originalBishopNewtonDenominator T
    d = Norm.normSqC den
    inv = BishopInverse._⁻¹ d (Reciprocal.normSquareNonzero nz)

    invNonnegative : BishopReal.NonNegative inv
    invNonnegative =
      BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx
          (BishopInverse.0<x⇒0<x⁻¹
            (Reciprocal.normSquareNonzero nz)
            (Reciprocal.normSquarePositive nz)))

    scaledLower :
      BishopReal._≤_
        (BishopReal._*_ centerDenominatorSquareLower inv)
        (BishopReal._*_ d inv)
    scaledLower =
      BishopP.*-monoʳ-≤-nonNeg
        denominatorLower invNonnegative

    productBelowOne :
      BishopReal._≤_
        (BishopReal._*_ centerDenominatorSquareLower inv)
        BishopReal.1ℝ
    productBelowOne =
      BishopP.≤-respʳ-≃
        (BishopInverse.*-inverseʳ
          d (Reciprocal.normSquareNonzero nz))
        scaledLower

    scaledUpper :
      BishopReal._≤_
        (BishopReal._*_
          (BishopReal._*_
            centerDenominatorSquareLower inv)
          centerDenominatorInverseSquareUpper)
        (BishopReal._*_
          BishopReal.1ℝ
          centerDenominatorInverseSquareUpper)
    scaledUpper =
      BishopP.*-monoʳ-≤-nonNeg
        productBelowOne
        centerDenominatorInverseSquareUpperNonnegative

    leftNormalizes :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_
            centerDenominatorSquareLower inv)
          centerDenominatorInverseSquareUpper)
        inv
    leftNormalizes =
      let open BishopP.ℝ-Solver in
      solve 1
        (λ x →
          ((Κ (+ 9 / 4) ⊗ x) ⊗ Κ (+ 4 / 9)) ⊜ x)
        BishopP.≃-refl inv

    invBelowRational :
      BishopReal._≤_ inv centerDenominatorInverseSquareUpper
    invBelowRational =
      BishopP.≤-respʳ-≃
        (BishopP.*-identityˡ centerDenominatorInverseSquareUpper)
        (BishopP.≤-respˡ-≃ leftNormalizes scaledUpper)

  in
  BishopP.≤-respˡ-≃
    (Reciprocal.normSquareReciprocal den nz)
    (BishopP.≤-respʳ-≃
      centerInverseUpperAsSquare invBelowRational)

record OriginalBishopNewtonLiteralTaylorCenterBounds
    (T : Cartesian.BishopSetoidComplexTranscendentals) : Set where
  field
    -- Taylor residual: actual native expC(c)-c.
    centerResidualUpper :
      BishopReal._≤_
        (Norm.normSqC (sourceNewtonResidual T))
        (Norm.square centerResidualSquareUpper)

    -- Taylor denominator: actual native expC(c)-1.
    centerDenominatorLower :
      BishopReal._≤_
        centerDenominatorSquareLower
        (Norm.normSqC (Newton.originalBishopNewtonDenominator T))

open OriginalBishopNewtonLiteralTaylorCenterBounds public

originalBishopNewtonTaylorBuildsFirstStepInputs :
  ∀ T nz →
  OriginalBishopNewtonLiteralTaylorCenterBounds T →
  OriginalBishopNewtonTaylorCenterEnclosures T nz
originalBishopNewtonTaylorBuildsFirstStepInputs T nz source =
  record
    { expResidualSquared = centerResidualUpper source
    ; reciprocalSquared =
        originalBishopReciprocalNormFromActualDenominatorLower
          T nz (centerDenominatorLower source)
    }

originalBishopActualTaylorBuildsFirstStepBound :
  ∀ T nz →
  OriginalBishopNewtonLiteralTaylorCenterBounds T →
  BishopReal._≤_
    (Disk.originalBishopNewtonIncrementSquare T nz zero)
    (Norm.square Constants.bishopSelectedNewtonIncrementConstant)
originalBishopActualTaylorBuildsFirstStepBound T nz source =
  originalBishopFirstStepBoundFromActualSourceEnclosures
    T nz (originalBishopNewtonTaylorBuildsFirstStepInputs T nz source)
