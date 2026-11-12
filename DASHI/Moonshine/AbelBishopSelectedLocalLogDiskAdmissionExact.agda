module DASHI.Moonshine.AbelBishopSelectedLocalLogDiskAdmissionExact where

------------------------------------------------------------------------
-- ACTUAL SELECTED BISHOP LOCAL LOG DISK ADMISSION.
--
-- Given a SAME-CARRIER Bishop complex p with normSq(p)>0 and
-- normSq(p) >= (27/20)^2, every displacement t with
-- normSq(t) <= (1/10)^2 satisfies
--
-- normSq(t) <= (2/27)^2 * normSq(p).
--
-- Its normalized displacement p^-1*t therefore lies inside the
-- source log(1+u) convergence disk of radius 2/27 < 1.
-- We construct the canonical ORIGINAL series germ for EVERY such
-- displacement via upper-radius (<=) bounds, not an exact radius.
--
-- The p norm lower, source exp fixed point, and principal inverse law
-- are still separate original analytic gates; the disk normalization,
-- radius admissibility and log-series convergence are paid here.
------------------------------------------------------------------------

open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using
  (0ℚᵘ; 1ℚᵘ; _/_; *<*)
import Data.Rational.Unnormalised.Properties as RationalP
import Data.Integer.Base as ℤ
import Data.Nat.Properties as NatP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopSquareNonnegativeExact as Squares
import DASHI.Moonshine.AbelBishopLogOnePlusUpperDiskConvergenceExact as LogUpper
import DASHI.Moonshine.AbelBishopKoenigsSelectedRationalConstantsExact as Constants

selectedLogRelativeRadius : BishopReal.ℝ
selectedLogRelativeRadius =
  BishopReal._⋆ (+ 2 / 27)

selectedLogRadius : BishopReal.ℝ
selectedLogRadius =
  BishopReal._⋆ (+ 1 / 10)

selectedLowerModulus : BishopReal.ℝ
selectedLowerModulus =
  BishopReal._⋆ (+ 27 / 20)

selectedLogRelativeNonnegative :
  BishopReal._≤_ BishopReal.0ℝ selectedLogRelativeRadius
selectedLogRelativeNonnegative =
  BishopP.p≤q⇒p⋆≤q⋆
    0ℚᵘ (+ 2 / 27)
    (RationalP.nonNegative⁻¹ (+ 2 / 27))

selectedLogRelativeBelowOne :
  BishopReal._<_ selectedLogRelativeRadius BishopReal.1ℝ
selectedLogRelativeBelowOne =
  BishopP.p<q⇒p⋆<q⋆
    (+ 2 / 27) 1ℚᵘ
    (ℚ.*<* (ℤ.+<+ (NatP.≤ᵇ⇒≤ tt)))

selectedLogRelativeInterval :
  Unit.BishopUnitIntervalRatio selectedLogRelativeRadius
selectedLogRelativeInterval = record
  { Unit.ratioNonnegative = selectedLogRelativeNonnegative
  ; Unit.ratioBelowOne = selectedLogRelativeBelowOne
  }

selectedRelativeSquareAtMinNorm :
  BishopReal._≃_
    (BishopReal._*_
      (Norm.square selectedLogRelativeRadius)
      (Norm.square selectedLowerModulus))
    (Norm.square selectedLogRadius)
selectedRelativeSquareAtMinNorm =
  let open BishopP.ℝ-Solver in
  solve 0
    (((Κ (+ 2 / 27) ⊗ Κ (+ 2 / 27))
        ⊗ (Κ (+ 27 / 20) ⊗ Κ (+ 27 / 20)))
      ⊜ (Κ (+ 1 / 10) ⊗ Κ (+ 1 / 10)))
    BishopP.≃-refl

selectedRelativeRadiusFromActualDisk :
  ∀ p t →
  BishopReal._≤_
    (Norm.square selectedLowerModulus)
    (Norm.normSqC p) →
  BishopReal._≤_
    (Norm.normSqC t)
    (Norm.square selectedLogRadius) →
  BishopReal._≤_
    (Norm.normSqC t)
    (BishopReal._*_
      (Norm.square selectedLogRelativeRadius)
      (Norm.normSqC p))
selectedRelativeRadiusFromActualDisk p t pLower tInside =
  BishopP.≤-trans tInside
    (BishopP.≤-respˡ-≃
      selectedRelativeSquareAtMinNorm
      (BishopP.*-monoˡ-≤-nonNeg
        pLower
        (Squares.bishopSquareNonnegative selectedLogRelativeRadius)))

selectedOriginalLocalLogGermOnDisk :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  BishopReal._≤_
    (Norm.square selectedLowerModulus)
    (Norm.normSqC p) →
  BishopReal._≤_
    (Norm.normSqC t)
    (Norm.square selectedLogRadius) →
  Complex.BishopComplex
selectedOriginalLocalLogGermOnDisk p nz t pLower tInside =
  LogUpper.originalBishopSelectedAffineUpperDiskLogGerm
    p nz t
    selectedLogRelativeRadius
    selectedLogRelativeInterval
    (selectedRelativeRadiusFromActualDisk p t pLower tInside)
