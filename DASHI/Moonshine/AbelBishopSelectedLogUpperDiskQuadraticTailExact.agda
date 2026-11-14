module DASHI.Moonshine.AbelBishopSelectedLogUpperDiskQuadraticTailExact where

------------------------------------------------------------------------
-- ACTUAL SELECTED LOCAL P-CHART: CLOSED-DISK BISHOP QUADRATIC TAIL.
--
-- This joins original SAME-VALUE upper-disk log convergence to the
-- literal selected p^{-1} t chart of radius 2/27. Unlike the earlier
-- exact-radius log owner, there is no artificial equality assumption
-- normSq(p^{-1}t) ~= (2/27)^2.
--
-- Original mathematical/implementation sources: Bishop--Bridges,
-- Murray/Csimma; DASHI original log/affine/normalization modules.
-- Source-written, not an Agda-kernel or principal-branch receipt.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine
import DASHI.Moonshine.AbelBishopSelectedLogNormalizedDiskUpperExact as Normalized
import DASHI.Moonshine.AbelBishopSelectedLocalLogDiskAdmissionExact as Selected
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite
import DASHI.Moonshine.AbelBishopLogQuadraticUpperDiskSeriesLimitExact as UpperTail

-- This record is the literal source upper-radius proof for the selected
-- original normalized displacement, not an arbitrarily chosen norm.
selectedOriginalNormalizedLogUpperDisk :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  BishopReal._≤_
    (Norm.square Selected.selectedLowerModulus)
    (Norm.normSqC p) →
  BishopReal._≤_
    (Norm.normSqC t)
    (Norm.square Selected.selectedLogRadius) →
  Upper.BishopComplexNormSquareUpperRadius
    (Affine.normalizedDisplacement p nz t)
    Selected.selectedLogRelativeRadius
selectedOriginalNormalizedLogUpperDisk p nz t pLower tInside =
  record
    { Upper.radiusNonnegative =
        BishopP.0≤x⇒nonNegx Selected.selectedLogRelativeNonnegative
    ; Upper.normSqBelowRadiusSquare =
        Normalized.originalBishopNormalizedDisplacementUpperBound
          p nz t Selected.selectedLogRelativeRadius
          (Selected.selectedRelativeRadiusFromActualDisk
            p t pLower tInside)
    }

selectedOriginalLogQuadraticTailLimit :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  (pLower :
    BishopReal._≤_
      (Norm.square Selected.selectedLowerModulus)
      (Norm.normSqC p)) →
  (tInside :
    BishopReal._≤_
      (Norm.normSqC t)
      (Norm.square Selected.selectedLogRadius)) →
  Complex.BishopComplex
selectedOriginalLogQuadraticTailLimit p nz t pLower tInside =
  UpperTail.originalBishopUpperDiskQuadraticRemainder
    Selected.selectedLogRelativeInterval
    (selectedOriginalNormalizedLogUpperDisk
      p nz t pLower tInside)

-- Actual source shifted log terms, and actual selected p-relative chart.
-- No intermediate Cauchy convergence hypothesis remains at this cut.
selectedOriginalLogQuadraticTailConverges :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  (pLower :
    BishopReal._≤_
      (Norm.square Selected.selectedLowerModulus)
      (Norm.normSqC p)) →
  (tInside :
    BishopReal._≤_
      (Norm.normSqC t)
      (Norm.square Selected.selectedLogRadius)) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Finite.originalBishopLogQuadraticTailPrefix
      (Affine.normalizedDisplacement p nz t))
    (selectedOriginalLogQuadraticTailLimit
      p nz t pLower tInside)
selectedOriginalLogQuadraticTailConverges p nz t pLower tInside =
  UpperTail.originalBishopUpperDiskQuadraticTailConverges
    Selected.selectedLogRelativeInterval
    (selectedOriginalNormalizedLogUpperDisk
      p nz t pLower tInside)
