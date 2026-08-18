module DASHI.Moonshine.P11Ell7PointCountBrandtTraceExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Close the same-object arithmetic seam between the direct E(F_7) point count
-- and the p=11 marked T7 correspondence.
--
-- P11Level11Ell7PointCountExact proves
--
--   #E(F_7)=10 = 7+1+2,
--
-- so the normalized weight-2 Hecke/Frobenius trace is a_7=-2.
--
-- P11MarkedX2T7HeckeCollisionExact uses cross unit t=2.  This file proves the
-- exact subtraction-free Brandt trace equation
--
--   (ell+1)+2 = 5t,
--
-- i.e.
--
--   8+2 = 5*2.
--
-- Consequently the coarse nonconstant Brandt eigenvalue difference
--
--   8 - 5*2
--
-- is exactly the point-count trace -2.  No LMFDB coefficient is needed as a
-- theorem premise; LMFDB remains only an external cross-check in neighbouring
-- source comments.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11Level11Ell7PointCountExact as Point7
import DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact as T7
import DASHI.Moonshine.P11MarkedHeckeThetaCollisionCriterionExact as Criterion

ell7TraceEquationConsumesPointCount :
  T7.p11Ell7Degree + Point7.a7NegativeMagnitude
  ≡ 5 * T7.p11Ell7CrossUnit
ell7TraceEquationConsumesPointCount = refl

-- The coarse Brandt eigenvalue represented as 8-10 equals the point-count
-- trace represented as 0-2.
ell7CoarseBrandtDifferenceIsPointCountTrace :
  Criterion.DifferenceEquivalent
    (Criterion.coarseNonconstantDifference
      T7.p11Ell7Degree T7.p11Ell7CrossUnit)
    (Criterion.natDifference 0 Point7.a7NegativeMagnitude)
ell7CoarseBrandtDifferenceIsPointCountTrace = refl

-- Combining with the marked-theta criterion gives a three-way weld:
--
--   direct curve point count
--     = coarse Brandt nonconstant trace
--     = marked deck-standard trace.
ell7MarkedStandardDifferenceIsPointCountTrace :
  Criterion.DifferenceEquivalent
    (Criterion.standardDeckDifference 0 T7.p11Ell7CrossUnit)
    (Criterion.natDifference 0 Point7.a7NegativeMagnitude)
ell7MarkedStandardDifferenceIsPointCountTrace = refl

record P11Ell7PointCountBrandtTraceBoundary : Set where
  field
    directPointCountConsumed : Bool
    directPointCountConsumedIsTrue : directPointCountConsumed ≡ true

    coarseBrandtTraceMatched : Bool
    coarseBrandtTraceMatchedIsTrue : coarseBrandtTraceMatched ≡ true

    markedStandardTraceMatched : Bool
    markedStandardTraceMatchedIsTrue : markedStandardTraceMatched ≡ true

canonicalP11Ell7PointCountBrandtTraceBoundary :
  P11Ell7PointCountBrandtTraceBoundary
canonicalP11Ell7PointCountBrandtTraceBoundary = record
  { directPointCountConsumed = true
  ; directPointCountConsumedIsTrue = refl
  ; coarseBrandtTraceMatched = true
  ; coarseBrandtTraceMatchedIsTrue = refl
  ; markedStandardTraceMatched = true
  ; markedStandardTraceMatchedIsTrue = refl
  }
