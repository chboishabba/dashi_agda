module DASHI.Physics.Closure.NSTriadKNBoundaryFiveLocalLimitsRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Boundary no longer belongs in numerical reserve optimization.  The only
-- remaining work is five local physical vanishings corresponding exactly to
-- the repository's existing classification:
--
--   exact absence;
--   fixed-cutoff finite support;
--   geometric tail;
--   strong convergence;
--   dominated convergence.
--
-- Once those five equalities are supplied, this module packages them into the
-- old `AllBoundarySubtypesVanish`, after which Round 45 gives an exact zero-tax
-- owner automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (0ℚ)

import DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact as Boundary

record FivePhysicalBoundaryLocalLimits
    (atoms : List Boundary.BoundaryAtom) : Set where
  field
    physicalExactAbsenceLimit :
      Boundary.reasonTotal Boundary.exactAbsence atoms ≡ 0ℚ

    physicalFixedCutoffFiniteSupportLimit :
      Boundary.reasonTotal Boundary.fixedCutoffFiniteSupport atoms ≡ 0ℚ

    physicalGeometricTailLimit :
      Boundary.reasonTotal Boundary.geometricTail atoms ≡ 0ℚ

    physicalStrongConvergenceLimit :
      Boundary.reasonTotal Boundary.strongConvergence atoms ≡ 0ℚ

    physicalDominatedConvergenceLimit :
      Boundary.reasonTotal Boundary.dominatedConvergence atoms ≡ 0ℚ

open FivePhysicalBoundaryLocalLimits public

fiveLocalLimitsToExistingBoundaryCertificate :
  ∀ {atoms} →
  FivePhysicalBoundaryLocalLimits atoms →
  Boundary.AllBoundarySubtypesVanish atoms
fiveLocalLimitsToExistingBoundaryCertificate limits =
  Boundary.all-boundary-subtypes-vanish
    (physicalExactAbsenceLimit limits)
    (physicalFixedCutoffFiniteSupportLimit limits)
    (physicalGeometricTailLimit limits)
    (physicalStrongConvergenceLimit limits)
    (physicalDominatedConvergenceLimit limits)

fiveLocalLimitsForceBoundaryTotalZero :
  ∀ {atoms} →
  FivePhysicalBoundaryLocalLimits atoms →
  Boundary.boundaryTotal atoms ≡ 0ℚ
fiveLocalLimitsForceBoundaryTotalZero {atoms} limits =
  Boundary.classifiedBoundaryTotalVanishes atoms
    (fiveLocalLimitsToExistingBoundaryCertificate limits)

boundaryCompletionReducedToFiveLocalLimits : Bool
boundaryCompletionReducedToFiveLocalLimits = true

physicalFiveBoundaryLocalLimitsConstructed : Bool
physicalFiveBoundaryLocalLimitsConstructed = false

boundaryCompletionReducedToFiveLocalLimitsIsTrue :
  boundaryCompletionReducedToFiveLocalLimits ≡ true
boundaryCompletionReducedToFiveLocalLimitsIsTrue = refl
