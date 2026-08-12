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
-- Once those five equalities are supplied, this module constructs the old
-- `AllBoundarySubtypesVanish`, the Round-45 physical zero-tax input, and the
-- final admissible boundary owner with eta = 0.  No further quantitative
-- boundary optimization remains after these five local propositions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact as Boundary
import DASHI.Physics.Closure.NSTriadKNBoundaryZeroTaxOwnerRound45Exact as Zero
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

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

record PhysicalBoundaryFiveLocalOwnerInput
    (environment : Owner.TaxEnvironment) : Set where
  field
    atoms : List Boundary.BoundaryAtom
    physicalBoundaryProduction : ℚ
    physicalBoundaryProductionNonnegative :
      0ℚ ≤ physicalBoundaryProduction
    physicalBoundaryProductionIsClassifiedTotal :
      physicalBoundaryProduction ≡ Boundary.boundaryTotal atoms
    fiveLocalLimits : FivePhysicalBoundaryLocalLimits atoms

open PhysicalBoundaryFiveLocalOwnerInput public

asRound45BoundaryZeroTaxInput :
  ∀ {environment} →
  PhysicalBoundaryFiveLocalOwnerInput environment →
  Zero.PhysicalBoundaryZeroTaxInput environment
asRound45BoundaryZeroTaxInput input = record
  { atoms = atoms input
  ; physicalBoundaryProduction = physicalBoundaryProduction input
  ; physicalBoundaryProductionNonnegative =
      physicalBoundaryProductionNonnegative input
  ; physicalBoundaryProductionIsClassifiedTotal =
      physicalBoundaryProductionIsClassifiedTotal input
  ; allPhysicalBoundarySubtypesVanish =
      fiveLocalLimitsToExistingBoundaryCertificate (fiveLocalLimits input)
  }

physicalBoundaryOwnerFromFiveLocalLimits :
  ∀ {environment} →
  PhysicalBoundaryFiveLocalOwnerInput environment →
  Owner.AdmissibleOwnerEstimate environment
physicalBoundaryOwnerFromFiveLocalLimits input =
  Zero.physicalBoundaryZeroTaxOwnerEstimate
    (asRound45BoundaryZeroTaxInput input)

physicalBoundaryOwnerFromFiveLocalLimitsIdentity :
  ∀ {environment}
    (input : PhysicalBoundaryFiveLocalOwnerInput environment) →
  Owner.owner (physicalBoundaryOwnerFromFiveLocalLimits input) ≡ Tax.boundary
physicalBoundaryOwnerFromFiveLocalLimitsIdentity input = refl

physicalBoundaryOwnerFromFiveLocalLimitsEtaZero :
  ∀ {environment}
    (input : PhysicalBoundaryFiveLocalOwnerInput environment) →
  Owner.eta (physicalBoundaryOwnerFromFiveLocalLimits input) ≡ 0ℚ
physicalBoundaryOwnerFromFiveLocalLimitsEtaZero input = refl

boundaryCompletionReducedToFiveLocalLimits : Bool
boundaryCompletionReducedToFiveLocalLimits = true

physicalFiveBoundaryLocalLimitsConstructed : Bool
physicalFiveBoundaryLocalLimitsConstructed = false

boundaryCompletionReducedToFiveLocalLimitsIsTrue :
  boundaryCompletionReducedToFiveLocalLimits ≡ true
boundaryCompletionReducedToFiveLocalLimitsIsTrue = refl
