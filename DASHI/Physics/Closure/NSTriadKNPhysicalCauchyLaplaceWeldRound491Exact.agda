module DASHI.Physics.Closure.NSTriadKNPhysicalCauchyLaplaceWeldRound491Exact where

------------------------------------------------------------------------
-- ROUND491 / STANDARD LAPLACE AUTHORITY -> LITERAL PHYSICAL CAUCHY CELLS
--
-- R446 defines its physical pair kernel definitionally by R443.cauchyEntry on
-- the two stored positive rates.  Therefore once standard analysis supplies a
-- scalar Laplace realization for R443.cauchyEntry, there is no additional
-- Navier--Stokes representation theorem to prove: the physical cell identity
-- follows by direct specialization to the stored rates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNPositiveRateLaplaceAuthorityRound490Exact as R490

record PhysicalCauchyLaplaceRealization : Set₁ where
  field
    scalarRealization :
      R490.PositiveRateKernelLaplaceRealization R443.cauchyEntry

open PhysicalCauchyLaplaceRealization public

physicalCauchyKernelLaplaceIdentity :
  (R : PhysicalCauchyLaplaceRealization) →
  (left right : R446.PositiveRateComplex3Cell) →
  R446.cauchyKernel left right
  ≡ R490.Integral (R490.authority (scalarRealization R))
      (λ s →
        R490.heatWeight (R490.authority (scalarRealization R))
          (R446.rate left) s
        * R490.heatWeight (R490.authority (scalarRealization R))
          (R446.rate right) s)
physicalCauchyKernelLaplaceIdentity R left right =
  R490.kernelLaplaceIdentity
    (scalarRealization R)
    (R446.rate left)
    (R446.rate right)
    (ℚP.positive⁻¹ (R446.ratePositive left))
    (ℚP.positive⁻¹ (R446.ratePositive right))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round491PhysicalKernelIsDefinitionallyR443CauchyEntry : Bool
round491PhysicalKernelIsDefinitionallyR443CauchyEntry = true

round491PhysicalCellLaplaceWeldNeedsNoNewNSIdentity : Bool
round491PhysicalCellLaplaceWeldNeedsNoNewNSIdentity = true

round491StandardScalarLaplaceAuthorityStillRequiresInhabitant : Bool
round491StandardScalarLaplaceAuthorityStillRequiresInhabitant = true

round491SignedSpacetimeEstimateClosed : Bool
round491SignedSpacetimeEstimateClosed = false

round491R423SignedCompanionBudgetClosed : Bool
round491R423SignedCompanionBudgetClosed = false

round491ClayPromotion : Bool
round491ClayPromotion = false

round491PhysicalKernelIsDefinitionallyR443CauchyEntryIsTrue :
  round491PhysicalKernelIsDefinitionallyR443CauchyEntry ≡ true
round491PhysicalKernelIsDefinitionallyR443CauchyEntryIsTrue = refl

round491PhysicalCellLaplaceWeldNeedsNoNewNSIdentityIsTrue :
  round491PhysicalCellLaplaceWeldNeedsNoNewNSIdentity ≡ true
round491PhysicalCellLaplaceWeldNeedsNoNewNSIdentityIsTrue = refl

round491ClayPromotionIsFalse : round491ClayPromotion ≡ false
round491ClayPromotionIsFalse = refl
