module DASHI.Physics.Closure.NSTriadKNPhysicalCoherentGramResidualTargetRound222Exact where

------------------------------------------------------------------------
-- ROUND222 / FINAL PACKAGE-A RESEARCH FRONTIER
--
-- BIDI backward audit:
--
-- Round220 does NOT require Gram negativity. At each physical time slice it
-- only needs an upper majorant R_coh for the signed coherent Gram debt:
--
--   gramDebt <= R_coh.
--
-- The cell-mass component is already paid by 36 E D. Round156 then requires
-- the resulting quartic companion contribution to admit a cutoff-uniform
-- time-integrated budget.
--
-- Therefore the weakest honest remaining mathematical theorem is NOT
--
--   gramDebt <= 0
--
-- and NOT an instantaneous cutoff-uniform bound. It is:
--
--   there exists a nonnegative coherent majorant R_coh(N,t) with
--
--     gramDebt(N,t) <= R_coh(N,t)
--
--   whose time integral is bounded uniformly in the Galerkin cutoff N.
--
-- This file freezes that statement as the unique active Package-A research
-- target. The actual analytic integral is intentionally represented by a
-- proof-bearing interface rather than postulated as a theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNRawCurlCellMassEnergyDissipationRound217Exact as R217
import DASHI.Physics.Closure.NSTriadKNCoherentGramOnlyCompanionCompilerRound220Exact as R220

F = R180.F

------------------------------------------------------------------------
-- Literal physical coherent-debt slice.
------------------------------------------------------------------------

record PhysicalCoherentGramSlice : Set where
  constructor physical-coherent-gram-slice
  field
    cells : List (C3.Complex3 F)
    energyDissipation : ℚ
    coherentMajorant : ℚ

    coherentMajorantNN : 0ℚ ≤ coherentMajorant

    -- The already-paid positive part.
    cellMassPayment :
      R180.cellMassSum cells
      ≤ R217.thirtySix * energyDissipation

    -- The ONLY remaining pointwise physical estimate.
    coherentDebtPayment :
      R180.gramDebt cells ≤ coherentMajorant

open PhysicalCoherentGramSlice public

asRound220Payment :
  (slice : PhysicalCoherentGramSlice) →
  R220.CoherentResidualCompanionPayment (cells slice)
asRound220Payment slice =
  R220.coherent-residual-companion-payment
    (energyDissipation slice)
    (coherentMajorant slice)
    (cellMassPayment slice)
    (coherentDebtPayment slice)

sliceCompanionBound :
  (slice : PhysicalCoherentGramSlice) →
  L2.complex3NormSquared (R180.sumCells (cells slice))
  ≤ R217.thirtySix * energyDissipation slice
      + coherentMajorant slice
sliceCompanionBound slice =
  R220.coherentResidualClosesCompanionMass
    (cells slice) (asRound220Payment slice)

------------------------------------------------------------------------
-- Cutoff-uniform integrated research target.
--
-- `IntegratedCoherentMajorantBound` is deliberately an externally inhabited
-- proposition supplied by the eventual PDE theorem. Its interpretation is
-- fixed here by the data it ranges over: same physical slices, same coherent
-- majorant, all cutoffs, all terminal times. No stronger pointwise theorem is
-- smuggled into the interface.
------------------------------------------------------------------------

record PhysicalCoherentGramResidualBudget : Set₁ where
  constructor physical-coherent-gram-residual-budget
  field
    Cutoff : Set
    Time : Set

    slice : Cutoff → Time → PhysicalCoherentGramSlice

    -- Cutoff-independent control value; it may depend on terminal time and
    -- initial data through the chosen analytic model, but not on the cutoff.
    coherentIntegralBound : Time → ℚ

    IntegratedCoherentMajorantBound : Set
    integratedCoherentMajorantBound : IntegratedCoherentMajorantBound

open PhysicalCoherentGramResidualBudget public

-- The finite/algebraic side is automatic once a physical budget is supplied:
-- at every cutoff and time slice Round220 consumes exactly the same majorant
-- appearing in the integrated theorem.
companionSliceAvailableFromPhysicalBudget :
  (budget : PhysicalCoherentGramResidualBudget) →
  (N : Cutoff budget) →
  (t : Time budget) →
  L2.complex3NormSquared
    (R180.sumCells (cells (slice budget N t)))
  ≤ R217.thirtySix * energyDissipation (slice budget N t)
      + coherentMajorant (slice budget N t)
companionSliceAvailableFromPhysicalBudget budget N t =
  sliceCompanionBound (slice budget N t)

------------------------------------------------------------------------
-- Scope flags.
------------------------------------------------------------------------

round222ResearchTargetExactlyCoherentGramResidual : Bool
round222ResearchTargetExactlyCoherentGramResidual = true

round222RequiresGramNegativity : Bool
round222RequiresGramNegativity = false

round222RequiresPointwiseCutoffUniformSmallness : Bool
round222RequiresPointwiseCutoffUniformSmallness = false

round222CellMassStillNovel : Bool
round222CellMassStillNovel = false

round222PhysicalCoherentGramResidualBudgetClosed : Bool
round222PhysicalCoherentGramResidualBudgetClosed = false

round222PackageAClosed : Bool
round222PackageAClosed = false

round222ClayPromotion : Bool
round222ClayPromotion = false

round222ResearchTargetExactlyCoherentGramResidualIsTrue :
  round222ResearchTargetExactlyCoherentGramResidual ≡ true
round222ResearchTargetExactlyCoherentGramResidualIsTrue = refl

round222RequiresGramNegativityIsFalse :
  round222RequiresGramNegativity ≡ false
round222RequiresGramNegativityIsFalse = refl

round222RequiresPointwiseCutoffUniformSmallnessIsFalse :
  round222RequiresPointwiseCutoffUniformSmallness ≡ false
round222RequiresPointwiseCutoffUniformSmallnessIsFalse = refl

round222CellMassStillNovelIsFalse : round222CellMassStillNovel ≡ false
round222CellMassStillNovelIsFalse = refl

round222PhysicalCoherentGramResidualBudgetClosedIsFalse :
  round222PhysicalCoherentGramResidualBudgetClosed ≡ false
round222PhysicalCoherentGramResidualBudgetClosedIsFalse = refl

round222PackageAClosedIsFalse : round222PackageAClosed ≡ false
round222PackageAClosedIsFalse = refl
