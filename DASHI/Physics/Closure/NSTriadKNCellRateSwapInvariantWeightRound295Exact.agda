module DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact where

------------------------------------------------------------------------
-- ROUND295 / CELL DAMPING RATE MAKES RESOLVENT/HEAT WEIGHTS SWAP-INVARIANT
--
-- For a selected incidence tau define the cell damping rate
--
--   lambda(tau) = rho(p(tau)) + rho(q(tau)).
--
-- Physical p/q swap exchanges the two summands and therefore preserves lambda
-- exactly.  Hence ANY scalar function phi(lambda) is a swap-invariant weight
-- and may be fed to R294.  This includes the future analytic realization
--
--   phi_s(lambda) = exp(-s lambda)
--
-- used in the heat representation of 1/(lambda_alpha+lambda_beta), but no
-- exponential/real-analysis carrier is introduced in this finite theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294

F : C3.RealField _
F = Rational.rationalRealField

cellRate :
  (rho : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
cellRate rho tau = rho (Physical.p tau) + rho (Physical.q tau)

cellRateSwapInvariant :
  (rho : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → ℚ) →
  (tau : Physical.PhysicalTriadIncidence) →
  cellRate rho (Symmetry.swapTriad tau) ≡ cellRate rho tau
cellRateSwapInvariant rho tau =
  ℚP.+-comm (rho (Physical.q tau)) (rho (Physical.p tau))

rateWeight :
  (rho : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → ℚ) →
  (phi : ℚ → C3.Complex F) →
  Physical.PhysicalTriadIncidence → C3.Complex F
rateWeight rho phi tau = phi (cellRate rho tau)

rateWeightSwapInvariant :
  (rho : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → ℚ) →
  (phi : ℚ → C3.Complex F) →
  (tau : Physical.PhysicalTriadIncidence) →
  rateWeight rho phi (Symmetry.swapTriad tau) ≡ rateWeight rho phi tau
rateWeightSwapInvariant rho phi tau =
  cong phi (cellRateSwapInvariant rho tau)

rateFunctionBuildsR294Weight :
  (rho : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode → ℚ) →
  (phi : ℚ → C3.Complex F) →
  R294.SwapInvariantCellWeight F
rateFunctionBuildsR294Weight rho phi = record
  { R294.weight = rateWeight rho phi
  ; R294.swapInvariant = rateWeightSwapInvariant rho phi
  }

round295CellDampingRateSwapInvariant : Bool
round295CellDampingRateSwapInvariant = true

round295AnyFunctionOfCellRatePreservesR230Collapse : Bool
round295AnyFunctionOfCellRatePreservesR230Collapse = true

round295HeatExponentialAnalyticRealizationInstalled : Bool
round295HeatExponentialAnalyticRealizationInstalled = false

round295WeightedNonlinearCommutatorPaid : Bool
round295WeightedNonlinearCommutatorPaid = false

round295SignedIntegratedGramBudgetClosed : Bool
round295SignedIntegratedGramBudgetClosed = false

round295PackageAClosed : Bool
round295PackageAClosed = false

round295ClayPromotion : Bool
round295ClayPromotion = false

round295CellDampingRateSwapInvariantIsTrue :
  round295CellDampingRateSwapInvariant ≡ true
round295CellDampingRateSwapInvariantIsTrue = refl
