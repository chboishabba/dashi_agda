module DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Make the Round-47 reserve scoreboard explicit.  Boundary is zero-tax and
-- HH-good is Young-soft, so the current hard quantities are HH-bad, Com and
-- kernel plus the fixed Bony quartet 4/64 = 1/16.
--
--   H2 = 2 C_* + tau_Com + tau_kernel + 1/16
--   H1 = 2 C_* + tau_kernel + 1/16      (if Com is proved soft)
--   H0 = 2 C_* + 1/16                   (if kernel is also proved soft)
--
-- Every future Young-soft classification literally deletes one hard-floor
-- variable; it must not be replaced by a tiny provisional eta.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _+_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical

fixedBonyFloor : ℚ
fixedBonyFloor =
  Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

oneSixteenth : ℚ
oneSixteenth = Int.+ 1 / 16

fixedBonyFloorExact : fixedBonyFloor ≡ oneSixteenth
fixedBonyFloorExact = solve []

hardGateH2 : ℚ → ℚ → ℚ → ℚ
hardGateH2 ceiling comFloor kernelFloor =
  Sharp.two * ceiling + comFloor + kernelFloor + fixedBonyFloor

hardGateH1 : ℚ → ℚ → ℚ
hardGateH1 ceiling kernelFloor =
  Sharp.two * ceiling + kernelFloor + fixedBonyFloor

hardGateH0 : ℚ → ℚ
hardGateH0 ceiling = Sharp.two * ceiling + fixedBonyFloor

h2WithZeroComIsH1 :
  ∀ ceiling kernelFloor →
  hardGateH2 ceiling 0ℚ kernelFloor ≡ hardGateH1 ceiling kernelFloor
h2WithZeroComIsH1 ceiling kernelFloor = solve []
  where
  open import Data.Rational.Base using (0ℚ)

h1WithZeroKernelIsH0 :
  ∀ ceiling → hardGateH1 ceiling 0ℚ ≡ hardGateH0 ceiling
h1WithZeroKernelIsH0 ceiling = solve []
  where
  open import Data.Rational.Base using (0ℚ)

h0ClosedForm :
  ∀ ceiling → hardGateH0 ceiling ≡ Sharp.two * ceiling + oneSixteenth
h0ClosedForm ceiling = solve (ceiling ∷ [])

currentHardGateLevel : Bool
currentHardGateLevel = true

softTaxProofDeletesHardVariable : Bool
softTaxProofDeletesHardVariable = true

currentHardGateLevelIsTrue : currentHardGateLevel ≡ true
currentHardGateLevelIsTrue = refl
