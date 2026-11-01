module DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Terence Tao.
-- Title: "Finite Time Blowup for an Averaged Three-Dimensional
-- Navier--Stokes Equation".
-- Journal of the American Mathematical Society 29 (2016), 601--674.
-- DOI: 10.1090/jams/838.
--
-- PURPOSE
-- Exhibit, in exact rational shell arithmetic, the scaling gap that prevents
-- an L2 energy bound from being a scale-uniform critical bound.  A unit-energy
-- state concentrated in shell n has constant energy but its critical shell
-- weight doubles under n -> n+1.  This is a finite algebraic warning: it does
-- not construct a Navier--Stokes solution or a blowup cascade.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

two : ℚ
two = Int.+ 2 / 1

dyadicScale : Nat → ℚ
dyadicScale = Geo.pow two

unitShellEnergy : Nat → ℚ
unitShellEnergy shell = 1ℚ

criticalShellWeight : Nat → ℚ
criticalShellWeight shell = dyadicScale shell * unitShellEnergy shell

energyIsScaleIndependent :
  (shell : Nat) →
  unitShellEnergy (suc shell) ≡ unitShellEnergy shell
energyIsScaleIndependent shell = refl

dyadicScaleSuccessor :
  (shell : Nat) →
  dyadicScale (suc shell) ≡ two * dyadicScale shell
dyadicScaleSuccessor shell = refl

criticalWeightDoubles :
  (shell : Nat) →
  criticalShellWeight (suc shell)
  ≡ two * criticalShellWeight shell
criticalWeightDoubles shell =
  solve (dyadicScale shell ∷ [])

fourShellCriticalAmplification :
  (shell : Nat) →
  criticalShellWeight (suc (suc (suc (suc shell))))
  ≡ (Int.+ 16 / 1) * criticalShellWeight shell
fourShellCriticalAmplification shell =
  solve (dyadicScale shell ∷ [])
