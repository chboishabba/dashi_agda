module DASHI.Physics.Closure.NSTriadKNCriticalAbsoluteValueAbsorptionNoGoRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator estimates and the Euler and Navier-Stokes equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / CRITICAL ABSOLUTE-VALUE ABSORPTION NO-GO
--
-- The standard critical product/commutator route has schematic form
--
--   nonlinear production <= C X D,
--
-- where X is the critical H^(1/2)-size and D is the H^(3/2)-dissipation.
-- Against viscosity nu D this leaves
--
--   (C X - nu) D.
--
-- This is useful for small data (C X < nu), but it cannot by itself prove an
-- arbitrary-data cutoff-uniform critical barrier: once C X reaches nu the
-- strict dissipative margin disappears, and for C X > nu the same majorant is
-- outward pointing.
--
-- This module does not claim that the Kato--Ponce theorem itself is false; it
-- proves the exact scalar obstruction to using an unsigned critical product
-- estimate as the missing arbitrary-data Clay mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _<_)
open import Data.Rational.Properties using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

sub : ℚ → ℚ → ℚ
sub x y = x + (- y)

record CriticalAbsoluteMajorant : Set where
  constructor critical-absolute-majorant
  field
    viscosity : ℚ
    productConstant : ℚ
    criticalSize : ℚ
    dissipation : ℚ

open CriticalAbsoluteMajorant public

viscousTerm nonlinearMajorant residualCoefficient residualProduction :
  CriticalAbsoluteMajorant → ℚ
viscousTerm A = viscosity A * dissipation A
nonlinearMajorant A = productConstant A * criticalSize A * dissipation A
residualCoefficient A = sub (productConstant A * criticalSize A) (viscosity A)
residualProduction A = residualCoefficient A * dissipation A

unsignedCriticalEstimateLeavesExactResidual :
  (A : CriticalAbsoluteMajorant) →
  sub (nonlinearMajorant A) (viscousTerm A) ≡ residualProduction A
unsignedCriticalEstimateLeavesExactResidual A =
  solve
    ( viscosity A ∷ productConstant A ∷ criticalSize A
    ∷ dissipation A ∷ [])

criticalThresholdKillsStrictMargin :
  (A : CriticalAbsoluteMajorant) →
  productConstant A * criticalSize A ≡ viscosity A →
  residualProduction A ≡ 0ℚ
criticalThresholdKillsStrictMargin A threshold rewrite threshold =
  solve (viscosity A ∷ dissipation A ∷ [])

one two : ℚ
one = 1ℚ
two = Int.+ 2 / 1

thresholdWitness : CriticalAbsoluteMajorant
thresholdWitness = critical-absolute-majorant one one one one

supercriticalWitness : CriticalAbsoluteMajorant
supercriticalWitness = critical-absolute-majorant one two one one

thresholdResidualIsZero : residualProduction thresholdWitness ≡ 0ℚ
thresholdResidualIsZero = solve []

supercriticalResidualIsOne : residualProduction supercriticalWitness ≡ one
supercriticalResidualIsOne = solve []

zeroBelowSupercriticalResidual : 0ℚ < residualProduction supercriticalWitness
zeroBelowSupercriticalResidual =
  toWitness {a? = 0ℚ <? residualProduction supercriticalWitness} _

round102UnsignedCriticalProductEstimateIsArbitraryDataBarrier : Bool
round102UnsignedCriticalProductEstimateIsArbitraryDataBarrier = false

round102StrictAbsorptionRequiresAdditionalSignedStructureOrSmallness : Bool
round102StrictAbsorptionRequiresAdditionalSignedStructureOrSmallness = true

round102UnsignedCriticalProductEstimateIsArbitraryDataBarrierIsFalse :
  round102UnsignedCriticalProductEstimateIsArbitraryDataBarrier ≡ false
round102UnsignedCriticalProductEstimateIsArbitraryDataBarrierIsFalse = refl

round102StrictAbsorptionRequiresAdditionalSignedStructureOrSmallnessIsTrue :
  round102StrictAbsorptionRequiresAdditionalSignedStructureOrSmallness ≡ true
round102StrictAbsorptionRequiresAdditionalSignedStructureOrSmallnessIsTrue = refl
