module DASHI.Physics.Closure.NSTriadKNLuoCommutatorScaleAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Compute the scale balance of the exact paired commutator.  A second kernel
-- moment contributes lambda_q^{-2}.  Variation of the high derivative costs
-- lambda_q, leaving lambda_q^{-1}; low-factor curvature at a gap d costs
-- lambda_q 2^{-d}, leaving lambda_q^{-1} 2^{-d}.
--
-- The crucial audit is also proved: multiplying the round-seven energy-only
-- near model 2 lambda_q by the bare commutator scale lambda_q^{-1} gives 2,
-- not 1/64.  The commutator repairs critical scaling but does not manufacture
-- the small constant.  Terminal dissipation smallness or a further geometric
-- coefficient is still required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Obstruction

oneHundredTwentyEighth : ℚ
oneHundredTwentyEighth = Int.+ 1 / 128

oneSixtyFourth : ℚ
oneSixtyFourth = Int.+ 1 / 64

inverseOutputScale : Nat → ℚ
inverseOutputScale = Near.windowRoot

secondKernelMoment : Nat → ℚ
secondKernelMoment = Near.windowLength

highDerivativeScale : Nat → ℚ
highDerivativeScale = Scale.dyadicScale

lowCurvatureScale : Nat → Nat → ℚ
lowCurvatureScale outputShell gap =
  Scale.dyadicScale outputShell * Near.windowRoot gap

secondMomentTimesHighDerivative :
  (outputShell : Nat) →
  secondKernelMoment outputShell * highDerivativeScale outputShell
  ≡ inverseOutputScale outputShell
secondMomentTimesHighDerivative outputShell =
  begin
    secondKernelMoment outputShell * highDerivativeScale outputShell
  ≡⟨ solve
       ( Near.windowRoot outputShell
       ∷ Scale.dyadicScale outputShell
       ∷ []) ⟩
    Near.windowRoot outputShell
      * (Near.windowRoot outputShell * Scale.dyadicScale outputShell)
  ≡⟨ cong
       (Near.windowRoot outputShell *_)
       (Obstruction.reciprocalDyadicIdentity outputShell) ⟩
    Near.windowRoot outputShell * 1ℚ
  ≡⟨ solve (Near.windowRoot outputShell ∷ []) ⟩
    inverseOutputScale outputShell
  ∎

secondMomentTimesLowCurvature :
  (outputShell gap : Nat) →
  secondKernelMoment outputShell * lowCurvatureScale outputShell gap
  ≡ inverseOutputScale outputShell * Near.windowRoot gap
secondMomentTimesLowCurvature outputShell gap =
  begin
    secondKernelMoment outputShell * lowCurvatureScale outputShell gap
  ≡⟨ solve
       ( Near.windowRoot outputShell
       ∷ Scale.dyadicScale outputShell
       ∷ Near.windowRoot gap
       ∷ []) ⟩
    Near.windowRoot outputShell
      * (Near.windowRoot outputShell * Scale.dyadicScale outputShell)
      * Near.windowRoot gap
  ≡⟨ cong
       (λ reciprocal →
         Near.windowRoot outputShell * reciprocal * Near.windowRoot gap)
       (Obstruction.reciprocalDyadicIdentity outputShell) ⟩
    Near.windowRoot outputShell * 1ℚ * Near.windowRoot gap
  ≡⟨ solve
       ( Near.windowRoot outputShell
       ∷ Near.windowRoot gap
       ∷ []) ⟩
    inverseOutputScale outputShell * Near.windowRoot gap
  ∎

bareCriticalCommutatorLeavesConstantTwo :
  (outputShell : Nat) →
  Obstruction.nearEnergyOnlyModel outputShell
    * inverseOutputScale outputShell
  ≡ Scale.two
bareCriticalCommutatorLeavesConstantTwo outputShell =
  begin
    Obstruction.nearEnergyOnlyModel outputShell
      * inverseOutputScale outputShell
  ≡⟨ cong
       (_* inverseOutputScale outputShell)
       (Obstruction.nearEnergyOnlyMeaning outputShell) ⟩
    (Scale.two * Scale.dyadicScale outputShell)
      * Near.windowRoot outputShell
  ≡⟨ solve
       ( Scale.two
       ∷ Scale.dyadicScale outputShell
       ∷ Near.windowRoot outputShell
       ∷ []) ⟩
    Scale.two
      * (Near.windowRoot outputShell * Scale.dyadicScale outputShell)
  ≡⟨ cong
       (Scale.two *_)
       (Obstruction.reciprocalDyadicIdentity outputShell) ⟩
    Scale.two * 1ℚ
  ≡⟨ solve (Scale.two ∷ []) ⟩
    Scale.two
  ∎

additionalOneOver128ClosesHalfBudget :
  (outputShell : Nat) →
  Obstruction.nearEnergyOnlyModel outputShell
    * (oneHundredTwentyEighth * inverseOutputScale outputShell)
  ≡ oneSixtyFourth
additionalOneOver128ClosesHalfBudget outputShell =
  begin
    Obstruction.nearEnergyOnlyModel outputShell
      * (oneHundredTwentyEighth * inverseOutputScale outputShell)
  ≡⟨ solve
       ( Obstruction.nearEnergyOnlyModel outputShell
       ∷ oneHundredTwentyEighth
       ∷ inverseOutputScale outputShell
       ∷ []) ⟩
    oneHundredTwentyEighth
      * (Obstruction.nearEnergyOnlyModel outputShell
        * inverseOutputScale outputShell)
  ≡⟨ cong
       (oneHundredTwentyEighth *_)
       (bareCriticalCommutatorLeavesConstantTwo outputShell) ⟩
    oneHundredTwentyEighth * Scale.two
  ≡⟨ solve [] ⟩
    oneSixtyFourth
  ∎
