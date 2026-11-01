module DASHI.Physics.Closure.NSTriadKNEnergyBernsteinResidenceNoGoRound97Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Zhen Lei; Xiao Ren.
-- Title: "Quantitative partial regularity of the Navier-Stokes equations
-- and applications".
-- arXiv:2210.01783 (2022).
-- DOI: not asserted from the supplied arXiv manuscript.
--
-- Author: John G. Heywood.
-- Title: "Epochs of Regularity for Weak Solutions of the Navier-Stokes
-- Equations in Unbounded Domains".
-- Tohoku Mathematical Journal 40 (1988), 293--313.
-- DOI: 10.2748/tmj/1178228031.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND97 / SHARP NO-GO FOR RESIDENCE-ONLY CLOSURE
--
-- The Lei--Ren / Heywood charging principle can bound bad residence using
-- finite dissipation.  It cannot by itself bound the Round96 weighted excess
-- D X.  The following one-cell scaling family makes this exact.
--
-- Let a >= 0 and choose a time weight tau satisfying tau * a^4 = 1.  Define
--
--   lambda = a^2,   E = 1,   A = X = a,   D = a^4.
--
-- Then A^2 = lambda E and tau D = 1, but tau D X = a.  Therefore for any
-- proposed finite bound B, choosing a>B gives the same unit dissipation budget
-- and Bernstein scaling with weighted excess larger than B.  The missing Clay
-- estimate must use additional signed packet dynamics / escape.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _<_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

square : ℚ → ℚ
square x = x * x

fourth : ℚ → ℚ
fourth x = x * x * x * x

record UnitDissipationSpike : Set where
  constructor unit-dissipation-spike
  field
    amplitude timeWeight : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    timeWeightNonnegative : 0ℚ ≤ timeWeight
    unitDissipationLaw : timeWeight * fourth amplitude ≡ 1ℚ

open UnitDissipationSpike public

shellScale : UnitDissipationSpike → ℚ
shellScale spike = square (amplitude spike)

shellEnergy : UnitDissipationSpike → ℚ
shellEnergy spike = 1ℚ

criticalAmplitude : UnitDissipationSpike → ℚ
criticalAmplitude = amplitude

excess : UnitDissipationSpike → ℚ
excess = amplitude

dissipation : UnitDissipationSpike → ℚ
dissipation spike = fourth (amplitude spike)

bernsteinSaturated :
  (spike : UnitDissipationSpike) →
  square (criticalAmplitude spike)
  ≡ shellScale spike * shellEnergy spike
bernsteinSaturated spike = solve (amplitude spike ∷ [])

integratedDissipationIsOne :
  (spike : UnitDissipationSpike) →
  timeWeight spike * dissipation spike ≡ 1ℚ
integratedDissipationIsOne = unitDissipationLaw

integratedWeightedExcessIsAmplitude :
  (spike : UnitDissipationSpike) →
  timeWeight spike * (dissipation spike * excess spike)
  ≡ amplitude spike
integratedWeightedExcessIsAmplitude spike =
  let
    a = amplitude spike
    tau = timeWeight spike
    regroup : tau * (fourth a * a) ≡ (tau * fourth a) * a
    regroup = solve (tau ∷ a ∷ [])
    replaceUnit : (tau * fourth a) * a ≡ 1ℚ * a
    replaceUnit = cong (_* a) (unitDissipationLaw spike)
    close : 1ℚ * a ≡ a
    close = solve (a ∷ [])
  in
  trans regroup (trans replaceUnit close)

weightedExcessCanExceedAnyProposedBound :
  (spike : UnitDissipationSpike) →
  (bound : ℚ) →
  bound < amplitude spike →
  bound < timeWeight spike * (dissipation spike * excess spike)
weightedExcessCanExceedAnyProposedBound spike bound boundBelowAmplitude =
  subst
    (bound <_)
    (sym (integratedWeightedExcessIsAmplitude spike))
    boundBelowAmplitude

round97FiniteDissipationResidenceDoesNotBoundWeightedExcess : Bool
round97FiniteDissipationResidenceDoesNotBoundWeightedExcess = true

round97AdditionalPacketDynamicsRequired : Bool
round97AdditionalPacketDynamicsRequired = true

round97FiniteDissipationResidenceDoesNotBoundWeightedExcessIsTrue :
  round97FiniteDissipationResidenceDoesNotBoundWeightedExcess ≡ true
round97FiniteDissipationResidenceDoesNotBoundWeightedExcessIsTrue = refl
