module DASHI.Physics.Closure.NSTriadKNHelicalCriticalExchangeReductionRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Zhen Lei; Fang-Hua Lin; Yi Zhou.
-- Title: "Structure of Helicity and Global Solutions of Incompressible
-- Navier-Stokes Equation".
-- Archive for Rational Mechanics and Analysis 218 (2015), 1417--1430.
-- DOI: 10.1007/s00205-015-0884-8.
--
-- Authors: Luca Biferale; Stefano Musacchio; Federico Toschi.
-- Title: "Inverse Energy Cascade in Three-Dimensional Isotropic Turbulence".
-- Physical Review Letters 108 (2012), 164501.
-- DOI: 10.1103/PhysRevLett.108.164501.
--
-- ROUND102 / HELICAL CRITICAL-EXCHANGE REDUCTION
--
-- The existing periodic helical infrastructure records the exact modewise
-- identity
--
--   helicity = Hplus - Hminus,
--
-- where Hplus/Hminus are the positive/negative curl contributions at the
-- critical half-derivative weight.  The Euler nonlinearity conserves helicity.
--
-- Let p and m denote the nonlinear tangents of those two critical energies.
-- Helicity conservation is
--
--   p - m = 0.
--
-- The nonlinear tangent of the unsigned critical norm is
--
--   Xdot = p + m.
--
-- Exact algebra therefore gives
--
--   Xdot = 2 p = 2 m.
--
-- Consequently a homochiral subsystem, where the opposite helical sector has
-- zero nonlinear tangent, has ZERO critical-norm production.  The entire
-- nonlinear critical-growth problem is reduced to exchange between the two
-- helicity sectors.
--
-- The final witness also records the sharp limitation: helicity conservation
-- alone does not give a sign.  p=m=1 conserves signed helicity while Xdot=2.
-- Thus the remaining frontier theorem is a quantitative heterochiral-exchange
-- estimate, not a generic helicity-conservation statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

sub : ℚ → ℚ → ℚ
sub x y = x + (- y)

two : ℚ
two = Int.+ 2 / 1

record HelicalCriticalTangent : Set where
  constructor helical-critical-tangent
  field
    plusTangent minusTangent : ℚ

open HelicalCriticalTangent public

signedHelicityTangent : HelicalCriticalTangent → ℚ
signedHelicityTangent D = sub (plusTangent D) (minusTangent D)

unsignedCriticalTangent : HelicalCriticalTangent → ℚ
unsignedCriticalTangent D = plusTangent D + minusTangent D

nonlinearHelicityConserved : HelicalCriticalTangent → Set
nonlinearHelicityConserved D = signedHelicityTangent D ≡ 0ℚ

helicityConservationEquatesSectorTangents :
  (D : HelicalCriticalTangent) →
  nonlinearHelicityConserved D →
  plusTangent D ≡ minusTangent D
helicityConservationEquatesSectorTangents D conserved =
  solve (plusTangent D ∷ minusTangent D ∷ []) conserved

criticalProductionIsTwicePlusExchange :
  (D : HelicalCriticalTangent) →
  nonlinearHelicityConserved D →
  unsignedCriticalTangent D ≡ two * plusTangent D
criticalProductionIsTwicePlusExchange D conserved
  rewrite helicityConservationEquatesSectorTangents D conserved =
  solve (plusTangent D ∷ [])

criticalProductionIsTwiceMinusExchange :
  (D : HelicalCriticalTangent) →
  nonlinearHelicityConserved D →
  unsignedCriticalTangent D ≡ two * minusTangent D
criticalProductionIsTwiceMinusExchange D conserved
  rewrite helicityConservationEquatesSectorTangents D conserved =
  solve (minusTangent D ∷ [])

homochiralPlusHasZeroCriticalProduction :
  (D : HelicalCriticalTangent) →
  nonlinearHelicityConserved D →
  minusTangent D ≡ 0ℚ →
  unsignedCriticalTangent D ≡ 0ℚ
homochiralPlusHasZeroCriticalProduction D conserved noMinus
  rewrite criticalProductionIsTwiceMinusExchange D conserved
        | noMinus =
  solve []

homochiralMinusHasZeroCriticalProduction :
  (D : HelicalCriticalTangent) →
  nonlinearHelicityConserved D →
  plusTangent D ≡ 0ℚ →
  unsignedCriticalTangent D ≡ 0ℚ
homochiralMinusHasZeroCriticalProduction D conserved noPlus
  rewrite criticalProductionIsTwicePlusExchange D conserved
        | noPlus =
  solve []

positiveExchangeWitness : HelicalCriticalTangent
positiveExchangeWitness = helical-critical-tangent 1ℚ 1ℚ

positiveExchangeConservesHelicity :
  nonlinearHelicityConserved positiveExchangeWitness
positiveExchangeConservesHelicity = solve []

positiveExchangeProducesCriticalGrowth :
  unsignedCriticalTangent positiveExchangeWitness ≡ two
positiveExchangeProducesCriticalGrowth = solve []

round102HomochiralCriticalProductionEliminatedByHelicity : Bool
round102HomochiralCriticalProductionEliminatedByHelicity = true

round102CriticalProductionReducesToHeterochiralExchange : Bool
round102CriticalProductionReducesToHeterochiralExchange = true

round102HelicityConservationAloneControlsExchangeSign : Bool
round102HelicityConservationAloneControlsExchangeSign = false

round102CriticalProductionReducesToHeterochiralExchangeIsTrue :
  round102CriticalProductionReducesToHeterochiralExchange ≡ true
round102CriticalProductionReducesToHeterochiralExchangeIsTrue = refl

round102HelicityConservationAloneControlsExchangeSignIsFalse :
  round102HelicityConservationAloneControlsExchangeSign ≡ false
round102HelicityConservationAloneControlsExchangeSignIsFalse = refl
