module DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegReductionRound102Exact where

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
-- DOI: 10.1007/s00205-015-0884-8.
--
-- ROUND102 / HETEROCHIRAL MINORITY-LEG NORMAL FORM
--
-- Round93 already derives the literal Waleffe transfer factor from the
-- repository convective coefficient.  On one three-leg cell write positive
-- radii rk,rp,rq abstractly and signed curl eigenvalues lambda_i=s_i r_i.
-- With one common real triple-product amplitude A, the cyclic transfers are
--
--   Tk = (lambda_q-lambda_p) A,
--   Tp = (lambda_k-lambda_q) A,
--   Tq = (lambda_p-lambda_k) A.
--
-- The unsigned critical H^(1/2) production is
--
--   Xdot = rk Tk + rp Tp + rq Tq.
--
-- This file exhausts all eight sign patterns by exact polynomial algebra.
-- The two homochiral classes vanish.  In each of the six mixed classes Xdot
-- is exactly twice the critical-weighted transfer of the UNIQUE minority
-- helicity leg:
--
--   minority k: Xdot = 2 rk Tk,
--   minority p: Xdot = 2 rp Tp,
--   minority q: Xdot = 2 rq Tq.
--
-- Hence the six heterochiral classes reduce to three geometric cases, and in
-- each case the transfer coefficient itself is a difference of the TWO
-- majority radii.  For example when k is the minority leg,
--
--   Xdot = +/- 2 rk (rq-rp) A.
--
-- The reverse triangle inequality for a resonant triad then suggests the
-- sharp next analytic estimate |rq-rp| <= rk, yielding a minority-radius
-- square rather than a major-radius tax.  That metric inequality and the
-- amplitude estimate are intentionally kept separate from this exact algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

sub : ℚ → ℚ → ℚ
sub x y = x + (- y)

two : ℚ
two = Int.+ 2 / 1

record WaleffeCriticalCell : Set where
  constructor waleffe-critical-cell
  field
    radiusK radiusP radiusQ amplitude : ℚ

open WaleffeCriticalCell public

-- Signed-eigenvalue transfer formulas specialized to each sign pattern.
transferK transferP transferQ : ℚ → ℚ → ℚ → ℚ → ℚ
transferK lambdaK lambdaP lambdaQ A = sub lambdaQ lambdaP * A
transferP lambdaK lambdaP lambdaQ A = sub lambdaK lambdaQ * A
transferQ lambdaK lambdaP lambdaQ A = sub lambdaP lambdaK * A

criticalProduction :
  WaleffeCriticalCell → ℚ → ℚ → ℚ → ℚ
criticalProduction C lambdaK lambdaP lambdaQ =
  radiusK C * transferK lambdaK lambdaP lambdaQ (amplitude C)
  + radiusP C * transferP lambdaK lambdaP lambdaQ (amplitude C)
  + radiusQ C * transferQ lambdaK lambdaP lambdaQ (amplitude C)

homochiralPlusCriticalProductionVanishes :
  (C : WaleffeCriticalCell) →
  criticalProduction C (radiusK C) (radiusP C) (radiusQ C) ≡ Int.+ 0 / 1
homochiralPlusCriticalProductionVanishes C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

homochiralMinusCriticalProductionVanishes :
  (C : WaleffeCriticalCell) →
  criticalProduction C (- radiusK C) (- radiusP C) (- radiusQ C) ≡ Int.+ 0 / 1
homochiralMinusCriticalProductionVanishes C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

-- k is the unique minority leg: -++ and +--.
minorityKMinusCriticalProduction :
  (C : WaleffeCriticalCell) →
  criticalProduction C (- radiusK C) (radiusP C) (radiusQ C)
  ≡ two * radiusK C
      * transferK (- radiusK C) (radiusP C) (radiusQ C) (amplitude C)
minorityKMinusCriticalProduction C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityKPlusCriticalProduction :
  (C : WaleffeCriticalCell) →
  criticalProduction C (radiusK C) (- radiusP C) (- radiusQ C)
  ≡ two * radiusK C
      * transferK (radiusK C) (- radiusP C) (- radiusQ C) (amplitude C)
minorityKPlusCriticalProduction C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityKMinusDifferenceNormalForm :
  (C : WaleffeCriticalCell) →
  criticalProduction C (- radiusK C) (radiusP C) (radiusQ C)
  ≡ two * radiusK C * sub (radiusQ C) (radiusP C) * amplitude C
minorityKMinusDifferenceNormalForm C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityKPlusDifferenceNormalForm :
  (C : WaleffeCriticalCell) →
  criticalProduction C (radiusK C) (- radiusP C) (- radiusQ C)
  ≡ - (two * radiusK C * sub (radiusQ C) (radiusP C) * amplitude C)
minorityKPlusDifferenceNormalForm C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

-- p is the unique minority leg: +-+ and -+-.
minorityPMinusCriticalProduction :
  (C : WaleffeCriticalCell) →
  criticalProduction C (radiusK C) (- radiusP C) (radiusQ C)
  ≡ two * radiusP C
      * transferP (radiusK C) (- radiusP C) (radiusQ C) (amplitude C)
minorityPMinusCriticalProduction C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityPPlusCriticalProduction :
  (C : WaleffeCriticalCell) →
  criticalProduction C (- radiusK C) (radiusP C) (- radiusQ C)
  ≡ two * radiusP C
      * transferP (- radiusK C) (radiusP C) (- radiusQ C) (amplitude C)
minorityPPlusCriticalProduction C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityPMinusDifferenceNormalForm :
  (C : WaleffeCriticalCell) →
  criticalProduction C (radiusK C) (- radiusP C) (radiusQ C)
  ≡ two * radiusP C * sub (radiusK C) (radiusQ C) * amplitude C
minorityPMinusDifferenceNormalForm C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityPPlusDifferenceNormalForm :
  (C : WaleffeCriticalCell) →
  criticalProduction C (- radiusK C) (radiusP C) (- radiusQ C)
  ≡ - (two * radiusP C * sub (radiusK C) (radiusQ C) * amplitude C)
minorityPPlusDifferenceNormalForm C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

-- q is the unique minority leg: ++- and --+.
minorityQMinusCriticalProduction :
  (C : WaleffeCriticalCell) →
  criticalProduction C (radiusK C) (radiusP C) (- radiusQ C)
  ≡ two * radiusQ C
      * transferQ (radiusK C) (radiusP C) (- radiusQ C) (amplitude C)
minorityQMinusCriticalProduction C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityQPlusCriticalProduction :
  (C : WaleffeCriticalCell) →
  criticalProduction C (- radiusK C) (- radiusP C) (radiusQ C)
  ≡ two * radiusQ C
      * transferQ (- radiusK C) (- radiusP C) (radiusQ C) (amplitude C)
minorityQPlusCriticalProduction C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityQMinusDifferenceNormalForm :
  (C : WaleffeCriticalCell) →
  criticalProduction C (radiusK C) (radiusP C) (- radiusQ C)
  ≡ two * radiusQ C * sub (radiusP C) (radiusK C) * amplitude C
minorityQMinusDifferenceNormalForm C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

minorityQPlusDifferenceNormalForm :
  (C : WaleffeCriticalCell) →
  criticalProduction C (- radiusK C) (- radiusP C) (radiusQ C)
  ≡ - (two * radiusQ C * sub (radiusP C) (radiusK C) * amplitude C)
minorityQPlusDifferenceNormalForm C =
  solve (radiusK C ∷ radiusP C ∷ radiusQ C ∷ amplitude C ∷ [])

round102AllMixedHelicityCriticalProductionReducesToMinorityLeg : Bool
round102AllMixedHelicityCriticalProductionReducesToMinorityLeg = true

round102MixedHelicityCoefficientIsMajorityRadiusDifference : Bool
round102MixedHelicityCoefficientIsMajorityRadiusDifference = true

round102AllMixedHelicityCriticalProductionReducesToMinorityLegIsTrue :
  round102AllMixedHelicityCriticalProductionReducesToMinorityLeg ≡ true
round102AllMixedHelicityCriticalProductionReducesToMinorityLegIsTrue = refl
