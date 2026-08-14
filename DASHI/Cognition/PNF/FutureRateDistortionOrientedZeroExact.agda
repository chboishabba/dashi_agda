module DASHI.Cognition.PNF.FutureRateDistortionOrientedZeroExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave

------------------------------------------------------------------------
-- FINITE FUTURE RATE-DISTORTION
--
-- Rate is additional residual cost beyond the retained scalar observation.
-- Distortion is future error on the oriented zero fibre.  This finite model
-- gives a literal zero-distortion optimum and a relaxed-distortion optimum.
------------------------------------------------------------------------

data Scheme : Set where
  scalarOnly orientedResidual : Scheme

rate : Scheme → Nat
rate scalarOnly = 0
rate orientedResidual = 1

-- Unit deterministic future distortion means that some scalar-collapsed pair
-- has a different declared next observation; zero means exact future safety.
distortion : Scheme → Nat
distortion scalarOnly = 1
distortion orientedResidual = 0

Feasible : Nat → Scheme → Set
Feasible epsilon scheme = distortion scheme ≤ epsilon

record OptimalAt (epsilon : Nat) (scheme : Scheme) : Set where
  constructor optimalAt
  field
    feasible : Feasible epsilon scheme
    minimal : (candidate : Scheme) → Feasible epsilon candidate → rate scheme ≤ rate candidate

open OptimalAt public

zeroDistortionForcesOrientation :
  Feasible 0 scalarOnly → ⊥
zeroDistortionForcesOrientation ()

orientedResidualIsZeroDistortionFeasible : Feasible 0 orientedResidual
orientedResidualIsZeroDistortionFeasible = z≤n

orientedResidualIsZeroDistortionOptimal : OptimalAt 0 orientedResidual
orientedResidualIsZeroDistortionOptimal = optimalAt
  orientedResidualIsZeroDistortionFeasible
  minimalZero
  where
    minimalZero : (candidate : Scheme) → Feasible 0 candidate → rate orientedResidual ≤ rate candidate
    minimalZero scalarOnly feasible = ⊥-elim (zeroDistortionForcesOrientation feasible)
    minimalZero orientedResidual feasible = s≤s z≤n

scalarOnlyIsUnitDistortionFeasible : Feasible 1 scalarOnly
scalarOnlyIsUnitDistortionFeasible = s≤s z≤n

scalarOnlyIsUnitDistortionOptimal : OptimalAt 1 scalarOnly
scalarOnlyIsUnitDistortionOptimal = optimalAt
  scalarOnlyIsUnitDistortionFeasible
  (λ candidate feasible → z≤n)

relaxingDistortionDropsOptimalResidualRate :
  rate scalarOnly < rate orientedResidual
relaxingDistortionDropsOptimalResidualRate = s≤s z≤n

------------------------------------------------------------------------
-- Generic monotonicity of feasibility under a relaxed distortion budget.
------------------------------------------------------------------------

feasibleMonotone :
  ∀ {epsilon epsilon′ scheme} →
  epsilon ≤ epsilon′ → Feasible epsilon scheme → Feasible epsilon′ scheme
feasibleMonotone epsilon≤epsilon′ feasible = ≤-trans feasible epsilon≤epsilon′

-- A zero-distortion safe scheme remains feasible at every larger budget.
zeroDistortionSchemeSurvivesRelaxation :
  (epsilon : Nat) → Feasible 0 orientedResidual → Feasible epsilon orientedResidual
zeroDistortionSchemeSurvivesRelaxation epsilon feasible =
  feasibleMonotone z≤n feasible

------------------------------------------------------------------------
-- Zero-distortion recovery: in this regression, retaining the oriented zero
-- residual is exactly the consumer-future-safe representation.
------------------------------------------------------------------------

zeroDistortionReopen :
  (state : Wave.Wave4) →
  Wave.adaptiveReopen (Wave.scalar state) (Wave.adaptiveResidual state) ≡ state
zeroDistortionReopen = Wave.adaptiveResidualReopensExactly

------------------------------------------------------------------------
-- Boundary: this is a finite deterministic rate-distortion instance.  The
-- normalized rational probability layer supplies total-variation distortion
-- for stochastic consumers; no Shannon asymptotic coding theorem is claimed.
------------------------------------------------------------------------
