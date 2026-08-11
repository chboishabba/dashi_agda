module DASHI.Physics.Closure.NSTriadKNLuoCriticalRestartContradictionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Tosio Kato.
-- Title: "Strong Lp-Solutions of the Navier-Stokes Equation in Rm, with
-- Applications to Weak Solutions".
-- DOI: 10.1007/BF01174182.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- This module formalises the exact last contradiction once the analytic
-- critical restart theorem and the uniform H^(1/2) approach bound are supplied.
-- A restart interface maps
--
--   ||u(t_0)||_critical <= M
--
-- to existence through `t_0 + tau(M,nu)`.  If an approach time is close enough
-- to a purported finite maximal time that this restart endpoint lies beyond
-- it, maximality and restart existence produce the empty type.
--
-- The module deliberately does not manufacture the Fujita--Kato local theorem,
-- time continuity, an approach sequence, or the uniform critical bound.  It
-- closes only the logically exact C4 endpoint and makes those analytic inputs
-- impossible to confuse with the contradiction itself.
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _+_; _≤_; _<_)

record CriticalRestartInterface : Set₁ where
  constructor criticalRestartInterface
  field
    State : Set
    SolutionExistsThrough : ℚ → Set
    stateAt : ℚ → State
    criticalNorm : State → ℚ
    restartLifetime : ℚ → ℚ → ℚ

    restartFromCriticalBound :
      (time normBound viscosity : ℚ) →
      criticalNorm (stateAt time) ≤ normBound →
      SolutionExistsThrough
        (time + restartLifetime normBound viscosity)

open CriticalRestartInterface public

record FiniteMaximalRestartContradictionData : Set₁ where
  constructor finiteMaximalRestartContradictionData
  field
    restartInterface : CriticalRestartInterface
    maximalTime approachTime normBound viscosity : ℚ

    approachCriticalBound :
      criticalNorm restartInterface
        (stateAt restartInterface approachTime)
      ≤ normBound

    restartPassesMaximalTime :
      maximalTime
      < approachTime
        + restartLifetime restartInterface normBound viscosity

    maximalityForbidsExtension :
      (endpoint : ℚ) →
      maximalTime < endpoint →
      SolutionExistsThrough restartInterface endpoint →
      ⊥

open FiniteMaximalRestartContradictionData public

criticalRestartContradictsFiniteMaximality :
  (dataSet : FiniteMaximalRestartContradictionData) → ⊥
criticalRestartContradictsFiniteMaximality dataSet =
  let
    interface = restartInterface dataSet
    endpoint =
      approachTime dataSet
      + restartLifetime interface (normBound dataSet) (viscosity dataSet)

    restarted : SolutionExistsThrough interface endpoint
    restarted =
      restartFromCriticalBound
        interface
        (approachTime dataSet)
        (normBound dataSet)
        (viscosity dataSet)
        (approachCriticalBound dataSet)
  in
  maximalityForbidsExtension
    dataSet
    endpoint
    (restartPassesMaximalTime dataSet)
    restarted

record CriticalRestartAuthorityBoundary : Set where
  constructor criticalRestartAuthorityBoundary
  field
    exactMaximalTimeContradictionProved : Set
    criticalRestartInterfaceExposed : Set
    fujitaKatoRestartProduced : Set
    boundedApproachSequenceProduced : Set
    timeContinuityAtRestartProduced : Set

canonicalCriticalRestartAuthorityBoundary : CriticalRestartAuthorityBoundary
canonicalCriticalRestartAuthorityBoundary =
  criticalRestartAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
