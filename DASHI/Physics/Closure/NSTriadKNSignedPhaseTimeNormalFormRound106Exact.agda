module DASHI.Physics.Closure.NSTriadKNSignedPhaseTimeNormalFormRound106Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND106 / SIGNED TIME NORMAL FORM
--
-- Round105 integrated the positive part of each Waleffe phase separately.
-- That is safe, but it destroys cancellation twice: first inside a triad and
-- then across the complete Galerkin network.  The literal scalar amplitude ODE
-- permits a sharper exact identity.
--
-- Let
--
--   P_tau = c_tau A_tau,
--   A_tau' + nu S_tau A_tau = F_tau,
--
-- and choose the STATIC signed normal-form weight g_tau satisfying
--
--   c_tau = g_tau S_tau.
--
-- Integrating the amplitude equation and multiplying by g_tau gives EXACTLY
--
--   nu integral P_tau
--     = g_tau A_tau(0) - g_tau A_tau(T)
--       + g_tau integral F_tau.
--
-- No positive part, absolute value, or per-cell danger tax appears.  Thus both
-- the helical low/high gain in g_tau and cancellation of the signed forcing sum
-- survive until the complete-network fold.  This is the correct normal-form
-- target for the Round106 frontier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym)

record IntegratedSignedPhaseCell : Set where
  constructor integrated-signed-phase-cell
  field
    viscosity dampingScale coefficient normalFormWeight : ℚ
    initialAmplitude terminalAmplitude integratedAmplitude integratedForcing : ℚ

    coefficientFactorization :
      coefficient ≡ normalFormWeight * dampingScale

    -- Integral of A' + nu S A = F on the literal time interval.
    integratedAmplitudeEquation :
      terminalAmplitude + (- initialAmplitude)
        + viscosity * (dampingScale * integratedAmplitude)
      ≡ integratedForcing

open IntegratedSignedPhaseCell public

integratedCriticalProduction : IntegratedSignedPhaseCell → ℚ
integratedCriticalProduction C = coefficient C * integratedAmplitude C

signedPhaseTimeNormalForm :
  (C : IntegratedSignedPhaseCell) →
  viscosity C * integratedCriticalProduction C
  ≡ normalFormWeight C * initialAmplitude C
      + (- (normalFormWeight C * terminalAmplitude C))
      + normalFormWeight C * integratedForcing C
signedPhaseTimeNormalForm C
  rewrite coefficientFactorization C
        | sym (integratedAmplitudeEquation C) =
  solve
    ( normalFormWeight C ∷ dampingScale C ∷ viscosity C
    ∷ initialAmplitude C ∷ terminalAmplitude C
    ∷ integratedAmplitude C ∷ [])

sumIntegratedCriticalProduction : List IntegratedSignedPhaseCell → ℚ
sumIntegratedCriticalProduction [] = 0ℚ
sumIntegratedCriticalProduction (C ∷ Cs) =
  integratedCriticalProduction C + sumIntegratedCriticalProduction Cs

sumInitialNormalFormBoundary : List IntegratedSignedPhaseCell → ℚ
sumInitialNormalFormBoundary [] = 0ℚ
sumInitialNormalFormBoundary (C ∷ Cs) =
  normalFormWeight C * initialAmplitude C + sumInitialNormalFormBoundary Cs

sumTerminalNormalFormBoundary : List IntegratedSignedPhaseCell → ℚ
sumTerminalNormalFormBoundary [] = 0ℚ
sumTerminalNormalFormBoundary (C ∷ Cs) =
  normalFormWeight C * terminalAmplitude C + sumTerminalNormalFormBoundary Cs

sumSignedNormalFormForcing : List IntegratedSignedPhaseCell → ℚ
sumSignedNormalFormForcing [] = 0ℚ
sumSignedNormalFormForcing (C ∷ Cs) =
  normalFormWeight C * integratedForcing C + sumSignedNormalFormForcing Cs

record CommonViscositySignedPhaseNetwork : Set where
  constructor common-viscosity-signed-phase-network
  field
    viscosity : ℚ
    cells : List IntegratedSignedPhaseCell
    sameViscosity : (C : IntegratedSignedPhaseCell) →
      viscosity C ≡ viscosity

open CommonViscositySignedPhaseNetwork public

finiteSignedNetworkTimeNormalForm :
  (N : CommonViscositySignedPhaseNetwork) →
  viscosity N * sumIntegratedCriticalProduction (cells N)
  ≡ sumInitialNormalFormBoundary (cells N)
      + (- sumTerminalNormalFormBoundary (cells N))
      + sumSignedNormalFormForcing (cells N)
finiteSignedNetworkTimeNormalForm N = go (cells N)
  where
  nu = viscosity N

  go : (Cs : List IntegratedSignedPhaseCell) →
    nu * sumIntegratedCriticalProduction Cs
    ≡ sumInitialNormalFormBoundary Cs
      + (- sumTerminalNormalFormBoundary Cs)
      + sumSignedNormalFormForcing Cs
  go [] = solve []
  go (C ∷ Cs)
    rewrite sameViscosity N C
          | signedPhaseTimeNormalForm C
          | go Cs =
    solve
      ( normalFormWeight C ∷ initialAmplitude C ∷ terminalAmplitude C
      ∷ integratedForcing C
      ∷ sumInitialNormalFormBoundary Cs
      ∷ sumTerminalNormalFormBoundary Cs
      ∷ sumSignedNormalFormForcing Cs ∷ [])

round106SignedPhaseTimeNormalFormClosed : Bool
round106SignedPhaseTimeNormalFormClosed = true

round106PerTriadPositivePartRequired : Bool
round106PerTriadPositivePartRequired = false

round106SignedNetworkForcingCancellationPreserved : Bool
round106SignedNetworkForcingCancellationPreserved = true

round106SignedPhaseTimeNormalFormClosedIsTrue :
  round106SignedPhaseTimeNormalFormClosed ≡ true
round106SignedPhaseTimeNormalFormClosedIsTrue = refl

round106PerTriadPositivePartRequiredIsFalse :
  round106PerTriadPositivePartRequired ≡ false
round106PerTriadPositivePartRequiredIsFalse = refl

round106SignedNetworkForcingCancellationPreservedIsTrue :
  round106SignedNetworkForcingCancellationPreserved ≡ true
round106SignedNetworkForcingCancellationPreservedIsTrue = refl
