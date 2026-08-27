module DASHI.Physics.Closure.NSTriadKNGlobalPhaseNormalFormCriticalEnergyExact where

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
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- DASHI MAKE-OR-BREAK NORMAL FORM
--
-- The adverse-episode route introduces triad-dependent masks and therefore
-- destroys generic complete-network cancellation.  There is a cleaner exact
-- alternative: keep the Round106 phase normal form on the WHOLE interval and
-- absorb its terminal cubic boundary into a corrected critical energy.
--
-- Suppose the critical Galerkin identity is
--
--   X_T + nu D = X_0 + sum_tau integral P_tau,
--
-- and every phase cell satisfies c_tau = g_tau S_tau and
--
--   A_tau' + nu S_tau A_tau = F_tau.
--
-- Round106 gives
--
--   nu sum integral P_tau = G_0 - G_T + sum g_tau integral F_tau,
--
-- where G_t = sum g_tau A_tau(t).  Therefore EXACTLY
--
--   (nu X_T + G_T) + nu^2 D
--     = (nu X_0 + G_0) + sum g_tau integral F_tau.
--
-- No adverse mask or positive part occurs.  This is the correct global
-- normal-form energy identity if the cubic correction can be proved coercive
-- and the complete signed quartic forcing can be controlled.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNSignedPhaseTimeNormalFormRound106Exact as Phase

record GlobalPhaseNormalFormCriticalEnergy : Set where
  constructor global-phase-normal-form-critical-energy
  field
    phaseNetwork : Phase.CommonViscositySignedPhaseNetwork
    criticalInitial criticalTerminal dissipation : ℚ

    criticalEnergyIdentity :
      criticalTerminal
        + Phase.viscosity phaseNetwork * dissipation
      ≡ criticalInitial
        + Phase.sumIntegratedCriticalProduction (Phase.cells phaseNetwork)

open GlobalPhaseNormalFormCriticalEnergy public

initialCorrectedCriticalEnergy : GlobalPhaseNormalFormCriticalEnergy → ℚ
initialCorrectedCriticalEnergy G =
  Phase.viscosity (phaseNetwork G) * criticalInitial G
  + Phase.sumInitialNormalFormBoundary (Phase.cells (phaseNetwork G))

terminalCorrectedCriticalEnergy : GlobalPhaseNormalFormCriticalEnergy → ℚ
terminalCorrectedCriticalEnergy G =
  Phase.viscosity (phaseNetwork G) * criticalTerminal G
  + Phase.sumTerminalNormalFormBoundary (Phase.cells (phaseNetwork G))

signedQuarticNormalFormForcing : GlobalPhaseNormalFormCriticalEnergy → ℚ
signedQuarticNormalFormForcing G =
  Phase.sumSignedNormalFormForcing (Phase.cells (phaseNetwork G))

globalCorrectedCriticalEnergyIdentity :
  (G : GlobalPhaseNormalFormCriticalEnergy) →
  terminalCorrectedCriticalEnergy G
    + (Phase.viscosity (phaseNetwork G) * Phase.viscosity (phaseNetwork G))
      * dissipation G
  ≡ initialCorrectedCriticalEnergy G
      + signedQuarticNormalFormForcing G
globalCorrectedCriticalEnergyIdentity G =
  let
    N = phaseNetwork G
    nu = Phase.viscosity N
    XT = criticalTerminal G
    X0 = criticalInitial G
    D = dissipation G
    P = Phase.sumIntegratedCriticalProduction (Phase.cells N)
    G0 = Phase.sumInitialNormalFormBoundary (Phase.cells N)
    GT = Phase.sumTerminalNormalFormBoundary (Phase.cells N)
    F = Phase.sumSignedNormalFormForcing (Phase.cells N)

    criticalScaled :
      nu * (XT + nu * D) ≡ nu * (X0 + P)
    criticalScaled = cong (nu *_) (criticalEnergyIdentity G)

    criticalRearranged :
      nu * XT + (nu * nu) * D ≡ nu * X0 + nu * P
    criticalRearranged =
      trans
        (sym (solve (nu ∷ XT ∷ D ∷ [])))
        (trans criticalScaled (solve (nu ∷ X0 ∷ P ∷ [])))

    phaseExact : nu * P ≡ G0 + (- GT) + F
    phaseExact = Phase.finiteSignedNetworkTimeNormalForm N

    substitutePhase :
      nu * XT + (nu * nu) * D
      ≡ nu * X0 + (G0 + (- GT) + F)
    substitutePhase =
      trans criticalRearranged (cong (nu * X0 +_) phaseExact)
  in
  trans
    (sym
      (solve (nu ∷ XT ∷ GT ∷ D ∷ [])))
    (trans
      (cong (_+ GT) substitutePhase)
      (solve (nu ∷ X0 ∷ G0 ∷ GT ∷ F ∷ [])))

globalNormalFormRemovesAdverseMasks : Bool
globalNormalFormRemovesAdverseMasks = true

globalNormalFormStillNeedsCubicCoercivityAndQuarticControl : Bool
globalNormalFormStillNeedsCubicCoercivityAndQuarticControl = true

globalNormalFormRemovesAdverseMasksIsTrue :
  globalNormalFormRemovesAdverseMasks ≡ true
globalNormalFormRemovesAdverseMasksIsTrue = refl

globalNormalFormStillNeedsCubicCoercivityAndQuarticControlIsTrue :
  globalNormalFormStillNeedsCubicCoercivityAndQuarticControl ≡ true
globalNormalFormStillNeedsCubicCoercivityAndQuarticControlIsTrue = refl
