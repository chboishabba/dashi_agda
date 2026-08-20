module DASHI.Physics.Closure.NSTriadKNAdverseWaleffeResidencePaymentRound94Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- Author: M. Hirota.
-- Title: "Lagrangian approach to resonant three-mode interaction in
-- magnetohydrodynamics".
-- 23rd IAEA Fusion Energy Conference, THS/P7-02 (2010).
-- DOI: no DOI recorded for the conference paper here.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND94 / FORCED-RESIDENCE PAYMENT
--
-- Round94 has already derived on the literal Galerkin carrier
--
--   dA + gamma A = F_network
--
-- for the real Waleffe amplitude A. On a bad interval with A >= threshold,
-- integration gives a cell inequality
--
--   A_end + gamma * threshold * residence
--     <= A_start + forcingCost.
--
-- This module proves the exact finite telescoping theorem for a chain of such
-- intervals. Persistent adverse residence is therefore paid by initial phase
-- amplitude and accumulated positive network forcing.  No isolated-triad
-- recurrence or phase-genericity theorem is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

record AdverseResidenceStep (startAmplitude : ℚ) : Set where
  constructor adverse-residence-step
  field
    endAmplitude forcingCost damping threshold residence : ℚ
    endAmplitudeNonnegative : 0ℚ ≤ endAmplitude
    forcingCostNonnegative : 0ℚ ≤ forcingCost
    dampingNonnegative : 0ℚ ≤ damping
    thresholdNonnegative : 0ℚ ≤ threshold
    residenceNonnegative : 0ℚ ≤ residence

    integratedDampedForcedBalance :
      endAmplitude + (damping * threshold) * residence
      ≤ startAmplitude + forcingCost

open AdverseResidenceStep public

payment : ∀ {start} → AdverseResidenceStep start → ℚ
payment step = (damping step * threshold step) * residence step

data AdverseResidenceChain (initialAmplitude : ℚ) : Set where
  chain-end :
    0ℚ ≤ initialAmplitude →
    AdverseResidenceChain initialAmplitude

  chain-step :
    (first : AdverseResidenceStep initialAmplitude) →
    AdverseResidenceChain (endAmplitude first) →
    AdverseResidenceChain initialAmplitude

sumPayment : ∀ {initial} → AdverseResidenceChain initial → ℚ
sumPayment (chain-end initialNN) = 0ℚ
sumPayment (chain-step first rest) = payment first + sumPayment rest

sumForcing : ∀ {initial} → AdverseResidenceChain initial → ℚ
sumForcing (chain-end initialNN) = 0ℚ
sumForcing (chain-step first rest) = forcingCost first + sumForcing rest

terminalAmplitude : ∀ {initial} → AdverseResidenceChain initial → ℚ
terminalAmplitude {initial} (chain-end initialNN) = initial
terminalAmplitude (chain-step first rest) = terminalAmplitude rest

terminalAmplitudeNonnegative :
  ∀ {initial} (chain : AdverseResidenceChain initial) →
  0ℚ ≤ terminalAmplitude chain
terminalAmplitudeNonnegative (chain-end initialNN) = initialNN
terminalAmplitudeNonnegative (chain-step first rest) =
  terminalAmplitudeNonnegative rest

adverseResidenceChainTelescopes :
  ∀ {initial} (chain : AdverseResidenceChain initial) →
  terminalAmplitude chain + sumPayment chain
  ≤ initial + sumForcing chain
adverseResidenceChainTelescopes {initial} (chain-end initialNN) =
  ℚP.≤-refl
adverseResidenceChainTelescopes {initial} (chain-step first rest) =
  let
    tail = adverseResidenceChainTelescopes rest

    tailWithPayment :
      payment first +
        (terminalAmplitude rest + sumPayment rest)
      ≤ payment first +
        (endAmplitude first + sumForcing rest)
    tailWithPayment = ℚP.+-mono-≤ ℚP.≤-refl tail

    tailReordered :
      terminalAmplitude rest + payment first + sumPayment rest
      ≤ endAmplitude first + payment first + sumForcing rest
    tailReordered =
      subst
        (λ left → left ≤ endAmplitude first + payment first + sumForcing rest)
        (solve
          (terminalAmplitude rest ∷ payment first ∷ sumPayment rest ∷ []))
        (subst
          (λ right →
            payment first +
              (terminalAmplitude rest + sumPayment rest) ≤ right)
          (solve
            (payment first ∷ endAmplitude first ∷ sumForcing rest ∷ []))
          tailWithPayment)

    localWithTail :
      endAmplitude first + payment first + sumForcing rest
      ≤ initial + forcingCost first + sumForcing rest
    localWithTail =
      ℚP.+-mono-≤ (integratedDampedForcedBalance first) ℚP.≤-refl

    chained = ℚP.≤-trans tailReordered localWithTail
  in
  subst
    (λ right →
      terminalAmplitude rest + payment first + sumPayment rest ≤ right)
    (solve (initial ∷ forcingCost first ∷ sumForcing rest ∷ []))
    chained

adverseResidencePaymentBound :
  ∀ {initial} (chain : AdverseResidenceChain initial) →
  sumPayment chain ≤ initial + sumForcing chain
adverseResidencePaymentBound {initial} chain =
  let
    terminalNN = terminalAmplitudeNonnegative chain
    addTerminal :
      0ℚ + sumPayment chain
      ≤ terminalAmplitude chain + sumPayment chain
    addTerminal = ℚP.+-mono-≤ terminalNN ℚP.≤-refl

    dropTerminal :
      sumPayment chain
      ≤ terminalAmplitude chain + sumPayment chain
    dropTerminal =
      subst
        (λ left → left ≤ terminalAmplitude chain + sumPayment chain)
        (solve (sumPayment chain ∷ []))
        addTerminal
  in
  ℚP.≤-trans dropTerminal (adverseResidenceChainTelescopes chain)

record UniformAdverseResidenceBudget : Set where
  constructor uniform-adverse-residence-budget
  field
    initialAmplitude totalForcing gammaFloor amplitudeThreshold totalResidence : ℚ
    initialAmplitudeNonnegative : 0ℚ ≤ initialAmplitude
    totalForcingNonnegative : 0ℚ ≤ totalForcing
    gammaFloorNonnegative : 0ℚ ≤ gammaFloor
    amplitudeThresholdNonnegative : 0ℚ ≤ amplitudeThreshold
    totalResidenceNonnegative : 0ℚ ≤ totalResidence

    paidResidenceBound :
      (gammaFloor * amplitudeThreshold) * totalResidence
      ≤ initialAmplitude + totalForcing

open UniformAdverseResidenceBudget public

round94FiniteAdverseResidenceTelescopingClosed : Bool
round94FiniteAdverseResidenceTelescopingClosed = true

round94AdverseResidencePaymentBoundClosed : Bool
round94AdverseResidencePaymentBoundClosed = true

round94PhysicalNetworkForcingBudgetClosed : Bool
round94PhysicalNetworkForcingBudgetClosed = false

round94FiniteAdverseResidenceTelescopingClosedIsTrue :
  round94FiniteAdverseResidenceTelescopingClosed ≡ true
round94FiniteAdverseResidenceTelescopingClosedIsTrue = refl

round94AdverseResidencePaymentBoundClosedIsTrue :
  round94AdverseResidencePaymentBoundClosed ≡ true
round94AdverseResidencePaymentBoundClosedIsTrue = refl

round94PhysicalNetworkForcingBudgetClosedIsFalse :
  round94PhysicalNetworkForcingBudgetClosed ≡ false
round94PhysicalNetworkForcingBudgetClosedIsFalse = refl
