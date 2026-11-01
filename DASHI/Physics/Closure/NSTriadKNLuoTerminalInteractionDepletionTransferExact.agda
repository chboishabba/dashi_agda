module DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Repository-original terminal-depletion transfer; no DOI is assigned.
--
-- Related references:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier--Stokes
-- Equations".
-- DOI: 10.1007/BF00253344.
--
-- PURPOSE
-- Formalise the exact relation between the stronger positive critical-root
-- route and the weaker interaction-depletion route.  Suppose shellwise
--
--   normalizedInteraction_q <= weightedCriticalRoot_q.
--
-- If the weighted critical root tends to zero, then the normalized
-- interaction tends to zero with the same cutoff.  Thus F2 plus the four-class
-- interaction estimate implies F3.  The converse is deliberately absent:
-- cancellation can make the signed interaction small without forcing a
-- positive critical norm to vanish.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚₚ

record EventuallyBelow
  (sequence : ℕ → ℚ)
  (epsilon : ℚ) : Set where
  constructor eventually-below
  field
    cutoff : ℕ
    tailBound :
      (shell : ℕ) →
      cutoff ≤ shell →
      sequence shell ≤ epsilon

open EventuallyBelow public

record TendsToZero (sequence : ℕ → ℚ) : Set where
  constructor tends-to-zero
  field
    eventuallySmall :
      (epsilon : ℚ) →
      0ℚ < epsilon →
      EventuallyBelow sequence epsilon

open TendsToZero public

record CriticalToInteractionData : Set where
  constructor critical-to-interaction-data
  field
    normalizedInteraction weightedCriticalRoot : ℕ → ℚ
    pointwiseInteractionBound :
      (shell : ℕ) →
      normalizedInteraction shell
      ≤ weightedCriticalRoot shell

open CriticalToInteractionData public

interactionDepletionFromCriticalDepletion :
  (dataSet : CriticalToInteractionData) →
  TendsToZero (weightedCriticalRoot dataSet) →
  TendsToZero (normalizedInteraction dataSet)
interactionDepletionFromCriticalDepletion dataSet criticalVanishing =
  tends-to-zero transfer
  where
    transfer :
      (epsilon : ℚ) →
      0ℚ < epsilon →
      EventuallyBelow
        (normalizedInteraction dataSet)
        epsilon
    transfer epsilon epsilonPositive =
      let
        criticalTail =
          eventuallySmall criticalVanishing epsilon epsilonPositive
      in
      eventually-below
        (cutoff criticalTail)
        (λ shell cutoffBelowShell →
          ℚₚ.≤-trans
            (pointwiseInteractionBound dataSet shell)
            (tailBound criticalTail shell cutoffBelowShell))
