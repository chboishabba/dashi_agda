module DASHI.Mathematics.NumberTheory.PartitionErdosNatMajorantBootstrapExact where

------------------------------------------------------------------------
-- EXACT RECURRENCE MAJORANT BOOTSTRAP
--
-- Once the arbitrary-n Erdos recurrence is known,
--
--   n * p(n) = divisorSumRHS(n),
--
-- any natural-number supersolution estimate on the right-hand side immediately
-- descends to p(n) after cancellation by positive n:
--
--   divisorSumRHS(n) <= n * M  ==>  p(n) <= M.
--
-- This theorem is purely finite arithmetic.  It is independent of how M is
-- produced (coarse box bound, rational estimate, Bishop exponential, ...).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.NumberTheory.PartitionDivisorSumRegroupingExact as Regroup
import DASHI.Mathematics.NumberTheory.PartitionErdosDivisorSumRecurrenceExact as Recurrence

recurrenceMajorantBootstrap :
  (n majorant : Nat) →
  suc zero ≤ n →
  Regroup.divisorSumRHS n ≤ n * majorant →
  Regroup.partitionCount n ≤ majorant
recurrenceMajorantBootstrap zero majorant () rhsBound
recurrenceMajorantBootstrap (suc n) majorant positive rhsBound =
  NatP.*-cancelˡ-≤ (suc n) scaledBound
  where
  recurrence :
    suc n * Regroup.partitionCount (suc n)
    ≡ Regroup.divisorSumRHS (suc n)
  recurrence =
    Recurrence.canonicalErdosDivisorSumRecurrence (suc n)

  scaledBound :
    suc n * Regroup.partitionCount (suc n)
    ≤ suc n * majorant
  scaledBound =
    subst
      (λ lower → lower ≤ suc n * majorant)
      (sym recurrence)
      rhsBound

------------------------------------------------------------------------
-- The analytic work is therefore cleanly localized: to prove an upper bound M
-- at grade n it suffices to dominate the exact divisor-sum RHS by n*M.
------------------------------------------------------------------------
