module DASHI.Physics.Closure.NSTriadKNSignedOwnerReserveRecoveryRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Connect the physically witnessed pre-tax cancellation path to the quantity
-- the nine-owner theorem actually cares about: viscosity reserve.
--
-- If a finite cancellation path starts with positive tax I and ends with F,
-- Round 38 already proves
--
--   I = F + T,
--
-- where T is the sum of all physically justified edge transfers.  Therefore
-- the reserve R(x)=1-x obeys the *exact* gain identity
--
--   R(F) = R(I) + T.
--
-- In particular a path can never destroy an already strict owner budget:
--
--   I < 1  =>  F < 1.
--
-- This is the correct algebraic interface for the future constrained-flow
-- optimizer.  It does not manufacture a physical cancellation path or claim
-- enough transfer exists to rescue an over-budget owner family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNSignedOwnerCancellationNetworkRound38Exact as Network

reserve : ℚ → ℚ
reserve tax = 1ℚ - tax

pathReserveGainExact :
  ∀ {initialTax finalTax}
    (path : Network.PhysicalCancellationPath initialTax finalTax) →
  reserve finalTax
  ≡ reserve initialTax + Network.pathTransferTotal path
pathReserveGainExact {initialTax} {finalTax} path =
  let
    taxIdentity :
      initialTax ≡ finalTax + Network.pathTransferTotal path
    taxIdentity = Network.pathTaxSavingExact path
  in
  trans
    (cong (1ℚ -_) (sym taxIdentity))
    (solve
      ( finalTax
      ∷ Network.pathTransferTotal path
      ∷ []))

strictBudgetSurvivesCancellationPath :
  ∀ {initialTax finalTax} →
  Network.PhysicalCancellationPath initialTax finalTax →
  initialTax < 1ℚ →
  finalTax < 1ℚ
strictBudgetSurvivesCancellationPath path initialStrict =
  ℚP.≤-<-trans
    (Network.pathCannotIncreasePositiveTax path)
    initialStrict

signedOwnerReserveRecoveryAlgebraClosed : Bool
signedOwnerReserveRecoveryAlgebraClosed = true

physicalReserveImprovingCancellationPathConstructed : Bool
physicalReserveImprovingCancellationPathConstructed = false

signedOwnerReserveRecoveryAlgebraClosedIsTrue :
  signedOwnerReserveRecoveryAlgebraClosed ≡ true
signedOwnerReserveRecoveryAlgebraClosedIsTrue = refl
