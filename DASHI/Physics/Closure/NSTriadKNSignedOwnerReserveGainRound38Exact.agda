module DASHI.Physics.Closure.NSTriadKNSignedOwnerReserveGainRound38Exact where

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
-- Connect the witnessed finite cancellation path to the viscosity reserve
-- optimized by the nine-owner architecture.  If a path proves
--
--   initialTax = finalTax + transferTotal,
--
-- then for reserve(tax)=1-tax we prove exactly
--
--   reserve(finalTax)
--     = reserve(initialTax) + transferTotal.
--
-- Thus every physically justified cancellation transfer is an exactly
-- quantified reserve gain, while a strict initial budget remains strict after
-- any admissible path.  No physical path or sufficient transfer is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _<_)
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
    transferTotal = Network.pathTransferTotal path
    taxIdentity : initialTax ≡ finalTax + transferTotal
    taxIdentity = Network.pathTaxSavingExact path

    splitFinal :
      reserve finalTax
      ≡ (1ℚ - (finalTax + transferTotal)) + transferTotal
    splitFinal = solve (finalTax ∷ transferTotal ∷ [])

    replaceInitial :
      (1ℚ - (finalTax + transferTotal)) + transferTotal
      ≡ reserve initialTax + transferTotal
    replaceInitial =
      cong
        (_+ transferTotal)
        (cong (1ℚ -_) (sym taxIdentity))
  in
  trans splitFinal replaceInitial

strictBudgetSurvivesCancellationPath :
  ∀ {initialTax finalTax} →
  Network.PhysicalCancellationPath initialTax finalTax →
  initialTax < 1ℚ →
  finalTax < 1ℚ
strictBudgetSurvivesCancellationPath path initialStrict =
  ℚP.≤-<-trans
    (Network.pathCannotIncreasePositiveTax path)
    initialStrict

signedOwnerReserveGainAlgebraClosed : Bool
signedOwnerReserveGainAlgebraClosed = true

physicalReserveImprovingCancellationPathConstructed : Bool
physicalReserveImprovingCancellationPathConstructed = false

signedOwnerReserveGainAlgebraClosedIsTrue :
  signedOwnerReserveGainAlgebraClosed ≡ true
signedOwnerReserveGainAlgebraClosedIsTrue = refl
