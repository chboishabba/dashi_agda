module DASHI.Physics.Closure.NSTriadKNComFiniteActiveDistanceRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- DASHI CONTRIBUTION
--
-- Once the literal Bool shell support is known to have finite width N, the
-- physical Com pair product vanishes identically for shell distances > N.
-- Hence the analytic active-channel theorem is required only at finitely many
-- distances d=0,...,N.  This is stronger than asking for generic exponential
-- decay at every shell separation.
--
-- The current repository's exact dyadic geometry records near width 1 and
-- transition span 2, but the physical odd-P/Q support graph has not yet been
-- identified with one of those predicates.  Therefore this module takes the
-- exact support-width theorem as input and does not guess N.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComBooleanSupportActiveReductionRound45Exact as BoolSupport

record FiniteComSupportWidth
    (physical : BoolSupport.PhysicalOddPQBooleanSupportInput) : Set where
  field
    maxActiveDistance : Nat
    activeDistanceBound : ∀ q r →
      BoolSupport.supportActive physical q r ≡ true →
      BoolSupport.shellDistance physical q r ≤ maxActiveDistance

open FiniteComSupportWidth public

farDistanceCannotBeActive :
  (physical : BoolSupport.PhysicalOddPQBooleanSupportInput) →
  (width : FiniteComSupportWidth physical) →
  ∀ q r →
  maxActiveDistance width < BoolSupport.shellDistance physical q r →
  BoolSupport.supportActive physical q r ≡ true → ⊥
farDistanceCannotBeActive physical width q r far active =
  NatP.<-irrefl _
    (NatP.≤-<-trans
      (activeDistanceBound width q r active)
      far)

farDistanceSupportInactive :
  (physical : BoolSupport.PhysicalOddPQBooleanSupportInput) →
  (width : FiniteComSupportWidth physical) →
  ∀ q r →
  maxActiveDistance width < BoolSupport.shellDistance physical q r →
  BoolSupport.supportActive physical q r ≡ false
farDistanceSupportInactive physical width q r far
  with BoolSupport.supportActive physical q r
... | false = refl
... | true = ⊥-elim (farDistanceCannotBeActive physical width q r far refl)

farDistancePairProductExactlyZero :
  (physical : BoolSupport.PhysicalOddPQBooleanSupportInput) →
  (width : FiniteComSupportWidth physical) →
  ∀ q r →
  maxActiveDistance width < BoolSupport.shellDistance physical q r →
  BoolSupport.physicalPairProduct physical q r ≡ 0ℚ
farDistancePairProductExactlyZero physical width q r far =
  BoolSupport.inactiveSupportAnnihilatesPairProduct physical q r
    (farDistanceSupportInactive physical width q r far)
  where
  open import Data.Rational.Base using (0ℚ)

record FiniteActiveDistanceComProblem
    (physical : BoolSupport.PhysicalOddPQBooleanSupportInput) : Set where
  field
    width : FiniteComSupportWidth physical
    activeChannelBound : ∀ q r →
      BoolSupport.shellDistance physical q r ≤ maxActiveDistance width →
      BoolSupport.supportActive physical q r ≡ true →
      BoolSupport.physicalPairProduct physical q r
      ≤ DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact.twoBranchSquaredGap
          (BoolSupport.shellDistance physical q r)

open FiniteActiveDistanceComProblem public

comAnalyticWorkReducedToFiniteDistances : Bool
comAnalyticWorkReducedToFiniteDistances = true

physicalOddPQExactSupportWidthConstructed : Bool
physicalOddPQExactSupportWidthConstructed = false

comAnalyticWorkReducedToFiniteDistancesIsTrue :
  comAnalyticWorkReducedToFiniteDistances ≡ true
comAnalyticWorkReducedToFiniteDistancesIsTrue = refl

physicalOddPQExactSupportWidthConstructedIsFalse :
  physicalOddPQExactSupportWidthConstructed ≡ false
physicalOddPQExactSupportWidthConstructedIsFalse = refl
