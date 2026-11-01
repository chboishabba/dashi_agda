module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact where

------------------------------------------------------------------------
-- S2b2d1b2 / B2: DFL-DHH BIPARTITE FRACTIONAL-SHELL FOLD
--
-- The bipartite combinatorics are already exact upstream.  This file isolates
-- the analytic leaf at the right granularity: shell-pair receipts are folded
-- with no cardinality multiplier.  A receipt may be produced by the intended
-- DFL Bernstein + DHH low-output/null-gain estimate after shell separation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay

F : C3.RealField _
F = Rational.rationalRealField

module DeepCrossPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output

  record ShellPairReceipt : Set where
    constructor shell-pair-receipt
    field
      signedMass budget : ℚ
      paid : signedMass ≤ budget

  open ShellPairReceipt public

  sumSignedMass : List ShellPairReceipt → ℚ
  sumSignedMass [] = 0ℚ
  sumSignedMass (receipt ∷ rest) =
    signedMass receipt + sumSignedMass rest

  sumBudget : List ShellPairReceipt → ℚ
  sumBudget [] = 0ℚ
  sumBudget (receipt ∷ rest) =
    budget receipt + sumBudget rest

  shellPairFoldPaid :
    (receipts : List ShellPairReceipt) →
    sumSignedMass receipts ≤ sumBudget receipts
  shellPairFoldPaid [] = ℚP.≤-refl
  shellPairFoldPaid (receipt ∷ rest) =
    ℚP.+-mono-≤ (paid receipt) (shellPairFoldPaid rest)

  record PhysicalDeepFarLowDeepHHFractionalShellData : Set where
    constructor physical-deep-far-low-deep-hh-fractional-shell-data
    field
      receipts : List ShellPairReceipt
      coefficient localED : ℚ

      liveBlockIsShellPairSum :
        P.deepFarLowDeepHighHighSigned ≡ sumSignedMass receipts

      shellPairBudgetsPaidByLocalED :
        sumBudget receipts ≤ coefficient * localED

  open PhysicalDeepFarLowDeepHHFractionalShellData public

  deepFarLowDeepHHFractionalShellPayment :
    (D : PhysicalDeepFarLowDeepHHFractionalShellData) →
    P.deepFarLowDeepHighHighSigned ≤ coefficient D * localED D
  deepFarLowDeepHHFractionalShellPayment D =
    subst
      (_≤ coefficient D * localED D)
      (sym (liveBlockIsShellPairSum D))
      (ℚP.≤-trans
        (shellPairFoldPaid (receipts D))
        (shellPairBudgetsPaidByLocalED D))

deepFarLowDeepHHBipartiteShellFoldClosed : Bool
deepFarLowDeepHHBipartiteShellFoldClosed = true

deepFarLowDeepHHLiteralShellPairExtractorInhabitedHere : Bool
deepFarLowDeepHHLiteralShellPairExtractorInhabitedHere = false

deepFarLowDeepHHPerShellNullBernsteinEstimateInhabitedHere : Bool
deepFarLowDeepHHPerShellNullBernsteinEstimateInhabitedHere = false

deepFarLowDeepHHShellFoldIntroducesCardinalityFactor : Bool
deepFarLowDeepHHShellFoldIntroducesCardinalityFactor = false

deepFarLowDeepHHShellFoldIntroducesPostulate : Bool
deepFarLowDeepHHShellFoldIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false
