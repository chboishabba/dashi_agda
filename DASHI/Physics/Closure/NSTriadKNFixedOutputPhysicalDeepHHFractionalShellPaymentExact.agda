module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact where

------------------------------------------------------------------------
-- S2b2d1b2 / B3: DHH-DHH FRACTIONAL-SHELL FOLD
--
-- R326/R574 own the radical-free low-output component estimate and R136 owns
-- cutoff-uniform HH gap summation.  The surviving leaf is intra-shell
-- aggregation on the literal filtered DHH block.  This owner makes that seam
-- explicit and folds theorem-bearing shell receipts without an output-count
-- or shell-count tax.
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
import DASHI.Physics.Closure.NSTriadKNHeterochiralHHGapEnvelopeRound136Exact as R136
import DASHI.Physics.Closure.NSTriadKNPhysicalInnerCommutatorLowOutputBoundRound326Exact as R326
import DASHI.Physics.Closure.NSTriadKNR106ComponentLowOutputBoundRound574Exact as R574

F : C3.RealField _
F = Rational.rationalRealField

module DeepHHPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output

  record ShellReceipt : Set where
    constructor shell-receipt
    field
      signedMass budget : ℚ
      paid : signedMass ≤ budget

  open ShellReceipt public

  sumSignedMass : List ShellReceipt → ℚ
  sumSignedMass [] = 0ℚ
  sumSignedMass (receipt ∷ rest) =
    signedMass receipt + sumSignedMass rest

  sumBudget : List ShellReceipt → ℚ
  sumBudget [] = 0ℚ
  sumBudget (receipt ∷ rest) =
    budget receipt + sumBudget rest

  shellFoldPaid :
    (receipts : List ShellReceipt) →
    sumSignedMass receipts ≤ sumBudget receipts
  shellFoldPaid [] = ℚP.≤-refl
  shellFoldPaid (receipt ∷ rest) =
    ℚP.+-mono-≤ (paid receipt) (shellFoldPaid rest)

  record PhysicalDeepHHFractionalShellData : Set where
    constructor physical-deep-hh-fractional-shell-data
    field
      receipts : List ShellReceipt
      coefficient localED : ℚ

      liveBlockIsShellSum :
        P.deepHighHighHighHighSigned ≡ sumSignedMass receipts

      shellBudgetsPaidByLocalED :
        sumBudget receipts ≤ coefficient * localED

  open PhysicalDeepHHFractionalShellData public

  deepHHFractionalShellPayment :
    (D : PhysicalDeepHHFractionalShellData) →
    P.deepHighHighHighHighSigned ≤ coefficient D * localED D
  deepHHFractionalShellPayment D =
    subst
      (_≤ coefficient D * localED D)
      (sym (liveBlockIsShellSum D))
      (ℚP.≤-trans
        (shellFoldPaid (receipts D))
        (shellBudgetsPaidByLocalED D))

------------------------------------------------------------------------
-- Source receipts kept theorem-bearing rather than copied as status prose.
------------------------------------------------------------------------

r136GapSummationReceipt :
  R136.round136HHGapIndexSummationClosed ≡ true
r136GapSummationReceipt = R136.round136HHGapIndexSummationClosedIsTrue

r574ComponentLowOutputReceipt :
  R574.round574AllFourPhysicalHelicalComponentsHaveLowOutputBound ≡ true
r574ComponentLowOutputReceipt =
  R574.round574AllFourPhysicalHelicalComponentsHaveLowOutputBoundIsTrue

deepHHShellFoldClosed : Bool
deepHHShellFoldClosed = true

deepHHLiteralFilteredBlockShellExtractorInhabitedHere : Bool
deepHHLiteralFilteredBlockShellExtractorInhabitedHere = false

deepHHIntraShellSignedL2AggregationInhabitedHere : Bool
deepHHIntraShellSignedL2AggregationInhabitedHere =
  R136.round136HHIntraShellSignedL2AggregationClosed

deepHHShellFoldIntroducesCardinalityFactor : Bool
deepHHShellFoldIntroducesCardinalityFactor = false

deepHHShellFoldIntroducesPostulate : Bool
deepHHShellFoldIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false
