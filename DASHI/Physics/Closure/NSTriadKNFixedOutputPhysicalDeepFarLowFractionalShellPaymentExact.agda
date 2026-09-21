module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowFractionalShellPaymentExact where

------------------------------------------------------------------------
-- S2b2d1b2 / B1: DFL-DFL FRACTIONAL-SHELL PAYMENT COMPILER
--
-- R466 already proves the finite Bernstein -> R234 E*D payment for one literal
-- dyadic shell package.  This owner performs the missing finite shell fold
-- without inserting absolute values or a shell-count factor.
--
-- The ONLY physical input left exposed is the same-object extraction:
--
--   live DFL-DFL signed block = sum shell productMass
--
-- together with the final allocation of the summed R466 shell budgets into
-- the literal local-ED currency.  No postulate is introduced.
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
import DASHI.Physics.Closure.NSTriadKNRationalFiniteBernstein as Bernstein
import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234
import DASHI.Physics.Closure.NSTriadKNDeepFarLowDyadicBernsteinWeldRound466Exact as R466
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay

F : C3.RealField _
F = Rational.rationalRealField

module DeepFarLowPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output

  record ShellReceipt : Set₁ where
    constructor shell-receipt
    field
      Slot : Set
      data : R466.PhysicalDeepFarLowDyadicData Slot

  open ShellReceipt public

  shellMass : ShellReceipt → ℚ
  shellMass receipt = R466.productMass (data receipt)

  shellBudget : ShellReceipt → ℚ
  shellBudget receipt =
    Bernstein.coefficientNormSquared
      (R466.retainedCoefficients (data receipt))
    * R234.highDissipation
        (R466.toR234DeepFarLowPayment (data receipt))

  shellPaid : (receipt : ShellReceipt) → shellMass receipt ≤ shellBudget receipt
  shellPaid receipt =
    R466.deepFarLowDyadicMassPaidByEnergyDissipation (data receipt)

  sumShellMass : List ShellReceipt → ℚ
  sumShellMass [] = 0ℚ
  sumShellMass (receipt ∷ rest) =
    shellMass receipt + sumShellMass rest

  sumShellBudget : List ShellReceipt → ℚ
  sumShellBudget [] = 0ℚ
  sumShellBudget (receipt ∷ rest) =
    shellBudget receipt + sumShellBudget rest

  shellFoldPaid :
    (receipts : List ShellReceipt) →
    sumShellMass receipts ≤ sumShellBudget receipts
  shellFoldPaid [] = ℚP.≤-refl
  shellFoldPaid (receipt ∷ rest) =
    ℚP.+-mono-≤ (shellPaid receipt) (shellFoldPaid rest)

  record PhysicalDeepFarLowFractionalShellData : Set₁ where
    constructor physical-deep-far-low-fractional-shell-data
    field
      receipts : List ShellReceipt
      coefficient localED : ℚ

      liveBlockIsShellMass :
        P.deepFarLowFarLowSigned ≡ sumShellMass receipts

      shellBudgetsPaidByLocalED :
        sumShellBudget receipts ≤ coefficient * localED

  open PhysicalDeepFarLowFractionalShellData public

  deepFarLowFarLowFractionalShellPayment :
    (D : PhysicalDeepFarLowFractionalShellData) →
    P.deepFarLowFarLowSigned ≤ coefficient D * localED D
  deepFarLowFarLowFractionalShellPayment D =
    subst
      (_≤ coefficient D * localED D)
      (sym (liveBlockIsShellMass D))
      (ℚP.≤-trans
        (shellFoldPaid (receipts D))
        (shellBudgetsPaidByLocalED D))

deepFarLowShellFoldCompilerClosed : Bool
deepFarLowShellFoldCompilerClosed = true

deepFarLowShellFoldReusesR466 : Bool
deepFarLowShellFoldReusesR466 = true

deepFarLowLiteralFilteredBlockShellExtractorInhabitedHere : Bool
deepFarLowLiteralFilteredBlockShellExtractorInhabitedHere = false

deepFarLowFractionalShellLocalEDAllocationInhabitedHere : Bool
deepFarLowFractionalShellLocalEDAllocationInhabitedHere = false

deepFarLowShellFoldIntroducesPostulate : Bool
deepFarLowShellFoldIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false

deepFarLowShellFoldCompilerClosedIsTrue :
  deepFarLowShellFoldCompilerClosed ≡ true
deepFarLowShellFoldCompilerClosedIsTrue = refl
