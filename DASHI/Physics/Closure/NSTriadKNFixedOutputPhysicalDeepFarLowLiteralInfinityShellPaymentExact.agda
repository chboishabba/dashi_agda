module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowLiteralInfinityShellPaymentExact where

------------------------------------------------------------------------
-- B1 / LITERAL INFINITY-SHELL PAYMENT FOLD
--
-- This is the literal-shell replacement for the older R466-backed B1 fold.
-- Each receipt is indexed by an actual duplicate-free InfinityShellSupport
-- package and is paid directly by
-- NSTriadKNLiteralInfinityShellBernsteinPaymentExact.
--
-- Consequently the remaining physical seam no longer has to manufacture the
-- synthetic Luo eightfold carrier used by R466.  It only has to extract:
--
--   * the actual shell number and shell support,
--   * the physical coefficient/high-energy/high-derivative quantities,
--   * the exact live-block = sum shell-mass identity, and
--   * the allocation of the summed shell budgets to local E*D.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
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
import DASHI.Physics.Closure.NSTriadKNLiteralInfinityShellBernsteinPaymentExact as LiteralShell
import DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount as ShellCount
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay

F : C3.RealField _
F = Rational.rationalRealField

module LiteralDeepFarLowPayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output

  -- The support list itself is no longer a physical obligation.  We may use
  -- the exact duplicate-free outer cube as the support and encode inactive
  -- modes by zero coefficients.  Only the coefficient/mass/energy data remain
  -- source-specific.
  canonicalLiteralInfinityShellData :
    (shell : Nat) →
    (coefficient : Z3.FourierMode → ℚ) →
    (highEnergy highDerivativeCoefficient productMass : ℚ) →
    0ℚ ≤ highEnergy →
    0ℚ ≤ highDerivativeCoefficient →
    LiteralShell.NatQ.natAsRational (ShellCount.infinityCubeModeCount shell)
      ≤ highDerivativeCoefficient →
    productMass
      ≤
      let coefficients =
        LiteralShell.Cube.map coefficient
          (ShellCount.shellModes (ShellCount.canonicalInfinityShellSupport shell))
      in
      Rational.square (Bernstein.coefficientSum coefficients) * highEnergy →
    LiteralShell.LiteralInfinityShellBernsteinData shell
  canonicalLiteralInfinityShellData shell coefficient highEnergy highDerivativeCoefficient
      productMass highEnergyNN highDerivativeCoefficientNN cubePaid massBound = record
    { LiteralShell.support = ShellCount.canonicalInfinityShellSupport shell
    ; LiteralShell.coefficient = coefficient
    ; LiteralShell.highEnergy = highEnergy
    ; LiteralShell.highDerivativeCoefficient = highDerivativeCoefficient
    ; LiteralShell.productMass = productMass
    ; LiteralShell.highEnergyNN = highEnergyNN
    ; LiteralShell.highDerivativeCoefficientNN = highDerivativeCoefficientNN
    ; LiteralShell.outerCubeCardinalityPaidByDerivative = cubePaid
    ; LiteralShell.productMassBelowFiniteBernsteinInput = massBound
    }

  record LiteralShellReceipt : Set₁ where
    constructor literal-shell-receipt
    field
      shell : Nat
      data : LiteralShell.LiteralInfinityShellBernsteinData shell

  open LiteralShellReceipt public

  shellMass : LiteralShellReceipt → ℚ
  shellMass receipt = LiteralShell.productMass (data receipt)

  shellBudget : LiteralShellReceipt → ℚ
  shellBudget receipt =
    Bernstein.coefficientNormSquared
      (LiteralShell.coefficients (data receipt))
    * R234.highDissipation
        (LiteralShell.toR234DeepFarLowPayment (data receipt))

  shellPaid :
    (receipt : LiteralShellReceipt) →
    shellMass receipt ≤ shellBudget receipt
  shellPaid receipt =
    LiteralShell.literalInfinityShellBernsteinPaidByEnergyDissipation
      (data receipt)

  sumShellMass : List LiteralShellReceipt → ℚ
  sumShellMass [] = 0ℚ
  sumShellMass (receipt ∷ rest) =
    shellMass receipt + sumShellMass rest

  sumShellBudget : List LiteralShellReceipt → ℚ
  sumShellBudget [] = 0ℚ
  sumShellBudget (receipt ∷ rest) =
    shellBudget receipt + sumShellBudget rest

  shellFoldPaid :
    (receipts : List LiteralShellReceipt) →
    sumShellMass receipts ≤ sumShellBudget receipts
  shellFoldPaid [] = ℚP.≤-refl
  shellFoldPaid (receipt ∷ rest) =
    ℚP.+-mono-≤ (shellPaid receipt) (shellFoldPaid rest)

  record PhysicalDeepFarLowLiteralShellData : Set₁ where
    constructor physical-deep-far-low-literal-shell-data
    field
      receipts : List LiteralShellReceipt
      coefficient localED : ℚ

      liveBlockIsLiteralShellMass :
        P.deepFarLowFarLowSigned ≡ sumShellMass receipts

      literalShellBudgetsPaidByLocalED :
        sumShellBudget receipts ≤ coefficient * localED

  open PhysicalDeepFarLowLiteralShellData public

  deepFarLowFarLowLiteralShellPayment :
    (D : PhysicalDeepFarLowLiteralShellData) →
    P.deepFarLowFarLowSigned ≤ coefficient D * localED D
  deepFarLowFarLowLiteralShellPayment D =
    subst
      (_≤ coefficient D * localED D)
      (sym (liveBlockIsLiteralShellMass D))
      (ℚP.≤-trans
        (shellFoldPaid (receipts D))
        (literalShellBudgetsPaidByLocalED D))

deepFarLowLiteralInfinityShellFoldCompilerClosed : Bool
deepFarLowLiteralInfinityShellFoldCompilerClosed = true

deepFarLowLiteralInfinityShellFoldUsesR466 : Bool
deepFarLowLiteralInfinityShellFoldUsesR466 = false

deepFarLowLiteralInfinityShellFoldUsesSyntheticEightfoldCarrier : Bool
deepFarLowLiteralInfinityShellFoldUsesSyntheticEightfoldCarrier = false

deepFarLowLiteralInfinityShellSupportChoiceClosed : Bool
deepFarLowLiteralInfinityShellSupportChoiceClosed = true

deepFarLowLiteralInfinityShellSupportChoiceClosedIsTrue :
  deepFarLowLiteralInfinityShellSupportChoiceClosed ≡ true
deepFarLowLiteralInfinityShellSupportChoiceClosedIsTrue = refl

deepFarLowLiteralInfinityShellPhysicalExtractorInhabitedHere : Bool
deepFarLowLiteralInfinityShellPhysicalExtractorInhabitedHere = false

deepFarLowLiteralInfinityShellLocalEDAllocationInhabitedHere : Bool
deepFarLowLiteralInfinityShellLocalEDAllocationInhabitedHere = false

deepFarLowLiteralInfinityShellFoldIntroducesPostulate : Bool
deepFarLowLiteralInfinityShellFoldIntroducesPostulate = false

deepFarLowLiteralInfinityShellFoldCompilerClosedIsTrue :
  deepFarLowLiteralInfinityShellFoldCompilerClosed ≡ true
deepFarLowLiteralInfinityShellFoldCompilerClosedIsTrue = refl

deepFarLowLiteralInfinityShellFoldUsesR466IsFalse :
  deepFarLowLiteralInfinityShellFoldUsesR466 ≡ false
deepFarLowLiteralInfinityShellFoldUsesR466IsFalse = refl

deepFarLowLiteralInfinityShellFoldUsesSyntheticEightfoldCarrierIsFalse :
  deepFarLowLiteralInfinityShellFoldUsesSyntheticEightfoldCarrier ≡ false
deepFarLowLiteralInfinityShellFoldUsesSyntheticEightfoldCarrierIsFalse = refl
