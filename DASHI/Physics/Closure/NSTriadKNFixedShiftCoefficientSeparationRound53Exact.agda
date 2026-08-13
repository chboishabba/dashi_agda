module DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 52 correctly observed that the abstract block-decay bridge left the
-- proposition `RecursionCoefficientStrictlyBelowOne` opaque.  The source-shaped
-- fixed-shift data already separates two mathematically different objects:
--
--   rho_shift * D_(p-b) + integratedFluxCorrection_p.
--
-- Here rho_shift is definitionally the corrected Luo shift coefficient.  The
-- nine-owner B coefficients aggregate instead in `admissibleRemainder` as
--
--   sumData + (sum B_i) * integralCritical.
--
-- Therefore the B_i do NOT enter the multiplicative predecessor coefficient at
-- this interface.  Any downstream restriction on the B_i can only arise when
-- the additive owner remainder is identified with / bounded by the physical
-- flux-correction majorant and then compared with the dyadic decay target.
--
-- This resolves the specific Round-52 ambiguity without inventing an extra
-- scalar cap.  It does NOT claim that the additive correction comparison is
-- already closed physically.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed

physicalFixedShiftRecursionCoefficientFormula :
  Fixed.FixedShiftRecursionPhysicalData → ℚ
physicalFixedShiftRecursionCoefficientFormula data =
  Fixed.correctedShiftCoefficient data

physicalFixedShiftAdditiveCorrectionFormula :
  Fixed.FixedShiftRecursionPhysicalData → Nat → ℚ
physicalFixedShiftAdditiveCorrectionFormula data shell =
  Fixed.integratedFluxCorrection data shell

fixedShiftRhsFormula :
  (data : Fixed.FixedShiftRecursionPhysicalData) →
  (shell : Nat) →
  physicalFixedShiftRecursionCoefficientFormula data
    * Fixed.cutoffDissipation data (Fixed.predecessorByFixedShift data shell)
    + physicalFixedShiftAdditiveCorrectionFormula data shell
  ≡
  Fixed.correctedShiftCoefficient data
    * Fixed.cutoffDissipation data (Fixed.predecessorByFixedShift data shell)
    + Fixed.integratedFluxCorrection data shell
fixedShiftRhsFormula data shell = refl

ownerAggregateCriticalCoefficient :
  Nine.NineOwnerCriticalBalance → ℚ
ownerAggregateCriticalCoefficient balance =
  Owner.sumCriticalCoefficient
    (Owner.nineOwnerList (Nine.family balance))

ownerAggregateDataRemainder :
  Nine.NineOwnerCriticalBalance → ℚ
ownerAggregateDataRemainder balance =
  Owner.sumDataRemainder
    (Owner.nineOwnerList (Nine.family balance))

ownerRemainderFormula :
  (balance : Nine.NineOwnerCriticalBalance) →
  Nine.admissibleRemainder balance
  ≡ ownerAggregateDataRemainder balance
      + ownerAggregateCriticalCoefficient balance
        * Owner.integralCritical (Nine.environment balance)
ownerRemainderFormula balance = refl

record SameObjectOwnerToFixedShiftCorrection
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (data : Fixed.FixedShiftRecursionPhysicalData) : Set where
  field
    ownerRemainderIsFluxCorrection : ∀ shell →
      Nine.admissibleRemainder (balances shell)
      ≡ Fixed.integratedFluxCorrection data shell

open SameObjectOwnerToFixedShiftCorrection public

ownerCriticalAggregateLivesInAdditiveCorrection :
  ∀ {balances data} →
  SameObjectOwnerToFixedShiftCorrection balances data →
  (shell : Nat) →
  physicalFixedShiftAdditiveCorrectionFormula data shell
  ≡ ownerAggregateDataRemainder (balances shell)
      + ownerAggregateCriticalCoefficient (balances shell)
        * Owner.integralCritical (Nine.environment (balances shell))
ownerCriticalAggregateLivesInAdditiveCorrection {balances} {data} same shell =
  trans
    (sym (ownerRemainderIsFluxCorrection same shell))
    (ownerRemainderFormula (balances shell))

fixedShiftCoefficientSeparatedFromOwnerAggregate : Bool
fixedShiftCoefficientSeparatedFromOwnerAggregate = true

remainingBCapQuestionMovedToCorrectionComparison : Bool
remainingBCapQuestionMovedToCorrectionComparison = true

physicalOwnerToFluxCorrectionSameObjectConstructed : Bool
physicalOwnerToFluxCorrectionSameObjectConstructed = false

fixedShiftCoefficientSeparatedFromOwnerAggregateIsTrue :
  fixedShiftCoefficientSeparatedFromOwnerAggregate ≡ true
fixedShiftCoefficientSeparatedFromOwnerAggregateIsTrue = refl

remainingBCapQuestionMovedToCorrectionComparisonIsTrue :
  remainingBCapQuestionMovedToCorrectionComparison ≡ true
remainingBCapQuestionMovedToCorrectionComparisonIsTrue = refl
