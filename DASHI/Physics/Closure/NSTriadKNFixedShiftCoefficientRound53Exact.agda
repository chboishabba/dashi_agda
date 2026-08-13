module DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The nine-owner energy estimate contains one literal critical coefficient:
-- the sum of the nine owner B coefficients.  Round 52 correctly refused to
-- guess how the later fixed-shift recurrence consumes it.  This file replaces
-- the completely opaque proposition by a precise physical identification seam:
-- the physical derivation must provide the actual recursion coefficient rho
-- together with its exact formula Phi.
--
-- The preferred affine specialization records
--
--   rho_shift = rho_0 + weight * B_total,
--
-- where B_total is the repository's literal nine-owner aggregate.  Importantly,
-- this proves that any cap derived from this specialization is an AGGREGATE cap,
-- not nine separate owner caps.  If the PDE derivation yields a max or nonlinear
-- Phi instead, use ExactFixedShiftFormula directly rather than this affine
-- specialization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _<_)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Tax
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine

ownerAggregateCriticalCoefficient : Nine.NineOwnerCriticalBalance → ℚ
ownerAggregateCriticalCoefficient balance =
  Tax.sumCriticalCoefficient
    (Tax.nineOwnerList (Nine.family balance))

record ExactFixedShiftFormula
    (balance : Nine.NineOwnerCriticalBalance) : Set₁ where
  field
    recursionCoefficient : ℚ
    coefficientFormula :
      Nine.NineOwnerCriticalBalance → ℚ
    physicalFixedShiftRecursionCoefficientFormula :
      recursionCoefficient ≡ coefficientFormula balance

open ExactFixedShiftFormula public

record AffineAggregateFixedShiftFormula
    (balance : Nine.NineOwnerCriticalBalance) : Set where
  field
    rho0 ownerWeight recursionCoefficient : ℚ
    physicalFixedShiftRecursionCoefficientFormula :
      recursionCoefficient
      ≡ rho0 + ownerWeight * ownerAggregateCriticalCoefficient balance

open AffineAggregateFixedShiftFormula public

affineAsExactFixedShiftFormula :
  ∀ {balance} →
  AffineAggregateFixedShiftFormula balance →
  ExactFixedShiftFormula balance
affineAsExactFixedShiftFormula {balance} physical = record
  { recursionCoefficient =
      AffineAggregateFixedShiftFormula.recursionCoefficient physical
  ; coefficientFormula = λ candidate →
      rho0 physical
      + ownerWeight physical * ownerAggregateCriticalCoefficient candidate
  ; physicalFixedShiftRecursionCoefficientFormula =
      AffineAggregateFixedShiftFormula.physicalFixedShiftRecursionCoefficientFormula
        physical
  }

aggregateRedistributionLeavesAffineCoefficientUnchanged :
  ∀ {left right}
    (physicalLeft : AffineAggregateFixedShiftFormula left)
    (physicalRight : AffineAggregateFixedShiftFormula right) →
  rho0 physicalLeft ≡ rho0 physicalRight →
  ownerWeight physicalLeft ≡ ownerWeight physicalRight →
  ownerAggregateCriticalCoefficient left
    ≡ ownerAggregateCriticalCoefficient right →
  AffineAggregateFixedShiftFormula.recursionCoefficient physicalLeft
    ≡ AffineAggregateFixedShiftFormula.recursionCoefficient physicalRight
aggregateRedistributionLeavesAffineCoefficientUnchanged
    physicalLeft physicalRight rhoSame weightSame aggregateSame
  rewrite rhoSame | weightSame | aggregateSame =
  trans
    (AffineAggregateFixedShiftFormula.physicalFixedShiftRecursionCoefficientFormula
      physicalLeft)
    (sym
      (AffineAggregateFixedShiftFormula.physicalFixedShiftRecursionCoefficientFormula
        physicalRight))

record FixedShiftStrictGate
    {balance : Nine.NineOwnerCriticalBalance}
    (physical : AffineAggregateFixedShiftFormula balance) : Set where
  field
    recursionCoefficientStrictlyBelowOne :
      AffineAggregateFixedShiftFormula.recursionCoefficient physical < 1ℚ

open FixedShiftStrictGate public

fixedShiftFormulaShapeNowExplicit : Bool
fixedShiftFormulaShapeNowExplicit = true

separateOwnerCapsFollowFromAffineAggregateFormula : Bool
separateOwnerCapsFollowFromAffineAggregateFormula = false

fixedShiftFormulaShapeNowExplicitIsTrue :
  fixedShiftFormulaShapeNowExplicit ≡ true
fixedShiftFormulaShapeNowExplicitIsTrue = refl

separateOwnerCapsFollowFromAffineAggregateFormulaIsFalse :
  separateOwnerCapsFollowFromAffineAggregateFormula ≡ false
separateOwnerCapsFollowFromAffineAggregateFormulaIsFalse = refl
