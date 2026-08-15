module DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact where

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
-- Round 53 proved that the nine-owner B-coefficients do not modify Luo's
-- multiplicative predecessor coefficient.  They live in the additive physical
-- flux correction.  The remaining downstream numerical question is therefore
-- not an abstract "global floor": it is exactly how much additive correction
-- the fixed-block induction can absorb.
--
-- The mature rational induction already exposes that capacity:
--
--   correction_n <= (r-q) C r^n.
--
-- This file identifies that quantity as the fixed-shift correction headroom and
-- proves that, once the literal owner remainder is the physical flux correction
-- and that correction is the block-induction correction, the COMPLETE owner
-- remainder obeys the exact headroom bound.  No new conservative cap is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNFixedShiftCoefficientSeparationRound53Exact as Round53

fixedShiftCorrectionHeadroom :
  Block.RationalFixedBlockDecay → Nat → ℚ
fixedShiftCorrectionHeadroom block n =
  (Block.r block - Block.q block)
    * Block.scaledTarget (Block.constant block) (Block.r block) n

record PhysicalOwnerBlockCorrectionIdentification
    (balances : Nat → Nine.NineOwnerCriticalBalance)
    (recursionData : Fixed.FixedShiftRecursionPhysicalData)
    (block : Block.RationalFixedBlockDecay) : Set where
  field
    ownerToFlux :
      Round53.SameObjectOwnerToFixedShiftCorrection balances recursionData

    physicalFluxCorrectionIsBlockCorrection : ∀ n →
      Fixed.integratedFluxCorrection recursionData n
      ≡ Block.correction block n

    blockShiftCoefficientIsPhysical :
      Block.q block ≡ Fixed.correctedShiftCoefficient recursionData

open PhysicalOwnerBlockCorrectionIdentification public

physicalFluxCorrectionBelowFixedShiftHeadroom :
  ∀ {balances recursionData block} →
  (identification : PhysicalOwnerBlockCorrectionIdentification
    balances recursionData block) →
  (n : Nat) →
  Fixed.integratedFluxCorrection recursionData n
  ≤ fixedShiftCorrectionHeadroom block n
physicalFluxCorrectionBelowFixedShiftHeadroom {block = block}
    identification n =
  subst
    (λ left → left ≤ fixedShiftCorrectionHeadroom block n)
    (sym (physicalFluxCorrectionIsBlockCorrection identification n))
    (Block.correctionBudget block n)

physicalOwnerRemainderBelowFixedShiftHeadroom :
  ∀ {balances recursionData block} →
  (identification : PhysicalOwnerBlockCorrectionIdentification
    balances recursionData block) →
  (n : Nat) →
  Nine.admissibleRemainder (balances n)
  ≤ fixedShiftCorrectionHeadroom block n
physicalOwnerRemainderBelowFixedShiftHeadroom
    {balances} {recursionData} {block} identification n =
  let
    same = ownerToFlux identification
    fluxBound =
      physicalFluxCorrectionBelowFixedShiftHeadroom identification n
  in
  subst
    (λ left → left ≤ fixedShiftCorrectionHeadroom block n)
    (sym (Round53.ownerRemainderIsFluxCorrection same n))
    fluxBound

physicalOwnerAggregateBelowFixedShiftHeadroom :
  ∀ {balances recursionData block} →
  (identification : PhysicalOwnerBlockCorrectionIdentification
    balances recursionData block) →
  (n : Nat) →
  Round53.ownerAggregateDataRemainder (balances n)
    + Round53.ownerAggregateCriticalCoefficient (balances n)
      * Owner.integralCritical (Nine.environment (balances n))
  ≤ fixedShiftCorrectionHeadroom block n
physicalOwnerAggregateBelowFixedShiftHeadroom
    {balances} {recursionData} {block} identification n =
  let
    same = ownerToFlux identification
    fluxBound =
      physicalFluxCorrectionBelowFixedShiftHeadroom identification n
    fluxAsAggregate =
      Round53.ownerCriticalAggregateLivesInAdditiveCorrection same n
  in
  subst
    (λ left → left ≤ fixedShiftCorrectionHeadroom block n)
    fluxAsAggregate
    fluxBound

fixedShiftHeadroomUsesPhysicalCoefficient :
  ∀ {balances recursionData block} →
  (identification : PhysicalOwnerBlockCorrectionIdentification
    balances recursionData block) →
  (n : Nat) →
  fixedShiftCorrectionHeadroom block n
  ≡
  (Block.r block - Fixed.correctedShiftCoefficient recursionData)
    * Block.scaledTarget (Block.constant block) (Block.r block) n
fixedShiftHeadroomUsesPhysicalCoefficient {block = block}
    identification n =
  cong
    (λ selected →
      (Block.r block - selected)
        * Block.scaledTarget (Block.constant block) (Block.r block) n)
    (blockShiftCoefficientIsPhysical identification)

fixedShiftCorrectionHeadroomIsExistingBlockBudget : Bool
fixedShiftCorrectionHeadroomIsExistingBlockBudget = true

ownerAggregateFitsExactFixedShiftHeadroomAfterSameObjectIdentification : Bool
ownerAggregateFitsExactFixedShiftHeadroomAfterSameObjectIdentification = true

physicalOwnerBlockCorrectionIdentificationConstructed : Bool
physicalOwnerBlockCorrectionIdentificationConstructed = false

fixedShiftCorrectionHeadroomIsExistingBlockBudgetIsTrue :
  fixedShiftCorrectionHeadroomIsExistingBlockBudget ≡ true
fixedShiftCorrectionHeadroomIsExistingBlockBudgetIsTrue = refl

ownerAggregateFitsExactFixedShiftHeadroomAfterSameObjectIdentificationIsTrue :
  ownerAggregateFitsExactFixedShiftHeadroomAfterSameObjectIdentification ≡ true
ownerAggregateFitsExactFixedShiftHeadroomAfterSameObjectIdentificationIsTrue = refl
