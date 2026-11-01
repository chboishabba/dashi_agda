module DASHI.Physics.Closure.NSTriadKNKernelPreTaxReductionRound52Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Refine Round 51's kernel literalization order.  Once the literal signed PDE
-- contribution exists, remove any exactly duplicated already-owned amount and
-- any proved signed cancellation BEFORE assigning multidegree or positive tax.
-- The only quantity eligible for later classification is the independent
-- remainder.
--
--   literal = duplicate + cancelled + independent,
--   cancelled = 0
--
-- gives
--
--   literal = duplicate + independent.
--
-- If the whole literal kernel is duplicate, the independent remainder is zero;
-- if it is exact cancellation, the independent remainder is zero.  Neither case
-- licenses a second positive kernel tax.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNKernelLiteralizationAuditRound51Exact as Literal

record KernelPreTaxSignedReduction
    (physical : Literal.PhysicalKernelConstituentInstantiation) : Set where
  field
    duplicateOwnedContribution : ℚ
    exactCancellationContribution : ℚ
    independentRemainder : ℚ

    literalDecomposition :
      Literal.literalKernelContribution physical
      ≡ duplicateOwnedContribution
        + exactCancellationContribution
        + independentRemainder

    cancellationIsExactZero : exactCancellationContribution ≡ 0ℚ

open KernelPreTaxSignedReduction public

literalAfterCancellation :
  ∀ {physical}
    (reduction : KernelPreTaxSignedReduction physical) →
  Literal.literalKernelContribution physical
  ≡ duplicateOwnedContribution reduction + independentRemainder reduction
literalAfterCancellation reduction =
  trans
    (literalDecomposition reduction)
    (trans
      (cong
        (λ cancelled →
          duplicateOwnedContribution reduction
          + cancelled
          + independentRemainder reduction)
        (cancellationIsExactZero reduction))
      (solve
        ( duplicateOwnedContribution reduction
        ∷ independentRemainder reduction
        ∷ [])))

record FullyDuplicatedKernel
    (physical : Literal.PhysicalKernelConstituentInstantiation)
    (reduction : KernelPreTaxSignedReduction physical) : Set where
  field
    independentRemainderIsZero : independentRemainder reduction ≡ 0ℚ

open FullyDuplicatedKernel public

fullyDuplicatedKernelLeavesNoIndependentTaxTerm :
  ∀ {physical reduction} →
  FullyDuplicatedKernel physical reduction →
  independentRemainder reduction ≡ 0ℚ
fullyDuplicatedKernelLeavesNoIndependentTaxTerm = independentRemainderIsZero

record FullyCancelledKernel
    (physical : Literal.PhysicalKernelConstituentInstantiation)
    (reduction : KernelPreTaxSignedReduction physical) : Set where
  field
    duplicateContributionIsZero : duplicateOwnedContribution reduction ≡ 0ℚ
    independentRemainderIsZero : independentRemainder reduction ≡ 0ℚ

open FullyCancelledKernel public

fullyCancelledKernelLiteralIsZero :
  ∀ {physical reduction} →
  FullyCancelledKernel physical reduction →
  Literal.literalKernelContribution physical ≡ 0ℚ
fullyCancelledKernelLiteralIsZero {reduction = reduction} cancelled =
  trans
    (literalAfterCancellation reduction)
    (trans
      (cong
        (λ duplicate → duplicate + independentRemainder reduction)
        (duplicateContributionIsZero cancelled))
      (trans
        (cong (0ℚ +_) (FullyCancelledKernel.independentRemainderIsZero cancelled))
        (solve [])))

kernelDeduplicationPrecedesMultidegree : Bool
kernelDeduplicationPrecedesMultidegree = true

kernelExactCancellationPrecedesPositiveEstimate : Bool
kernelExactCancellationPrecedesPositiveEstimate = true

physicalKernelPreTaxReductionConstructed : Bool
physicalKernelPreTaxReductionConstructed = false

kernelDeduplicationPrecedesMultidegreeIsTrue :
  kernelDeduplicationPrecedesMultidegree ≡ true
kernelDeduplicationPrecedesMultidegreeIsTrue = refl
