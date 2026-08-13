module DASHI.Physics.Closure.NSTriadKNKernelLiteralResidualRound55Exact where

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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Round 55 introduced the signed residual split.  Round 56 removes a subtle
-- circularity in that first version: `independent = 0` is NO LONGER a field of
-- the residual split itself.  The raw literal residual may genuinely contain a
-- surviving independent kernel.  Exact signed cancellation is performed first,
-- and only a separate `IndependentZeroBranch` witness can promote the kernel to
-- the Round-53 structural zero-tax route.
--
-- Hence the binary physical test is now real:
--
--   literal residual = duplicate + independent,
--
-- and `literal residual != duplicate` mechanically forces
-- `independent != 0`.  This makes K_independent=0 falsifiable rather than
-- encoding it in the datatype.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; trans)

import DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact as Signed
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNKernelLiteralizationAuditRound51Exact as Literal
import DASHI.Physics.Closure.NSTriadKNKernelPreTaxReductionRound52Exact as PreTax
import DASHI.Physics.Closure.NSTriadKNKernelIndependentZeroOwnerRound53Exact as Zero
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

record LiteralKernelResidualSplit : Set where
  field
    duplicateOwned cancelLeft cancelRight independent : ℚ
    cancellation : cancelLeft + cancelRight ≡ 0ℚ

open LiteralKernelResidualSplit public

literalKernelResidual : LiteralKernelResidualSplit → ℚ
literalKernelResidual split =
  duplicateOwned split + (cancelLeft split + cancelRight split) + independent split

-- Until the independent remainder is proved zero, the conservative ownership
-- outcome is `independentKernel`.  Deduplication is represented separately by
-- the pre-tax reduction below.
literalKernelInstantiation :
  LiteralKernelResidualSplit → Literal.PhysicalKernelConstituentInstantiation
literalKernelInstantiation split = record
  { literalKernelContribution = literalKernelResidual split
  ; signedKernelConstituent =
      Signed.signed-constituent Signed.kernelSource Tax.kernel refl
        (literalKernelResidual split)
  ; sourceIsKernelSource = refl
  ; ownerIsKernel = refl
  ; signedContributionIsLiteralKernel = refl
  ; ownershipOutcome = Literal.independentKernel
  }

literalKernelReduction :
  (split : LiteralKernelResidualSplit) →
  PreTax.KernelPreTaxSignedReduction (literalKernelInstantiation split)
literalKernelReduction split = record
  { duplicateOwnedContribution = duplicateOwned split
  ; exactCancellationContribution = cancelLeft split + cancelRight split
  ; independentRemainder = independent split
  ; literalDecomposition = refl
  ; cancellationIsExactZero = cancellation split
  }

literalKernelAfterCancellation :
  (split : LiteralKernelResidualSplit) →
  literalKernelResidual split ≡ duplicateOwned split + independent split
literalKernelAfterCancellation split =
  PreTax.literalAfterCancellation (literalKernelReduction split)

record IndependentZeroBranch (split : LiteralKernelResidualSplit) : Set where
  field
    independentZero : independent split ≡ 0ℚ

open IndependentZeroBranch public

literalKernelIndependentZero :
  ∀ {environment : Owner.TaxEnvironment}
    (split : LiteralKernelResidualSplit) →
  IndependentZeroBranch split →
  Zero.PhysicalIndependentKernelZero environment
    (literalKernelInstantiation split)
    (literalKernelReduction split)
literalKernelIndependentZero split zeroBranch = record
  { independentRemainderIsZero = independentZero zeroBranch }

literalKernelEqualsDuplicateOnZeroBranch :
  (split : LiteralKernelResidualSplit) →
  IndependentZeroBranch split →
  literalKernelResidual split ≡ duplicateOwned split
literalKernelEqualsDuplicateOnZeroBranch split zeroBranch =
  trans
    (literalKernelAfterCancellation split)
    (trans
      (cong (duplicateOwned split +_) (independentZero zeroBranch))
      (solve (duplicateOwned split ∷ [])))
  where
  open import Agda.Builtin.List using (_∷_; [])

nonDuplicateLiteralForcesIndependentNonzero :
  (split : LiteralKernelResidualSplit) →
  literalKernelResidual split ≢ duplicateOwned split →
  independent split ≢ 0ℚ
nonDuplicateLiteralForcesIndependentNonzero split differs independentIsZero =
  differs
    (trans
      (literalKernelAfterCancellation split)
      (trans
        (cong (duplicateOwned split +_) independentIsZero)
        (solve (duplicateOwned split ∷ []))))
  where
  open import Agda.Builtin.List using (_∷_; [])

zeroIndependentBranchIsSeparatePhysicalObligation : Bool
zeroIndependentBranchIsSeparatePhysicalObligation = true

kernelResidualCancellationBeforePositivity : Bool
kernelResidualCancellationBeforePositivity = true

zeroIndependentBranchIsSeparatePhysicalObligationIsTrue :
  zeroIndependentBranchIsSeparatePhysicalObligation ≡ true
zeroIndependentBranchIsSeparatePhysicalObligationIsTrue = refl

kernelResidualCancellationBeforePositivityIsTrue :
  kernelResidualCancellationBeforePositivity ≡ true
kernelResidualCancellationBeforePositivityIsTrue = refl
