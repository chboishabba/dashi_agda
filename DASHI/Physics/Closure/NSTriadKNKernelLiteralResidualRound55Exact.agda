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
-- DASHI CONTRIBUTION
--
-- Define the literal kernel term as the residual of the signed localized
-- identity AFTER already-owned pieces have been removed.  A residual split
-- carries duplicate + cancelling + independent contributions.  When the
-- cancellation is exact and the independent residual is zero, this file
-- constructs the Round-51 literal kernel constituent, the Round-52 pre-tax
-- reduction and the Round-53 structural zero-tax witness without any positive
-- kernel estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

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
    independentZero : independent ≡ 0ℚ

open LiteralKernelResidualSplit public

literalKernelResidual : LiteralKernelResidualSplit → ℚ
literalKernelResidual split =
  duplicateOwned split + (cancelLeft split + cancelRight split) + independent split

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
  ; ownershipOutcome = Literal.exactZero
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

literalKernelIndependentZero :
  ∀ {environment : Owner.TaxEnvironment}
    (split : LiteralKernelResidualSplit) →
  Zero.PhysicalIndependentKernelZero environment
    (literalKernelInstantiation split)
    (literalKernelReduction split)
literalKernelIndependentZero split = record
  { independentRemainderIsZero = independentZero split }

literalKernelAfterCancellation :
  (split : LiteralKernelResidualSplit) →
  literalKernelResidual split ≡ duplicateOwned split
literalKernelAfterCancellation split
  rewrite cancellation split | independentZero split = refl

kernelResidualZeroBranchConstructed : Bool
kernelResidualZeroBranchConstructed = true

kernelResidualZeroBranchConstructedIsTrue :
  kernelResidualZeroBranchConstructed ≡ true
kernelResidualZeroBranchConstructedIsTrue = refl
